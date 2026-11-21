-- Prove2me | Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine
-- name    : RandomSizeStable_Stability_RankCutCertEngine
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-20T17:26:09.774188+00:00
-- url     : https://prove2.me/theorems/c87f0708-6575-403b-b83f-f94164684b57
-- title:
--   Rank-cut certificate at D* — a kernel-evaluated Taylor-model checker
-- statement:
--   Computable checkers whose `true` result certifies `CellOK` or `P1OK` (from the bundle `RandomSizeStable_Stability_RankCutCert`), meant to be run by `decide +kernel`.
--
--   - Integers are pairs of naturals `Z` $=\langle p, n\rangle$ standing for $p - n$; a fixed-point integer $z$ stands for the real `toR z` $= z/2^{64}$.
--   - A `Box` is a product of three intervals $|x_i - m_i/2^{64}| \le h_i/2^{64}$; a first-order Taylor model `TM` $(c, g_0, g_1, g_2, r)$ is `Valid B f t` when $|f(x) - c - \sum_i g_i (x_i - m_i)| \le r$ (all scaled by $2^{-64}$) on the box.
--   - Arithmetic on models (`add`, `sub`, `mul`, `qmul` by a rational, `cq` rational constant) rounds by floor division and adds every rounding error to the remainder; `pows`, `phiT`, `PhiT`, `QT` build the models of $x^k$, $\phi$, $\Phi$ and of the divided difference $Q(x,y) = (\Phi(y) - \Phi(x))/(y - x)$ as a polynomial.
--   - `run`/`runAll` walk a subdivision tree given as a preorder code (0 = leaf, $i+1$ = bisect along coordinate $i$) and evaluate a leaf test on every leaf box.
--   - A cell is a `CellData` (centre and half-width of the $p$-interval, the rational multiplier coefficients, two trees). In coordinates $w, p, v \in [0,1]\times[p_0,p_1]\times[0,1]$ with $a = p(1-w)$ and $A = p + (1-p)v$, the leaf tests `leaf1`/`leaf2` (interior cells), `leafN1`/`leafN2` (cells near $p = 1$, with $B/(1-p)$ written through $Q$), `leaf1`/`leafZ2` (cells near $p = 0$, with case 2 divided by $p$) check that a lower bound of the corresponding slack is $\ge 0$ for every piece of `tail` and `rho` the box can meet; `leafP1` is the one-variable test at $p = 1$.
--   - `cellCheck`, `cellNCheck`, `cell0Check` and `p1Check` combine the root tests (multipliers nonnegative at the cell ends) with the tree walks.
--
--   This bundle is not from the paper; the paper checks its own certificate with 1.15 million exact interval boxes outside Lean.
-- source:
--   Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission 1342 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1342.pdf), a kernel-evaluated Taylor-model checker for the rank-cut certificate (not from the paper).

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert

set_option autoImplicit false

/-!
A kernel-evaluated first-order Taylor-model checker for the rank-cut certificate at D*
(integers as pairs of naturals, fixed point 2^-64; cell checkers for interior cells, cells near 0 and 1, and p = 1).
-/


namespace RandomSizeStable.Stability.RankCutCert.Dev

/-- The integer `p - n`. -/
structure Z where
  p : Nat
  n : Nat

def zero : Z := ⟨0, 0⟩
def zadd (a b : Z) : Z := ⟨Nat.add a.p b.p, Nat.add a.n b.n⟩
def zsub (a b : Z) : Z := ⟨Nat.add a.p b.n, Nat.add a.n b.p⟩
def zneg (a : Z) : Z := ⟨a.n, a.p⟩
def zmul (a b : Z) : Z :=
  ⟨Nat.add (Nat.mul a.p b.p) (Nat.mul a.n b.n), Nat.add (Nat.mul a.p b.n) (Nat.mul a.n b.p)⟩
def zabs (a : Z) : Z := ⟨Nat.add (Nat.sub a.p a.n) (Nat.sub a.n a.p), 0⟩
def zaddk (a : Z) (k : Nat) : Z := ⟨Nat.add a.p k, a.n⟩
/-- Floor division of `P - N` by 2^64. -/
def zq' (P N : Nat) : Z :=
  ⟨Nat.shiftRight (Nat.sub P N) 64,
   Nat.shiftRight (Nat.add (Nat.sub N P) 18446744073709551615) 64⟩
/-- Floor division by 2^64. -/
def zq (a : Z) : Z := zq' a.p a.n
/-- Floor division by `d` (`d = 0` gives 0). -/
def zdiv (a : Z) (d : Nat) : Z :=
  ⟨Nat.div (Nat.sub a.p a.n) d, Nat.div (Nat.add (Nat.sub a.n a.p) (Nat.sub d 1)) d⟩
/-- `a ≤ b`. -/
def zle (a b : Z) : Bool := Nat.ble (Nat.add a.p b.n) (Nat.add b.p a.n)
/-- `a < b`. -/
def zlt (a b : Z) : Bool := Nat.blt (Nat.add a.p b.n) (Nat.add b.p a.n)

/-- The fixed-point scale 2^64. -/
def SN : Nat := 18446744073709551616
def S : Z := ⟨18446744073709551616, 0⟩

structure TM where
  c : Z
  g0 : Z
  g1 : Z
  g2 : Z
  r : Z

structure Box where
  m0 : Z
  m1 : Z
  m2 : Z
  h0 : Z
  h1 : Z
  h2 : Z

/-- An upper bound (times S) for the linear part's absolute value on the box. -/
def gsum (B : Box) (t : TM) : Z :=
  zaddk (zq (zadd (zadd (zmul (zabs t.g0) B.h0) (zmul (zabs t.g1) B.h1)) (zmul (zabs t.g2) B.h2))) 1

/-- Rounding slack of one rounded affine part on the box. -/
def hsum (B : Box) : Z := zaddk (zq (zadd (zadd B.h0 B.h1) B.h2)) 3

def add (x y : TM) : TM :=
  ⟨zadd x.c y.c, zadd x.g0 y.g0, zadd x.g1 y.g1, zadd x.g2 y.g2, zadd x.r y.r⟩

def sub (x y : TM) : TM :=
  ⟨zsub x.c y.c, zsub x.g0 y.g0, zsub x.g1 y.g1, zsub x.g2 y.g2, zadd x.r y.r⟩

def mul2 (B : Box) (x y : TM) (Rx Ry : Z) : TM :=
  ⟨zq (zmul x.c y.c), zq (zadd (zmul x.c y.g0) (zmul y.c x.g0)),
    zq (zadd (zmul x.c y.g1) (zmul y.c x.g1)), zq (zadd (zmul x.c y.g2) (zmul y.c x.g2)),
    zadd (zq (zadd (zadd (zadd (zmul Rx Ry) (zmul (zadd (zabs x.c) Rx) y.r))
      (zmul (zadd (zabs y.c) Ry) x.r)) (zmul x.r y.r))) (hsum B)⟩

def mul (B : Box) (x y : TM) : TM := mul2 B x y (gsum B x) (gsum B y)

/-- Multiplication by the rational `n / d` (`d > 0`). -/
def qmul (B : Box) (n : Z) (d : Nat) (x : TM) : TM :=
  ⟨zdiv (zmul n x.c) d, zdiv (zmul n x.g0) d, zdiv (zmul n x.g1) d, zdiv (zmul n x.g2) d,
    zadd (zaddk (zdiv (zmul (zabs n) x.r) d) 1) (hsum B)⟩

/-- The exact constant `k / S`. -/
def cnst (k : Z) : TM := ⟨k, zero, zero, zero, zero⟩

/-- The rational constant `n / d` (`d > 0`), within `1/S`. -/
def cq (n : Z) (d : Nat) : TM := ⟨zdiv (zmul n S) d, zero, zero, zero, ⟨1, 0⟩⟩

/-- The degenerate box {0}. -/
def B0 : Box := ⟨zero, zero, zero, zero, zero, zero⟩

/-- A constant model computed on `B0`, with its linear part dropped. -/
def constOf (t : TM) : TM := ⟨t.c, zero, zero, zero, t.r⟩

def var0 (B : Box) : TM := ⟨B.m0, S, zero, zero, zero⟩
def var1 (B : Box) : TM := ⟨B.m1, zero, S, zero, zero⟩
def var2 (B : Box) : TM := ⟨B.m2, zero, zero, S, zero⟩

/-- Lower bound (times S) of a valid model on the box. -/
def lower (B : Box) (t : TM) : Z := zsub (zsub t.c (gsum B t)) t.r

/-- Upper bound (times S) of a valid model on the box. -/
def upper (B : Box) (t : TM) : Z := zadd (zadd t.c (gsum B t)) t.r

/-- One rounded-up squaring step. -/
def sqS (u : Z) : Z := zaddk (zq (zmul u u)) 1

/-- Upper bound (times S) of `(u/S)^32` for `u ≥ 0`. -/
def upow32 (u : Z) : Z := sqS (sqS (sqS (sqS (sqS u))))

/-- Powers x^2, x^3, x^32, x^33 of a model. -/
structure Pw where
  x1 : TM
  x2 : TM
  x3 : TM
  x32 : TM
  x33 : TM

/-- Squaring. -/
def sqT (B : Box) (x : TM) : TM := mul B x x

def pow32a (B : Box) (x x2 : TM) (U : Z) : TM :=
  cond (zle zero (lower B x) && zle U ⟨17179869184, 0⟩)
    ⟨zdiv U 2, zero, zero, zero, zsub U (zdiv U 2)⟩
    (sqT B (sqT B (sqT B (sqT B x2))))

/-- The 32nd power from x and x^2: an enclosure when x ≥ 0 and x^32 ≤ 2^-30 on the box,
repeated squaring otherwise. -/
def pow32 (B : Box) (x x2 : TM) : TM := pow32a B x x2 (upow32 (upper B x))

def pows2 (B : Box) (x x2 : TM) (x32 : TM) : Pw := ⟨x, x2, mul B x2 x, x32, mul B x32 x⟩

def pows1 (B : Box) (x x2 : TM) : Pw := pows2 B x x2 (pow32 B x x2)

def pows (B : Box) (x : TM) : Pw := pows1 B x (mul B x x)

/-- phi(x) = 19/73 x + 35/146 x^2 + x^32/2. -/
def phiT (B : Box) (P : Pw) : TM :=
  add (add (qmul B ⟨19, 0⟩ 73 P.x1) (qmul B ⟨35, 0⟩ 146 P.x2)) (qmul B ⟨1, 0⟩ 2 P.x32)

/-- Phi(x) = 19/146 x^2 + 35/438 x^3 + x^33/66. -/
def PhiT (B : Box) (P : Pw) : TM :=
  add (add (qmul B ⟨19, 0⟩ 146 P.x2) (qmul B ⟨35, 0⟩ 438 P.x3)) (qmul B ⟨1, 0⟩ 66 P.x33)

/-! ## Subdivision trees -/

def splitL (B : Box) : Nat → Box
  | 0 => ⟨zsub B.m0 (zdiv B.h0 2), B.m1, B.m2, zdiv B.h0 2, B.h1, B.h2⟩
  | 1 => ⟨B.m0, zsub B.m1 (zdiv B.h1 2), B.m2, B.h0, zdiv B.h1 2, B.h2⟩
  | _ => ⟨B.m0, B.m1, zsub B.m2 (zdiv B.h2 2), B.h0, B.h1, zdiv B.h2 2⟩

def splitR (B : Box) : Nat → Box
  | 0 => ⟨zadd B.m0 (zdiv B.h0 2), B.m1, B.m2, zdiv B.h0 2, B.h1, B.h2⟩
  | 1 => ⟨B.m0, zadd B.m1 (zdiv B.h1 2), B.m2, B.h0, zdiv B.h1 2, B.h2⟩
  | _ => ⟨B.m0, B.m1, zadd B.m2 (zdiv B.h2 2), B.h0, B.h1, zdiv B.h2 2⟩

/-- `p - n` is even. -/
def zeven (a : Z) : Bool := Nat.beq (Nat.mod (Nat.add a.p a.n) 2) 0

def evenH (B : Box) : Nat → Bool
  | 0 => zeven B.h0
  | 1 => zeven B.h1
  | _ => zeven B.h2

/-- Walk a preorder code (0 = leaf, i+1 = split along dimension i), checking every leaf.
Returns the unread rest of the code. -/
def run (leaf : Box → Bool) : Nat → Box → List Nat → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | _ + 1, B, 0 :: rest => if leaf B then some rest else none
  | n + 1, B, (i + 1) :: rest =>
    if evenH B i then
      match run leaf n (splitL B i) rest with
      | some rest' => run leaf n (splitR B i) rest'
      | none => none
    else none

def runAll (leaf : Box → Bool) (B : Box) (code : List Nat) : Bool :=
  match run leaf 64 B code with
  | some [] => true
  | _ => false

/-! ## Semantics -/

/-- Real value of a fixed-point integer `p - n`. -/
noncomputable def toR (a : Z) : ℝ := ((a.p : ℝ) - (a.n : ℝ)) / (SN : ℝ)

def InBox (B : Box) (x0 x1 x2 : ℝ) : Prop :=
  |x0 - toR B.m0| ≤ toR B.h0 ∧ |x1 - toR B.m1| ≤ toR B.h1 ∧ |x2 - toR B.m2| ≤ toR B.h2

/-- The affine part of a model at a point. -/
noncomputable def aff (B : Box) (t : TM) (x0 x1 x2 : ℝ) : ℝ :=
  toR t.c + toR t.g0 * (x0 - toR B.m0) + toR t.g1 * (x1 - toR B.m1) + toR t.g2 * (x2 - toR B.m2)

def Valid (B : Box) (f : ℝ → ℝ → ℝ → ℝ) (t : TM) : Prop :=
  ∀ x0 x1 x2 : ℝ, InBox B x0 x1 x2 → |f x0 x1 x2 - aff B t x0 x1 x2| ≤ toR t.r

end RandomSizeStable.Stability.RankCutCert.Dev


namespace RandomSizeStable.Stability.RankCutCert.Dev

/-- The rational n / d (n = p - n' as a pair). -/
structure Q where
  n : Z
  d : Nat

noncomputable def qR (q : Q) : ℝ := (((q.n.p : ℝ) - (q.n.n : ℝ))) / (q.d : ℝ)

/-! Global witness rationals (equal to the values in `Defs`). -/

def loQ : Fin 9 → Q :=
  ![⟨⟨49, 0⟩, 100⟩, ⟨⟨21, 0⟩, 50⟩, ⟨⟨7, 0⟩, 20⟩, ⟨⟨3, 0⟩, 10⟩, ⟨⟨13, 0⟩, 50⟩, ⟨⟨21, 0⟩, 100⟩,
    ⟨⟨7, 0⟩, 50⟩, ⟨⟨3, 0⟩, 100⟩, ⟨⟨0, 0⟩, 1⟩]
def hiQ : Fin 9 → Q :=
  ![⟨⟨2840189, 0⟩, 5000000⟩, ⟨⟨49, 0⟩, 100⟩, ⟨⟨21, 0⟩, 50⟩, ⟨⟨7, 0⟩, 20⟩, ⟨⟨3, 0⟩, 10⟩,
    ⟨⟨13, 0⟩, 50⟩, ⟨⟨21, 0⟩, 100⟩, ⟨⟨7, 0⟩, 50⟩, ⟨⟨3, 0⟩, 100⟩]
def etaQ : Fin 9 → Q :=
  ![⟨⟨350540817, 0⟩, 186650000⟩, ⟨⟨362108663961, 0⟩, 186650000000⟩, ⟨⟨93594398139, 0⟩, 46662500000⟩,
    ⟨⟨193849071801, 0⟩, 93325000000⟩, ⟨⟨198756643239, 0⟩, 93325000000⟩,
    ⟨⟨202963133043, 0⟩, 93325000000⟩, ⟨⟨416793031413, 0⟩, 186650000000⟩,
    ⟨⟨108317112453, 0⟩, 46662500000⟩, ⟨⟨231006398403, 0⟩, 93325000000⟩]
def hQ : Fin 9 → Q :=
  ![⟨⟨19140111, 0⟩, 19531250⟩, ⟨⟨4890063411, 0⟩, 5000000000⟩, ⟨⟨1219935897, 0⟩, 1250000000⟩,
    ⟨⟨4868611269, 0⟩, 5000000000⟩, ⟨⟨9720888189, 0⟩, 10000000000⟩, ⟨⟨2426730247, 0⟩, 2500000000⟩,
    ⟨⟨4844454213, 0⟩, 5000000000⟩, ⟨⟨386464593, 0⟩, 400000000⟩, ⟨⟨4806920783, 0⟩, 5000000000⟩]
def bQ : Q := ⟨⟨2840189, 0⟩, 5000000⟩
def C0Q : Q := ⟨⟨113609, 0⟩, 200000⟩
def muQ : Q := ⟨⟨1085, 0⟩, 4818⟩

def cqQ (q : Q) : TM := cq q.n q.d
def qm (B : Box) (q : Q) (x : TM) : TM := qmul B q.n q.d x

def phiConst (q : Q) : TM := phiT B0 (pows B0 (cqQ q))

/-- eta_j phi(h_j) - h_j. -/
def ktT (j : Fin 9) : TM := constOf (sub (qm B0 (etaQ j) (phiConst (hQ j))) (cqQ (hQ j)))
/-- mu - phi(lo_j). -/
def psiLoT (j : Fin 9) : TM := constOf (sub (cqQ muQ) (phiConst (loQ j)))
/-- mu - phi(b). -/
def psiBT : TM := constOf (sub (cqQ muQ) (phiConst bQ))

/-- floor(q S). -/
def floorS (q : Q) : Z := zdiv (zmul q.n S) q.d
/-- ceil(q S). -/
def ceilS (q : Q) : Z := zneg (zdiv (zneg (zmul q.n S)) q.d)

/-- Tail pieces: 0 = (y ≤ b), 1 = (b < y < h_j), 2 = (y ≥ h_j); is the piece possible for
y ∈ [lo/S, hi/S]? -/
def tailOK (j : Fin 9) (lo hi : Z) : Nat → Bool
  | 0 => zle lo (floorS bQ)
  | 1 => zlt (floorS bQ) hi && zlt lo (ceilS (hQ j))
  | _ => zle (ceilS (hQ j)) hi

/-- rho pieces: 0 = (y < lo_j), 1 = (lo_j ≤ y ≤ hi_j or y ≥ b), 2 = (hi_j < y < b). -/
def rhoOK (j : Fin 9) (lo hi : Z) : Nat → Bool
  | 0 => zlt lo (ceilS (loQ j))
  | 1 => (zle (ceilS (loQ j)) hi && zle lo (floorS (hiQ j))) || zle (ceilS bQ) hi
  | _ => zlt (floorS (hiQ j)) hi && zlt lo (ceilS bQ)

/-- The tail on a piece, from the models of y and phi(y). -/
def tailT (B : Box) (j : Fin 9) (y phiy : TM) : Nat → TM
  | 0 => cqQ C0Q
  | 1 => sub (add (ktT j) y) (qm B (etaQ j) phiy)
  | _ => cnst zero

/-- mu - phi(rho_j y) on a piece. -/
def psiT (j : Fin 9) (phiy : TM) : Nat → TM
  | 0 => psiLoT j
  | 1 => sub (cqQ muQ) phiy
  | _ => psiBT

structure CellData where
  pm : Z
  ph : Z
  l0 : Q
  l1 : Q
  l2 : Q
  t0 : Fin 9 → Q
  t1 : Fin 9 → Q
  tree1 : List Nat
  tree2 : List Nat

/-- D(p) = mu p - Phi(p). -/
def DT (B : Box) (P : TM) : TM := sub (qm B muQ P) (PhiT B (pows B P))

/-- The multiplier F of E: (1-p), times D(p) when l2 ≠ 0. -/
def mulF (cd : CellData) (B : Box) (P : TM) : TM :=
  cond (Nat.beq cd.l2.n.p cd.l2.n.n) (sub (cnst S) P) (mul B (DT B P) (sub (cnst S) P))

/-- M = lam * F. -/
def mulM (cd : CellData) (B : Box) (P : TM) : TM :=
  cond (Nat.beq cd.l2.n.p cd.l2.n.n) (add (cqQ cd.l0) (qm B cd.l1 P))
    (add (mul B (add (cqQ cd.l0) (qm B cd.l1 P)) (DT B P)) (qm B cd.l2 (mul B P (sub (cnst S) P))))

def tauT (cd : CellData) (B : Box) (j : Fin 9) (P : TM) : TM :=
  mul B P (add (cqQ (cd.t0 j)) (qm B (cd.t1 j) P))

def pcs : List Nat := [0, 1, 2]

/-! Case 1 (A = 1), x2 unused. -/

def fam1 (B : Box) (a F MB phia tau : TM) (alo ahi : Z) (j : Fin 9) : Bool :=
  pcs.all fun ka => !(tailOK j alo ahi ka) ||
    pcs.all fun kr => !(rhoOK j alo ahi kr) ||
      zle zero (lower B (sub (mul B F (sub (sub (tailT B j a phia ka) a) (mul B tau (psiT j phia kr)))) MB))

def leaf1c (cd : CellData) (B : Box) (P a F MB phia : TM) : Bool :=
  (List.finRange 9).all fun j => fam1 B a F MB phia (tauT cd B j P) (lower B a) (upper B a) j

def leaf1b (cd : CellData) (B : Box) (P a : TM) (pa py : Pw) : Bool :=
  leaf1c cd B P a (mulF cd B P)
    (mul B (mulM cd B P) (sub (add (PhiT B pa) (cqQ muQ)) (add (PhiT B py) (qm B muQ P)))) (phiT B pa)

def leaf1a (cd : CellData) (B : Box) (P s : TM) : Bool :=
  leaf1b cd B P (sub P s) (pows B (sub P s)) (pows B (sub (cnst S) s))

def leaf1 (cd : CellData) (B : Box) : Bool := leaf1a cd B (var1 B) (mul B (var1 B) (var0 B))

/-! Case 2 (r ≥ A). -/

def fam2 (B : Box) (a A F MB phia phiA tau : TM) (alo ahi Alo Ahi : Z) (j : Fin 9) : Bool :=
  pcs.all fun ka => !(tailOK j alo ahi ka) ||
    pcs.all fun kA => !(tailOK j Alo Ahi kA) ||
      pcs.all fun kr => !(rhoOK j Alo Ahi kr) ||
        zle zero (lower B (sub (mul B F (sub (sub (sub (tailT B j a phia ka) (tailT B j A phiA kA)) a)
          (mul B tau (psiT j phiA kr)))) MB))

def leaf2c (cd : CellData) (B : Box) (P a A F MB phia phiA : TM) : Bool :=
  (List.finRange 9).all fun j =>
    fam2 B a A F MB phia phiA (tauT cd B j P) (lower B a) (upper B a) (lower B A) (upper B A) j

def leaf2b (cd : CellData) (B : Box) (P a A : TM) (pa pA py : Pw) : Bool :=
  leaf2c cd B P a A (mulF cd B P)
    (mul B (mulM cd B P) (sub (add (PhiT B pa) (PhiT B pA)) (add (PhiT B py) (qm B muQ P))))
    (phiT B pa) (phiT B pA)

def leaf2a (cd : CellData) (B : Box) (P s a A : TM) : Bool :=
  leaf2b cd B P a A (pows B a) (pows B A) (pows B (sub A s))

def leaf2 (cd : CellData) (B : Box) : Bool :=
  leaf2a cd B (var1 B) (mul B (var1 B) (var0 B)) (sub (var1 B) (mul B (var1 B) (var0 B)))
    (add (var1 B) (mul B (sub (cnst S) (var1 B)) (var2 B)))

/-- The p-only box of the cell. -/
def pBox (cd : CellData) : Box := ⟨zero, cd.pm, zero, zero, cd.ph, zero⟩

/-- q0 + q1 (x / S) ≥ 0, exactly, with positive denominators. -/
def linNonneg (q0 q1 : Q) (x : Z) : Bool :=
  Nat.blt 0 q0.d && Nat.blt 0 q1.d &&
  zle zero (zadd (zmul (zmul q0.n ⟨q1.d, 0⟩) S) (zmul (zmul q1.n ⟨q0.d, 0⟩) x))

/-- lam ≥ 0, tau_j ≥ 0 and D > 0 on the whole cell (linear parts checked at both ends). -/
def rootOK (cd : CellData) : Bool :=
  linNonneg cd.l0 cd.l1 (zsub cd.pm cd.ph) && linNonneg cd.l0 cd.l1 (zadd cd.pm cd.ph) &&
  zle zero cd.l2.n &&
  (Nat.beq cd.l2.n.p cd.l2.n.n || zlt zero (lower (pBox cd) (DT (pBox cd) (var1 (pBox cd))))) &&
  (List.finRange 9).all fun j =>
    linNonneg (cd.t0 j) (cd.t1 j) (zsub cd.pm cd.ph) && linNonneg (cd.t0 j) (cd.t1 j) (zadd cd.pm cd.ph)

def half : Z := ⟨9223372036854775808, 0⟩

def root1 (cd : CellData) : Box := ⟨half, cd.pm, zero, half, cd.ph, zero⟩
def root2 (cd : CellData) : Box := ⟨half, cd.pm, half, half, cd.ph, half⟩

def cellCheck (cd : CellData) : Bool :=
  zle zero cd.ph && zlt zero (zsub cd.pm cd.ph) && zlt (zadd cd.pm cd.ph) S && rootOK cd &&
  runAll (leaf1 cd) (root1 cd) cd.tree1 && runAll (leaf2 cd) (root2 cd) cd.tree2

/-! ## The statement a successful check proves -/

noncomputable def lamv (cd : CellData) (p : ℝ) : ℝ :=
  (qR cd.l0 + qR cd.l1 * p) / (1 - p) + qR cd.l2 * p / (mu * p - Phi p)

noncomputable def tauv (cd : CellData) (j : Fin 9) (p : ℝ) : ℝ :=
  p * (qR (cd.t0 j) + qR (cd.t1 j) * p)

def CellStmt (cd : CellData) : Prop :=
  ∀ p : ℝ, toR (zsub cd.pm cd.ph) ≤ p → p ≤ toR (zadd cd.pm cd.ph) →
    0 ≤ lamv cd p ∧ (∀ j, 0 ≤ tauv cd j p) ∧
    ∀ (j : Fin 9) (a A : ℝ), 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 →
      0 ≤ G1 j (lamv cd p) (tauv cd j p) a p ∧ 0 ≤ G2 j (lamv cd p) (tauv cd j p) a p A

end RandomSizeStable.Stability.RankCutCert.Dev


namespace RandomSizeStable.Stability.RankCutCert.Dev

def H32c (B : Box) (x y x2 y2 x4 y4 x8 y8 x16 y16 x32 : TM) : TM :=
  add (mul B y (mul B (mul B (mul B (mul B (add x y) (add x2 y2)) (add x4 y4)) (add x8 y8))
    (add x16 y16))) x32

def QT1 (B : Box) (x y x2 y2 : TM) : TM :=
  add (add (qmul B ⟨19, 0⟩ 146 (add x y)) (qmul B ⟨35, 0⟩ 438 (add (add x2 (mul B x y)) y2)))
    (qmul B ⟨1, 0⟩ 66 (H32c B x y x2 y2 (sqT B x2) (sqT B y2) (sqT B (sqT B x2)) (sqT B (sqT B y2))
      (sqT B (sqT B (sqT B x2))) (sqT B (sqT B (sqT B y2))) (sqT B (sqT B (sqT B (sqT B x2))))))

/-- Q(x, y). -/
def QT (B : Box) (x y : TM) : TM := QT1 B x y (sqT B x) (sqT B y)

/-! Last cell. -/

def famN1 (B : Box) (a L Bt phia tau : TM) (alo ahi : Z) (j : Fin 9) : Bool :=
  pcs.all fun ka => !(tailOK j alo ahi ka) ||
    pcs.all fun kr => !(rhoOK j alo ahi kr) ||
      zle zero (lower B (sub (sub (sub (tailT B j a phia ka) a) (mul B tau (psiT j phia kr)))
        (mul B L Bt)))

def leafN1b (cd : CellData) (B : Box) (P a L Bt : TM) (pa : Pw) : Bool :=
  (List.finRange 9).all fun j =>
    famN1 B a L Bt (phiT B pa) (tauT cd B j P) (lower B a) (upper B a) j

def leafN1a (cd : CellData) (B : Box) (P s a : TM) : Bool :=
  leafN1b cd B P a (add (cqQ cd.l0) (qm B cd.l1 P)) (sub (cqQ muQ) (QT B a (sub (cnst S) s))) (pows B a)

def leafN1 (cd : CellData) (B : Box) : Bool :=
  leafN1a cd B (var1 B) (mul B (var1 B) (var0 B)) (sub (var1 B) (mul B (var1 B) (var0 B)))

def famN2 (B : Box) (a A L Bt phia phiA tau : TM) (alo ahi Alo Ahi : Z) (j : Fin 9) : Bool :=
  pcs.all fun ka => !(tailOK j alo ahi ka) ||
    pcs.all fun kA => !(tailOK j Alo Ahi kA) ||
      pcs.all fun kr => !(rhoOK j Alo Ahi kr) ||
        zle zero (lower B (sub (sub (sub (sub (tailT B j a phia ka) (tailT B j A phiA kA)) a)
          (mul B tau (psiT j phiA kr))) (mul B L Bt)))

def leafN2b (cd : CellData) (B : Box) (P a A L Bt : TM) (pa pA : Pw) : Bool :=
  (List.finRange 9).all fun j =>
    famN2 B a A L Bt (phiT B pa) (phiT B pA) (tauT cd B j P) (lower B a) (upper B a) (lower B A)
      (upper B A) j

def leafN2a (cd : CellData) (B : Box) (P V a t A : TM) : Bool :=
  leafN2b cd B P a A (add (cqQ cd.l0) (qm B cd.l1 P))
    (sub (sub (cqQ muQ) (mul B V (QT B a (add a t)))) (mul B (sub (cnst S) V) (QT B A (cnst S))))
    (pows B a) (pows B A)

def leafN2 (cd : CellData) (B : Box) : Bool :=
  leafN2a cd B (var1 B) (var2 B) (sub (var1 B) (mul B (var1 B) (var0 B)))
    (mul B (sub (cnst S) (var1 B)) (var2 B))
    (add (var1 B) (mul B (sub (cnst S) (var1 B)) (var2 B)))

/-- l2 = 0 and lam ≥ 0, tau_j ≥ 0 at both ends (both linear). -/
def rootOK0 (cd : CellData) : Bool :=
  linNonneg cd.l0 cd.l1 (zsub cd.pm cd.ph) && linNonneg cd.l0 cd.l1 (zadd cd.pm cd.ph) &&
  Nat.beq cd.l2.n.p 0 && Nat.beq cd.l2.n.n 0 &&
  (List.finRange 9).all fun j =>
    linNonneg (cd.t0 j) (cd.t1 j) (zsub cd.pm cd.ph) && linNonneg (cd.t0 j) (cd.t1 j) (zadd cd.pm cd.ph)

/-- A cell [p0, p1] near 1, 0 < p0, p1 ≤ 1 (statement for p < 1). -/
def cellNCheck (cd : CellData) : Bool :=
  zle zero cd.ph && zlt zero (zsub cd.pm cd.ph) && zle (zadd cd.pm cd.ph) S &&
  rootOK0 cd && runAll (leafN1 cd) (root1 cd) cd.tree1 && runAll (leafN2 cd) (root2 cd) cd.tree2

def CellNStmt (cd : CellData) : Prop :=
  ∀ p : ℝ, toR (zsub cd.pm cd.ph) ≤ p → p ≤ toR (zadd cd.pm cd.ph) → p < 1 →
    0 ≤ lamv cd p ∧ (∀ j, 0 ≤ tauv cd j p) ∧
    ∀ (j : Fin 9) (a A : ℝ), 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 →
      0 ≤ G1 j (lamv cd p) (tauv cd j p) a p ∧ 0 ≤ G2 j (lamv cd p) (tauv cd j p) a p A

/-! p = 1, with tau_j(1) = t0_j + t1_j of the last cell. -/

def famP1 (B : Box) (a phia tau1 : TM) (alo ahi : Z) (j : Fin 9) : Bool :=
  pcs.all fun ka => !(tailOK j alo ahi ka) ||
    pcs.all fun kr => !(rhoOK j alo ahi kr) ||
      zle zero (lower B (sub (sub (tailT B j a phia ka) a) (mul B tau1 (psiT j phia kr))))

def leafP1 (cd : CellData) (B : Box) : Bool :=
  (List.finRange 9).all fun j =>
    famP1 B (var0 B) (phiT B (pows B (var0 B))) (add (cqQ (cd.t0 j)) (cqQ (cd.t1 j)))
      (lower B (var0 B)) (upper B (var0 B)) j

def rootP1 : Box := ⟨half, zero, zero, half, zero, zero⟩

def p1Check (cd : CellData) (tree : List Nat) : Bool :=
  ((List.finRange 9).all fun j => linNonneg (cd.t0 j) (cd.t1 j) S) && runAll (leafP1 cd) rootP1 tree

def P1Stmt (cd : CellData) : Prop :=
  (∀ j : Fin 9, 0 ≤ tauv cd j 1) ∧ ∀ (j : Fin 9) (a : ℝ), 0 ≤ a → a ≤ 1 → a + tauv cd j 1 * (mu - phi (rho j a)) ≤ tail j a

/-! First cell (0, p1]: case 2 scaled by p. -/

/-- K(a) = 19/146 + 35/438 a + a^31/66, with a^31 = a^16 a^8 a^4 a^3 / ... by squarings. -/
def KT1 (B : Box) (a a2 a4 a8 a16 : TM) : TM :=
  add (add (cq ⟨19, 0⟩ 146) (qmul B ⟨35, 0⟩ 438 a))
    (qmul B ⟨1, 0⟩ 66 (mul B a16 (mul B a8 (mul B a4 (mul B a2 a)))))

def KT (B : Box) (a : TM) : TM :=
  KT1 B a (sqT B a) (sqT B (sqT B a)) (sqT B (sqT B (sqT B a))) (sqT B (sqT B (sqT B (sqT B a))))

def famZ2 (B : Box) (a A om p1 Lp1Bp phia phiA tau' : TM) (alo ahi Alo Ahi : Z) (u : TM) (j : Fin 9) : Bool :=
  pcs.all fun ka => !(tailOK j alo ahi ka) ||
    pcs.all fun kA => !(tailOK j Alo Ahi kA) ||
      pcs.all fun kr => !(rhoOK j Alo Ahi kr) ||
        zle zero (lower B (sub (mul B om (sub (sub (sub (tailT B j a phia ka) (tailT B j A phiA kA))
          (mul B p1 u)) (mul B p1 (mul B tau' (psiT j phiA kr))))) Lp1Bp))

def leafZ2b (cd : CellData) (B : Box) (P u a A p1 : TM) (Lp1Bp : TM) (pa pA : Pw) : Bool :=
  (List.finRange 9).all fun j =>
    famZ2 B a A (sub (cnst S) P) p1 Lp1Bp (phiT B pa) (phiT B pA)
      (add (cqQ (cd.t0 j)) (qm B (cd.t1 j) P)) (lower B a) (upper B a) (lower B A) (upper B A) u j

def leafZ2a (cd : CellData) (B : Box) (P W u a A : TM) : Bool :=
  leafZ2b cd B P u a A (cnst (zadd cd.pm cd.ph))
    (mul B (mul B (cnst (zadd cd.pm cd.ph)) (add (cqQ cd.l0) (qm B cd.l1 P)))
      (sub (add (mul B (mul B (mul B u u) P) (KT B a)) (mul B W (QT B (sub A (mul B P W)) A))) (cqQ muQ)))
    (pows B a) (pows B A)

def leafZ2 (cd : CellData) (B : Box) : Bool :=
  leafZ2a cd B (var1 B) (var0 B) (sub (cnst S) (var0 B)) (sub (var1 B) (mul B (var1 B) (var0 B)))
    (add (var1 B) (mul B (sub (cnst S) (var1 B)) (var2 B)))

/-- A cell [p0, p1] near 0, 0 ≤ p0, p1 < 1 (statement for p > 0). -/
def cell0Check (cd : CellData) : Bool :=
  zle zero cd.ph && zle zero (zsub cd.pm cd.ph) && zlt (zadd cd.pm cd.ph) S &&
  rootOK0 cd && runAll (leaf1 cd) (root1 cd) cd.tree1 && runAll (leafZ2 cd) (root2 cd) cd.tree2

def Cell0Stmt (cd : CellData) : Prop :=
  ∀ p : ℝ, 0 < p → toR (zsub cd.pm cd.ph) ≤ p → p ≤ toR (zadd cd.pm cd.ph) →
    0 ≤ lamv cd p ∧ (∀ j, 0 ≤ tauv cd j p) ∧
    ∀ (j : Fin 9) (a A : ℝ), 0 ≤ a → a ≤ p → p ≤ A → A ≤ 1 →
      0 ≤ G1 j (lamv cd p) (tauv cd j p) a p ∧ 0 ≤ G2 j (lamv cd p) (tauv cd j p) a p A

end RandomSizeStable.Stability.RankCutCert.Dev


