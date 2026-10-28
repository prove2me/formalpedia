-- Prove2me | Definitions.Def_ArdaRS_Arithmetic
-- name    : ArdaRS_Arithmetic
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:45:39.40835+00:00
-- url     : https://prove2.me/theorems/fc6c083f-c5e0-4ea1-83eb-f29e0975c365
-- title:
--   Fixed-point Dirichlet-sum arithmetic
-- statement:
--   Natural-number fixed-point states and operations used to evaluate finite Dirichlet sums at dyadic heights. The definitions describe computations; their analytic soundness is established separately.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Eval.lean

/- Source: Arda, commit af4fde897, Probes/ArbEconomics_Eval.lean; Apache-2.0. -/
/-  Probes/ArbEconomics_Eval.lean -- ANDURIL economics seat: a Nat-only kernel evaluator of the
    Dirichlet part of the Euler-Maclaurin zeta sum on the critical line.

    WHAT THIS COMPUTES.  For `s = 1/2 + i t` with `t = tn / 2^tq`, the partial sum
    `Sum_{n=1}^{M} n^(-s) = Sum n^(-1/2) (cos(t log n) - i sin(t log n))` as two signed balls
    (Re, Im) at fixed precision `P` bits (`one = 2^P`):

        signed ball (pos, neg, rad) encloses x   iff   |x * 2^P - (pos - neg)| <= rad.

    Per term m it computes, with Nat arithmetic ONLY:
      * `log m` incrementally: `log m = log (m-1) + (-log (1 - 1/m))`, the increment by the
        series `Sum_{i<K} (1/m)^(i+1)/(i+1)` (Mathlib `Real.abs_log_sub_add_sum_range_le` tail);
      * `m^(-1/2)` by integer Newton; whichever side of the root the iterate `g` lands on, the
        pair `(g, 2^(2P) / (m g))` brackets `2^P / sqrt m` (decided by `g^2 m <= 2^(2P)`);
      * `theta = t log m`, reduced by `k = round(theta / (pi/2))` with a (pi/2) ball from Mathlib's
        20-digit pi bounds; cos/sin of the reduced angle by an order-(2K+1) Horner scheme; the
        quadrant rotation `k mod 4`;
      * the term and its radius, accumulated.

    COST DESIGN (every choice below is MEASURED, see Probes/ArbEconomics_Micro.lean):
      * hot-path ops are DIRECT calls of the GMP-accelerated kernel Nat primitives
        (`Nat.add`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.sub`, `Nat.shiftRight`, `Nat.beq`,
        `Nat.ble`): `Int` ops are ~20x slower in the kernel, typeclass notation ~4x slower;
      * loops are raw `Nat.rec` (structural `brecOn` recursion is ~5x slower);
      * the per-config Horner and log kernels are UNROLLED functions stored in the config
        (`List.rec`/`Nat.rec` overhead is ~7 us per step, the unrolled step ~2.5 us); the proofs
        in ArbEconomics_Sound.lean are about the generic `horner`/`logFix` specs, and each
        instance links its unrolled functions to the specs by `rfl`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/

namespace ArbEcon

-- Raw recursors (`Bool.rec`, `List.rec`) have no compiled code; the kernel does not need any.
noncomputable section

/-! ## Generic specifications (the objects the soundness proofs talk about) -/

/-- Log series loop.  State `(i, pw, S)` with `pw = m^(i+1)`; adds `f = one / (pw (i+1))` and
    stops at the first zero term.  Returns `(S, K, pw)` with `pw = m^(K+1)`. -/
def logLoop (one m : Nat) (fuel : Nat) : Nat → Nat → Nat → Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat × Nat)
    (fun i pw S => (S, i, pw))
    (fun _ ih i pw S =>
      let f := Nat.div one (Nat.mul pw (Nat.succ i))
      Bool.rec (ih (Nat.succ i) (Nat.mul pw m) (Nat.add S f)) (S, i, pw) (Nat.beq f 0))
    fuel

/-- Fixed-length log series (no early exit): `K` terms. -/
def logFix (one m : Nat) (K : Nat) : Nat → Nat → Nat → Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat × Nat)
    (fun i pw S => (S, i, pw))
    (fun _ ih i pw S =>
      ih (Nat.succ i) (Nat.mul pw m) (Nat.add S (Nat.div one (Nat.mul pw (Nat.succ i)))))
    K

/-- Integer Newton square root from above with early exit. -/
def isqrtLoop (A : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun g => g)
    (fun _ ih g =>
      let g2 := Nat.shiftRight (Nat.add g (Nat.div A g)) 1
      Bool.rec (ih g2) g (Nat.ble g g2))
    fuel

/-- Horner `h <- one - (w h) / D` over the divisor list (head processed first). -/
def horner (one w : Nat) (ds : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun h => h)
    (fun D _ ih h => ih (Nat.sub one (Nat.div (Nat.mul w h) D))) ds

/-- `[f K, f (K-1), ..., f 1]` -/
def divList (f : Nat → Nat) : Nat → List Nat
  | 0 => []
  | K + 1 => f (K + 1) :: divList f K

/-! ## Configuration -/

/-- Evaluator configuration (all literals / unrolled kernels, emitted per instance). -/
structure Cfg where
  /-- precision bits, `one = 2^P`, `two1 = 2^(P+1)`, `oneSq = 2^(2P)` -/
  P : Nat
  one : Nat
  two1 : Nat
  oneSq : Nat
  /-- `t = tn / 2^tq` -/
  tn : Nat
  tq : Nat
  /-- `|pi/2 * 2^P - hp| <= rp`, `hph = hp / 2` -/
  hp : Nat
  hph : Nat
  rp : Nat
  /-- Taylor validity cap on `|phi| * 2^P`, truncation bound (ulps) -/
  umax : Nat
  tau : Nat
  /-- Horner divisor lists (the SPEC) and their unrolled kernels (the COMPUTATION) -/
  dcos : List Nat
  dsin : List Nat
  hc : Nat → Nat
  hs : Nat → Nat
  /-- log series: early-exit loop fuel, fast-path threshold, fast-path length, fast kernel -/
  lnfuel : Nat
  lnbig : Nat
  lnK : Nat
  lnf : Nat → Nat × Nat × Nat
  /-- square root: loop fuel, fast-path threshold (two unrolled Newton steps above it) -/
  sqfuel : Nat
  sqbig : Nat

/-- Loop state after processing terms `1..n`. -/
structure St where
  n : Nat
  llo : Nat
  lhi : Nat
  g : Nat
  reP : Nat
  reN : Nat
  reR : Nat
  imP : Nat
  imN : Nat
  imR : Nat

/-- cos / sin of an angle as (magnitude, sign, radius) each (sign `true` = nonnegative). -/
structure Trig where
  cm : Nat
  cs : Bool
  cr : Nat
  sm : Nat
  ss : Bool
  sr : Nat

/-! ## per-term pieces -/

/-- log increment `(S, K, pw)` for `m`: fast fixed-length kernel above `lnbig`, loop below. -/
def logInc (c : Cfg) (m : Nat) : Nat × Nat × Nat :=
  Bool.rec (logLoop c.one m c.lnfuel 0 m 0) (c.lnf m) (Nat.ble c.lnbig m)

/-- Newton square root of `A` from the guess `g`. -/
def isqrt (c : Cfg) (m A g : Nat) : Nat :=
  Bool.rec (isqrtLoop A c.sqfuel g)
    (let g1 := Nat.shiftRight (Nat.add g (Nat.div A g)) 1
     Nat.shiftRight (Nat.add g1 (Nat.div A g1)) 1)
    (Nat.ble c.sqbig m)

/-- Quadrant rotation by `j = k mod 4` given cos/sin of the reduced angle. -/
def rotate (b0 b1 : Bool) (C rc S0 : Nat) (sy : Bool) (rs : Nat) : Trig :=
  Bool.rec
    (Bool.rec ⟨C, true, rc, S0, sy, rs⟩ ⟨S0, !sy, rs, C, true, rc⟩ b0)
    (Bool.rec ⟨C, false, rc, S0, !sy, rs⟩ ⟨S0, sy, rs, C, false, rc⟩ b0)
    b1

/-- cos/sin of `theta in [thlo, thhi] / 2^P`. -/
def trig (c : Cfg) (thlo thhi : Nat) : Trig :=
  let k := Nat.div (Nat.add thlo c.hph) c.hp
  let M1 := Nat.add thlo thhi
  let M2 := Nat.shiftLeft (Nat.mul k c.hp) 1
  let pos := Nat.ble M2 M1
  let mag := Nat.shiftRight (Bool.rec (Nat.sub M2 M1) (Nat.sub M1 M2) pos) 1
  let rphi := Nat.add (Nat.add (Nat.shiftRight (Nat.sub thhi thlo) 1) (Nat.mul k c.rp)) 2
  let j := Nat.mod k 4
  let b0 := Nat.beq (Nat.mod j 2) 1
  let b1 := Nat.ble 2 j
  Bool.rec
    (rotate b0 b1 0 c.one 0 pos c.one)
    (let w := Nat.shiftRight (Nat.mul mag mag) c.P
     rotate b0 b1 (c.hc w) (Nat.add (Nat.add 3 c.tau) rphi)
       (Nat.shiftRight (Nat.mul mag (c.hs w)) c.P) pos (Nat.add (Nat.add 4 c.tau) rphi))
    (Nat.ble mag c.umax)

/-- Everything about term `m = n + 1` given the state after `n`. -/
structure TermOut where
  llo : Nat
  lhi : Nat
  g : Nat
  Rlo : Nat
  Rhi : Nat
  tr : Trig

def termOf (c : Cfg) (s : St) : TermOut :=
  let m := Nat.succ s.n
  let lg := logInc c m
  let llo := Nat.add s.llo lg.1
  let lhi := Nat.add (Nat.add (Nat.add s.lhi lg.1) lg.2.1) (Nat.add (Nat.div c.two1 lg.2.2) 1)
  let g := isqrt c m (Nat.div c.oneSq m) s.g
  -- g below the root  (g^2 m <= 2^(2P)) : [g, q + 1];  g above the root : [q, g];  g = 0 : [0, one]
  let q := Nat.div c.oneSq (Nat.mul m g)
  let b := Nat.ble (Nat.mul (Nat.mul g g) m) c.oneSq
  let pos := Nat.ble 1 g
  ⟨llo, lhi, g, Bool.rec 0 (Bool.rec q g b) pos, Bool.rec c.one (Bool.rec g (Nat.add q 1) b) pos,
   trig c (Nat.shiftRight (Nat.mul c.tn llo) c.tq)
     (Nat.add (Nat.shiftRight (Nat.mul c.tn lhi) c.tq) 1)⟩

/-- Term center/radius of `R * v` for `v` given as (magnitude, radius). -/
def tmul (c : Cfg) (o : TermOut) (vm vr : Nat) : Nat × Nat :=
  (Nat.shiftRight (Nat.mul o.Rhi vm) c.P,
   Nat.add (Nat.add (Nat.shiftRight (Nat.mul o.Rhi vr) c.P) (Nat.sub o.Rhi o.Rlo)) 2)

/-- One step: process term `m = n + 1`. -/
def step (c : Cfg) (s : St) : St :=
  let o := termOf c s
  let re := tmul c o o.tr.cm o.tr.cr
  let im := tmul c o o.tr.sm o.tr.sr
  ⟨Nat.succ s.n, o.llo, o.lhi, o.g,
   Bool.rec s.reP (Nat.add s.reP re.1) o.tr.cs,
   Bool.rec (Nat.add s.reN re.1) s.reN o.tr.cs,
   Nat.add s.reR re.2,
   -- Im term is  -R sin theta : positive sin goes to the negative side
   Bool.rec (Nat.add s.imP im.1) s.imP o.tr.ss,
   Bool.rec s.imN (Nat.add s.imN im.1) o.tr.ss,
   Nat.add s.imR im.2⟩

/-- `count` steps. -/
def run (c : Cfg) (count : Nat) : St → St :=
  Nat.rec (motive := fun _ => St → St) (fun s => s) (fun _ ih s => ih (step c s)) count

/-- Field-wise Boolean equality of states (kernel-cheap `Nat.beq`). -/
def St.beq (a b : St) : Bool :=
  Nat.beq a.n b.n && Nat.beq a.llo b.llo && Nat.beq a.lhi b.lhi && Nat.beq a.g b.g &&
  Nat.beq a.reP b.reP && Nat.beq a.reN b.reN && Nat.beq a.reR b.reR &&
  Nat.beq a.imP b.imP && Nat.beq a.imN b.imN && Nat.beq a.imR b.imR

/-- The initial state after term `n = 1` (`1^(-s) = 1` exactly). -/
def St.init (c : Cfg) : St := ⟨1, 0, 0, c.one, c.one, 0, 0, 0, 0, 0⟩

end

end ArbEcon

def ArdaRS_Arithmetic : Nat := 0


