-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
-- name    : ArdaRH65K_Turing121_EMZetaOfflineEval
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:05.184992+00:00
-- url     : https://prove2.me/theorems/3e28e4c9-0779-4cec-a820-aab523ab3909
-- title:
--   EMZetaOfflineEval certificate definitions
-- statement:
--   This bundle defines rational interval-evaluation configurations, accumulators, and operations. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArbEcon.Off.OCfg},\;\mathtt{ArbEcon.Off.OCfg.q},\;\mathtt{ArbEcon.Off.OCfg.mk},\;\mathtt{ArbEcon.Off.OCfg.oneQ}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineEval.lean

import Definitions.Def_ArdaRS_Arithmetic
/-  EMZetaOfflineEval.lean -- lane offline: a Nat-only kernel evaluator of the Dirichlet part of the
    Euler-Maclaurin zeta sum at an ARBITRARY point `s = σ + i t`, `σ = (a - b)/q` rational,
    `t = tn / 2^tq` dyadic.

    It extends the on-line evaluator of `Probes/ArbEconomics_Eval` (amplitude `m^(-1/2)` only) by
      * the amplitude `m^(-σ)` for any rational `σ`: an integer Newton `q`-th root, VALIDATED in the
        kernel by `g^q m^a ≤ 2^(qP) m^b ≤ (g+1)^q m^a` (fallback bracket `[0, 2^P m^b]` if a check
        fails, so the evaluator is sound for every input; the generator makes the checks pass);
      * `p + 1` accumulators: accumulator `k` encloses `Σ_{m ≤ n} (log m)^k m^(-s)` (`k = 0` is the
        Dirichlet partial sum; `k ≥ 1` are the Taylor coefficients the slab certificate needs).
    The log increment, the `(π/2)`-reduction and the cos/sin Horner kernels are the unchanged
    `ArbEcon.logInc` / `ArbEcon.trig` at the shared P = 64 configuration `EMZetaHighCfg64.cfg64`.

    A signed ball `(P, N, R)` (resp. a term ball `(sign, mag, rad)`) encloses `x` iff
    `|x 2^P - (P - N)| ≤ R` (resp. `|x 2^P - sgn · mag| ≤ rad`).

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/


namespace ArbEcon

namespace Off

noncomputable section

/-- Off-line configuration: `σ = (a - b) / q`, `oneQ = 2^(q P)`, Newton fuel. -/
structure OCfg where
  a : Nat
  b : Nat
  q : Nat
  oneQ : Nat
  nfuel : Nat

/-- A complex signed ball (real and imaginary parts). -/
structure Acc where
  reP : Nat
  reN : Nat
  reR : Nat
  imP : Nat
  imN : Nat
  imR : Nat

/-- Loop state after the terms `1..n`: log bracket, amplitude guess, accumulators. -/
structure StO where
  n : Nat
  llo : Nat
  lhi : Nat
  g : Nat
  acc : List Acc

/-- A complex term ball: `(sign, magnitude, radius)` for the real and the imaginary part. -/
structure TB where
  rs : Bool
  rm : Nat
  rr : Nat
  is : Bool
  im : Nat
  ir : Nat

/-- Integer Newton for the `q`-th root of `A / D`: `g <- ((q-1) g + A / (D g^(q-1))) / q`, stopping
    at the first non-decrease. -/
def rootLoop (q A D : Nat) (fuel : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun g => g)
    (fun _ ih g =>
      let g2 := Nat.div (Nat.add (Nat.mul (Nat.sub q 1) g)
        (Nat.div A (Nat.mul D (Nat.pow g (Nat.sub q 1))))) q
      Bool.rec (ih g2) g (Nat.ble g g2))
    fuel

/-- Center of `x · v` for `x ∈ [lo, hi] / 2^P`, `v` a term ball of magnitude `vm`. -/
def imC (P hi vm : Nat) : Nat := Nat.shiftRight (Nat.mul hi vm) P

/-- Radius of `x · v`. -/
def imR (P lo hi vm vr : Nat) : Nat :=
  Nat.add (Nat.add (Nat.shiftRight (Nat.mul hi vr) P) (Nat.shiftRight (Nat.mul (Nat.sub hi lo) vm) P)) 3

/-- `x · t` for a nonnegative real `x ∈ [lo, hi] / 2^P`. -/
def tbMul (P lo hi : Nat) (t : TB) : TB :=
  ⟨t.rs, imC P hi t.rm, imR P lo hi t.rm t.rr, t.is, imC P hi t.im, imR P lo hi t.im t.ir⟩

/-- Accumulate a term ball. -/
def accAdd (x : Acc) (t : TB) : Acc :=
  ⟨Bool.rec x.reP (Nat.add x.reP t.rm) t.rs, Bool.rec (Nat.add x.reN t.rm) x.reN t.rs,
   Nat.add x.reR t.rr,
   Bool.rec x.imP (Nat.add x.imP t.im) t.is, Bool.rec (Nat.add x.imN t.im) x.imN t.is,
   Nat.add x.imR t.ir⟩

/-- Add `t, L t, L² t, …` to the accumulators `0, 1, 2, …` (`L ∈ [lo, hi] / 2^P`). -/
def addChain (P lo hi : Nat) : List Acc → TB → List Acc :=
  List.rec (motive := fun _ => TB → List Acc) (fun _ => [])
    (fun x _ ih t => accAdd x t :: ih (tbMul P lo hi t))

/-- The amplitude of term `m`: `(g, Xlo, Xhi)` with `Xlo ≤ 2^P m^(-σ) ≤ Xhi`. -/
def ampl (c : Cfg) (o : OCfg) (m gprev : Nat) : Nat × Nat × Nat :=
  let A := Nat.mul o.oneQ (Nat.pow m o.b)
  let D := Nat.pow m o.a
  let g0 := Nat.add (Nat.add gprev (Nat.div gprev (Nat.sub m 1))) 2
  let g := rootLoop o.q A D o.nfuel g0
  (g, Bool.rec 0 g (Nat.ble (Nat.mul (Nat.pow g o.q) D) A),
   Bool.rec (Nat.mul c.one (Nat.pow m o.b)) (Nat.succ g)
     (Nat.ble A (Nat.mul (Nat.pow (Nat.succ g) o.q) D)))

/-- The term ball of `m^(-s) = m^(-σ) (cos θ - i sin θ)` from an amplitude bracket and trig balls. -/
def termTB (P Xlo Xhi : Nat) (tr : Trig) : TB :=
  ⟨tr.cs, imC P Xhi tr.cm, imR P Xlo Xhi tr.cm tr.cr,
   !tr.ss, imC P Xhi tr.sm, imR P Xlo Xhi tr.sm tr.sr⟩

/-- One step: process the term `m = n + 1`. -/
def stepO (c : Cfg) (o : OCfg) (s : StO) : StO :=
  let m := Nat.succ s.n
  let lg := logInc c m
  let llo := Nat.add s.llo lg.1
  let lhi := Nat.add (Nat.add (Nat.add s.lhi lg.1) lg.2.1) (Nat.add (Nat.div c.two1 lg.2.2) 1)
  let am := ampl c o m s.g
  let tr := trig c (Nat.shiftRight (Nat.mul c.tn llo) c.tq)
    (Nat.add (Nat.shiftRight (Nat.mul c.tn lhi) c.tq) 1)
  ⟨m, llo, lhi, am.1, addChain c.P llo lhi s.acc (termTB c.P am.2.1 am.2.2 tr)⟩

/-- `count` steps. -/
def runO (c : Cfg) (o : OCfg) (count : Nat) : StO → StO :=
  Nat.rec (motive := fun _ => StO → StO) (fun s => s) (fun _ ih s => ih (stepO c o s)) count







/-- The zero ball. -/
def Acc.zero : Acc := ⟨0, 0, 0, 0, 0, 0⟩

/-- The state after the term `n = 1` (`1^(-s) = 1`, `log 1 = 0`), with `p + 1` accumulators. -/
def StO.init (c : Cfg) (p : Nat) : StO :=
  ⟨1, 0, 0, c.one, ⟨c.one, 0, 0, 0, 0, 0⟩ :: List.replicate p Acc.zero⟩

end

end Off

end ArbEcon


def ArdaRH65K_Turing121_EMZetaOfflineEval : Nat := 0


