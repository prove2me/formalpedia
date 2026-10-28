-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
-- name    : ArdaRH65K_Turing121_EMZetaOfflineSound
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:21.460755+00:00
-- url     : https://prove2.me/theorems/7a580c1e-33bb-406e-a3b1-f4b953150626
-- title:
--   EMZetaOfflineSound certificate definitions
-- statement:
--   This bundle defines the invariants connecting offline integer accumulators to complex sums. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArbEcon.Off.sOfG},\;\mathtt{ArbEcon.Off.psumK},\;\mathtt{ArbEcon.Off.AccOK},\;\mathtt{ArbEcon.Off.TBOK}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSound.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

namespace ArbEcon

namespace Off



/-! ## A. Specifications. -/

/-- `s = σ + i t`. -/
noncomputable def sOfG (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

/-- `Σ_{m=1}^{n} (log m)^k m^(-s)`. -/
noncomputable def psumK (σ t : ℝ) (k n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico 1 (n + 1), ((Real.log m : ℝ) : ℂ) ^ k * (m : ℂ) ^ (-sOfG σ t)

/-- A complex signed ball encloses `z`. -/
def AccOK (P : ℕ) (z : ℂ) (x : Acc) : Prop :=
  |z.re * 2 ^ P - ((x.reP : ℝ) - x.reN)| ≤ x.reR ∧ |z.im * 2 ^ P - ((x.imP : ℝ) - x.imN)| ≤ x.imR

/-- A term ball encloses `z`. -/
def TBOK (P : ℕ) (z : ℂ) (t : TB) : Prop :=
  |z.re * 2 ^ P - sgn t.rs * t.rm| ≤ t.rr ∧ |z.im * 2 ^ P - sgn t.is * t.im| ≤ t.ir

/-- The accumulator list encloses `f k, f (k+1), …`. -/
def AccsOK (P : ℕ) (f : ℕ → ℂ) : ℕ → List Acc → Prop
  | _, [] => True
  | k, x :: xs => AccOK P (f k) x ∧ AccsOK P f (k + 1) xs

/-- The loop invariant after `n` terms. -/
def InvO (c : Cfg) (σ t : ℝ) (n : ℕ) (s : StO) : Prop :=
  s.n = n ∧ 1 ≤ n ∧ (s.llo : ℝ) ≤ Real.log n * 2 ^ c.P ∧ Real.log n * 2 ^ c.P ≤ s.lhi ∧
    AccsOK c.P (fun k => psumK σ t k n) 0 s.acc

/-- Validity of an off-line configuration for `σ`. -/
structure OValid (c : Cfg) (o : OCfg) (σ : ℝ) : Prop where
  oneQ_eq : o.oneQ = 2 ^ (o.q * c.P)
  q_pos : 1 ≤ o.q
  sigma_eq : σ = ((o.a : ℝ) - o.b) / o.q

/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/





/-! ## E. The term `m^(-s)`. -/





/-! ## F. The partial sums. -/







/-! ## G. One step, the run, the chunks. -/

















end Off

end ArbEcon


def ArdaRH65K_Turing121_EMZetaOfflineSound : Nat := 0


