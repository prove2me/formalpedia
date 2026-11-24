-- Prove2me | Definitions.Def_LogMeanVar_Complete_Supplement_BSDE
-- name    : LogMeanVar_Complete_Supplement_BSDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:59:01.069816+00:00
-- url     : https://prove2.me/theorems/885b793f-43ea-421b-814c-c1681bf95e46
-- title:
--   (15), (38), pp. 18, O–2, O–12 — scalar classical BSDE and equality of solutions
-- statement:
--   For a scalar state Brownian motion $W$, a scalar driver $g$, and terminal time $T$, a classical solution is an adapted pair $(Y,Z)$ satisfying
--
--   $$Y_t=\int_t^Tg(s,Z_s)\,ds-\int_t^TZ_s\,dW_s,\qquad Y_T=0.$$
--
--   The solution has continuous $Y$, right-continuous $Z$, finite expected squared integrand and driver, square-integrable time slices of $Y$, and a true compensated martingale. The stochastic integral is the published Itô relation. Equality of $Y$ means indistinguishability on the horizon; equality of $Z$ means $dt\otimes P$ almost everywhere.
--
--   This is the scalar specialization needed to exhibit a counterexample to a theorem whose domain includes $N=K=1$; it is not offered as a reduced version of the general vector theorem.
--
--   **Formalization Note** The right-continuous integrand, square-integrable driver and true-martingale clauses are expressly used in the proof on p. O–12. The counterexample satisfies all of them. No equilibrium, annual-return, Markov representation or PDE is built into the solution predicate.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. 18, (15); pp. O–2, O–12, (38) and proof of Theorem 4

import Definitions.Def_LogMeanVar_Complete_Supplement_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

namespace LogMeanVar.Complete.Supplement

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns,
SSRN 3437268 (version of Aug 2019), p.18 (15), pp.O–2, O–11–O–13 (38), (45).
A general scalar classical BSDE with terminal zero. It contains only the equation
and ordinary solution regularity, never equilibrium, returns or a Markov/PDE claim.
Formalization Note: the right-continuous Z, L² driver and true martingale are
explicitly used in the proof on O–12. This counterexample class meets all three,
so it does not exploit those otherwise unstated assumptions. The definition is
scalar because a scalar counterexample already refutes the general vector claim. -/
def ClassicalBSDE (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (T : ℝ) (g : ℝ → Ω → ℝ → ℝ)
    (Y Z : ℝ → Ω → ℝ) : Prop :=
  (∀ t ∈ Set.Icc 0 T, StronglyMeasurable[F t.toNNReal] (Y t) ∧
    StronglyMeasurable[F t.toNNReal] (Z t) ∧ MemLp (Y t) 2 P) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Ico 0 T, ContinuousWithinAt (fun s => Z s ω) (Set.Ici t) t) ∧
    IntervalIntegrable (fun s => Z s ω ^ 2) volume 0 T ∧
    IntervalIntegrable (fun s => g s ω (Z s ω)) volume 0 T) ∧
  (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Z s ω ^ 2) ∂volume ∂P) < ⊤ ∧
  (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (g s ω (Z s ω) ^ 2) ∂volume ∂P) < ⊤ ∧
  Martingale (fun (u : ℝ≥0) ω => Y (min (u : ℝ) T) ω +
    ∫ s in (0 : ℝ)..min (u : ℝ) T, g s ω (Z s ω)) F P ∧
  ∃ I : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral P (fun u => F u) W (cutoff T Z) I ∧
    ∀ t ∈ Set.Icc 0 T, ∀ᵐ ω ∂P,
      Y t ω = (∫ s in t..T, g s ω (Z s ω)) - (I T.toNNReal ω - I t.toNNReal ω)

/-- Equality of Y is indistinguishability on the horizon, and equality of Z is
Lebesgue×P almost everywhere. No pointwise uniqueness of Itô integrands is asserted. -/
def SameSolution (P : Measure Ω) (T : ℝ) (Y Z Y' Z' : ℝ → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, Y t ω = Y' t ω) ∧
  ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P), Z q.1 q.2 = Z' q.1 q.2

end LogMeanVar.Complete.Supplement


