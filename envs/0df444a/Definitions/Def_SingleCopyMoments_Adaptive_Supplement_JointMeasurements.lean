-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Supplement_JointMeasurements
-- name    : SingleCopyMoments_Adaptive_Supplement_JointMeasurements
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:38:20.942011+00:00
-- url     : https://prove2.me/theorems/73c534c8-3aa6-4a5e-80ac-fbc925bdf64c
-- title:
--   Born sampling of a local joint POVM on tensor powers
-- statement:
--   For $n$ independent copies of a state $\rho$, the local input is the published tensor power $\rho^{\otimes n}$, with its basis relabeled by $\operatorname{Fin}(d^n)$. In the product basis its entries are
--   $$ (\rho^{\otimes n})_{x,y}=\prod_{k=0}^{n-1}\rho_{x_k,y_k}.$$
--   At $n=0$, the empty tensor product has dimension one and entry one. A local block measurement consists of the published normalized POVM $E$ on this tensor space, together with its Markov sampling kernel on original states, fixed by the Born equality
--   $$\Pr_\rho\{Y\in A\}=\operatorname{Re}\operatorname{Tr}(\rho^{\otimes n}E(A))$$
--   for every measurable outcome event $A$.
--
--   This is a measure representation of arbitrary local joint measurement, including local quantum memory and auxiliary operations absorbed into a POVM. Positivity, normalization and Born probabilities are measurement axioms; the interface contains no estimation guarantee. Outcome spaces may be continuous.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §6.4, printed pp.30–32 (PDF pp.32–34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation
import Definitions.Def_IncoherentPurity_Adaptive_Estimators

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Topology Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace SingleCopyMoments.Adaptive.Supplement

/-- A basis relabeling only; at n=0 there is exactly one empty string. -/
def copyIndex (d n : ℕ) : (Fin n → Fin d) ≃ Fin (d^n) :=
  Fintype.equivFinOfCardEq (by simp)

/-- Reuse the published tensor power, expressed in the Fin(d^n) basis. -/
def copiesMatrix {d : ℕ} (ρ : State d) (n : ℕ) : Op (d^n) :=
  fun i j => IncoherentPurity.Adaptive.tensorPower ρ.val n
    ((copyIndex d n).symm i) ((copyIndex d n).symm j)

/-- A joint measurement on n local copies. The general POVM is reused, and the
sampling kernel is its exact Born law on rho^{tensor n}. No estimation bound,
concentration assertion or state-dependent choice of effects is part of this interface. -/
structure BlockMeasurement (d n : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  povm : IncoherentPurity.Adaptive.POVM (d^n) Ω
  sample : Kernel (State d) Ω
  markov : IsMarkovKernel sample
  born_eq : ∀ (ρ : State d) A, MeasurableSet A →
    sample ρ A = ENNReal.ofReal ((copiesMatrix ρ n * povm.effect A).trace.re)

end SingleCopyMoments.Adaptive.Supplement


