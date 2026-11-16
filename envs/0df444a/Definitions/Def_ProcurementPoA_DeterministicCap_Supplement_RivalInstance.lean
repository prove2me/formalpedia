-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_RivalInstance
-- name    : ProcurementPoA_DeterministicCap_Supplement_RivalInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:35:02.873222+00:00
-- url     : https://prove2.me/theorems/c1fed87d-43f6-45e6-89f5-cd5767acf5bf
-- title:
--   The rival cost instance and its loss function
-- statement:
--   For $0<m<R-1$, $0<\theta<1$ and $n\ge1$, the rival instance has $n+1$ suppliers. Supplier $M$, indexed by $0$, has cost $1$ deterministically. The other $n$ suppliers have independent costs with law
--   $$\Pr[c_i=R]=\theta^{1/n},\qquad \Pr[c_i=1+m]=1-\theta^{1/n}.$$
--   The measurable possible-type sets are $\{1\}$ for $M$ and $\{1+m,R\}$ for each rival. Define
--   $$\Phi_{m,\theta}(\pi)=\begin{cases}m(1-\theta)(1-m/(\theta\pi)),&m<\theta\pi,\\0,&\theta\pi\le m.\end{cases}$$
--   Tie freedom means that, almost surely under the actual joint type-and-bid law, the real suppliers' bids are pairwise distinct. The phantom bid is not one of these suppliers.
--
--   This constructs the exact fixed instance used across acceptance functions and signals in the regular-mechanism lower bound. It does not prescribe its equilibrium or assume its loss bound.
--
--   **Formalization Note** The high-cost weight is a real power. Mathlib's Bernoulli measure assigns this weight to $R$ and the complementary weight to $1+m$. The constructor is total for $n=0$ and $\theta\in[0,1]$, but Lemma A.2 uses precisely the strict source parameter domain and $n\ge1$; it never uses division by a zero population parameter.
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Lemma A.2, Appendix A.2.1, printed pp. 18–19 (PDF pp. 20–21)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Acceptance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- The exact probability of a high-cost rival, including the finite-n factor. -/
noncomputable def rivalHighProbability (θ : ℝ) (n : ℕ) : ℝ := θ ^ (1 / (n : ℝ))

/-- The rival cost law, with the high-cost branch of mass θ^(1/n). -/
noncomputable def rivalLaw (R m : ℝ) (p : unitInterval) : Measure ℝ :=
  bernoulliMeasure R (1 + m) p

/-- The paper's constructed independent instance, not a free law with a promised bound. -/
noncomputable def rivalInstance (R m θ : ℝ) (n : ℕ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    IndependentTypes n where
  types i := if i = 0 then {1} else {1 + m, R}
  measurable_types i := by split_ifs <;> measurability
  law i := if i = 0 then Measure.dirac 1 else
    rivalLaw R m ⟨θ ^ (1 / (n : ℝ)),
      Real.rpow_nonneg hθ _, Real.rpow_le_one hθ hθ1 (by positivity)⟩
  probability i := by
    split_ifs
    · infer_instance
    · unfold rivalLaw
      infer_instance
  concentrated i := by
    classical
    split_ifs
    · simp
    · simp [rivalLaw, bernoulliMeasure_def]

noncomputable def Phi (m θ π : ℝ) : ℝ :=
  if m < θ * π then m * (1 - θ) * (1 - m / (θ * π)) else 0

/-- Pairwise distinct real bids almost surely under the actual type/bid law. -/
def NoBidTies {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) : Prop :=
  ∀ᵐ x ∂(playLaw D σ), Function.Injective (fun i => (x i).2)

end ProcurementPoA.DeterministicCap.Supplement


