-- Prove2me | Definitions.Def_DistQuantumQuery_Supplement_AAdv
-- name    : DistQuantumQuery_Supplement_AAdv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:47:03.705209+00:00
-- url     : https://prove2.me/theorems/864ee780-3907-4d7e-b154-7e672e299f85
-- title:
--   Alberti adversary measure $\mathrm{AAdv}^\mu_\alpha(f)$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$, $f\subseteq\Sigma\times\Omega$ a search problem, $\mu$ a distribution on $\Sigma$ and $\alpha\in(0,1]$ a success parameter. With $\mathcal W^\mu_f$ the set of $\mu$-witnesses of $f$ (Definition 3.2), the **Alberti adversary measure** is
--   $$
--   \mathrm{AAdv}^\mu_\alpha(f):=\min_{W\in\mathcal W^\mu_f}\bar\delta^\mu_2\big(J,\,W/\alpha\mid\{S_i\}\big).
--   $$
--
--   It is the minimum filtered-$\delta_2$ cost of moving from the all-ones Gram matrix $J$ to a scaled witness; it lower-bounds $Q^\mu_{1-\alpha}(f)$ and, up to a loss in the success parameter, upper-bounds $Q^\mu_{1-\beta}(f)$ (Proposition 9.5).
--
--   **Formalization Note** The witnesses are the base mission's published `IsWitness`. The minimum is written as an infimum in the extended reals; the paper proves it is attained and finite (footnote 10), so the two agree. The condition $\alpha\in(0,1]$ is a hypothesis of the theorems that use the measure.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 9.1 and footnote 10, p.80

import Mathlib
import Definitions.Def_DistQuantumQuery_Adv
import Definitions.Def_DistQuantumQuery_Supplement_deltaBar

open scoped Matrix ComplexOrder

namespace DistQuantumQuery.Supplement

open DistQuantumQuery

/-- The **Alberti adversary measure** (Ben-David, Ebtehaj, *Distributional Quantum Query
Complexity*, arXiv:2610.06835, held version, sha256 6334ffaf…, Definition 9.1, p.80): for
`Σ ⊆ {0,1}^n`, a search problem `f ⊆ Σ × Ω`, a distribution `μ` and a success parameter `α`,
`AAdv^μ_α(f) := min_{W ∈ W^μ_f} δ̄^μ₂(J, W/α | {S_i})`, where `W^μ_f` is the set of `μ`-witnesses
of Definition 3.2.

**Formalization Note** The `μ`-witnesses are the base mission's published `IsWitness`; `J` is
`allOnes`; `W/α` is `α⁻¹ • W`. The minimum is written as the infimum in `EReal` over witnesses;
the paper proves it is attained and finite (footnote 10), so the two agree, and attainment is not
built in. The condition `α ∈ (0,1]` is a hypothesis of the theorems that use the measure. -/
noncomputable def AAdv {ι Ω : Type*} [Fintype Ω] (S : Finset (ι → Bool)) (μ : S → ℝ)
    (R : S → Ω → Prop) (α : ℝ) : EReal :=
  ⨅ (W : Matrix S S ℂ) (_ : IsWitness μ R W), deltaBar S μ (allOnes S) (((α : ℂ)⁻¹) • W)

end DistQuantumQuery.Supplement


