-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_IsProper
-- name    : RockafellianRelax_Supplement_IsProper
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:10:26.265918+00:00
-- url     : https://prove2.me/theorems/3ec80bf5-7a6b-4299-8ee6-49b6c2fb2a1a
-- title:
--   Proper extended-real-valued function
-- statement:
--   For $\psi : \alpha \to \overline{\mathbb R} = [-\infty,\infty]$ with effective domain $\operatorname{dom}\psi = \{x \mid \psi(x) < \infty\}$, the function $\psi$ is **proper** if
--
--   $$
--   \operatorname{dom}\psi \ne \emptyset \quad\text{and}\quad \psi(x) > -\infty \ \text{ for all } x .
--   $$
--
--   It is the standing assumption on the functions $f_i$ and $g$ of §4 and on the objective $\varphi$ of §5.
--
--   **Formalization Note** $\operatorname{dom}$ is the published `AubinLipschitz.effDom` ($\psi \ne +\infty$), the domain used by the published base mission. The type $\alpha$ is arbitrary.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3, p.7 (notation: proper)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom

namespace RockafellianRelax.Supplement

/-- **Proper function.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3, p.7: "ψ is proper when dom ψ ≠ ∅ and ψ(x) > −∞ for all x ∈ ℝⁿ."

**Formalization Note.** `dom ψ = {x | ψ x ≠ ⊤}` is the published `AubinLipschitz.effDom`, the domain
of p.6 that the published base mission uses. `ψ ≡ ⊤` is not proper, and neither is a `ψ` taking the
value `⊥`. -/
def IsProper {α : Type*} (ψ : α → EReal) : Prop :=
  (AubinLipschitz.effDom ψ).Nonempty ∧ ∀ x, ψ x ≠ ⊥

end RockafellianRelax.Supplement


