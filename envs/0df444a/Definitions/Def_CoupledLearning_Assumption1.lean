-- Prove2me | Definitions.Def_CoupledLearning_Assumption1
-- name    : CoupledLearning_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:05.900791+00:00
-- url     : https://prove2.me/theorems/e9e8bf0a-30d6-4b98-8b68-91e8ebf19504
-- title:
--   Assumption 1 (upper-hemicontinuous strategy updates)
-- statement:
--   For every player $i$, the correspondence $(\theta,q)\mapsto F_i(\theta,q)$ is upper hemicontinuous on $\Delta(S)\times Q$.
--
--   It is satisfied by belief-based best responses (Berge's maximum theorem) and by belief-based no-regret learning with continuously differentiable utilities.
--
--   **Formalization Note** "Upper hemicontinuous in $\theta$ and $q$" is read as joint upper hemicontinuity in the open-set sense on the domain $\Delta(S)\times Q$.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Assumption 1, p.9; footnote 4, p.11

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_IsUHC

namespace CoupledLearning

/-- Assumption 1 (upper-hemicontinuous strategy updates), arXiv:2206.05637v2, p.9: for any
`i ∈ I`, `F_i(θ, q)` is upper hemicontinuous in `θ` and `q`.

**Formalization Note.** Read as upper hemicontinuity of the correspondence
`(θ, q) ↦ F_i(θ, q)` on its domain `Δ(S) × Q` (footnote 4 obtains it for best responses from
Berge's theorem, which gives joint upper hemicontinuity), in the open-set sense of `IsUHC`. -/
def Assumption1 {I S : Type*} [Fintype S] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i))))
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i)))) : Prop :=
  ∀ i, IsUHC (stdSimplex ℝ S ×ˢ Qset Q) (fun p : (S → ℝ) × Prof d => F i p.1 p.2)

end CoupledLearning


