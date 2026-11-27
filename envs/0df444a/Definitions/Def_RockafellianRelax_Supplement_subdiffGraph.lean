-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_subdiffGraph
-- name    : RockafellianRelax_Supplement_subdiffGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:16:21.103101+00:00
-- url     : https://prove2.me/theorems/2fde0787-5bd9-4810-96db-d97ea68dc66f
-- title:
--   Graph of the subdifferential
-- statement:
--   For $\psi : \mathbb R^m\times\mathbb R^n \to \overline{\mathbb R}$, the **graph of the subdifferential** is
--
--   $$
--   \operatorname{gph}\partial\psi = \{(z,v) \mid v \in \partial\psi(z)\} \subseteq (\mathbb R^m\times\mathbb R^n)^2 .
--   $$
--
--   Condition (5.1) of Theorem 5.2 compares these graphs.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §5, p.24 (graph of ∂ψ)

import Mathlib
import Definitions.Def_RockafellianRelax_Supplement_subdiff

namespace RockafellianRelax.Supplement

/-- **Graph of the subdifferential.**
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §5, p.24: "The graph of ∂ψ is gph ∂ψ = {(x, v) ∈ ℝⁿ × ℝⁿ | v ∈ ∂ψ(x)}."

**Formalization Note.** The space is `ℝᵐ × ℝⁿ`; a member is the pair (point, subgradient). -/
def subdiffGraph {m n : ℕ} (ψ : (Fin m → ℝ) × (Fin n → ℝ) → EReal) :
    Set (((Fin m → ℝ) × (Fin n → ℝ)) × ((Fin m → ℝ) × (Fin n → ℝ))) :=
  {a | a.2 ∈ subdiff ψ a.1}

end RockafellianRelax.Supplement


