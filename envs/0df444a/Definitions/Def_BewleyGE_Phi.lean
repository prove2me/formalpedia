-- Prove2me | Definitions.Def_BewleyGE_Phi
-- name    : BewleyGE_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:34:12.389137+00:00
-- url     : https://prove2.me/theorems/99ca865c-3ea7-4f60-8903-f51a785b9e72
-- title:
--   The correspondence $\Phi:\Lambda\to2^\Lambda$
-- statement:
--   For $p\in\Lambda$ let
--   $$
--   \Phi(p)=\{z\in\Lambda : z_k=0\ \text{ for all }k\notin W(p)\}.
--   $$
--   A fixed point $p\in\Phi(p)$ is an equilibrium price; the paper obtains one from Kakutani's theorem.
--
--   **Formalization Note** The paper writes both $\Phi$ and $\varphi$ for this map.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Proof of Theorem 1, p.29

import Mathlib
import Definitions.Def_BewleyGE_maxSet
import Definitions.Def_BewleyGE_priceSimplex

open MeasureTheory

namespace BewleyGE

/-- **The correspondence `Φ : Λ → 2^Λ`** of the proof of Theorem 1. Light, arXiv:1906.06810v2,
Proof of Theorem 1, p.29: `Φ(p) = {z ∈ Λ : zₖ = 0 for all k ∉ W(p)}`.

**Formalization Note.** The paper writes both `Φ` and `φ` for this map. -/
def Phi {n : ℕ} (E : Economy n)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (π : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {z | z ∈ priceSimplex n ∧ ∀ k, k ∉ maxSet E x g μ π → z k = 0}

end BewleyGE


