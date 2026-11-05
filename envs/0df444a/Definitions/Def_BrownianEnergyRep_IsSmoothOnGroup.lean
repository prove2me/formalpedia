-- Prove2me | Definitions.Def_BrownianEnergyRep_IsSmoothOnGroup
-- name    : BrownianEnergyRep_IsSmoothOnGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:35.076935+00:00
-- url     : https://prove2.me/theorems/0851f0a0-089d-43ba-9990-a3c2d29d5df0
-- title:
--   Smooth functions on the matrix group $G$
-- statement:
--   A function $f:G\to\mathbb R$ belongs to $C^\infty(G)$ if it is the restriction of a smooth function of the $n^2$ matrix entries. These are the test functions of the martingale property (2.3) and of the heat semigroup's generator.
--
--   **Formalization Note** For a compact matrix group, which is an embedded submanifold of the matrices, this is the usual notion of smoothness. The module also fixes the Borel $\sigma$-algebra on $G$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, p.4

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The Borel σ-algebra of the group `G`. -/
instance groupMeasurableSpace {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) : MeasurableSpace ↥G :=
  borel ↥G

instance groupBorelSpace {n : ℕ} (G : Subgroup (GL (Fin n) ℝ)) : BorelSpace ↥G := ⟨rfl⟩

/-- The matrix entries of `x ∈ G ⊂ GLₙ(ℝ)`. -/
def entries {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} (x : ↥G) : Fin n → Fin n → ℝ :=
  fun i j => ((x : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j

/-- `f ∈ C^∞(G)` (arXiv:1511.07378v1, p.4).

**Formalization Note** `G` is a matrix group, so `f` is smooth exactly when it is the restriction
of a smooth function of the matrix entries (`G` is a compact embedded submanifold of the matrices). -/
def IsSmoothOnGroup {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} (f : ↥G → ℝ) : Prop :=
  ∃ F : (Fin n → Fin n → ℝ) → ℝ, ContDiff ℝ ∞ F ∧ ∀ x, f x = F (entries x)

end BrownianEnergyRep


