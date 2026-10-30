-- Prove2me | Definitions.Def_HorodeckiBoundKey_IsSeparable
-- name    : HorodeckiBoundKey_IsSeparable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:41.715529+00:00
-- url     : https://prove2.me/theorems/b1e73a58-909d-491d-9882-70391f071547
-- title:
--   Separable state across a bipartite cut
-- statement:
--   A matrix $X$ on $\mathbb C^{I}\otimes\mathbb C^{J}$ is a **separable state** if it is a finite convex combination of product states:
--   $$
--   X = \sum_{j=1}^{q} w_j\, A_j\otimes B_j,\qquad w_j\ge 0,\quad \sum_j w_j = 1,
--   $$
--   with every $A_j$ and every $B_j$ a density matrix (positive semidefinite, trace one). States that are not separable are **entangled**; the paper's bound entangled states are entangled states from which no pure entanglement can be distilled (p.1: "states which require entanglement to create").
--
--   **Formalization Note** The body is that of the published `QAlgorithms.Entanglement.IsSeparableDensity` without its `Nonempty` instance arguments, which cannot be synthesized for the register types used here; on nonempty types the two definitions agree definitionally (a proved sanity check). The tensor product is `Matrix.kronecker`.
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, p.1 ("states which require entanglement to create") and p.4 ("sep being the set of separable states")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

open QAlgorithms

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, p.1 ("bound entangled
states (states which require entanglement to create …)") and p.4 ("sep being the set of
separable states"): a matrix `X` on `I × J` is a *separable state* across the cut `I : J` if it
is a finite convex combination of product states,
`X = ∑ⱼ wⱼ Aⱼ ⊗ Bⱼ` with `wⱼ ≥ 0`, `∑ⱼ wⱼ = 1` and every `Aⱼ`, `Bⱼ` a density matrix.

**Formalization Note.** The body is word for word that of the published
`QAlgorithms.Entanglement.IsSeparableDensity` (bundle `QAlgorithms_Defs_BipartiteSeparability`),
without its `[Nonempty I] [Nonempty J]` instance binders, which cannot be synthesized for the
register types `Fin (Fintype.card (Fin 2 × S))` of this mission. On nonempty types the two
predicates are definitionally equal. The tensor product is `Matrix.kronecker`, `I` first. -/
def IsSeparable {I J : Type*} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ q : ℕ, ∃ w : Fin q → ℝ, ∃ A : Fin q → Matrix I I ℂ, ∃ B : Fin q → Matrix J J ℂ,
    (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
    (∀ j, IsDensityMatrix (A j) ∧ IsDensityMatrix (B j)) ∧
    X = ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)

end HorodeckiBoundKey


