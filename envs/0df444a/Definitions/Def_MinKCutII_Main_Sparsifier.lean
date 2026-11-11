-- Prove2me | Definitions.Def_MinKCutII_Main_Sparsifier
-- name    : MinKCutII_Main_Sparsifier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:38:01.629469+00:00
-- url     : https://prove2.me/theorems/ea9863b4-47f0-4ea2-9aa8-f254fbd7a87a
-- title:
--   Laplacian quadratic form and (1 ± ε)-spectral sparsifiers (Definition 59)
-- statement:
--   For $G=(V,E,c)$ and $x\in\mathbb R^V$ the Laplacian quadratic form is
--   $$x^\top L_Gx=\sum_{e\in E}c(e)\,(x_a-x_b)^2\qquad(e\text{ with ends }\{a,b\}).$$
--   A **reweighted subgraph** of $G$ is a graph $H$ on $V$ whose records are a subfamily of $E$ (same ends) carrying new positive capacities. **Definition 59:** for $0<\varepsilon<1$, $H$ is a spectral sparsifier of $G$ if it is a reweighted subgraph and $(1-\varepsilon)x^\top L_Gx\le x^\top L_Hx\le(1+\varepsilon)x^\top L_Gx$ for every $x\in\mathbb R^V$.
--
--   **Formalization Note.** The subfamily is given by an injective map of record types preserving ends; the inequality is required for all real vectors, not only for cut indicator vectors.
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 43, Definition 59

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-!
# Laplacian quadratic form and spectral sparsifiers (Definition 59)

Vaughn, *Faster Minimum k-Cut II*, arXiv:2609.27797 (version of November 1, 2026, sha256
b01b5a6f…), §6.2 p. 43, Definition 59.

* `lapForm G x = xᵀ L_G x = Σ_e c(e) (x_a − x_b)²`, `e` with ends `{a, b}` (a loop contributes `0`).
* A reweighted subgraph of `G = (V, E, c)` is a graph `H` on the same `V` whose edge records are
  an injectively indexed subfamily of `E` (map `ι : E' → E`, same ends) with new, positive
  capacities.
* `IsSpectralSparsifier H G ε`: `H` is a reweighted subgraph of `G` and
  `(1 − ε) xᵀL_G x ≤ xᵀL_H x ≤ (1 + ε) xᵀL_G x` for **every** `x : V → ℝ`.
-/

/-- The Laplacian quadratic form `xᵀ L_G x = Σ_e c(e) (x_a − x_b)²`. -/
noncomputable def lapForm {V E : Type*} [Fintype E] (G : CapGraph V E) (x : V → ℝ) : ℝ :=
  ∑ e, G.u e * Sym2.lift ⟨fun a b => (x a - x b) ^ 2, fun a b => by ring⟩ (G.ends e)

/-- `H` is a reweighted subgraph of `G`: its records are an injectively indexed subfamily of `G`'s
records with the same ends, and its capacities are positive. -/
def IsReweightedSubgraph {V E E' : Type*} (H : CapGraph V E') (G : CapGraph V E) : Prop :=
  ∃ ι : E' → E, Function.Injective ι ∧ (∀ e, H.ends e = G.ends (ι e)) ∧ ∀ e, 0 < H.u e

/-- Definition 59: `H` is a `(1 ± ε)`-spectral sparsifier of `G`. -/
def IsSpectralSparsifier {V E E' : Type*} [Fintype E] [Fintype E'] (H : CapGraph V E')
    (G : CapGraph V E) (ε : ℝ) : Prop :=
  IsReweightedSubgraph H G ∧
    ∀ x : V → ℝ, (1 - ε) * lapForm G x ≤ lapForm H x ∧ lapForm H x ≤ (1 + ε) * lapForm G x

end MinKCutII.Main


