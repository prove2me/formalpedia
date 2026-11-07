-- Prove2me | Definitions.Def_TIEMaximin_Bihierarchy
-- name    : TIEMaximin_Bihierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:17.318767+00:00
-- url     : https://prove2.me/theorems/ec13b5b5-e772-4462-b2a7-d17409db0d2c
-- title:
--   The bihierarchy polytope
-- statement:
--   For two families $\mathcal F_1,\mathcal F_2$ of subsets of a finite set $E$ and integers $\ell_F,u_F$, the **bihierarchy polytope** is
--
--   $$P=\Bigl\{y\in[0,1]^E:\ \ell_F\le\sum_{e\in F}y_e\le u_F\ \text{ for all }F\in\mathcal F_1\cup\mathcal F_2\Bigr\}.$$
--
--   This is the polytope of Lemma 2.7, which every implementation step of the mechanism relies on.
--
--   **Formalization Note** The bounds $\ell,u$ are integer-valued functions on sets, read only on members of the two families.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 2.7, p.9

import Mathlib

namespace TIEMaximin

/-- **The bihierarchy polytope of Lemma 2.7** (p.9):
`P = { y ∈ [0,1]^E : ℓ_F ≤ Σ_{e∈F} y_e ≤ u_F for all F ∈ 𝓕₁ ∪ 𝓕₂ }`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 2.7, p.9.

**Formalization Note.** Points are real vectors `E → ℝ`; the integer bounds `ℓ, u` are functions
on sets, only read on members of `𝓕₁ ∪ 𝓕₂`. -/
def bihierPolytope {E : Type} [DecidableEq E] (𝓕₁ 𝓕₂ : Finset (Finset E))
    (l u : Finset E → ℤ) : Set (E → ℝ) :=
  {y | (∀ e, 0 ≤ y e ∧ y e ≤ 1) ∧
    ∀ F ∈ 𝓕₁ ∪ 𝓕₂, ((l F : ℤ) : ℝ) ≤ ∑ e ∈ F, y e ∧ ∑ e ∈ F, y e ≤ ((u F : ℤ) : ℝ)}

end TIEMaximin


