-- Prove2me | Definitions.Def_ROGCones_CondII
-- name    : ROGCones_CondII
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:50.242045+00:00
-- url     : https://prove2.me/theorems/e297ff61-2628-4792-aab6-e081d6e7799a
-- title:
--   Condition (ii): $M_1 = \mathrm{Sym}(ac^\top)$, $M_2 = \mathrm{Sym}(bc^\top)$ with a common $c$
-- statement:
--   Two matrices $M_1, M_2$ satisfy **condition (ii)** if there are vectors $a, b, c \in \mathbb R^n$ with
--   $$
--   M_1 = \mathrm{Sym}(ac^\top), \qquad M_2 = \mathrm{Sym}(bc^\top),
--   $$
--   where $\mathrm{Sym}(ac^\top) = (ac^\top + ca^\top)/2$. The vector $c$ is the same for both matrices. Then $\langle M_1, X\rangle = a^\top X c$ and $\langle M_2, X\rangle = b^\top X c$ for symmetric $X$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ` and $ac^\top$ is `Matrix.vecMulVec a c`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Theorems 3 and 4, p.15

import Mathlib
import Definitions.Def_ROGCones_Sym

namespace ROGCones

/-- **Condition (ii) of Theorems 3 and 4**: `M₁ = Sym(acᵀ)`, `M₂ = Sym(bcᵀ)` with a common `c`.
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Theorems 3 and 4, p.15: "(ii) there exists
a, b, c ∈ ℝⁿ such that M₁ = Sym(ac⊤) and M₂ = Sym(bc⊤)."

**Formalization Note.** ℝⁿ is `Fin n → ℝ`, the outer product `acᵀ` is `Matrix.vecMulVec a c`,
and `Sym(M) = (M + Mᵀ)/2` (so `Sym(acᵀ) = (acᵀ + caᵀ)/2`). The vector `c` is shared by both
matrices. -/
def CondII {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ a b c : Fin n → ℝ, M₁ = Sym (Matrix.vecMulVec a c) ∧ M₂ = Sym (Matrix.vecMulVec b c)

end ROGCones


