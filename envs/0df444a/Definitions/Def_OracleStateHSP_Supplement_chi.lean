-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_chi
-- name    : OracleStateHSP_Supplement_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:06:03.294338+00:00
-- url     : https://prove2.me/theorems/59354341-e5cd-44a5-a223-8cae0b18824e
-- title:
--   Characters $\chi_\lambda(g) = \prod_l e^{2\pi i g_l\lambda_l/M_l}$ (eq. (11))
-- statement:
--   For $G = \mathbb Z_{M_1} \times \dots \times \mathbb Z_{M_n}$ and a dual label $\lambda = (\lambda_1, \dots, \lambda_n)$, the character (one-dimensional irreducible representation) indexed by $\lambda$ is
--   $$
--   \chi_\lambda(g) = \prod_{l=1}^{n} e^{\frac{2\pi i}{M_l} g_l \lambda_l}.
--   $$
--   For $G = \mathbb Z_2^n$ this is $\chi_\lambda(g) = (-1)^{g\cdot\lambda}$. The characters are the labels returned by weak Fourier sampling.
--
--   **Formalization Note** $g_l$ and $\lambda_l$ are the representatives in $\{0, \dots, M_l - 1\}$ (`ZMod.val`). The formula is symmetric in $\lambda$ and $g$, so the same function also pairs elements of $\hat G$ with elements of $G \cong \hat{\hat G}$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (11), p.15

import Mathlib
import Definitions.Def_OracleStateHSP_Supplement_CycProd

namespace OracleStateHSP

namespace Supplement

/-- The character `χ_λ` of the finite abelian group `G = Z_(M_1) × ⋯ × Z_(M_n)` indexed by the dual
label `λ` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (11), p.15):
`χ_λ(g) = ∏_(l=1)^n exp(2πi g_l λ_l / M_l)`.

**Formalization Note.** `g_l, λ_l ∈ [M_l]` are the representatives `ZMod.val` in
`{0, …, M_l − 1}`. The pairing is symmetric in `(λ, g)`, so the same function also evaluates a
character of `Ĝ` at an element of `G` (`Ĝ̂ ≅ G`), as used for `(K⊥)⊥` in Definition 3.3. -/
noncomputable def chi {n : ℕ} {M : Fin n → ℕ} (lam g : CycProd n M) : ℂ :=
  ∏ l, Complex.exp (2 * Real.pi * Complex.I * ((g l).val : ℂ) * ((lam l).val : ℂ) / (M l : ℂ))

end Supplement

end OracleStateHSP


