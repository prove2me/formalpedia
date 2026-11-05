-- Prove2me | Definitions.Def_Chi2QEC_annihilation
-- name    : Chi2QEC_annihilation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:25.80784+00:00
-- url     : https://prove2.me/theorems/dbc0afba-52cc-4779-a368-326ef0cd24bc
-- title:
--   Annihilation operator $\hat a_{\ell,k}$ of one mode
-- statement:
--   The annihilation operator $\hat a_{\ell,k}$ of mode $k$ of qudit $\ell$ acts on Fock states by
--   $$
--   \hat a|m\rangle=\sqrt m\,|m-1\rangle,\qquad \hat a|0\rangle=0
--   $$
--   on that mode, and as the identity on every other mode.
--
--   These are the operators $\hat a_{k_\ell}$ of the paper's Kraus operators for single-photon loss. The weight $\sqrt m$ is what makes the probability of a loss depend on the state, and so what gives the error-correction condition its content.
--
--   **Formalization Note** The operator is a matrix on the truncated Fock basis `FockIdx n q`, whose entry at row $x$ and column $y$ is $\langle x|\hat a_{\ell,k}|y\rangle$. It agrees with the true operator on the truncated space, since $\hat a$ never raises a photon number.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, (20)–(21), p.7

import Mathlib
import Definitions.Def_Chi2QEC_FockIdx

namespace Chi2QEC

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. III C, p.7, the operators `â_{k_ℓ}` of (20)–(21) (`â_{s_1}, â_{i_1},
â_{p_1}, …`): the photon annihilation operator of mode `k` of qudit `ℓ`, `â|m⟩ = √m |m - 1⟩` on
that mode (and `â|0⟩ = 0`), the identity on every other mode.

**Formalization Note.** The matrix entry at row `x`, column `y` is `⟨x|â|y⟩`: it is `√(y ℓ k)` when
`x` and `y` agree off `(ℓ, k)` and `x ℓ k + 1 = y ℓ k`, and `0` otherwise. Modes are signal, idler,
pump = `0, 1, 2`. On the truncated Fock space of `FockIdx` this matrix agrees with the true
operator, because `â` never raises a photon number. -/
noncomputable def annihilation (n q : ℕ) (ℓ : Fin n) (k : Fin 3) :
    Matrix (FockIdx n q) (FockIdx n q) ℂ :=
  fun x y =>
    if (∀ ℓ' k', (ℓ', k') ≠ (ℓ, k) → x ℓ' k' = y ℓ' k') ∧ (x ℓ k : ℕ) + 1 = (y ℓ k : ℕ) then
      (Real.sqrt ((y ℓ k : ℕ) : ℝ) : ℂ)
    else 0

end Chi2QEC


