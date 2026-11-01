-- Prove2me | Definitions.Def_NoSignalPA_gammaVec
-- name    : NoSignalPA_gammaVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:46.584561+00:00
-- url     : https://prove2.me/theorems/d868afad-7f08-4935-a3d4-712d688e9ba0
-- title:
--   The vector $|\Gamma_{\mathbf a}\rangle=|\gamma_{a_1}\rangle\otimes\cdots\otimes|\gamma_{a_{N_r}}\rangle$
-- statement:
--   For a string $\mathbf s\in\{0,1\}^n$, $|\Gamma_{\mathbf s}\rangle=|\gamma_{s_1}\rangle\otimes\cdots\otimes|\gamma_{s_n}\rangle\in\mathbb R^{16^n}$, with entries
--
--   $$
--   \Gamma_{\mathbf s}(\mathbf a,\mathbf b,\mathbf x,\mathbf y)=\prod_{i=1}^n\gamma_{s_i}(a_i,b_i,x_i,y_i),
--   $$
--
--   where $|\gamma_0\rangle,|\gamma_1\rangle$ are the (transposed) tables of Lemma 1. Lemma 1 says that $\langle\Gamma_{\mathbf s}|P\rangle$ is the probability that Alice outputs $\mathbf s$ on input $\mathbf 0$; in the proof of Lemma 2, $\mu_{\mathbf a}=\Gamma_{\mathbf a}(\mathbf a_0,\mathbf b_0,\mathbf x_0,\mathbf y_0)$.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Lemma 1, p.2; Appendix, p.5

import Mathlib
import Definitions.Def_NoSignalPA_Str
import Definitions.Def_NoSignalPA_gammaCoef

namespace NoSignalPA

/-- **The vector `|Γ_s⟩ = |γ_{s_1}⟩ ⊗ ⋯ ⊗ |γ_{s_n}⟩` of Lemma 1.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Lemma 1, p. 2 (PDF p. 2): "`|Γ_a⟩ = |γ_{a_1}⟩ ⊗ · · · ⊗ |γ_{a_{Nr}}⟩`".

`gammaVec s` is the vector indexed by the string `s` (the paper's subscript `a`); its entry at
`(a, b, x, y)` is `∏ᵢ γ_{s_i}(a_i, b_i, x_i, y_i)`, the single-system entries being
`gammaCoef` (the corrected, transposed tables). In the proof of Lemma 2 (p. 5),
`μ_a = Γ_a(a₀, b₀, x₀, y₀)` is `gammaVec a a₀ b₀ x₀ y₀`. -/
noncomputable def gammaVec {n : ℕ} (s a b x y : Str n) : ℝ :=
  ∏ i, gammaCoef (s i) (a i) (b i) (x i) (y i)

end NoSignalPA


