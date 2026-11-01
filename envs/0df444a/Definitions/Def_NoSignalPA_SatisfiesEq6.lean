-- Prove2me | Definitions.Def_NoSignalPA_SatisfiesEq6
-- name    : NoSignalPA_SatisfiesEq6
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:05:20.888205+00:00
-- url     : https://prove2.me/theorems/d5f46768-b0f2-45a8-a4c7-fe2b8783a40e
-- title:
--   The entrywise inequality (6) of Lemma 2
-- statement:
--   For a hash function $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$ and a key value $\mathbf k$, let $\mathcal A_{\mathbf k}=h^{-1}(\mathbf k)$ and $|\Gamma_{\mathcal A_{\mathbf k}}\rangle=\sum_{\mathbf a\in\mathcal A_{\mathbf k}}|\Gamma_{\mathbf a}\rangle$. The function $h$ **satisfies (6)** when, for every $\mathbf k$ and every entry $(\mathbf a,\mathbf b,\mathbf x,\mathbf y)$,
--
--   $$
--   \Bigl|2^{N_s}\,\Gamma_{\mathcal A_{\mathbf k}}(\mathbf a,\mathbf b,\mathbf x,\mathbf y)-4^{-N_r}\Bigr|\ \le\ \sqrt{2^{\,N_s+\sqrt{N_r}}}\ \mathrm{CHSH}^{\otimes N_r}(\mathbf a,\mathbf b,\mathbf x,\mathbf y).
--   $$
--
--   This is the property Lemma 2 shows almost every $h$ has, and from which the proof of the main result derives the security bound (5).
--
--   **Formalization Note** $|\Gamma_{\mathbf a}\rangle$ is built from the transposed tables of Lemma 1 (see the definition of $\gamma_0,\gamma_1$).
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Lemma 2, eq. (6), p.2

import Mathlib
import Definitions.Def_NoSignalPA_chshPow
import Definitions.Def_NoSignalPA_gammaVec

namespace NoSignalPA

/-- **The entrywise inequality (6) of Lemma 2.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Lemma 2, eq. (6), p. 2 (PDF p. 2): for `A_k = h^{−1}(k)` and `|Γ_{A_k}⟩ = Σ_{a∈A_k} |Γ_a⟩`,

`|2^{Ns} |Γ_{A_k}⟩ − 4^{−Nr} |1s⟩| ⪯ √2^{Ns+√Nr} |CHSH⟩^{⊗Nr}` for all `k`,

where `|·|` is the entrywise absolute value and `⪯` the entrywise order.

`SatisfiesEq6 h` states this for every `k` and every entry `(a, b, x, y)`, with `|Γ_a⟩` the
corrected vector `gammaVec` (transposed tables). -/
def SatisfiesEq6 {Nr Ns : ℕ} (h : Str Nr → Str Ns) : Prop :=
  ∀ (k : Str Ns) (a b x y : Str Nr),
    |(2 : ℝ) ^ Ns * ∑ s ∈ Finset.univ.filter (fun s => h s = k), gammaVec s a b x y
        - ((4 : ℝ) ^ Nr)⁻¹|
      ≤ Real.sqrt ((2 : ℝ) ^ ((Ns : ℝ) + Real.sqrt Nr)) * chshPow a b x y

end NoSignalPA


