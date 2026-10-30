-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_Mbar
-- name    : WainwrightHDS_NucNorm_Mbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:28:35.388989+00:00
-- url     : https://prove2.me/theorems/d3794f54-d59e-42f7-95cd-a8f7814fe296
-- title:
--   The subspace $\overline{\mathbb M}(\mathbb U,\mathbb V)$, orthogonal complement of $\overline{\mathbb M}^\perp$
-- statement:
--   For linear subspaces $\mathbb U\subseteq\mathbb R^{d_1}$, $\mathbb V\subseteq\mathbb R^{d_2}$, the subspace $\overline{\mathbb M}(\mathbb U,\mathbb V)$ is the orthogonal complement of $\overline{\mathbb M}^\perp(\mathbb U,\mathbb V)$ with respect to the trace inner product:
--
--   $$
--   \overline{\mathbb M}(\mathbb U,\mathbb V) \;:=\; \{\Theta\in\mathbb R^{d_1\times d_2} \;:\; \langle\!\langle \Theta,B\rangle\!\rangle=0\ \text{ for all } B\in\overline{\mathbb M}^\perp(\mathbb U,\mathbb V)\}.
--   $$
--
--   It contains $\mathbb M(\mathbb U,\mathbb V)$, strictly so in general; when $\dim\mathbb U,\dim\mathbb V\le r$ its members have rank at most $2r$.
--
--   **Formalization Note** The subspaces are arbitrary.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.2.1, p. 317 (PDF p. 337), text after (10.12b), and p. 318 (PDF p. 338), (10.14)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner
import Definitions.Def_WainwrightHDS_NucNorm_MbarPerp

namespace WainwrightHDS.NucNorm

/-- **The subspace** `𝕄̄(𝕌, 𝕍)`: the orthogonal complement of `𝕄̄⊥(𝕌, 𝕍)` in the trace inner
product, `𝕄̄ = {Θ | ⟨⟨Θ, B⟩⟩ = 0 for all B ∈ 𝕄̄⊥(𝕌, 𝕍)}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.2.1, p. 317 (PDF p. 337) ("equation (10.12b) defines the subspace 𝕄̄(𝕌, 𝕍) implicitly,
via taking the orthogonal complement") and p. 318 (PDF p. 338), (10.14) ("Since the trace inner
product defines orthogonality, any member Ā of 𝕄̄(𝕌, 𝕍) must take the form (10.14)").

Formalization Note: `𝕌`, `𝕍` are arbitrary subspaces. -/
def Mbar {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) : Set (Matrix (Fin d₁) (Fin d₂) ℝ) :=
  {Θ | ∀ B ∈ MbarPerp U V, traceInner Θ B = 0}

end WainwrightHDS.NucNorm


