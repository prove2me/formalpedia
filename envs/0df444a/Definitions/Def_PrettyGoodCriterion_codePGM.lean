-- Prove2me | Definitions.Def_PrettyGoodCriterion_codePGM
-- name    : PrettyGoodCriterion_codePGM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:32:34.951788+00:00
-- url     : https://prove2.me/theorems/9d06cc3e-5955-4366-8300-958f784920e9
-- title:
--   The PGM of a code, block success probability and expected Hamming distance
-- statement:
--   Fix output states $\sigma_0,\sigma_1$ and a binary code $\mathcal C\subseteq\{0,1\}^n$. The paper identifies $\mathcal C$ with the uniform ensemble
--   $$\{(|\mathcal C|^{-1},\sigma_c):c\in\mathcal C\},\qquad \sigma_c=\sigma_{c_1}\otimes\cdots\otimes\sigma_{c_n}.$$
--
--   1. The **PGM of $\mathcal C$** is the pretty good measurement of this ensemble, with outcomes $\hat c\in\mathcal C$ and observables $M_{\hat c}$.
--   2. For a decoder POVM $\{D_c:c\in\mathcal C\}$ and a uniformly random codeword $c$, the **block success probability** is
--   $$\Pr[\hat c=c]=\frac{1}{|\mathcal C|}\sum_{c\in\mathcal C}\operatorname{Tr}(\sigma_cD_c);$$
--   for the PGM, $D_c=M_c$.
--   3. The **expected Hamming distance** between $c$ and the PGM outcome $\hat c$ is
--   $$\mathbb E[d(\hat c,c)]=\sum_{c,\hat c\in\mathcal C}\frac{1}{|\mathcal C|}\operatorname{Tr}(\sigma_cM_{\hat c})\,d(\hat c,c).$$
--
--   These are the quantities compared in the proof of the main theorem: the PGM makes few bit errors (Theorem 17), hence decodes whole blocks with constant probability (Corollary 18), which the strong converse (Theorem 7) caps unless the rate is at most the Holevo information.
--
--   **Formalization Note** The outcome set is the subtype `{c // c ∈ C}`; a decoder is a function on it. $\sigma_c$ is the published `HolevoCQ.wordState σ n c`. Real parts of traces are taken.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), p.18 (PDF 20) and §3, p.21 (PDF 23) (code ensemble); Theorem 7, p.17 (PDF 19) and (65), p.70 (PDF 72) (success probability); Theorem 17 and Corollary 18, p.22 (PDF 24)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_HolevoCQ_wordState

namespace PrettyGoodCriterion

/-- The uniform prior `|𝒞|⁻¹` of the code ensemble `{(|𝒞|⁻¹, σ_c) : c ∈ 𝒞}`, with which the paper
conflates the code `𝒞`, Alrabiah–Guruswami, arXiv:2608.09347 (held version), p.18 (PDF 20) and
§3, p.21 (PDF 23).

**Formalization Note.** The outcome set is the code itself, the subtype `{c // c ∈ 𝒞}`. -/
noncomputable def codePrior {n : ℕ} (C : Finset (Fin n → Fin 2)) : C → ℝ :=
  fun _ => ((C.card : ℝ))⁻¹

/-- The states `σ_c = σ_{c₁} ⊗ ⋯ ⊗ σ_{cₙ}` (`c ∈ 𝒞`) of the code ensemble,
arXiv:2608.09347 (held version), Definition 2.4, p.15 and §3, p.21 (PDF 17, 23).

**Formalization Note.** `σ_c` is the published `HolevoCQ.wordState σ n c`: the matrix indexed by
`Fin n → ι` (coordinate `i` is the `i`-th tensor factor) with entries `∏ᵢ σ_{cᵢ}(aᵢ, bᵢ)`. -/
def codeStates {ι : Type} {n : ℕ} (σ : Fin 2 → Matrix ι ι ℂ) (C : Finset (Fin n → Fin 2)) :
    C → Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  fun c => HolevoCQ.wordState σ n c.1

/-- The **PGM of the code** `𝒞`: the pretty good measurement (Definition 2.7) of the uniform
ensemble `{(|𝒞|⁻¹, σ_c) : c ∈ 𝒞}`, with outcomes `ĉ ∈ 𝒞`, arXiv:2608.09347 (held version),
§3, p.21–22 (PDF 23–24). -/
noncomputable def codePGM {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (σ : Fin 2 → Matrix ι ι ℂ) (C : Finset (Fin n → Fin 2)) :
    C → Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  pgm (codePrior C) (codeStates σ C)

/-- The average block success probability `Pr[ĉ = c] = |𝒞|⁻¹ ∑_{c∈𝒞} Tr(σ_c D_c)` of a decoder
`{D_c : c ∈ 𝒞}` for a uniformly random codeword `c`, arXiv:2608.09347 (held version),
Theorem 7, p.17 (PDF 19), and (65), p.70 (PDF 72).

**Formalization Note.** Real part of the trace. -/
noncomputable def decoderSuccess {ι : Type} [Fintype ι] {n : ℕ} (σ : Fin 2 → Matrix ι ι ℂ)
    (C : Finset (Fin n → Fin 2)) (D : C → Matrix (Fin n → ι) (Fin n → ι) ℂ) : ℝ :=
  ∑ c : C, ((C.card : ℝ))⁻¹ * (HolevoCQ.wordState σ n c.1 * D c).trace.re

/-- `Pr[ĉ = c]` for the PGM of the code, arXiv:2608.09347 (held version), Corollary 18, p.22
(PDF 24). -/
noncomputable def pgmBlockSuccess {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (σ : Fin 2 → Matrix ι ι ℂ) (C : Finset (Fin n → Fin 2)) : ℝ :=
  decoderSuccess σ C (codePGM σ C)

/-- `E[d(ĉ, c)] = ∑_{c, ĉ ∈ 𝒞} |𝒞|⁻¹ Tr(σ_c M_ĉ) d(ĉ, c)`, the expected Hamming distance between
a uniform codeword `c` and the outcome `ĉ` of the code's PGM applied to `σ_c`,
arXiv:2608.09347 (held version), Theorem 17, p.22 (PDF 24).

**Formalization Note.** Real parts of traces; Hamming distance `hammingDist`. -/
noncomputable def pgmExpectedDistance {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (σ : Fin 2 → Matrix ι ι ℂ) (C : Finset (Fin n → Fin 2)) : ℝ :=
  ∑ c : C, ∑ ch : C,
    ((C.card : ℝ))⁻¹ * (HolevoCQ.wordState σ n c.1 * codePGM σ C ch).trace.re * (hammingDist ch.1 c.1 : ℝ)

end PrettyGoodCriterion


