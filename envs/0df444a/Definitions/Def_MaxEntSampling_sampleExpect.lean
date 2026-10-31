-- Prove2me | Definitions.Def_MaxEntSampling_sampleExpect
-- name    : MaxEntSampling_sampleExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:47.661318+00:00
-- url     : https://prove2.me/theorems/5a3c0d86-c905-4641-bcce-ce317dce4622
-- title:
--   Expected $\det^s$ of the sampled set under the law (13)
-- statement:
--   Given $\hat x\in D$, the sampling procedure of §3.2 draws a random size-$s$ subset $\tilde S\subseteq[n]$ with
--
--   $$
--   \mathbb P[\tilde S=S] = \frac{\prod_{i\in S}\hat x_i}{\sum_{\bar S\in\binom{[n]}{s}}\prod_{i\in\bar S}\hat x_i}\qquad(|S|=s).
--   $$
--
--   The quantity defined here is the expected objective
--
--   $$
--   \mathbb E\Bigl[{\det}^s\Bigl(\sum_{i\in\tilde S}v_iv_i^\top\Bigr)\Bigr] = \sum_{S\in\binom{[n]}{s}}\frac{\prod_{i\in S}\hat x_i}{E_s(\hat x)}\,{\det}^s\Bigl(\sum_{i\in S}v_iv_i^\top\Bigr).
--   $$
--
--   **Formalization Note** The expectation is the finite sum over the support of the law (the first equality of the proof of Theorem 5); $\sum_{i\in S}v_iv_i^\top=V_SV_S^\top$ is `PropVolSampling.Reduction.gram V S`. The denominator $E_s(\hat x)$ is positive on $D$, so the law is well defined there.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, eq. (13), p.14 (PDF p.14); proof of Theorem 5, p.15

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Definitions.Def_MaxEntSampling_detTop
import Definitions.Def_MaxEntSampling_esymm

open Finset

namespace MaxEntSampling

open PropVolSampling.Reduction

/-- **`E[det^s(Σ_{i∈S̃} v_i v_iᵀ)]` under the sampling law (13).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, eq. (13), p.14 (PDF p.14): a size-`s` subset `S ⊆ [n]` is sampled with
"P[S̃ = S] := ∏_{i∈S} x̂i / Σ_{S̄∈C([n],s)} ∏_{i∈S̄} x̂i"; the expectation is the first equality of
the proof of Theorem 5, p.15:
"E[det^s(Σ_{i∈S̃} vi vi^⊤)] = Σ_{S∈C([n],s)} P[S̃ = S] det^s(V_S V_S^⊤)".

`sampleExpect V s x = Σ_{|S| = s} (∏_{i∈S} x_i / E_s(x)) · det^s(Σ_{i∈S} v_i v_iᵀ)`.

**Formalization Note.** The expectation is written as the finite sum over the support of the law;
`Σ_{i∈S} v_i v_iᵀ = V_S V_Sᵀ` is `PropVolSampling.Reduction.gram V S` and `∏_{i∈S} x_i` is
`xPow x S`. The denominator `E_s(x)` is positive for every `x` in the feasible set `D` of PC (9)
with `s ≤ n` (proved in `Solutions/verification/MaxEntSampling_sanity.lean`), so the division is
genuine there. -/
noncomputable def sampleExpect {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Fin n)).powersetCard s, xPow x S / esymm s x * detTop s (gram V S)

end MaxEntSampling


