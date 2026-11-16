-- Prove2me | Definitions.Def_KMPMixing_Supplement_labeledParallelKMP
-- name    : KMPMixing_Supplement_labeledParallelKMP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:53:27.770211+00:00
-- url     : https://prove2.me/theorems/7332511d-189c-4fc2-99be-faa9c64ad688
-- title:
--   The labeled parallel KMP chain $M^{(t,d)}_{\mathrm{LPKMP}}$
-- statement:
--   Let $d\ge2$ be even, $t\ge1$ and $\Omega=[d]^t$, where $x_\ell$ is the site of particle $\ell$. One step of the **labeled parallel KMP chain** samples a uniformly random perfect matching $\mathcal M$ of $[d]$ and an independent $p_{ij}\sim\mathrm{Unif}[0,1]$ for every pair $\{i,j\}\in\mathcal M$; every particle at $i$ or $j$ is then placed at $i$ independently with probability $p_{ij}$, and at $j$ otherwise.
--
--   For a pair $\{i,j\}$ let $a$ and $b$ be the numbers of particles of $x$ in $\{i,j\}$ that $y$ places at $i$ and at $j$. The transition matrix is
--   $$
--   M_{\mathrm{LPKMP}}(x,y)=\mathbb E_{\mathcal M}\prod_{\{i,j\}\in\mathcal M}\mathbb 1[\forall\ell:\ x_\ell\in\{i,j\}\Rightarrow y_\ell\in\{i,j\}]\int_0^1p^a(1-p)^b\,dp.
--   $$
--   Its stationary law is $\pi_{\mathrm{LPKMP}}(x)=\prod_i\#_i(x)!/(t!\binom{t+d-1}{d-1})$ (Lemma B.3), the base mission's `KMPMixing.labeledStationary`.
--
--   This chain is the labeled lift used to bound the mixing of the parallel KMP chain.
--
--   **Formalization Note** $\Omega$ is `Fin t → Fin d`. Each pair $\{i,\sigma(i)\}$ is taken once with $i<\sigma(i)$ and $p$ is the probability of going to $i$; the law of $p$ is symmetric, so the orientation is immaterial. Every site lies in one pair, so the indicators keep every particle inside its pair.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Definition B.2, p.71 (PDF p.73); Lemma B.3, p.71 (PDF p.73)

import Mathlib
import Definitions.Def_KMPMixing_labeledChain
import Definitions.Def_KMPMixing_Supplement_perfectMatching

namespace KMPMixing.Supplement

open MarkovMixing KMPMixing

/-- The transition matrix `M^{(t,d)}_LPKMP` of the **labeled parallel KMP chain** on
`Ω = [d]^t` (arXiv:2609.38044, Definition B.2, p.71 (PDF p.73)): sample a uniformly random
perfect matching `M` of `[d]`; for every pair `{i, j} ∈ M` sample an independent
`p_{ij} ∼ Unif[0, 1]`; every particle currently at `i` or `j` is independently placed at `i`
with probability `p_{ij}` and otherwise at `j`. Hence, for each pair, with
`a = #{ℓ : x_ℓ ∈ {i, j}, y_ℓ = i}` and `b = #{ℓ : x_ℓ ∈ {i, j}, y_ℓ = j}`, the pair contributes
`𝟙[∀ ℓ, x_ℓ ∈ {i, j} → y_ℓ ∈ {i, j}] · ∫₀¹ p^a (1 − p)^b dp`, and
`M_LPKMP(x, y) = E_M ∏_{{i,j} ∈ M} (that factor)`.

**Formalization Note** `Ω` is `Fin t → Fin d` (particle `ℓ` sits at `x ℓ`). The matching is a
fixed-point-free involution `σ`, averaged uniformly; the pair `{i, σ i}` is taken once, with
`i < σ i`, and `p` is the probability of going to `i` (the law of `p` is symmetric, so the
orientation does not matter). Every site lies in exactly one pair, so the indicators force every
particle to stay inside its pair. For odd `d` the matrix is `0`; every statement assumes `d`
even. -/
noncomputable def lpkmpChain (d t : ℕ) : Matrix (Fin t → Fin d) (Fin t → Fin d) ℝ :=
  fun x y => ((Fintype.card (PerfectMatching d) : ℝ))⁻¹ *
    ∑ σ : PerfectMatching d, ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i),
      (if ∀ ℓ, (x ℓ = i ∨ x ℓ = σ.1 i) → (y ℓ = i ∨ y ℓ = σ.1 i) then
        ∫ p in (0 : ℝ)..1,
          p ^ (Finset.univ.filter fun ℓ => (x ℓ = i ∨ x ℓ = σ.1 i) ∧ y ℓ = i).card *
          (1 - p) ^ (Finset.univ.filter fun ℓ => (x ℓ = i ∨ x ℓ = σ.1 i) ∧ y ℓ = σ.1 i).card
      else 0)

end KMPMixing.Supplement


