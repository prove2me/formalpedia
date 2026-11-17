-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_pStay
-- name    : TwoFoldOPI_Supplement_pStay
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:50:06.5772+00:00
-- url     : https://prove2.me/theorems/068c7c60-13e6-4021-9a2b-0bd4d52664a8
-- title:
--   The stay probability $p_{\mathrm{stay}}$
-- statement:
--   Fix load data $B_1,\dots,B_R\subseteq\mathbb Z_{\ge0}$, weights $\alpha_1,\dots,\alpha_R>0$, a mean load $\eta>0$ and a tilt $\nu>0$, and write $p^{(r)}_k$ for the probability of $k$ under $\mathrm{TiltPoiss}_{\nu,B_r}$. Let $(I_{\mathrm{src}},K_{\mathrm{src}})$ and $(I_{\mathrm{tar}},K_{\mathrm{tar}})$ be independent with
--   $$\Pr[I_{\mathrm{src}}=r,K_{\mathrm{src}}=k]=\frac{\alpha_r}{\eta}\,k\,p^{(r)}_k,\qquad \Pr[I_{\mathrm{tar}}=r,K_{\mathrm{tar}}=k]=\alpha_r\,p^{(r)}_k .$$
--   The **stay probability** is
--   $$p_{\mathrm{stay}}=\Pr[K_{\mathrm{src}}-1\in B_{I_{\mathrm{src}}}]\cdot\Pr[K_{\mathrm{tar}}+1\in B_{I_{\mathrm{tar}}}].$$
--
--   It is the limit of the probability that one coordinate-replacement step keeps a uniform word of a load set inside the set (Theorem 10.11), and it governs the rate thresholds of Theorems 11.3, 11.9 and 12.2.
--
--   **Formalization Note** The module defines the two factors (`srcStay`, `tarStay`) and their product. The event $K_{\mathrm{src}}-1\in B$ is false at $K_{\mathrm{src}}=0$, a value of probability $0$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.11, p. 56; §5.4, Definition 5.36, p. 33; Theorems 11.9 (p. 62) and 12.2 (p. 65)

import Mathlib
import Definitions.Def_TwoFoldOPI_Supplement_tiltPoiss

namespace TwoFoldOPI

namespace Supplement

open Classical in
/-- **The stay probability `p_stay = Pr[K_src − 1 ∈ B_{I_src}] · Pr[K_tar + 1 ∈ B_{I_tar}]`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.11, p.56: "Define independent random variables (I_src, K_src) and
(I_tar, K_tar) by Pr[I_src = r ∧ K_src = k] = (α_r/η) k Pr_{K∼TiltPoiss_{ν,B_r}}[K = k],
(I_tar, K_tar) ∼ TiltPoiss_{ν,{B_r},{α_r}}. Then Pr[X′ ∈ T] = Pr[K_src − 1 ∈ B_{I_src}]
Pr[K_tar + 1 ∈ B_{I_tar}] + O(n^{−1/2})"; §5.4, Definition 5.36, p.33 (the multi-class law
Pr[I = i ∧ K = k] = α_i p^{(i)}_k); Theorem 11.9, p.62 and Theorem 12.2, p.65
("p_stay = Pr[K_src − 1 ∈ B_{I_src}] Pr[K_tar + 1 ∈ B_{I_tar}]").

With `p^{(r)}_k = tiltPoiss ν (B r) k`:
* `srcStay = Σ_r Σ_{k ≥ 1, k−1 ∈ B_r} (α_r/η) · k · p^{(r)}_k` (the size-biased source law);
* `tarStay = Σ_r Σ_{k+1 ∈ B_r} α_r · p^{(r)}_k` (the multi-class tilted Poisson law);
* `pStay = srcStay · tarStay` (the two pairs are independent).

**Formalization Note.** `K_src − 1 ∈ B` is false at `K_src = 0` (`B ⊆ ℤ_{≥0}`); that term has
weight `0` anyway. The size-biased weights sum to `1` exactly when the mixture mean is `η`
(admissibility, Definition 10.9), which every statement using `pStay` assumes. -/
noncomputable def srcStay {R : ℕ} (B : Fin R → Set ℕ) (α : Fin R → ℝ) (η ν : ℝ) : ℝ :=
  ∑ r, ∑' k : ℕ,
    if 1 ≤ k ∧ k - 1 ∈ B r then α r / η * (k : ℝ) * tiltPoiss ν (B r) k else 0

open Classical in
/-- `Pr[K_tar + 1 ∈ B_{I_tar}]` for `(I_tar, K_tar) ∼ TiltPoiss_{ν,{B_r},{α_r}}`
(Theorem 10.11, p.56; Definition 5.36, p.33). -/
noncomputable def tarStay {R : ℕ} (B : Fin R → Set ℕ) (α : Fin R → ℝ) (ν : ℝ) : ℝ :=
  ∑ r, ∑' k : ℕ, if k + 1 ∈ B r then α r * tiltPoiss ν (B r) k else 0

/-- `p_stay = Pr[K_src − 1 ∈ B_{I_src}] · Pr[K_tar + 1 ∈ B_{I_tar}]` (Theorems 10.11, 11.9, 12.2). -/
noncomputable def pStay {R : ℕ} (B : Fin R → Set ℕ) (α : Fin R → ℝ) (η ν : ℝ) : ℝ :=
  srcStay B α η ν * tarStay B α ν

end Supplement

end TwoFoldOPI


