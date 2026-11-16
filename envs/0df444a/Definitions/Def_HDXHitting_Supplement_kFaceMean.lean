-- Prove2me | Definitions.Def_HDXHitting_Supplement_kFaceMean
-- name    : HDXHitting_Supplement_kFaceMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:50:54.243196+00:00
-- url     : https://prove2.me/theorems/9e325a55-7822-4dc6-ac2c-432e3adfd024
-- title:
--   The mean $\mathbb E_{\pi_k}f$ of a function on $k$-faces
-- statement:
--   Let $X$ be a $d$-dimensional complex with top distribution $\pi_d$ and let $1\le k\le d$. The induced distribution $\pi_k$ on $k$-faces gives each $k$-set $\tau$ weight proportional to the probability that a random top face contains it:
--   $$
--   \pi_k(\tau)=\frac{\Pr_{\sigma\sim\pi_d}[\tau\subseteq\sigma]}{\binom dk},
--   $$
--   which sums to $1$ because every top face has $\binom dk$ subsets of size $k$. For $f$ a real function on $k$-sets,
--   $$
--   \mathbb E_{\pi_k}f=\sum_{|\tau|=k}\pi_k(\tau)\,f(\tau).
--   $$
--
--   This is the mean in the hypothesis $\mathbb E_{\pi_k}f\le\mu$ of Theorem 4.1; it equals $\mathbb E_{\sigma\sim\pi_d}\bar f(\sigma)$.
--
--   **Formalization Note** The complex is the published top distribution `HDXHitting.IsTopDist`; a $k$-set in no top face gets weight $0$. This is the $\pi_k$ mean, not the uniform mean over $X(k)$.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d9400dc6e1b6e21e0efe05488a4e247d1be3b89a9c202e92f1e3e56d3), §2.2.1, p.12 (π_k(τ) ∝ Pr_{σ∼π_d}[τ ⊂ σ]); Theorem 4.1, p.20

import Mathlib

namespace HDXHitting.Supplement

/-- The mean `E_{π_k} f` of a function on `k`-faces under the induced distribution `π_k`
(Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript
(sha256 60d23b0d…e56d3), §2.2.1, p.12: "`π_k(τ) ∝ Pr_{σ∼π_d}[τ ⊂ σ]`, the probability that a
maximal face drawn from `π_d` contains `τ`"; used in Theorem 4.1, p.20):
`E_{π_k} f = ∑_{|τ| = k} π_k(τ) f(τ)` with `π_k(τ) = Pr_{σ∼π_d}[τ ⊆ σ] / C(d, k)`.

**Formalization Note** The complex is encoded by its top distribution `p = π_d` (published
`HDXHitting.IsTopDist`). Every top face has `C(d, k)` subsets of size `k`, so
`∑_{|τ| = k} Pr_{σ∼p}[τ ⊆ σ] = C(d, k)` for `k ≤ d` and the normalization makes `π_k` a
probability distribution. A `k`-set contained in no top face has weight `0`, so only `k`-faces
of `X` contribute. This is the `π_k` mean, not the uniform mean over `X(k)`. -/
noncomputable def kFaceMean {V : Type*} [Fintype V] [DecidableEq V] (d k : ℕ)
    (p : Finset V → ℝ) (f : Finset V → ℝ) : ℝ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : Finset V => τ.card = k),
    ((∑ σ ∈ Finset.univ.filter (fun σ : Finset V => τ ⊆ σ), p σ) / (d.choose k : ℝ)) * f τ

end HDXHitting.Supplement


