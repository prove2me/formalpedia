-- Prove2me | Definitions.Def_KMPMixing_Supplement_perfectMatching
-- name    : KMPMixing_Supplement_perfectMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:52:14.591613+00:00
-- url     : https://prove2.me/theorems/96bf7cc9-b6c5-4a51-afe8-4a4c7f01519b
-- title:
--   Perfect matchings of $[d]$ as fixed-point-free involutions
-- statement:
--   A **perfect matching** of $[d]$ is a partition of $[d]$ into $d/2$ unordered pairs $\{i,j\}$; it is the random object sampled at every step of the partition resampling chain, the parallel KMP chain and the labeled parallel KMP chain, always uniformly among all perfect matchings of the complete graph on $[d]$.
--
--   A perfect matching $\mathcal M=\{\{i_1,j_1\},\dots,\{i_{d/2},j_{d/2}\}\}$ is recorded as the permutation $\sigma$ of $[d]$ that swaps $i_s$ and $j_s$ for every $s$; these are exactly the permutations with $\sigma\circ\sigma=\mathrm{id}$ and $\sigma(x)\neq x$ for all $x$.
--
--   The three parallel chains of the supplement average over this finite set.
--
--   **Formalization Note** Vertices are `Fin d` (the paper's vertex $i$ is index $i-1$). Each pair $\{i,\sigma(i)\}$ is listed once, as the index $i$ with $i<\sigma(i)$. For odd $d$ the set is empty, and every statement assumes $d$ even.
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Definition 6.9 step 2, p.45 (PDF p.47); Definition 6.13 step 1, p.50 (PDF p.52); Definition B.2 step 1, p.71 (PDF p.73)

import Mathlib

namespace KMPMixing.Supplement

/-- The perfect matchings of `[d]` (the complete graph on `d` vertices), the random object
sampled in step 1 of the partition resampling chain, the parallel KMP chain and the labeled
parallel KMP chain (Chen, Liu, Qin, Schulman, Song, Yao, Zhao, *A Tale of Two Walks: From Kac to
KMP and Back*, arXiv:2609.38044, Definition 6.9, p.45 (PDF p.47); Definition 6.13, p.50
(PDF p.52); Definition B.2, p.71 (PDF p.73)).

**Formalization Note** Vertices are `Fin d` (the paper's vertex `i` is index `i − 1`). A perfect
matching `M = {{i₁, j₁}, …, {i_{d/2}, j_{d/2}}}` is encoded as the fixed-point-free involution
`σ` of `Fin d` with `σ iₛ = jₛ` and `σ jₛ = iₛ`; this is a bijection between perfect matchings
and fixed-point-free involutions. Each pair `{i, σ i}` is listed once as the index `i` with
`i < σ i`. For odd `d` the type is empty; every statement using it assumes `d` even. -/
abbrev PerfectMatching (d : ℕ) := {σ : Equiv.Perm (Fin d) // σ * σ = 1 ∧ ∀ x, σ x ≠ x}

end KMPMixing.Supplement


