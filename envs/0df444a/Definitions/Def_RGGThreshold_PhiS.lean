-- Prove2me | Definitions.Def_RGGThreshold_PhiS
-- name    : RGGThreshold_PhiS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:40.457466+00:00
-- url     : https://prove2.me/theorems/cc1dc9b2-f0e7-45c9-8a1f-99557219e8b5
-- title:
--   The edge factors $\Phi_{sij}$, their product, and the term $Z_s$
-- statement:
--   For $0\le s\le n$, a graph $H$ and Gram–Schmidt coordinates revealed up to coordinate $s$, let
--
--   $$
--   \Phi_{sij}=\begin{cases}\Phi\big(-z_p+\sqrt d\,\langle\pi_s(v_i),\pi_s(v_j)\rangle\big), & ij\in E(H),\\ \Phi\big(z_p-\sqrt d\,\langle\pi_s(v_i),\pi_s(v_j)\rangle\big), & ij\notin E(H),\end{cases}
--   $$
--
--   and
--
--   $$
--   Z_s=\sum_{\substack{s<i<j\le n\\ s<r\le n}}\lambda_{ij}\lambda_{ir}\lambda_{jr}(z_p-\lambda_{ij})\,\langle\pi_s(v_i),\pi_s(v_j)\rangle .
--   $$
--
--   The product $\prod_{s<i<j\le n}\Phi_{sij}$ is the leading term of the probability that the random geometric graph agrees with $H$ on $\{s+1,\dots,n\}$ given $\mathcal G_s$; at $s=0$ it is $p^{e(H)}(1-p)^{\binom n2-e(H)}$ and $Z_0=0$ (both proved in the sanity file).
--
--   **Formalization Note** All three are functions of a coordinate matrix, so that Lemma 5.4 can evaluate them on revealed data plus a new column. The sum over $r$ includes $r=i,j$, where $\lambda_{ii}=0$ kills the term.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Lemma 5.1, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_RGGThreshold_gsCoord
import Definitions.Def_RGGThreshold_centredAdj

namespace RGGThreshold

open Classical in
/-- The edge factor `Φ_{sij}` (Hunter–Milojević–Sudakov, arXiv:2607.22480, held version, sha256
1a398ef9…, Lemma 5.1, p.15 (PDF p.17)):
`Φ_{sij} = Φ(-z_p + √d ⟨π_s(v_i), π_s(v_j)⟩)` if `ij ∈ E(H)`, and
`Φ_{sij} = Φ(z_p - √d ⟨π_s(v_i), π_s(v_j)⟩)` if `ij ∉ E(H)`.

**Formalization Note** It is a function of the coordinate matrix `W` (`W = gsCoord x` for a
configuration, or revealed data in Setup (⋆)); `s` is the paper's number of revealed coordinates. -/
noncomputable def PhiS {n : ℕ} (p : ℝ) (d : ℕ) (H : SimpleGraph (Fin n)) (s : ℕ)
    (W : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  if H.Adj i j then gaussCDF (-zp p + Real.sqrt d * ipUpTo s W i j)
  else gaussCDF (zp p - Real.sqrt d * ipUpTo s W i j)

/-- The product `∏_{s<i<j≤n} Φ_{sij}` (arXiv:2607.22480, held version, Lemma 5.1, p.14 (PDF p.16)).

**Formalization Note** The paper's vertices `s < i` (1-based) are the 0-based `i` with `s ≤ i`. -/
noncomputable def prodPhi {n : ℕ} (p : ℝ) (d : ℕ) (H : SimpleGraph (Fin n)) (s : ℕ)
    (W : Fin n → Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if s ≤ i.val ∧ i < j then PhiS p d H s W i j else 1

/-- The term `Z_s = ∑_{s<i<j≤n, s<r≤n} λ_{ij} λ_{ir} λ_{jr} (z_p - λ_{ij}) ⟨π_s(v_i), π_s(v_j)⟩`
(arXiv:2607.22480, held version, Lemma 5.1, p.15 (PDF p.17)).

**Formalization Note** The paper's `s < i` (1-based) is the 0-based `s ≤ i`. The sum over `r`
includes `r = i` and `r = j`, where `λ_{ii} = λ_{jj} = 0` kills the term. -/
noncomputable def Zs {n : ℕ} (p : ℝ) (H : SimpleGraph (Fin n)) (s : ℕ)
    (W : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ r : Fin n,
    if s ≤ i.val ∧ i < j ∧ s ≤ r.val then
      lam p H i j * lam p H i r * lam p H j r * (zp p - lam p H i j) * ipUpTo s W i j
    else 0

end RGGThreshold


