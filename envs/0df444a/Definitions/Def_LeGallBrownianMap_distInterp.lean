-- Prove2me | Definitions.Def_LeGallBrownianMap_distInterp
-- name    : LeGallBrownianMap_distInterp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:20.073979+00:00
-- url     : https://prove2.me/theorems/cf15a8d5-f0f1-40db-ba0a-76df2ddf00f9
-- title:
--   The interpolated distance process $d_n(s,t)$
-- statement:
--   For $\theta\in\mathbb T^p_n$ and $i,j\in\{0,\dots,pn\}$ put $d_n(i,j)=d_{gr}(v_i,v_j)$, the graph distance in the BDG map between the corners $v_i$ and $v_j$. For real $(s,t)\in[0,pn]^2$,
--
--   $$
--   \begin{aligned}
--   d_n(s,t)={}&(s-\lfloor s\rfloor)(t-\lfloor t\rfloor)\,d_n(\lceil s\rceil,\lceil t\rceil)+(s-\lfloor s\rfloor)(\lceil t\rceil-t)\,d_n(\lceil s\rceil,\lfloor t\rfloor)\\
--   &+(\lceil s\rceil-s)(t-\lfloor t\rfloor)\,d_n(\lfloor s\rfloor,\lceil t\rceil)+(\lceil s\rceil-s)(\lceil t\rceil-t)\,d_n(\lfloor s\rfloor,\lfloor t\rfloor),
--   \end{aligned}
--   $$
--
--   where $\lceil t\rceil=\min\{k\in\mathbb Z: k>t\}$.
--
--   **Formalization Note** With the paper's convention $\lceil t\rceil=\lfloor t\rfloor+1$ for every real $t$, including integers.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.5, p.16

import Mathlib
import Definitions.Def_LeGallBrownianMap_bdgGraph

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.5, p.16:
"If i, j ∈ {0, 1, ..., pn}, we set d_n(i, j) = d_gr(v^n_i, v^n_j). […] we extend the definition of
d_n(s, t) to noninteger values of (s, t) ∈ [0, pn]² by setting
d_n(s, t) = (s − ⌊s⌋)(t − ⌊t⌋) d_n(⌈s⌉, ⌈t⌉) + (s − ⌊s⌋)(⌈t⌉ − t) d_n(⌈s⌉, ⌊t⌋)
+ (⌈s⌉ − s)(t − ⌊t⌋) d_n(⌊s⌋, ⌈t⌉) + (⌈s⌉ − s)(⌈t⌉ − t) d_n(⌊s⌋, ⌊t⌋),
where ⌊t⌋ = max{k ∈ ℤ : k ≤ t} and ⌈t⌉ = min{k ∈ ℤ : k > t}."

`distInterp θ s t` is this interpolated distance process for the labeled p-tree `θ`, with
`d(i, j)` the graph distance in `bdgGraph θ` between the corners `v_i` and `v_j`.

**Formalization Note.** The paper's `⌈t⌉ = min{k ∈ ℤ : k > t}` is `⌊t⌋ + 1` for every real `t`
(including integers), and is written so. `⌊·⌋` is `Nat.floor` (only `s, t ≥ 0` are used). At
`s = pn` the index `pn + 1` appears with weight `0`; the contour sequence is periodic there. -/
noncomputable def distInterp (θ : Finset (List ℕ+) × (List ℕ+ → ℤ)) (s t : ℝ) : ℝ :=
  let d : ℕ → ℕ → ℝ := fun i j =>
    ((bdgGraph θ).dist (some (contourSeq θ.1 i)) (some (contourSeq θ.1 j)) : ℝ)
  (s - ⌊s⌋₊) * (t - ⌊t⌋₊) * d (⌊s⌋₊ + 1) (⌊t⌋₊ + 1) +
    (s - ⌊s⌋₊) * ((⌊t⌋₊ : ℝ) + 1 - t) * d (⌊s⌋₊ + 1) ⌊t⌋₊ +
    ((⌊s⌋₊ : ℝ) + 1 - s) * (t - ⌊t⌋₊) * d ⌊s⌋₊ (⌊t⌋₊ + 1) +
    ((⌊s⌋₊ : ℝ) + 1 - s) * ((⌊t⌋₊ : ℝ) + 1 - t) * d ⌊s⌋₊ ⌊t⌋₊

end LeGallBrownianMap


