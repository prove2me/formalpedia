-- Prove2me | Definitions.Def_QMCBeyondHK_haar
-- name    : QMCBeyondHK_haar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:59.28319+00:00
-- url     : https://prove2.me/theorems/f09f278d-33b3-4e54-8398-6ef46c937c02
-- title:
--   One- and $d$-dimensional Haar functions $h_{j,k}$, $H_{j,k}$ and their norms
-- statement:
--   **One-dimensional Haar functions.** For integers $j \ge 1$ and $0 \le k < 2^{j-1}$, $h_{j,k}$ equals $1$ on $[(2k)2^{-j}, (2k+1)2^{-j})$, $-1$ on $[(2k+1)2^{-j}, (2k+2)2^{-j})$, and $0$ elsewhere; $h_{0,0}$ is the constant $1$ on $[0,1)$.
--
--   **Haar indices.** A $d$-dimensional Haar index is a pair of vectors $j, k \in \mathbb N^d$ such that in every coordinate either $j_i = k_i = 0$, or $j_i \ge 1$ and $0 \le k_i < 2^{j_i - 1}$. The vector $j$ is the **scale vector**.
--
--   **Multidimensional Haar functions.** For a Haar index $(j,k)$,
--   $$
--   H_{j,k}(x) = \prod_{i=1}^d h_{j_i,k_i}(x_i), \qquad x \in [0,1)^d,
--   $$
--   and $\|H_{j,k}\|_2^2 = \int_{[0,1)^d} H_{j,k}(x)^2\,dx$.
--
--   The Haar functions form an orthogonal basis of $L^2([0,1)^d)$; they are the coordinates in which the whole analysis of the mission is carried out.
--
--   **Formalization Note** `haar1 0 k` is the indicator of $[0,1)$ for every $k$, but only $k = 0$ occurs, through the index structure `HaarIdx`. Outside $[0,1)$ every valid $h_{j,k}$ vanishes, so $H_{j,k}$ vanishes off the cube.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §2 'Haar Functions and Boxes', p.6 (PDF p.8)

import Mathlib
import Definitions.Def_QMCBeyondHK_cube

set_option autoImplicit false

open MeasureTheory

namespace QMCBeyondHK

/-- The one-dimensional Haar function `h_{j,k}` (arXiv:2609.10921, sha256 bc273e88…, §2, p.6,
PDF p.8): for `j ≥ 1` it equals `1` on `[(2k)2^{−j}, (2k+1)2^{−j})`, `−1` on
`[(2k+1)2^{−j}, (2k+2)2^{−j})` and `0` elsewhere; `h_{0,0}` is the constant `1` on `[0,1)`.

**Formalization Note** `haar1 0 k` is the indicator of `[0,1)` for every `k`; only `k = 0` is
used, through `HaarIdx`. Outside `[0,1)` every `haar1 j k` vanishes when `k < 2^{j−1}`. -/
noncomputable def haar1 (j k : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then (if 0 ≤ x ∧ x < 1 then 1 else 0)
  else if (2 * k : ℝ) / 2 ^ j ≤ x ∧ x < (2 * k + 1 : ℝ) / 2 ^ j then 1
  else if (2 * k + 1 : ℝ) / 2 ^ j ≤ x ∧ x < (2 * k + 2 : ℝ) / 2 ^ j then -1
  else 0

/-- An index `(j, k)` of a `d`-dimensional Haar function (arXiv:2609.10921, sha256 bc273e88…, §2,
p.6, PDF p.8): a scale vector `j ∈ ℕ^d` and a shift vector `k ∈ ℕ^d` with, in every coordinate,
either `j_i = k_i = 0` or `j_i ≥ 1` and `0 ≤ k_i < 2^{j_i − 1}`.

**Formalization Note** This is §2's index range. Definition 2.1 prints `0 ≤ k_i < 2^{j_i}`; the
extra indices name no Haar function of §2 and are read as a typo. -/
@[ext]
structure HaarIdx (d : ℕ) where
  /-- The scale vector `j`. -/
  j : Fin d → ℕ
  /-- The shift vector `k`. -/
  k : Fin d → ℕ
  valid : ∀ i, (j i = 0 ∧ k i = 0) ∨ (1 ≤ j i ∧ k i < 2 ^ (j i - 1))

/-- The multidimensional Haar function `H_{j,k}(x) = ∏_{i∈[d]} h_{j_i,k_i}(x_i)`
(arXiv:2609.10921, sha256 bc273e88…, §2, p.6, PDF p.8). -/
noncomputable def haar {d : ℕ} (H : HaarIdx d) (x : Fin d → ℝ) : ℝ :=
  ∏ i, haar1 (H.j i) (H.k i) (x i)

/-- The squared norm `‖H‖₂² = ∫_{[0,1)^d} H(x)² dx` of a Haar function (arXiv:2609.10921,
sha256 bc273e88…, §2, p.6, PDF p.8). -/
noncomputable def haarNormSq {d : ℕ} (H : HaarIdx d) : ℝ := ∫ x in cube d, haar H x ^ 2

end QMCBeyondHK


