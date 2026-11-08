-- Prove2me | Definitions.Def_PureDPQR_errQ
-- name    : PureDPQR_errQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:34.603196+00:00
-- url     : https://prove2.me/theorems/3c7c1b06-e133-47e4-a502-75374d1bd295
-- title:
--   Query error $\mathrm{err}_Q(p,h)$ and the signed query list
-- statement:
--   A query table $Q=\{q_i\}_{i\in[k]}$ consists of vectors $q_i\in\mathbb R^d$ (in the paper, $q_i\in[0,1]^d$). For $p\in\mathbb R^d$ and a histogram $h$ of mass $N$, the $\ell_\infty$ **query error** is
--
--   $$\mathrm{err}_Q(p,h)=\max_{i\in[k]}\Big|\langle p,q_i\rangle-\frac{\langle h,q_i\rangle}{N}\Big| .$$
--
--   The **signed list** has $K=2k$ labels: $s_{2i-1}=q_i$ and $s_{2i}=-q_i$, so that two-sided errors become one-sided scores; labels stay distinct even when two signed vectors agree.
--
--   These objects are shared by the accuracy statements (Propositions 21, 23 and Theorem 2) and by Algorithms 1 and 2.
--
--   **Formalization Note** Indices are 0-based: $s(2i)=q_i$, $s(2i+1)=-q_i$ on `Fin (2k)`. The maximum is a supremum over `Fin k`; every use has $k\ge1$, where it is a maximum of finitely many reals. Division by $N$ is total; every use has $N\ge1$. The simplex $\Delta_d$ is Mathlib's `stdSimplex`.
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), §1.1, p.4 (PDF p.5); §5, p.18 (PDF p.19)

import Mathlib

namespace PureDPQR

/-!
# Query error and the signed query list

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…), §1.1, p.4 (PDF p.5) and §5, p.18 (PDF p.19).

**Formalization Note.**
* A query table `{q_i}_{i ∈ [k]}` is `Q : Fin k → Fin d → ℝ`, row `i` being the vector `q_i`
  (0-based indices). The probability simplex `Δ_d` is Mathlib's `stdSimplex ℝ (Fin d)`.
* `errQ N Q p h` is a supremum over `Fin k`. For `k ≥ 1` (every use in this mission) it is the
  maximum of finitely many reals; for `k = 0` Lean returns `0`. The division by `N` is Lean's
  total division; every use has `N ≥ 1`.
* The signed list is 0-based: `s (2i) = q_i` and `s (2i+1) = −q_i` on `Fin (2k)`, the paper's
  `s_{2i−1} = q_i`, `s_{2i} = −q_i` after shifting indices by one. Labels stay distinct even when
  two signed vectors agree.
-/

/-- The `ℓ∞` query error (§1.1, p.4):
`errQ(p, h) := max_{i ∈ [k]} |⟨p, q_i⟩ − ⟨h, q_i⟩ / N|`. -/
noncomputable def errQ {k d : ℕ} (N : ℕ) (Q : Fin k → Fin d → ℝ) (p : Fin d → ℝ)
    (h : Fin d → ℕ) : ℝ :=
  ⨆ i : Fin k, |∑ j, p j * Q i j - (∑ j, (h j : ℝ) * Q i j) / (N : ℝ)|

/-- The signed list of §5 (p.18), 0-based: `K = 2k`, `s (2i) = q_i`, `s (2i+1) = −q_i`. -/
def signed {k d : ℕ} (Q : Fin k → Fin d → ℝ) : Fin (2 * k) → Fin d → ℝ :=
  fun a j =>
    (if a.val % 2 = 0 then (1 : ℝ) else -1) *
      Q ⟨a.val / 2, by have := a.isLt; omega⟩ j

end PureDPQR


