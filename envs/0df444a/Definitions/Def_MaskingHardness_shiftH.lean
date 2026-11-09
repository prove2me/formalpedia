-- Prove2me | Definitions.Def_MaskingHardness_shiftH
-- name    : MaskingHardness_shiftH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:51.304867+00:00
-- url     : https://prove2.me/theorems/f7fc4c07-56dd-49c7-9836-b3c1b9f02ddd
-- title:
--   The shifted fidelity $h_1(y,b)$ of Lemma A.1
-- statement:
--   Given $h:[k]\times\Delta_k\to\overline{\mathbb R}$, define $h_1:[k]\times\mathbb R^k\to\overline{\mathbb R}$ by
--
--   $$
--   h_1(y,b)=\begin{cases}h(y,z) & \text{if } b=z-\vec 1/k \text{ for some } z\in\Delta_k,\\ -\infty & \text{otherwise.}\end{cases}
--   $$
--
--   It translates the domain of $h$ from the simplex to the mean-zero hyperplane; it is the concave partner of $g_1(y,a)=g(y,\pi(a))$ in the proof of the main theorem.
--
--   **Formalization Note** The point $z$ with $b=z-\vec 1/k$ is $z=b+\vec 1/k$, so $h_1(y,b)=h(y,b+\vec 1/k)$ if $b+\vec 1/k\in\Delta_k$ and $-\infty$ otherwise.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Lemma A.1, p.39 (PDF p.41); proof of Theorem 1.9, p.22 (PDF p.24)

import Mathlib

namespace MaskingHardness

open Classical in
/-- **The shifted fidelity function `h₁`** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From
Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Lemma A.1, printed
p.39 = PDF p.41, and proof of Theorem 1.9, printed p.22 = PDF p.24):
`h₁(y, b) = h(y, z)` if `b = z − 1⃗/k` for some `z ∈ Δ_k`, and `h₁(y, b) = −∞` otherwise.

**Formalization Note** The `z` with `b = z − 1⃗/k` is `b + 1⃗/k`, where `1⃗/k` is the vector with
all entries `1/k`; `Δ_k` is `stdSimplex ℝ (Fin k)`. -/
noncomputable def shiftH {k : ℕ} (h : Fin k → (Fin k → ℝ) → EReal) (y : Fin k)
    (b : Fin k → ℝ) : EReal :=
  if (b + fun _ => (k : ℝ)⁻¹) ∈ stdSimplex ℝ (Fin k) then h y (b + fun _ => (k : ℝ)⁻¹) else ⊥

end MaskingHardness


