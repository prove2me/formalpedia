-- Prove2me | Definitions.Def_MaskingHardness_centered
-- name    : MaskingHardness_centered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:34.67244+00:00
-- url     : https://prove2.me/theorems/561d3280-deb0-4bfd-9ed1-336ddf5c162d
-- title:
--   The centering map $\pi(a)=a-\langle a,\vec 1/k\rangle\cdot\vec 1$
-- statement:
--   For an action vector $a\in\mathbb R^k$, its **centered** version is
--
--   $$
--   \pi(a)=a-\langle a,\vec 1/k\rangle\cdot\vec 1,\qquad\text{i.e.}\qquad \pi(a)_i=a_i-\frac1k\sum_{j=1}^k a_j ,
--   $$
--
--   the mean-zero vector obtained by subtracting the average entry from every entry. The main theorem evaluates the loss $g$ at $\pi(c_\lambda(x))$.
--
--   **Formalization Note** Coordinates are indexed by `Fin k`; the division by $k$ is real division.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Section 1.1, p.6 (PDF p.8)

import Mathlib

namespace MaskingHardness

/-- **The centering map** `π(a) = a − ⟨a, 1⃗/k⟩ · 1⃗` (Gopalan–Prabhakaran–Tankala, *Universal
Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Section
1.1, printed p.6 = PDF p.8): the mean-zero version of an action vector `a ∈ ℝᵏ`; every entry of
`⟨a, 1⃗/k⟩ · 1⃗` is `(∑ⱼ aⱼ)/k`. -/
noncomputable def centered {k : ℕ} (a : Fin k → ℝ) : Fin k → ℝ :=
  fun i => a i - (∑ j, a j) / k

end MaskingHardness


