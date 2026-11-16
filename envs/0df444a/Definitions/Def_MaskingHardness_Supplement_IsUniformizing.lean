-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsUniformizing
-- name    : MaskingHardness_Supplement_IsUniformizing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:29:51.169427+00:00
-- url     : https://prove2.me/theorems/01322337-a88d-4291-903a-70c19d09f21b
-- title:
--   Feasible response channels: $W\in\Delta_k^k$ with $Wz=\vec1/k$
-- statement:
--   For a label distribution $z\in\Delta_k$, a $k\times k$ matrix $W$ is a **feasible response channel** at $z$ if every column $We_i$ lies in $\Delta_k$ (so $W\in\Delta_k^k$) and
--
--   $$
--   Wz=\vec 1/k ,
--   $$
--
--   i.e. the channel maps the label distribution $z$ to the uniform distribution (Example 1.4). These are the channels over which highest-fidelity responses optimize (Definition 1.18).
--
--   **Formalization Note** Column $i$ of $W$ is the image of the label $e_i$; $Wz$ is the matrix–vector product.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.18, p.10 (PDF p.12); Example 1.4

import Mathlib
open Matrix

namespace MaskingHardness.Supplement

/-- **Feasible response channels at `z`** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.18, printed p.10 = PDF p.12, and
Example 1.4): a matrix `W ∈ Δ_k^k` (every column a distribution in `Δ_k`) with `W z = 1⃗/k`, i.e.
the channel `W` maps the label distribution `z` to the uniform distribution.

**Formalization Note** Column `i` of `W` is `fun j => W j i` (the image of the label `e_i`);
`W z` is `W *ᵥ z`; `1⃗/k` is the constant vector `(k : ℝ)⁻¹`. -/
def IsUniformizing {k : ℕ} (z : Fin k → ℝ) (W : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (∀ i, (fun j => W j i) ∈ stdSimplex ℝ (Fin k)) ∧ W *ᵥ z = fun _ => (k : ℝ)⁻¹

end MaskingHardness.Supplement


