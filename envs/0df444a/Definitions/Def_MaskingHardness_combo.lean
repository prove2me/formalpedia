-- Prove2me | Definitions.Def_MaskingHardness_combo
-- name    : MaskingHardness_combo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:46.353926+00:00
-- url     : https://prove2.me/theorems/d751e1fd-40c9-427e-bfa0-fc15e5a18e48
-- title:
--   The linear combination $c_\lambda=\sum_i\lambda_i c_i$ of a finite class
-- statement:
--   Let $\mathcal C=\{c_i\}_{i}$ be a finite collection of functions $c_i:\mathcal X\to\mathbb R^k$ and $\lambda\in\mathbb R^{\mathcal C}$ a coefficient vector. Then
--
--   $$
--   c_\lambda(x)=\sum_i \lambda_i\,c_i(x)\in\mathbb R^k
--   $$
--
--   is the function in $\mathrm{span}(\mathcal C)$ with coefficients $\lambda$.
--
--   **Formalization Note** The class is a finite indexed family `c : ι → X → (Fin k → ℝ)` with `[Fintype ι]`; the paper's finite set $\mathcal C$ is the family indexed by its own elements.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Section 1.1, Eq. (2) discussion, p.3 (PDF p.5); Theorem 1.9, p.6 (PDF p.8)

import Mathlib

namespace MaskingHardness

/-- **The linear combination `c_λ`** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From
Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Section 1.1, printed
p.3 = PDF p.5, and Theorem 1.9, printed p.6 = PDF p.8): `c_λ(x) = ∑ᵢ λᵢ cᵢ(x)` for a finite
collection `C = {cᵢ} ⊆ {X → ℝᵏ}` and a coefficient vector `λ ∈ ℝ^C`.

**Formalization Note** The collection `C` is a finite indexed family `c : ι → X → ℝᵏ`
(`ι = C` with `c` the inclusion recovers the paper's set). -/
noncomputable def combo {ι X : Type*} [Fintype ι] {k : ℕ} (c : ι → X → Fin k → ℝ) (lam : ι → ℝ) :
    X → Fin k → ℝ :=
  fun x => ∑ i, lam i • c i x

end MaskingHardness


