-- Prove2me | Definitions.Def_QStateSearch_IsPUniform
-- name    : QStateSearch_IsPUniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:27.109208+00:00
-- url     : https://prove2.me/theorems/3ff6388a-37a9-486e-bb45-5ce2c8f69e77
-- title:
--   $p$-uniform measure (Definition 1)
-- statement:
--   For $0<p\le1$, a probability measure $\nu$ is **$p$-uniform** (with respect to $\mu$) if
--   $$
--   p\,\nu(G)\le\mu(G)\qquad\text{for every measurable set }G .
--   $$
--   In the paper $\mu$ is the Haar measure $\mu_D$; a $p$-uniform measure is the Haar measure conditioned on a set of Haar mass at least $p$, or a mixture of such.
--
--   **Formalization Note** Stated for measures on any measurable space; in this mission $\mu$ is the uniform probability measure on the unit sphere of $\mathbb C^D$, not on $\mathbb{CP}^{D-1}$.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Definition 1, p.10

import Mathlib

namespace QStateSearch

/-- Definition 1 (p-uniform measure): `ν` is a probability measure with `p ν ≤ μ`, for
`0 < p ≤ 1`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Definition 1, p.10: "A probability measure ν on CP^{D−1} is p-uniform, for 0 < p ≤ 1, if
pν(G) ≤ μ_D(G) for every measurable set G. Equivalently, we write pν ≤ μ_D as an inequality of
measures."

**Formalization Note.** Stated for measures on any measurable space; in this mission `μ` is the
Haar measure `uniformSphere D` on `ℂ^D` (supported on the unit sphere) rather than on
`CP^{D−1}`. Mathlib's order on measures is "for every measurable set". -/
def IsPUniform {α : Type*} [MeasurableSpace α] (μ ν : MeasureTheory.Measure α) (p : ℝ) : Prop :=
  0 < p ∧ p ≤ 1 ∧ MeasureTheory.IsProbabilityMeasure ν ∧ ENNReal.ofReal p • ν ≤ μ

end QStateSearch


