-- Prove2me | Definitions.Def_FractionalSpectralGP_IsSpectralPair
-- name    : FractionalSpectralGP_IsSpectralPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:50.751718+00:00
-- url     : https://prove2.me/theorems/fef9fa60-9795-4a23-aa8a-f0e849f08ec6
-- title:
--   Spectral pair $(\sigma,\Lambda)$ (Definition 2.2)
-- statement:
--   Let $\sigma$ be a finite Borel measure on $\mathbb R$ and $\Lambda\subset\mathbb R$. Then $\sigma$ **has spectrum** $\Lambda$, and $(\sigma,\Lambda)$ is a **spectral pair**, if
--
--   1. $\Lambda$ is a discrete set, and
--   2. $\{e_\lambda:\lambda\in\Lambda\}$, $e_\lambda(u)=e^{i\lambda u}$, is an orthonormal basis of $L^2(d\sigma)$: the family is orthonormal and its linear span is dense.
--
--   Spectral pairs are the measures with a Fourier orthonormal basis; the Cantor-type measures $\sigma_m$ of Jorgensen–Pedersen are the paper's examples.
--
--   **Formalization Note** "Discrete" is read as: every point of $\Lambda$ is isolated in $\Lambda$. $L^2(d\sigma)$ is complex.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Definition 2.2, p.7

import Mathlib
import Definitions.Def_FractionalSpectralGP_expL2

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Definition 2.2 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.7): a finite Borel measure `σ` on `ℝ` has spectrum
`Λ ⊂ ℝ` if `Λ` is a discrete set and `{e_λ, λ ∈ Λ}` is an orthonormal basis of `L²(dσ)`; then
`(σ, Λ)` is a spectral pair.

**Formalization Note.** "Discrete" is `DiscreteTopology Λ` (every point of `Λ` is isolated). An
orthonormal basis of a Hilbert space is an orthonormal family whose span is dense. `L²(dσ)` is
the complex space `L²(σ; ℂ)`. -/
def IsSpectralPair (σ : Measure ℝ) [IsFiniteMeasure σ] (Λ : Set ℝ) : Prop :=
  DiscreteTopology Λ ∧ Orthonormal ℂ (fun l : Λ => expL2 σ l) ∧
    ⊤ ≤ (Submodule.span ℂ (Set.range fun l : Λ => expL2 σ l)).topologicalClosure

end FractionalSpectralGP


