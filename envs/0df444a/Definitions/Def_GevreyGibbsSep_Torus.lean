-- Prove2me | Definitions.Def_GevreyGibbsSep_Torus
-- name    : GevreyGibbsSep_Torus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:43.059992+00:00
-- url     : https://prove2.me/theorems/865b4f0b-14f2-41cd-a524-28b7e3cc1053
-- title:
--   The flat torus $\mathbb T^d=\mathbb R^d/(2\pi\mathbb Z)^d$
-- statement:
--   The **flat torus** $\mathbb T^d=\mathbb R^d/(2\pi\mathbb Z)^d$ is the cube $[0,2\pi]^d$ with opposite faces identified. It carries the product of the Haar measures of the circles $\mathbb R/2\pi\mathbb Z$, normalized so that $\mathrm{vol}(\mathbb T^d)=(2\pi)^d$, and the product Borel $\sigma$-algebra.
--
--   Every distribution, query point and output of the mission lives on this space.
--
--   **Formalization Note** The torus is the product type `Fin d → AddCircle (2π)`; the module also registers the fact $0<2\pi$ that the Haar measure on `AddCircle (2π)` needs.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Section II, p.5; Appendix B 1, p.34

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- `Fact (0 < 2π)`, needed for the Haar measure on `AddCircle (2π)`. -/
noncomputable instance factTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The flat torus `T^d = ℝ^d/(2πℤ)^d` (Olivucci et al., *Provable Quantum–Classical Separation
for Continuous Gibbs Sampling*, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Section II,
p.5, and Appendix B 1, p.34).

**Formalization Note** The torus is the product `Fin d → AddCircle (2π)`. Its `volume` is the
product of the Haar measures of total mass `2π`, so `vol(T^d) = (2π)^d` as in the paper; its
σ-algebra is the product of the Borel σ-algebras. -/
abbrev Torus (d : ℕ) : Type := Fin d → AddCircle (2 * Real.pi)

end GevreyGibbsSep


