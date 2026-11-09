-- Prove2me | Definitions.Def_ConstGapCircuits_spectralGap
-- name    : ConstGapCircuits_spectralGap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:47:31.934977+00:00
-- url     : https://prove2.me/theorems/aa821c38-ea68-4142-8d3d-d89dd633bb15
-- title:
--   All continuous unitary representations, moment operators and the real spectral-gap infimum (Definition 1.1)
-- statement:
--   Let $G$ be a compact Hausdorff group and $\nu$ a probability measure on its Borel sets. A representation consists of a dimension $d\in\mathbb N$ and a continuous homomorphism $\rho:G\to\mathrm U(d)$. All dimensions are included. Define
--   $$M(\nu,\rho)=\int_G\rho(g)\,d\nu(g),\qquad \Pi_\rho=M(\mu_G,\rho),$$
--   $$g(\nu,\rho)=\|M(\nu,\rho)-\Pi_\rho\|_{\mathrm{op}},\qquad
--   \Delta(\nu,\rho)=1-g(\nu,\rho),\qquad
--   \Delta(\nu,G)=\inf_{d,\rho}\Delta(\nu,\rho).$$
--   For a closed subgroup $H$, $\Pi(\rho|H)=M(\mu_H^G,\rho)$. The norm is the operator norm on Euclidean complex space.
--
--   This is Definition 1.1, with continuity explicit and the infimum literally real-valued. The representation family contains the trivial representation, and its values for probability measures are bounded. No restriction to tensor powers is built into the definition; the Haar projector is subtracted even on representations with invariant vectors.
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 2, 6–7, Definition 1.1 and (1.12)

import Definitions.Def_ConstGapCircuits_compactGroups

noncomputable section

namespace ConstGapCircuits
open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- All continuous finite-dimensional unitary representations, in a fixed universe. -/
structure UnitaryRep (G : Type) [Group G] [TopologicalSpace G] where
  dim : ℕ
  hom : G →* Matrix.unitaryGroup (Fin dim) ℂ
  continuous_hom : Continuous hom

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]

/-- Bochner integral of the represented matrix. -/
def moment (ν : Measure G) (ρ : UnitaryRep G) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ :=
  ∫ g, (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) ∂ν

/-- The Euclidean operator norm, never the entrywise matrix norm. -/
def opNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) A‖

section Compact
variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]

def invariantProjector (ρ : UnitaryRep G) := moment (haarProbability (G := G)) ρ

def essentialNorm (ν : Measure G) (ρ : UnitaryRep G) : ℝ :=
  opNorm (moment ν ρ - invariantProjector ρ)

def repGap (ν : Measure G) (ρ : UnitaryRep G) : ℝ := 1 - essentialNorm ν ρ

/-- Literal infimum over all dimensions and all continuous unitary representations. -/
def spectralGap (ν : Measure G) : ℝ := ⨅ ρ : UnitaryRep G, repGap ν ρ

def subgroupProjector (H : ClosedSubgroup G) (ρ : UnitaryRep G) := moment (haarOn H) ρ

end Compact
end ConstGapCircuits


