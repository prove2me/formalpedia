-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteGenOfWeakAxioms
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteGenOfWeakAxioms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:50.142026+00:00
-- url     : https://prove2.me/theorems/91fdb479-8c84-417a-ab32-96a1b8a68017
-- title:
--   Finite Gen Of Weak Axioms
-- statement:
--   Definitions and structural lemmas for Finite Gen Of Weak Axioms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteGenOfWeakAxioms.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GenericSectionOfAxioms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
namespace Data
variable (d : Data K ι Ω WT A) (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
structure AxW : Prop where
  tower : ∀ c, IsScalarTower K (Ω c) (A c)
  towerO : ∀ c, IsScalarTower (𝓞 K) K (A c)
  D_ge : 3 ≤ d.D
  fg : ∀ c, (⊤ : IntermediateField K (Ω c)).FG
  trdeg : ∀ c, Algebra.trdeg K (Ω c) = d.D
  algClosed : ∀ c (a : Ω c), IsAlgebraic K a → a ∈ (algebraMap K (Ω c)).range
  graded : ∀ c, SetLike.GradedMonoid (𝒜 c)
  finrank_one : ∀ c G, Module.finrank (Ω c) (𝒜 c G) = 1
  mul_ne_zero : ∀ c {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' → f ≠ 0 → g ≠ 0 →
    f * g ≠ 0
  w_mem : ∀ j c, d.w j c ∈ 𝒜 c d.wL
  w_base : ∀ c, d.w (d.jc c) c ≠ 0
  nrm_pos : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → f ≠ 0 → 0 < d.nrm c G f P
  nrm_zero : ∀ c (G : WT) (P : Ω c →+* ℂ), d.nrm c G 0 P = 0
  nrm_mul : ∀ c {G G' : WT} {f g : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.nrm c (G + G') (f * g) P = d.nrm c G f P * d.nrm c G' g P
  nrm_smul : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ) (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    d.nrm c G (a • f) P = ‖P a‖ * d.nrm c G f P
  a1 : ∀ c, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))
variable {d 𝒜}
end Data
end ReciprocityTheory.ChartRestriction.G.T0


