-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_mem_isFrameOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/9fc0841a-a9c4-5a03-aa6c-f1ff8dd2a0a6

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : Scheme.Modules.ProjPresentation M f N) (x : ↥X) :
    ∃ (i : Fin (N + 1)) (U : X.Opens), x ∈ U ∧ Scheme.Modules.IsFrameOn (𝔓.σ i) U := by
  have hcov := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R) (ProjSpace.irrelevant_le_span_X R N)
  have hx : 𝔓.toProj.base x ∈ (⨆ i, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨i, 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i), hi,
    fun W _ hWV => 𝔓.frame i W hWV⟩

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn (solution)
