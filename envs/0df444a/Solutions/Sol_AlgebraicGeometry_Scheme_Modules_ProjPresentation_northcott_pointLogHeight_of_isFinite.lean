-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.northcott_pointLogHeight_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:57.719759+00:00
-- url     : https://prove2.me/submissions/afe9040e-3316-42c6-8f16-cd27a801fe26

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_northcott_projMulHeight_numberField
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_finite_fibre_pointProjectivization

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

/-- Northcott for a finite projective presentation, transported through its finite fibres. -/
theorem _root_.solution {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ} (P : M.ProjPresentation f N)
    (hfin : IsFinite P.toProj) : ∀ B : ℝ, {x : Scheme.KPoint f | P.pointLogHeight x ≤ B}.Finite := by
  letI : Northcott (Projectivization.mulHeight :
      Projectivization K (Fin (N + 1) → K) → ℝ) :=
    northcott_projMulHeight_numberField K (Fin (N + 1))
  letI : Northcott (Projectivization.logHeight :
      Projectivization K (Fin (N + 1) → K) → ℝ) := by
    simpa only [← Projectivization.logHeight_eq_log_mulHeight, Function.comp_def] using
      (Northcott.comp_of_bddAbove
        (Projectivization.mulHeight : Projectivization K (Fin (N + 1) → K) → ℝ)
        Real.log (fun B => bddAbove_def.mpr ⟨Real.exp B, fun _ => Real.le_exp_of_log_le⟩))
  intro B
  have hz : {z : Projectivization K (Fin (N + 1) → K) |
      Projectivization.logHeight z ≤ B}.Finite := Northcott.finite_le B
  refine Set.Finite.of_finite_fibers P.pointProjectivization ?_ ?_
  · exact hz.subset (by
      rintro z ⟨x, hx, rfl⟩
      change P.pointLogHeight x ≤ B at hx
      change Projectivization.logHeight (P.pointProjectivization x) ≤ B
      simpa only [pointLogHeight] using hx)
  · intro z _
    exact (P.finite_fibre_pointProjectivization hfin z).inter_of_right _

end AlgebraicGeometry.Scheme.Modules.ProjPresentation
