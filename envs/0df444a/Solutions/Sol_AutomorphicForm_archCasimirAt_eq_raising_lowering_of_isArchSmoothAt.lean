-- Prove2me | solution 1 for AutomorphicForm.archCasimirAt_eq_raising_lowering_of_isArchSmoothAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5f76c927-ede9-588f-8fd6-47fb4bb40ced

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace Ws23
namespace M2

p2m_open "NumberField NumberField.InfinitePlace.NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem archDerivAt_sub {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ)
    (d : ArchDir) : archDerivAt hw d (φ - ψ) = archDerivAt hw d φ - archDerivAt hw d ψ := by
  rw [sub_eq_add_neg, archDerivAt_add hφ hψ.neg, ← neg_one_smul ℂ ψ, archDerivAt_smul]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem archDerivAt_lowerComb_apply {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ)) g =
      archDerivAt hw d (archDerivAt hw .H φ) g -
        Complex.I * (archDerivAt hw d (archDerivAt hw .E φ) g + archDerivAt hw d (archDerivAt hw .Fm φ) g) := by
  have hH := hφ.archDerivAt .H
  have hE := hφ.archDerivAt .E
  have hF := hφ.archDerivAt .Fm
  rw [archDerivAt_sub hw hH ((hE.add hF).smul _), archDerivAt_smul, archDerivAt_add hE hF]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem archDerivAt_rotComb_apply {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (archDerivAt hw .E φ - archDerivAt hw .Fm φ) g =
      archDerivAt hw d (archDerivAt hw .E φ) g - archDerivAt hw d (archDerivAt hw .Fm φ) g := by
  rw [archDerivAt_sub hw (hφ.archDerivAt .E) (hφ.archDerivAt .Fm)]
  simp only [Pi.sub_apply]

theorem main
        (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw φ =
      -(1 / 4 : ℂ) • (archDerivAt hw .H (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
          + Complex.I • (archDerivAt hw .E (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
            + archDerivAt hw .Fm (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))))
      - (Complex.I / 2) • (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
      + (1 / 4 : ℂ) • (archDerivAt hw .E (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
          - archDerivAt hw .Fm (archDerivAt hw .E φ - archDerivAt hw .Fm φ)) := by
  obtain ⟨hHE, hHF, hEF⟩ := AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt F hw φ hφ
  funext g
  have h1 := congrFun hHE g
  have h2 := congrFun hHF g
  have h3 := congrFun hEF g
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    archDerivAt_lowerComb_apply hw hφ, archDerivAt_rotComb_apply hw hφ]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (-(Complex.I / 4)) * h1 + (-(Complex.I / 4)) * h2 + (-(1 / 2 : ℂ)) * h3 +
    (-(1 / 4 : ℂ) * (archDerivAt hw .E (archDerivAt hw .E φ) g + archDerivAt hw .E (archDerivAt hw .Fm φ) g +
      archDerivAt hw .Fm (archDerivAt hw .E φ) g + archDerivAt hw .Fm (archDerivAt hw .Fm φ) g)) * hI2

end Ws23.M2

end

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archCasimirAt hw φ =
      -(1 / 4 : ℂ) • (archDerivAt hw .H (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
          + Complex.I • (archDerivAt hw .E (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))
            + archDerivAt hw .Fm (archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ))))
      - (Complex.I / 2) • (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
      + (1 / 4 : ℂ) • (archDerivAt hw .E (archDerivAt hw .E φ - archDerivAt hw .Fm φ)
          - archDerivAt hw .Fm (archDerivAt hw .E φ - archDerivAt hw .Fm φ)) :=
  Ws23.M2.main hw φ hφ

end S_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt
end P2MW
export P2MW.S_AutomorphicForm_archCasimirAt_eq_raising_lowering_of_isArchSmoothAt (solution)
