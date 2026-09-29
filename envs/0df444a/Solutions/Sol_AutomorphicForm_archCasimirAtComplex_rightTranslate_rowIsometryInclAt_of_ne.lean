-- Prove2me | solution 1 for AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/190fadf7-28e3-5240-91c5-68471e11a2ef

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

noncomputable section

namespace CommAway40

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F]

section Commuting

variable {w : InfinitePlace F} (hw : w.IsComplex) {k : AdelicGL2 (𝓞 F) F}
  (hk : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * k = k * archComplexGLAt hw m)

include hk

theorem archComplexLiftAt_mul_comm (e : Fin 2 → Fin 2 → ℂ) : archComplexLiftAt hw e * k = k * archComplexLiftAt hw e := by
  unfold archComplexLiftAt
  split_ifs
  · exact hk _
  · rw [one_mul, mul_one]

theorem archFlowAtComplex_mul_comm (d : ArchDirComplex) (t : ℝ) :
    archFlowAtComplex hw d t * k = k * archFlowAtComplex hw d t :=
  hk _

theorem isArchSmoothAtComplex_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    IsArchSmoothAtComplex hw (rightTranslate F k φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e * k)) =
      fun e => φ (g * k * archComplexLiftAt hw e) := by
    funext e
    rw [mul_assoc, archComplexLiftAt_mul_comm hw hk e, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

theorem archDerivAtComplex_rightTranslate (d : ArchDirComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAtComplex hw d (rightTranslate F k φ) = rightTranslate F k (archDerivAtComplex hw d φ) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t * k)) 0 =
    deriv (fun t : ℝ => φ (g * k * archFlowAtComplex hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAtComplex_mul_comm hw hk d t, ← mul_assoc]

theorem archDelAt_rightTranslate (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDelAt hw d (rightTranslate F k φ) = rightTranslate F k (archDelAt hw d φ) := by
  unfold archDelAt
  rw [archDerivAtComplex_rightTranslate hw hk, archDerivAtComplex_rightTranslate hw hk]
  rfl

theorem archDelBarAt_rightTranslate (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDelBarAt hw d (rightTranslate F k φ) = rightTranslate F k (archDelBarAt hw d φ) := by
  unfold archDelBarAt
  rw [archDerivAtComplex_rightTranslate hw hk, archDerivAtComplex_rightTranslate hw hk]
  rfl

theorem archCasimirAtComplex_rightTranslate (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAtComplex hw (rightTranslate F k φ) = rightTranslate F k (archCasimirAtComplex hw φ) := by
  unfold archCasimirAtComplex
  simp only [archDelAt_rightTranslate hw hk]
  rfl

theorem archCasimirBarAtComplex_rightTranslate (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirBarAtComplex hw (rightTranslate F k φ) = rightTranslate F k (archCasimirBarAtComplex hw φ) := by
  unfold archCasimirBarAtComplex
  simp only [archDelBarAt_rightTranslate hw hk]
  rfl

omit hk in
theorem continuous_rightTranslate {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (k' : AdelicGL2 (𝓞 F) F) :
    Continuous (rightTranslate F k' φ) :=
  hφ.comp (continuous_id.mul continuous_const)

theorem package (x : AdelicGL2 (𝓞 F) F → ℂ) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    IsArchSmoothAtComplex hw (rightTranslate F k x) ∧
    (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate F k x))) ∧
    (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (rightTranslate F k x)))) ∧
    archCasimirAtComplex hw (rightTranslate F k x) = rightTranslate F k (archCasimirAtComplex hw x) ∧
    archCasimirBarAtComplex hw (rightTranslate F k x) = rightTranslate F k (archCasimirBarAtComplex hw x) := by
  refine ⟨isArchSmoothAtComplex_rightTranslate hw hk hxs, fun d => ?_, fun d d' => ?_,
    archCasimirAtComplex_rightTranslate hw hk x, archCasimirBarAtComplex_rightTranslate hw hk x⟩
  · rw [archDerivAtComplex_rightTranslate hw hk]
    exact continuous_rightTranslate (hD1 d) k
  · rw [archDerivAtComplex_rightTranslate hw hk, archDerivAtComplex_rightTranslate hw hk]
    exact continuous_rightTranslate (hD2 d d') k

end Commuting

theorem archComplexGLAt_mul_rowIsometryInclAt₀_comm {w w' : InfinitePlace F} (hw : w.IsComplex) (hne : w' ≠ w)
    (k : rowIsometrySubgroup₀ w'.Completion) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m * rowIsometryInclAt₀ F w' k = rowIsometryInclAt₀ F w' k * archComplexGLAt hw m := by
  rw [rowIsometryInclAt₀_apply]
  show adelicArchGLInclAt F w _ * adelicArchGLInclAt F w' _ = adelicArchGLInclAt F w' _ * adelicArchGLInclAt F w _
  exact (commute_adelicArchGLInclAt_of_ne F (Ne.symm hne) _ _).eq

end CommAway40

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x))) :
    ∀ (w' : InfinitePlace K) (hw' : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAtComplex hw x) ∧
        archCasimirBarAtComplex hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirBarAtComplex hw x) := by
  intro w' hw' k
  exact CommAway40.package hw (CommAway40.archComplexGLAt_mul_rowIsometryInclAt₀_comm hw hw' k) x hxs hD1 hD2

end S_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne
end P2MW
export P2MW.S_AutomorphicForm_archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne (solution)
