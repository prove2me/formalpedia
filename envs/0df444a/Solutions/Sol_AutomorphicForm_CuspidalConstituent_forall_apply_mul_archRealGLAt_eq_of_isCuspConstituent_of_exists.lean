-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/439cad60-bb3d-53ec-8133-89483c3f2574

import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

noncomputable section

namespace InvSub22

open NumberField NumberField.InfinitePlace.Completion NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

omit [NumberField F] in
theorem glArch_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (H : ∀ v : InfinitePlace F, archComponent F v g = archComponent F v h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion)) (H v)) i) j
  rwa [archComponent_apply, archComponent_apply] at this

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 F) F (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

theorem glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    glArch (𝓞 F) F (archRealGLAt hw m) = archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl F _

theorem archComponent_archRealGLAt_self (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem archComponent_archRealGLAt_of_ne {v : InfinitePlace F} (hv : v ≠ w) (m : GL (Fin 2) ℝ) :
    archComponent F v (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_of_ne F hv]

theorem symm_apply_proj (y : AdelicGL2 (𝓞 F) F) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw y) = archComponent F w (glArch (𝓞 F) F y) := by
  show glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
    (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (archComponent F w (glArch (𝓞 F) F y))) = _
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivRealOfIsReal hw).symm_apply_apply _

theorem archRealGLAt_mul (h : GL (Fin 2) ℝ) (y : AdelicGL2 (𝓞 F) F) :
    archRealGLAt hw h * y = y * archRealGLAt hw ((archRealProjAt hw y)⁻¹ * h * archRealProjAt hw y) := by
  refine eq_of_glArch_eq_of_glFin_eq (glArch_ext fun v => ?_) ?_
  · simp only [map_mul, map_inv]
    by_cases hv : v = w
    · subst hv
      simp only [archComponent_archRealGLAt_self, map_mul, map_inv, symm_apply_proj]
      rw [mul_assoc, mul_inv_cancel_left]
    · simp only [archComponent_archRealGLAt_of_ne hw hv, inv_one, one_mul, mul_one]
  · simp only [map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul, mul_one]

theorem det_conj (h a : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    Matrix.GeneralLinearGroup.det (a⁻¹ * h * a) = 1 := by
  rw [map_mul, map_mul, map_inv, hh, mul_one, inv_mul_cancel]

theorem det_glEquiv_eq_one (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion)) = 1 := by
  have hd := ((mem_rowIsometrySubgroup₀_iff _).mp k.2).1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  change (RingEquiv.mapMatrix (m := Fin 2) (ringEquivRealOfIsReal hw)
    ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)).det = 1
  rw [← RingEquiv.map_det, hd, map_one]

def W (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {x | x ∈ V ∧ ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ),
    Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hw h) = x g}
  zero_mem' := ⟨V.zero_mem, fun _ _ _ => rfl⟩
  add_mem' := fun {a b} ha hb => ⟨V.add_mem ha.1 hb.1, fun g h hh => by
    simp only [Pi.add_apply, ha.2 g h hh, hb.2 g h hh]⟩
  smul_mem' := fun c {a} ha => ⟨V.smul_mem c ha.1, fun g h hh => by
    simp only [Pi.smul_apply, ha.2 g h hh]⟩

theorem mem_W {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} {x : AdelicGL2 (𝓞 F) F → ℂ} :
    x ∈ W hw V ↔ x ∈ V ∧ ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ),
      Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hw h) = x g := Iff.rfl

theorem isCuspSubrep_W (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F pins ξ V) : IsCuspSubrep F pins ξ (W hw V) where
  le := fun x hx => hV.le hx.1
  rightTranslate_fin_mem := fun g hg x hx => ⟨hV.rightTranslate_fin_mem g hg x hx.1, fun y h hh => by
    rw [rightTranslate_apply, rightTranslate_apply, mul_assoc,
      archRealGLAt_mul_comm_of_glArch_eq_one hw h ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg), ← mul_assoc,
      hx.2 _ h hh]⟩
  rightTranslate_arch_mem := fun v k x hx => ⟨hV.rightTranslate_arch_mem v k x hx.1, fun y h hh => by
    rw [rightTranslate_apply, rightTranslate_apply, rowIsometryInclAt₀_apply]
    by_cases hv : v = w
    · subst hv
      rw [← archRealGLAt_glEquivOfRingEquiv hw, mul_assoc, ← map_mul,
        hx.2 _ _ (by rw [map_mul, hh, one_mul, det_glEquiv_eq_one hw k]), hx.2 _ _ (det_glEquiv_eq_one hw k)]
    · have hcomm : archRealGLAt hw h * adelicArchGLInclAt F v (k : GL (Fin 2) v.Completion)
          = adelicArchGLInclAt F v (k : GL (Fin 2) v.Completion) * archRealGLAt hw h :=
        (commute_adelicArchGLInclAt_of_ne F (Ne.symm hv) _ _).eq
      rw [mul_assoc, hcomm, ← mul_assoc, hx.2 _ h hh]⟩
  rightConv_mem := fun f tys hf hbf x hx => ⟨hV.rightConv_mem f tys hf hbf x hx.1, fun g h hh => by
    rw [rightConv_apply, rightConv_apply]
    congr 1
    funext y
    rw [mul_assoc, archRealGLAt_mul hw h y, ← mul_assoc, hx.2 _ _ (det_conj h _ hh)]⟩

theorem main (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F pins ξ V)
    (x₀ : AdelicGL2 (𝓞 F) F → ℂ) (hx₀ : x₀ ∈ V) (hne : x₀ ≠ 0)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      x₀ (g * archRealGLAt hw h) = x₀ g)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    x (g * archRealGLAt hw h) = x g := by
  obtain ⟨hsub, _, hmin⟩ := hV
  have hW := isCuspSubrep_W hw pins ξ V hsub
  have hle : W hw V ≤ V := fun x hx => hx.1
  rcases hmin (W hw V) hW hle with hbot | heq
  · exfalso
    apply hne
    have hmem : x₀ ∈ W hw V := ⟨hx₀, hinv⟩
    rw [hbot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  · have hmem : x ∈ W hw V := by rw [heq]; exact hx
    exact hmem.2 g h hh

end InvSub22

end

open NumberField AutomorphicForm IsDedekindDomain

open AutomorphicForm.CuspidalConstituent

theorem solution
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F pins ξ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (x₀ : AdelicGL2 (𝓞 F) F → ℂ) (hx₀ : x₀ ∈ V) (hne : x₀ ≠ 0)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      x₀ (g * archRealGLAt hw h) = x₀ g)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    x (g * archRealGLAt hw h) = x g := by
  exact InvSub22.main hw pins ξ V hV x₀ hx₀ hne hinv x hx g h hh

end S_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists (solution)
