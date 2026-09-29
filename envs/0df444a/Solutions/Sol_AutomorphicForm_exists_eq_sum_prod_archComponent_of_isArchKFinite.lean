-- Prove2me | solution 1 for AutomorphicForm.exists_eq_sum_prod_archComponent_of_isArchKFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/903121bb-9d53-5e9d-9fc1-2745c5cd875e

import Mathlib
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.TateGlobal NumberField.AdelicVolume
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped Classical

namespace R4Split

section Eval

variable {X : Type*}

theorem exists_eval_combination (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → X), ∀ w : W, φ w = ∑ l, e l * (w : X → ℂ) (x l) := by
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : X → ℂ) x := fun x w => rfl
  let Φ : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev)
  have hco : Φ.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [hev] at this
    simpa using this
  have hΦ : Φ = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Φ)
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  have hφ : φ ∈ Φ := by rw [hΦ]; exact Submodule.mem_top
  rw [Submodule.mem_span_set'] at hφ
  obtain ⟨m, e, g, hg⟩ := hφ
  have hg' : ∀ l, ∃ x, ev x = ((g l : Set.range ev) : Module.Dual ℂ W) := fun l => (g l).2
  choose x hx using hg'
  refine ⟨m, e, x, fun w => ?_⟩
  rw [← hg, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [LinearMap.smul_apply, ← hx l, hev, smul_eq_mul]

theorem exists_basis_eval_expansion (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (n : ℕ) (ω : Fin n → (X → ℂ)) (_ : ∀ c, ω c ∈ W) (m : Fin n → ℕ)
      (e : (c : Fin n) → Fin (m c) → ℂ) (pt : (c : Fin n) → Fin (m c) → X),
      ∀ h ∈ W, ∀ x : X, h x = ∑ c, (∑ l, e c l * h (pt c l)) * ω c x := by
  let β := Module.finBasis ℂ W
  have hc : ∀ c : Fin (Module.finrank ℂ W), ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → X),
      ∀ w : W, β.coord c w = ∑ l, e l * (w : X → ℂ) (x l) :=
    fun c => exists_eval_combination W (β.coord c)
  choose m e pt hpt using hc
  refine ⟨Module.finrank ℂ W, fun c => (β c : X → ℂ), fun c => (β c).2, m, e, pt, fun h hh x => ?_⟩
  have hsum := β.sum_repr ⟨h, hh⟩
  have hx := congrArg (fun w : W => (w : X → ℂ) x) hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at hx
  rw [← hx]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact hpt c ⟨h, hh⟩

end Eval

section Adelic

variable (F : Type) [Field F] [NumberField F]

def Rt (g : AdelicGL2 (𝓞 F) F) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun f x := f (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Rt_apply (g : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    Rt F g f x = f (x * g) := rfl

theorem Rt_mul (g h : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    Rt F (g * h) f = Rt F g (Rt F h f) := by
  funext x
  simp only [Rt_apply, mul_assoc]

theorem Rt_one (f : AdelicGL2 (𝓞 F) F → ℂ) : Rt F 1 f = f := by
  funext x
  simp only [Rt_apply, mul_one]

theorem continuous_Rt {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f) (g : AdelicGL2 (𝓞 F) F) :
    Continuous (Rt F g f) :=
  hf.comp (continuous_id.mul continuous_const)

theorem archComponent_glArch_inclAt_self (w : InfinitePlace F) (x : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w x)) = x := by
  show archComponent F w (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w x))) = x
  rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_glArch_inclAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (x : GL (Fin 2) w.Completion) :
    archComponent F v (glArch (𝓞 F) F (adelicArchGLInclAt F w x)) = 1 := by
  show archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w x))) = 1
  rw [glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne F hvw]

theorem glFin_inclAt (w : InfinitePlace F) (x : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w x) = 1 := by
  show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w x)) = 1
  rw [glFin_adelicArchGLIncl]

theorem eq_of_glFin_eq_of_forall_archComponent_eq {g g' : AdelicGL2 (𝓞 F) F}
    (hf : glFin (𝓞 F) F g = glFin (𝓞 F) F g')
    (ha : ∀ v : InfinitePlace F,
      archComponent F v (glArch (𝓞 F) F g) = archComponent F v (glArch (𝓞 F) F g')) :
    g = g' := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  refine Prod.ext ?_ ?_
  · funext v
    have h := congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j)
      (ha v)
    simp only [archComponent_apply, glArch_apply] at h
    exact h
  · have h := congrArg
      (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
        (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) hf
    simp only [glFin_apply] at h
    exact h

theorem commute_inclAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (a : GL (Fin 2) v.Completion) (b : GL (Fin 2) w.Completion) :
    Commute (adelicArchGLInclAt F v a) (adelicArchGLInclAt F w b) := by
  refine eq_of_glFin_eq_of_forall_archComponent_eq F ?_ ?_
  · rw [map_mul, map_mul, glFin_inclAt, glFin_inclAt]
  · intro u
    rw [map_mul, map_mul, map_mul, map_mul]
    by_cases huv : u = v
    · subst huv
      rw [archComponent_glArch_inclAt_self, archComponent_glArch_inclAt_of_ne F hvw, mul_one, one_mul]
    · rw [archComponent_glArch_inclAt_of_ne F huv]
      by_cases huw : u = w
      · subst huw
        rw [archComponent_glArch_inclAt_self, one_mul, mul_one]
      · rw [archComponent_glArch_inclAt_of_ne F huw, one_mul]

def piIncl : ((w : InfinitePlace F) → GL (Fin 2) w.Completion) →* AdelicGL2 (𝓞 F) F :=
  MonoidHom.noncommPiCoprod (fun w => adelicArchGLInclAt F w)
    (fun _ _ hvw x y => commute_inclAt_of_ne F hvw x y)

theorem piIncl_mulSingle (w : InfinitePlace F) (x : GL (Fin 2) w.Completion) :
    piIncl F (Pi.mulSingle w x) = adelicArchGLInclAt F w x :=
  MonoidHom.noncommPiCoprod_mulSingle (fun w => adelicArchGLInclAt F w) w x

theorem archComponent_glArch_piIncl (x : (w : InfinitePlace F) → GL (Fin 2) w.Completion)
    (v : InfinitePlace F) :
    archComponent F v (glArch (𝓞 F) F (piIncl F x)) = x v := by
  have key : ((archComponent F v).comp ((glArch (𝓞 F) F).comp (piIncl F))) =
      Pi.evalMonoidHom (fun w : InfinitePlace F => GL (Fin 2) w.Completion) v := by
    refine MonoidHom.pi_ext fun w y => ?_
    simp only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
    rw [piIncl_mulSingle]
    by_cases hvw : v = w
    · subst hvw
      rw [archComponent_glArch_inclAt_self, Pi.mulSingle_eq_same]
    · rw [archComponent_glArch_inclAt_of_ne F hvw, Pi.mulSingle_eq_of_ne hvw]
  exact DFunLike.congr_fun key x

theorem glFin_piIncl (x : (w : InfinitePlace F) → GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (piIncl F x) = 1 := by
  have key : ((glFin (𝓞 F) F).comp (piIncl F)) = 1 := by
    refine MonoidHom.pi_ext fun w y => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
    rw [piIncl_mulSingle, glFin_inclAt]
  exact DFunLike.congr_fun key x

theorem piIncl_archComponent_eq {k : AdelicGL2 (𝓞 F) F} (hk : glFin (𝓞 F) F k = 1) :
    piIncl F (fun w => archComponent F w (glArch (𝓞 F) F k)) = k :=
  eq_of_glFin_eq_of_forall_archComponent_eq F ((glFin_piIncl F _).trans hk.symm)
    fun v => archComponent_glArch_piIncl F _ v

theorem mulSingle_mul_update (x : (w : InfinitePlace F) → GL (Fin 2) w.Completion)
    (w₀ : InfinitePlace F) :
    Pi.mulSingle w₀ (x w₀) * Function.update x w₀ 1 = x := by
  funext w
  by_cases hw : w = w₀
  · subst hw; simp
  · simp [Pi.mulSingle_eq_of_ne hw, Function.update_of_ne hw]

theorem commute_inclAt_piIncl {w₀ : InfinitePlace F} (a : GL (Fin 2) w₀.Completion)
    (x : (w : InfinitePlace F) → GL (Fin 2) w.Completion) (hx : x w₀ = 1) :
    Commute (adelicArchGLInclAt F w₀ a) (piIncl F x) := by
  rw [← piIncl_mulSingle]
  refine Commute.map ?_ (piIncl F)
  show Pi.mulSingle w₀ a * x = x * Pi.mulSingle w₀ a
  refine funext fun w => ?_
  rw [Pi.mul_apply, Pi.mul_apply]
  by_cases hw : w = w₀
  · subst hw; simp [hx]
  · simp [Pi.mulSingle_eq_of_ne hw]

theorem continuous_archGLIncl (w : InfinitePlace F) : Continuous (archGLIncl F w) := by
  have hval : ∀ {f : GL (Fin 2) w.Completion → Matrix (Fin 2) (Fin 2) w.Completion}, Continuous f →
      Continuous fun k => archMatrixUpdate F w (f k) := by
    intro f hf
    refine continuous_matrix fun i j => continuous_pi fun v => ?_
    by_cases hv : v = w
    · subst hv
      simp only [archMatrixUpdate_apply_self]
      exact hf.matrix_elem i j
    · simp only [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      exact continuous_const
  rw [Units.continuous_iff]
  exact ⟨hval Units.continuous_val, hval Units.continuous_coe_inv⟩

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
          InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_inclAt (w : InfinitePlace F) : Continuous (adelicArchGLInclAt F w) := by
  show Continuous fun k => adelicArchGLIncl F (archGLIncl F w k)
  exact (continuous_adelicArchGLIncl F).comp (continuous_archGLIncl F w)

theorem inclAt_apply_fst (w : InfinitePlace F) (b : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt F w b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
      = archMatrixUpdate F w (b : Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl

theorem inclAt_apply_snd (w : InfinitePlace F) (b : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt F w b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := rfl

theorem inclAt_mem_adelicBorel (w : InfinitePlace F) {b : GL (Fin 2) w.Completion}
    (hb : b ∈ borelSubgroup w.Completion) : adelicArchGLInclAt F w b ∈ adelicBorel (𝓞 F) F := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := hb
  show (((adelicArchGLInclAt F w b : AdelicGL2 (𝓞 F) F) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) = 0
  refine Prod.ext ?_ ?_
  · rw [inclAt_apply_fst]
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, hb']; rfl
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv, Matrix.one_apply_ne (by decide)]; rfl
  · rw [inclAt_apply_snd, Matrix.one_apply_ne (by decide)]; rfl

theorem borelDiagFst_inclAt (w : InfinitePlace F) {b : GL (Fin 2) w.Completion}
    (hb : b ∈ borelSubgroup w.Completion) (hmem : adelicArchGLInclAt F w b ∈ adelicBorel (𝓞 F) F) :
    borelDiagFst (⟨adelicArchGLInclAt F w b, hmem⟩ : ↥(adelicBorel (𝓞 F) F))
      = archCentralUnit F w (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · show (((adelicArchGLInclAt F w b : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).1 = _
    rw [inclAt_apply_fst]
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, archCentralUnit_fst_self]; rfl
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv, Matrix.one_apply_eq, archCentralUnit_fst_of_ne _ _ hv]
  · show (((adelicArchGLInclAt F w b : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 = _
    rw [inclAt_apply_snd, Matrix.one_apply_eq, archCentralUnit_snd]

theorem borelDiagSnd_inclAt (w : InfinitePlace F) {b : GL (Fin 2) w.Completion}
    (hb : b ∈ borelSubgroup w.Completion) (hmem : adelicArchGLInclAt F w b ∈ adelicBorel (𝓞 F) F) :
    borelDiagSnd (⟨adelicArchGLInclAt F w b, hmem⟩ : ↥(adelicBorel (𝓞 F) F))
      = archCentralUnit F w (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · show (((adelicArchGLInclAt F w b : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 = _
    rw [inclAt_apply_fst]
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, archCentralUnit_fst_self]; rfl
    · rw [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv, Matrix.one_apply_eq, archCentralUnit_fst_of_ne _ _ hv]
  · show (((adelicArchGLInclAt F w b : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 = _
    rw [inclAt_apply_snd, Matrix.one_apply_eq, archCentralUnit_snd]

end Adelic

section Span

variable (F : Type) [Field F] [NumberField F]

abbrev Loc := (w : InfinitePlace F) → GL (Fin 2) w.Completion

def gen (U : AdelicGL2 (𝓞 F) F → ℂ) (s : Finset (InfinitePlace F)) : Set (AdelicGL2 (𝓞 F) F → ℂ) :=
  {f | ∃ k : Loc F, (∀ w, IsRowIsometry (k w)) ∧ (∀ w, w ∉ s → k w = 1) ∧ f = Rt F (piIncl F k) U}

def Vs (U : AdelicGL2 (𝓞 F) F → ℂ) (s : Finset (InfinitePlace F)) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (gen F U s)

theorem Rt_piIncl_mem_Vs (U : AdelicGL2 (𝓞 F) F → ℂ) (s : Finset (InfinitePlace F)) (k : Loc F)
    (hk : ∀ w, IsRowIsometry (k w)) (hks : ∀ w, w ∉ s → k w = 1) :
    Rt F (piIncl F k) U ∈ Vs F U s :=
  Submodule.subset_span ⟨k, hk, hks, rfl⟩

theorem self_mem_Vs (U : AdelicGL2 (𝓞 F) F → ℂ) (s : Finset (InfinitePlace F)) : U ∈ Vs F U s := by
  have h := Rt_piIncl_mem_Vs F U s 1 (fun _ => isRowIsometry_one) (fun _ _ => rfl)
  rwa [map_one, Rt_one] at h

theorem exists_span_of_isArchKFiniteAt {U : AdelicGL2 (𝓞 F) F → ℂ} {w : InfinitePlace F}
    (hU : IsArchKFiniteAt F w U) :
    ∃ W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k → Rt F (adelicArchGLInclAt F w k) U ∈ W := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨Submodule.span ℂ (t : Set (AdelicGL2 (𝓞 F) F → ℂ)), FiniteDimensional.span_of_finite ℂ t.finite_toSet,
    fun k hk => ?_⟩
  exact ht _ (Subgroup.mem_map_of_mem _ (x := k) hk)

def FinTr (w₀ : InfinitePlace F) (v : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ W ∧
    ∀ k : GL (Fin 2) w₀.Completion, IsRowIsometry k → Rt F (adelicArchGLInclAt F w₀ k) v ∈ W

theorem finTr_zero (w₀ : InfinitePlace F) : FinTr F w₀ 0 :=
  ⟨⊥, inferInstance, fun k _ => by rw [map_zero]; exact Submodule.zero_mem _⟩

theorem finTr_add (w₀ : InfinitePlace F) {u v : AdelicGL2 (𝓞 F) F → ℂ} (hu : FinTr F w₀ u)
    (hv : FinTr F w₀ v) : FinTr F w₀ (u + v) := by
  obtain ⟨W₁, h₁, hu⟩ := hu
  obtain ⟨W₂, h₂, hv⟩ := hv
  haveI := h₁; haveI := h₂
  refine ⟨W₁ ⊔ W₂, inferInstance, fun k hk => ?_⟩
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hu k hk)) (Submodule.mem_sup_right (hv k hk))

theorem finTr_smul (w₀ : InfinitePlace F) (a : ℂ) {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : FinTr F w₀ v) :
    FinTr F w₀ (a • v) := by
  obtain ⟨W, h, hv⟩ := hv
  refine ⟨W, h, fun k hk => ?_⟩
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hv k hk)

theorem finTr_gen {U : AdelicGL2 (𝓞 F) F → ℂ} (hUK : IsArchKFinite F U) {s : Finset (InfinitePlace F)}
    {w₀ : InfinitePlace F} (hw₀ : w₀ ∉ s) {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ gen F U s) :
    FinTr F w₀ f := by
  obtain ⟨k, hk, hks, rfl⟩ := hf
  obtain ⟨W, hW, hmem⟩ := exists_span_of_isArchKFiniteAt F (hUK w₀)
  haveI := hW
  refine ⟨W.map (Rt F (piIncl F k)), inferInstance, fun k₀ hk₀ => ?_⟩
  rw [← Rt_mul, (commute_inclAt_piIncl F k₀ k (hks w₀ hw₀)).eq, Rt_mul]
  exact Submodule.mem_map_of_mem (hmem k₀ hk₀)

theorem finTr_of_mem_Vs {U : AdelicGL2 (𝓞 F) F → ℂ} (hUK : IsArchKFinite F U)
    {s : Finset (InfinitePlace F)} {w₀ : InfinitePlace F} (hw₀ : w₀ ∉ s)
    {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ Vs F U s) : FinTr F w₀ v := by
  induction hv using Submodule.span_induction with
  | mem f hf => exact finTr_gen F hUK hw₀ hf
  | zero => exact finTr_zero F w₀
  | add u v _ _ hu hv => exact finTr_add F w₀ hu hv
  | smul a v _ hv => exact finTr_smul F w₀ a hv

theorem finiteDimensional_Vs {U : AdelicGL2 (𝓞 F) F → ℂ} (hUK : IsArchKFinite F U)
    (s : Finset (InfinitePlace F)) : FiniteDimensional ℂ (Vs F U s) := by
  induction s using Finset.induction_on with
  | empty =>
    haveI : FiniteDimensional ℂ (Submodule.span ℂ ({U} : Set (AdelicGL2 (𝓞 F) F → ℂ))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_singleton U)
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ({U} : Set (AdelicGL2 (𝓞 F) F → ℂ))) (Submodule.span_le.mpr ?_)
    rintro f ⟨k, hk, hks, rfl⟩
    have hk1 : k = 1 := funext fun w => hks w (Finset.notMem_empty w)
    rw [hk1, map_one, Rt_one]
    exact Submodule.subset_span (Set.mem_singleton U)
  | insert w₀ s hw₀ ih =>
    haveI := ih

    let β := Module.finBasis ℂ (Vs F U s)
    have hb : ∀ j, FinTr F w₀ ((β j : Vs F U s) : AdelicGL2 (𝓞 F) F → ℂ) :=
      fun j => finTr_of_mem_Vs F hUK hw₀ (β j).2
    choose W hW hmem using hb
    haveI : ∀ j, FiniteDimensional ℂ (W j) := hW
    refine Submodule.finiteDimensional_of_le (S₂ := ⨆ j, W j) (Submodule.span_le.mpr ?_)
    rintro f ⟨k, hk, hks, rfl⟩

    set k₂ : Loc F := Function.update k w₀ 1 with hk₂
    have hk₂r : ∀ w, IsRowIsometry (k₂ w) := by
      intro w
      by_cases hw : w = w₀
      · subst hw; rw [hk₂, Function.update_self]; exact isRowIsometry_one
      · rw [hk₂, Function.update_of_ne hw]; exact hk w
    have hk₂s : ∀ w, w ∉ s → k₂ w = 1 := by
      intro w hw
      by_cases hw' : w = w₀
      · subst hw'; rw [hk₂, Function.update_self]
      · rw [hk₂, Function.update_of_ne hw']
        exact hks w (fun h => (Finset.mem_insert.mp h).elim hw' hw)
    have hsplit : piIncl F k = adelicArchGLInclAt F w₀ (k w₀) * piIncl F k₂ := by
      rw [← piIncl_mulSingle, ← map_mul, mulSingle_mul_update]
    have hu : Rt F (piIncl F k₂) U ∈ Vs F U s := Rt_piIncl_mem_Vs F U s k₂ hk₂r hk₂s

    have hrepr := β.sum_repr ⟨Rt F (piIncl F k₂) U, hu⟩
    have hcoe := congrArg (fun v : Vs F U s => (v : AdelicGL2 (𝓞 F) F → ℂ)) hrepr
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hcoe
    show Rt F (piIncl F k) U ∈ ⨆ j, W j
    rw [hsplit, Rt_mul, ← hcoe, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem j (hmem j (k w₀) (hk w₀)))

def V (U : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Vs F U Finset.univ

theorem finiteDimensional_V {U : AdelicGL2 (𝓞 F) F → ℂ} (hUK : IsArchKFinite F U) :
    FiniteDimensional ℂ (V F U) :=
  finiteDimensional_Vs F hUK _

theorem self_mem_V (U : AdelicGL2 (𝓞 F) F → ℂ) : U ∈ V F U := self_mem_Vs F U _

theorem Rt_piIncl_mem_V {U : AdelicGL2 (𝓞 F) F → ℂ} {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ V F U)
    (k : Loc F) (hk : ∀ w, IsRowIsometry (k w)) : Rt F (piIncl F k) v ∈ V F U := by
  induction hv using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k', hk', -, rfl⟩ := hf
    rw [← Rt_mul, ← map_mul]
    exact Rt_piIncl_mem_Vs F U _ (k * k') (fun w => (hk w).mul (hk' w)) (fun w hw => absurd (Finset.mem_univ w) hw)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul a v _ hv => rw [map_smul]; exact Submodule.smul_mem _ _ hv

theorem Rt_inclAt_mem_V {U : AdelicGL2 (𝓞 F) F → ℂ} {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ V F U)
    (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (hk : IsRowIsometry k) :
    Rt F (adelicArchGLInclAt F w k) v ∈ V F U := by
  rw [← piIncl_mulSingle]
  refine Rt_piIncl_mem_V F hv _ fun v => ?_
  by_cases hvw : v = w
  · subst hvw; rw [Pi.mulSingle_eq_same]; exact hk
  · rw [Pi.mulSingle_eq_of_ne hvw]; exact isRowIsometry_one

end Span

section Props

variable (F : Type) [Field F] [NumberField F]

def BEquiv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (U : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
    glFin (𝓞 F) F b = 1 →
    (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
    ∀ g : AdelicGL2 (𝓞 F) F,
      U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g

variable {F}

theorem bEquiv_Rt {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {U : AdelicGL2 (𝓞 F) F → ℂ} (hU : BEquiv F μ ν U)
    (κ : AdelicGL2 (𝓞 F) F) : BEquiv F μ ν (Rt F κ U) := by
  intro b hb hf hr g
  simp only [Rt_apply]
  rw [mul_assoc]
  exact hU b hb hf hr (g * κ)

theorem bEquiv_zero (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) : BEquiv F μ ν 0 := by
  intro b hb hf hr g; simp

theorem bEquiv_add {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {u v : AdelicGL2 (𝓞 F) F → ℂ}
    (hu : BEquiv F μ ν u) (hv : BEquiv F μ ν v) : BEquiv F μ ν (u + v) := by
  intro b hb hf hr g
  simp only [Pi.add_apply]
  rw [hu b hb hf hr g, hv b hb hf hr g]
  ring

theorem bEquiv_smul {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (a : ℂ) {v : AdelicGL2 (𝓞 F) F → ℂ}
    (hv : BEquiv F μ ν v) : BEquiv F μ ν (a • v) := by
  intro b hb hf hr g
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hv b hb hf hr g]
  ring

theorem bEquiv_of_mem_V {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {U : AdelicGL2 (𝓞 F) F → ℂ}
    (hU : BEquiv F μ ν U) {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ V F U) : BEquiv F μ ν v := by
  induction hv using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, -, -, rfl⟩ := hf
    exact bEquiv_Rt hU _
  | zero => exact bEquiv_zero μ ν
  | add u v _ _ hu hv => exact bEquiv_add hu hv
  | smul a v _ hv => exact bEquiv_smul a hv

theorem continuous_of_mem_V {U : AdelicGL2 (𝓞 F) F → ℂ} (hU : Continuous U)
    {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ V F U) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, -, -, rfl⟩ := hf
    exact continuous_Rt F hU _
  | zero => exact continuous_const
  | add u v _ _ hu hv => exact hu.add hv
  | smul a v _ hv => exact continuous_const.mul hv

end Props

section Local

variable (F : Type) [Field F] [NumberField F]

def locRes (w : InfinitePlace F) : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (GL (Fin 2) w.Completion → ℂ) where
  toFun b g := b (adelicArchGLInclAt F w g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem locRes_apply (w : InfinitePlace F) (b : AdelicGL2 (𝓞 F) F → ℂ) (g : GL (Fin 2) w.Completion) :
    locRes F w b g = b (adelicArchGLInclAt F w g) := rfl

def Good (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) (f : GL (Fin 2) w.Completion → ℂ) : Prop :=
  Continuous f ∧ RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f ∧
    ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion),
      IsRowIsometry b → ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
        f (b * g) = ((archLocalChar μ w (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
          * ((archLocalChar ν w (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
          * f g

variable {F}

theorem good_const_mul {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {w : InfinitePlace F}
    {f : GL (Fin 2) w.Completion → ℂ} (hf : Good F μ ν w f) (a : ℂ) :
    Good F μ ν w (fun g => a * f g) := by
  obtain ⟨hc, ⟨t, ht⟩, he⟩ := hf
  refine ⟨continuous_const.mul hc, ⟨t, fun k hk => ?_⟩, fun b hb hbr g hg => ?_⟩
  · have h : (fun x => a * f (x * k)) = a • (fun x => f (x * k)) := by
      funext x; simp
    rw [h]
    exact Submodule.smul_mem _ _ (ht k hk)
  · show a * f (b * g) = _ * (a * f g)
    rw [he b hb hbr g hg]; ring

theorem good_locRes {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {U : AdelicGL2 (𝓞 F) F → ℂ}
    (hUc : Continuous U) (hUK : IsArchKFinite F U) (hUB : BEquiv F μ ν U)
    (w : InfinitePlace F) {b : AdelicGL2 (𝓞 F) F → ℂ} (hb : b ∈ V F U) :
    Good F μ ν w (locRes F w b) := by
  haveI := finiteDimensional_V F hUK
  refine ⟨(continuous_of_mem_V hUc hb).comp (continuous_inclAt F w), ?_, ?_⟩
  ·
    let β := Module.finBasis ℂ (V F U)
    refine ⟨Finset.univ.image fun j => locRes F w ((β j : V F U) : AdelicGL2 (𝓞 F) F → ℂ), ?_⟩
    intro k hk
    have hk' : IsRowIsometry k := hk
    have hmem : Rt F (adelicArchGLInclAt F w k) b ∈ V F U := Rt_inclAt_mem_V F hb w k hk'
    have htr : (fun x => locRes F w b (x * k)) = locRes F w (Rt F (adelicArchGLInclAt F w k) b) := by
      funext x
      simp only [locRes_apply, Rt_apply, map_mul]
    rw [htr]
    have hrepr := β.sum_repr ⟨_, hmem⟩
    have hcoe := congrArg (fun v : V F U => (v : AdelicGL2 (𝓞 F) F → ℂ)) hrepr
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hcoe
    rw [← hcoe, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨j, rfl⟩
  ·
    intro bb hbb hbbr g _
    have hB := bEquiv_of_mem_V hUB hb
    have hmem := inclAt_mem_adelicBorel F w hbb
    have hrow : ∀ v : InfinitePlace F,
        IsRowIsometry (archComponent F v (glArch (𝓞 F) F (adelicArchGLInclAt F w bb))) := by
      intro v
      by_cases hvw : v = w
      · subst hvw; rw [archComponent_glArch_inclAt_self]; exact hbbr
      · rw [archComponent_glArch_inclAt_of_ne F hvw]; exact isRowIsometry_one
    have key := hB _ hmem (glFin_inclAt F w bb) hrow (adelicArchGLInclAt F w g)
    simp only [locRes_apply, map_mul]
    rw [key, borelDiagFst_inclAt F w hbb hmem, borelDiagSnd_inclAt F w hbb hmem]
    rfl

end Local

section Expand

variable (F : Type) [Field F] [NumberField F]

theorem exists_expansion {U : AdelicGL2 (𝓞 F) F → ℂ} (hUK : IsArchKFinite F U) (w₀ : InfinitePlace F) :
    ∃ (n : ℕ) (bv : Fin n → (AdelicGL2 (𝓞 F) F → ℂ)) (_ : ∀ c, bv c ∈ V F U) (m : Fin n → ℕ)
      (e : (c : Fin n) → Fin (m c) → ℂ) (pt : (c : Fin n) → Fin (m c) → GL (Fin 2) w₀.Completion),
      (∀ c l, IsRowIsometry (pt c l)) ∧
      ∀ u ∈ V F U, ∀ k : GL (Fin 2) w₀.Completion, IsRowIsometry k →
        u (adelicArchGLInclAt F w₀ k)
          = ∑ c, (∑ l, e c l * u (adelicArchGLInclAt F w₀ (pt c l))) * bv c (adelicArchGLInclAt F w₀ k) := by
  haveI := finiteDimensional_V F hUK

  let res : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (↥(rowIsometrySubgroup w₀.Completion) → ℂ) :=
    { toFun := fun b k => b (adelicArchGLInclAt F w₀ (k : GL (Fin 2) w₀.Completion))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Submodule ℂ (↥(rowIsometrySubgroup w₀.Completion) → ℂ) := (V F U).map res
  haveI : FiniteDimensional ℂ W := inferInstance
  obtain ⟨n, ω, hω, m, e, pt, hexp⟩ := exists_basis_eval_expansion W
  have hpre : ∀ c, ∃ b ∈ V F U, res b = ω c := fun c => Submodule.mem_map.mp (hω c)
  choose bv hbv hres using hpre
  refine ⟨n, bv, hbv, m, e, fun c l => (pt c l : GL (Fin 2) w₀.Completion), fun c l => (pt c l).2,
    fun u hu k hk => ?_⟩
  have h := hexp (res u) (Submodule.mem_map_of_mem hu) ⟨k, hk⟩
  convert h using 2 with c
  · rfl
  · rw [← hres c]
    rfl

end Expand

section Induct

variable (F : Type) [Field F] [NumberField F]

theorem expand_finset {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {U : AdelicGL2 (𝓞 F) F → ℂ}
    (hUc : Continuous U) (hUK : IsArchKFinite F U) (hUB : BEquiv F μ ν U)
    (s : Finset (InfinitePlace F)) :
    ∀ v ∈ V F U, ∃ (J : Type) (_ : Fintype J) (c : J → ℂ)
      (f : J → (w : InfinitePlace F) → GL (Fin 2) w.Completion → ℂ),
      (∀ j, ∀ w ∈ s, Good F μ ν w (f j w)) ∧
      ∀ k : Loc F, (∀ w, IsRowIsometry (k w)) → (∀ w, w ∉ s → k w = 1) →
        v (piIncl F k) = ∑ j, c j * ∏ w ∈ s, f j w (k w) := by
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    refine ⟨Unit, inferInstance, fun _ => v 1, fun _ _ _ => 0, fun _ w hw => absurd hw (Finset.notMem_empty w),
      fun k hk hks => ?_⟩
    have hk1 : k = 1 := funext fun w => hks w (Finset.notMem_empty w)
    rw [hk1, map_one]
    simp
  | insert w₀ s hw₀ ih =>
    intro v hv
    obtain ⟨n, bv, hbv, m, e, pt, hpt, hexp⟩ := exists_expansion F hUK w₀
    have hvcl : ∀ (c : Fin n) (l : Fin (m c)), Rt F (adelicArchGLInclAt F w₀ (pt c l)) v ∈ V F U :=
      fun c l => Rt_inclAt_mem_V F hv w₀ _ (hpt c l)
    choose J hJ cc ff hgood hff using ih

    let Jn : Type := Σ c : Fin n, Σ l : Fin (m c), J _ (hvcl c l)
    letI : ∀ (c : Fin n) (l : Fin (m c)), Fintype (J _ (hvcl c l)) := fun c l => hJ _ _
    let c' : Jn → ℂ := fun x => e x.1 x.2.1 * cc _ (hvcl x.1 x.2.1) x.2.2
    let f' : Jn → (w : InfinitePlace F) → GL (Fin 2) w.Completion → ℂ := fun x w g =>
      if w = w₀ then bv x.1 (adelicArchGLInclAt F w g) else ff _ (hvcl x.1 x.2.1) x.2.2 w g
    refine ⟨Jn, inferInstance, c', f', ?_, ?_⟩
    ·
      rintro ⟨c, l, j⟩ w hw
      by_cases hww : w = w₀
      · subst hww
        have hf : f' ⟨c, l, j⟩ w = locRes F w (bv c) := by
          funext g; simp [f', locRes_apply]
        rw [hf]
        exact good_locRes hUc hUK hUB w (hbv c)
      · have hws : w ∈ s := (Finset.mem_insert.mp hw).resolve_left hww
        have hf : f' ⟨c, l, j⟩ w = ff _ (hvcl c l) j w := by
          funext g; simp [f', hww]
        rw [hf]
        exact hgood _ (hvcl c l) j w hws
    ·
      intro k hk hks
      set k₂ : Loc F := Function.update k w₀ 1 with hk₂
      have hk₂w₀ : k₂ w₀ = 1 := by rw [hk₂, Function.update_self]
      have hk₂w : ∀ w, w ≠ w₀ → k₂ w = k w := fun w hw => by rw [hk₂, Function.update_of_ne hw]
      have hk₂r : ∀ w, IsRowIsometry (k₂ w) := by
        intro w
        by_cases hw : w = w₀
        · subst hw; rw [hk₂w₀]; exact isRowIsometry_one
        · rw [hk₂w w hw]; exact hk w
      have hk₂s : ∀ w, w ∉ s → k₂ w = 1 := by
        intro w hw
        by_cases hw' : w = w₀
        · subst hw'; exact hk₂w₀
        · rw [hk₂w w hw']
          exact hks w (fun h => (Finset.mem_insert.mp h).elim hw' hw)
      have hsplit : piIncl F k = adelicArchGLInclAt F w₀ (k w₀) * piIncl F k₂ := by
        rw [← piIncl_mulSingle, ← map_mul, mulSingle_mul_update]
      have hu : Rt F (piIncl F k₂) v ∈ V F U := Rt_piIncl_mem_V F hv k₂ hk₂r

      have h1 : v (piIncl F k) = Rt F (piIncl F k₂) v (adelicArchGLInclAt F w₀ (k w₀)) := by
        rw [Rt_apply, hsplit]
      have h2 := hexp _ hu (k w₀) (hk w₀)

      have h3 : ∀ (c : Fin n) (l : Fin (m c)),
          Rt F (piIncl F k₂) v (adelicArchGLInclAt F w₀ (pt c l))
            = ∑ j, cc _ (hvcl c l) j * ∏ w ∈ s, ff _ (hvcl c l) j w (k w) := by
        intro c l
        rw [Rt_apply, (commute_inclAt_piIncl F (pt c l) k₂ hk₂w₀).eq]
        have hre : v (piIncl F k₂ * adelicArchGLInclAt F w₀ (pt c l))
            = Rt F (adelicArchGLInclAt F w₀ (pt c l)) v (piIncl F k₂) := rfl
        rw [hre, hff _ (hvcl c l) k₂ hk₂r hk₂s]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        refine Finset.prod_congr rfl fun w hw => ?_
        rw [hk₂w w (fun h => hw₀ (h ▸ hw))]

      have hR : ∀ x : Jn, c' x * ∏ w ∈ insert w₀ s, f' x w (k w)
          = e x.1 x.2.1 * cc _ (hvcl x.1 x.2.1) x.2.2 *
            (bv x.1 (adelicArchGLInclAt F w₀ (k w₀)) * ∏ w ∈ s, ff _ (hvcl x.1 x.2.1) x.2.2 w (k w)) := by
        intro x
        rw [Finset.prod_insert hw₀]
        have hx0 : f' x w₀ (k w₀) = bv x.1 (adelicArchGLInclAt F w₀ (k w₀)) := by simp [f']
        have hxs : ∀ w ∈ s, f' x w (k w) = ff _ (hvcl x.1 x.2.1) x.2.2 w (k w) := by
          intro w hw
          have hww : w ≠ w₀ := fun h => hw₀ (h ▸ hw)
          simp [f', hww]
        rw [hx0, Finset.prod_congr rfl hxs]
      rw [h1, h2, Finset.sum_congr rfl (fun x _ => hR x), Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Fintype.sum_sigma, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [h3 c l, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end Induct

section Main

variable (F : Type) [Field F] [NumberField F]

theorem main
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (U : AdelicGL2 (𝓞 F) F → ℂ) (hUc : Continuous U) (hUK : IsArchKFinite F U)
    (hUB : BEquiv F μ ν U) :
    ∃ (m : ℕ) (f : Fin m → (w : InfinitePlace F) → GL (Fin 2) w.Completion → ℂ),
      (∀ j w, Continuous (f j w)) ∧
      (∀ j w, RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) (f j w)) ∧
      (∀ (j : Fin m) (w : InfinitePlace F) (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion),
        IsRowIsometry b → ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f j w (b * g) = ((archLocalChar μ w (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((archLocalChar ν w (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * f j w g) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
        U k = ∑ j, ∏ w, f j w (archComponent F w (glArch (𝓞 F) F k)) := by
  obtain ⟨J, hJ, c, f, hgood, hexp⟩ := expand_finset F hUc hUK hUB Finset.univ U (self_mem_V F U)
  let w₁ : InfinitePlace F := Classical.arbitrary _
  let eJ := Fintype.equivFin J
  let f'' : Fin (Fintype.card J) → (w : InfinitePlace F) → GL (Fin 2) w.Completion → ℂ := fun i w g =>
    if w = w₁ then c (eJ.symm i) * f (eJ.symm i) w g else f (eJ.symm i) w g
  have hgood'' : ∀ i w, Good F μ ν w (f'' i w) := by
    intro i w
    by_cases hw : w = w₁
    · have h : f'' i w = fun g => c (eJ.symm i) * f (eJ.symm i) w g := by funext g; exact if_pos hw
      rw [h]
      exact good_const_mul (hgood _ w (Finset.mem_univ w)) _
    · have h : f'' i w = f (eJ.symm i) w := by funext g; exact if_neg hw
      rw [h]
      exact hgood _ w (Finset.mem_univ w)
  refine ⟨Fintype.card J, f'', fun i w => (hgood'' i w).1, fun i w => (hgood'' i w).2.1,
    fun i w => (hgood'' i w).2.2, fun k hk hfin => ?_⟩
  let kk : Loc F := fun w => archComponent F w (glArch (𝓞 F) F k)
  have hkr : ∀ w, IsRowIsometry (kk w) := hk.2
  have hU : U k = U (piIncl F kk) := by rw [piIncl_archComponent_eq F hfin]
  have hs : ∑ j, c j * ∏ w, f j w (kk w) = ∑ i, c (eJ.symm i) * ∏ w, f (eJ.symm i) w (kk w) :=
    (Equiv.sum_comp eJ.symm (fun j => c j * ∏ w, f j w (kk w))).symm
  rw [hU, hexp kk hkr (fun w hw => absurd (Finset.mem_univ w) hw), hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  show c (eJ.symm i) * ∏ w, f (eJ.symm i) w (kk w) = ∏ w, f'' i w (kk w)
  rw [← Finset.mul_prod_erase Finset.univ (fun w => f'' i w (kk w)) (Finset.mem_univ w₁),
    ← Finset.mul_prod_erase Finset.univ (fun w => f (eJ.symm i) w (kk w)) (Finset.mem_univ w₁)]
  have h1 : f'' i w₁ (kk w₁) = c (eJ.symm i) * f (eJ.symm i) w₁ (kk w₁) := if_pos rfl
  have h2 : ∀ w ∈ Finset.univ.erase w₁, f'' i w (kk w) = f (eJ.symm i) w (kk w) := by
    intro w hw
    exact if_neg (Finset.ne_of_mem_erase hw)
  rw [h1, Finset.prod_congr rfl h2, mul_assoc]

end Main

end R4Split

end

open NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem solution
    (F : Type) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (U : AdelicGL2 (𝓞 F) F → ℂ) (_hUc : Continuous U) (_hUK : IsArchKFinite F U)
    (_hUB : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F),
        glFin (𝓞 F) F b = 1 →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F b))) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          U (b * g) = ((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
            * ((ν (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ) * U g) :
    ∃ (m : ℕ) (f : Fin m → (w : InfinitePlace F) → GL (Fin 2) w.Completion → ℂ),
      (∀ j w, Continuous (f j w)) ∧
      (∀ j w, RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) (f j w)) ∧
      (∀ (j : Fin m) (w : InfinitePlace F) (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion),
        IsRowIsometry b → ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f j w (b * g) = ((archLocalChar μ w (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((archLocalChar ν w (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * f j w g) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F → glFin (𝓞 F) F k = 1 →
        U k = ∑ j, ∏ w, f j w (archComponent F w (glArch (𝓞 F) F k)) :=
  R4Split.main F μ ν U _hUc _hUK _hUB

end S_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_sum_prod_archComponent_of_isArchKFinite (solution)
