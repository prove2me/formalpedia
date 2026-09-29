-- Prove2me | solution 1 for AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/91c47127-5bc3-57bb-86cb-34c9a18f7a89

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm
open scoped Matrix

noncomputable section

namespace BIFIN

section Generic

variable {H G : Type*} [Group H] [Group G] (ι : H →* G)

def rTrans (g : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rTrans_apply (g : G) (u : G → ℂ) (x : G) : rTrans g u x = u (x * g) := rfl

theorem rTrans_one (u : G → ℂ) : rTrans (1 : G) u = u := by
  funext x; simp

theorem rTrans_rTrans (a b : G) (u : G → ℂ) : rTrans a (rTrans b u) = rTrans (a * b) u := by
  funext x; simp [mul_assoc]

def Stable (V : Submodule ℂ (G → ℂ)) : Prop := ∀ k : H, ∀ u ∈ V, rTrans (ι k) u ∈ V

def trSpan (φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun k : H => rTrans (ι k) φ)

theorem mem_trSpan (φ : G → ℂ) : φ ∈ trSpan ι φ :=
  Submodule.subset_span ⟨1, by show rTrans (ι 1) φ = φ; rw [map_one, rTrans_one]⟩

theorem rTrans_mem_trSpan (φ : G → ℂ) (k : H) : rTrans (ι k) φ ∈ trSpan ι φ :=
  Submodule.subset_span ⟨k, rfl⟩

theorem stable_trSpan (φ : G → ℂ) : Stable ι (trSpan ι φ) := by
  intro k u hu
  have hmap : Submodule.map (rTrans (ι k)) (trSpan ι φ) ≤ trSpan ι φ := by
    rw [trSpan, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨k', rfl⟩, rfl⟩
    exact ⟨k * k', by show rTrans (ι (k * k')) φ = rTrans (ι k) (rTrans (ι k') φ); rw [map_mul, rTrans_rTrans]⟩
  exact hmap (Submodule.mem_map_of_mem hu)

theorem trSpan_le {φ : G → ℂ} {V : Submodule ℂ (G → ℂ)} (hV : Stable ι V) (hφ : φ ∈ V) : trSpan ι φ ≤ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  exact hV k φ hφ

theorem exists_fd_stable_of_mem_typeSubmodule {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H W) {g : G → ℂ} (hg : g ∈ typeSubmodule ι ρ) :
    ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U := by
  refine Submodule.span_induction (p := fun g _ => ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨T, hT, v, rfl⟩
    refine ⟨LinearMap.range T, inferInstance, LinearMap.mem_range_self T v, ?_⟩
    rintro k _ ⟨v', rfl⟩
    refine ⟨ρ k v', ?_⟩
    funext x
    exact hT k v' x
  · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k u hu => by
      rw [(Submodule.mem_bot ℂ).1 hu, map_zero]; exact Submodule.zero_mem _⟩
  · rintro a b - - ⟨U₁, hU₁, ha, hs₁⟩ ⟨U₂, hU₂, hb, hs₂⟩
    haveI := hU₁; haveI := hU₂
    refine ⟨U₁ ⊔ U₂, inferInstance, Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb), ?_⟩
    intro k u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hs₁ k u₁ hu₁)) (Submodule.mem_sup_right (hs₂ k u₂ hu₂))
  · rintro c a - ⟨U, hU, ha, hs⟩
    exact ⟨U, hU, Submodule.smul_mem _ c ha, hs⟩

theorem exists_fd_stable_of_mem_iSup {ι₀ : Type*} (S : ι₀ → Submodule ℂ (G → ℂ))
    (hS : ∀ i, ∀ g ∈ S i, ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U)
    {g : G → ℂ} (hg : g ∈ ⨆ i, S i) :
    ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U := by
  refine Submodule.iSup_induction _ (motive := fun g => ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U)
    hg hS ?_ ?_
  · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k u hu => by
      rw [(Submodule.mem_bot ℂ).1 hu, map_zero]; exact Submodule.zero_mem _⟩
  · rintro a b ⟨U₁, hU₁, ha, hs₁⟩ ⟨U₂, hU₂, hb, hs₂⟩
    haveI := hU₁; haveI := hU₂
    refine ⟨U₁ ⊔ U₂, inferInstance, Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb), ?_⟩
    intro k u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hs₁ k u₁ hu₁)) (Submodule.mem_sup_right (hs₂ k u₂ hu₂))

theorem exists_rep_of_fd_stable (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : Stable ι V)
    {φ : G → ℂ} (hφ : φ ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)) (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι ρ T ∧ φ ∈ LinearMap.range T := by

  let ρV : Representation ℂ H V :=
    { toFun := fun k => (rTrans (ι k)).restrict (hV k)
      map_one' := by
        refine LinearMap.ext fun u => Subtype.ext ?_
        show rTrans (ι 1) (u : G → ℂ) = u
        rw [map_one, rTrans_one]
      map_mul' := fun a b => by
        refine LinearMap.ext fun u => Subtype.ext ?_
        show rTrans (ι (a * b)) (u : G → ℂ) = rTrans (ι a) (rTrans (ι b) (u : G → ℂ))
        rw [map_mul, rTrans_rTrans] }
  have hρV : ∀ (k : H) (u : V), ((ρV k u : V) : G → ℂ) = rTrans (ι k) (u : G → ℂ) := fun _ _ => rfl
  set n := Module.finrank ℂ V
  let L : V ≃ₗ[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ V).equivFun
  let ρ : Representation ℂ H (Fin n → ℂ) :=
    { toFun := fun k => L.toLinearMap ∘ₗ ρV k ∘ₗ L.symm.toLinearMap
      map_one' := by
        refine LinearMap.ext fun v => ?_
        simp [map_one]
      map_mul' := fun a b => by
        refine LinearMap.ext fun v => ?_
        simp [map_mul] }
  have hρ : ∀ (k : H) (v : Fin n → ℂ), ρ k v = L (ρV k (L.symm v)) := fun _ _ => rfl
  let T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) := V.subtype ∘ₗ L.symm.toLinearMap
  have hT : ∀ v : Fin n → ℂ, T v = ((L.symm v : V) : G → ℂ) := fun _ => rfl
  refine ⟨n, ρ, T, ?_, ⟨L ⟨φ, hφ⟩, ?_⟩⟩
  · intro k v x
    rw [hT, hT, hρ, LinearEquiv.symm_apply_apply, hρV, rTrans_apply]
  · rw [hT, LinearEquiv.symm_apply_apply]

theorem exists_rep_mem_typeSubmodule (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : Stable ι V)
    {φ : G → ℂ} (hφ : φ ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), φ ∈ typeSubmodule ι ρ := by
  obtain ⟨n, ρ, T, hT, v, rfl⟩ := exists_rep_of_fd_stable ι V hV hφ
  exact ⟨n, ρ, mem_typeSubmodule_of_isRightEquivariant hT v⟩

theorem basisFun_toDual_apply (n : ℕ) (v w : Fin n → ℂ) :
    (Pi.basisFun ℂ (Fin n)).toDual v w = v ⬝ᵥ w := by
  conv_lhs => rw [← (Pi.basisFun ℂ (Fin n)).sum_repr w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_rep_mem_typeSubmodule_dual (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : Stable ι V)
    {φ : G → ℂ} (hφ : φ ∈ V) :
    ∃ (n : ℕ) (σ : Representation ℂ H (Fin n → ℂ)), φ ∈ typeSubmodule ι σ.dual := by
  obtain ⟨n, ρ, T, hT, v₀, rfl⟩ := exists_rep_of_fd_stable ι V hV hφ

  let σ : Representation ℂ H (Fin n → ℂ) :=
    { toFun := fun k => Matrix.toLin' (LinearMap.toMatrix' (ρ k⁻¹))ᵀ
      map_one' := by
        rw [inv_one, map_one]
        show Matrix.toLin' (LinearMap.toMatrix' (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))ᵀ = 1
        rw [LinearMap.toMatrix'_id, Matrix.transpose_one, Matrix.toLin'_one]
        rfl
      map_mul' := fun a b => by
        rw [mul_inv_rev, map_mul, LinearMap.toMatrix'_mul, Matrix.transpose_mul, Matrix.toLin'_mul]
        rfl }
  have hσ : ∀ k : H, σ k = Matrix.toLin' (LinearMap.toMatrix' (ρ k⁻¹))ᵀ := fun _ => rfl
  let D : (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).toDualEquiv
  have hD : ∀ v w : Fin n → ℂ, D v w = v ⬝ᵥ w := basisFun_toDual_apply n

  have hkey : ∀ (k : H) (v : Fin n → ℂ), (D v) ∘ₗ σ k⁻¹ = D (ρ k v) := by
    intro k v
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, hσ, inv_inv, Matrix.toLin'_apply, hD, hD, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    congr 1
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  let T' : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) := T ∘ₗ D.symm.toLinearMap
  have hT' : IsRightEquivariant ι σ.dual T' := by
    intro k f x
    obtain ⟨v, rfl⟩ : ∃ v, D v = f := ⟨D.symm f, D.apply_symm_apply f⟩
    show T (D.symm (σ.dual k (D v))) x = T (D.symm (D v)) (x * ι k)
    rw [Representation.dual_apply, Module.Dual.transpose_apply, hkey, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
    exact hT k v x
  refine ⟨n, σ, ?_⟩
  have : T v₀ = T' (D v₀) := by
    show T v₀ = T (D.symm (D v₀)); rw [LinearEquiv.symm_apply_apply]
  rw [this]
  exact mem_typeSubmodule_of_isRightEquivariant hT' _

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem continuous_and_hasCompactSupport_of_mem_trSpan (w : InfinitePlace F) {φ : (AdelicGL2 (𝓞 F) F) → ℂ}
    (hc : Continuous φ) (hs : HasCompactSupport φ) {ψ : (AdelicGL2 (𝓞 F) F) → ℂ} (hψ : ψ ∈ trSpan (rowIsometryInclAt₀ F w) φ) :
    Continuous ψ ∧ HasCompactSupport ψ := by
  refine Submodule.span_induction (p := fun ψ _ => Continuous ψ ∧ HasCompactSupport ψ) ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k, rfl⟩
    exact ⟨hc.comp (continuous_mul_right _), hs.comp_homeomorph (Homeomorph.mulRight _)⟩
  · exact ⟨continuous_const, HasCompactSupport.zero⟩
  · rintro a b - - ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, ha'.add hb'⟩
  · rintro c a - ⟨ha, ha'⟩
    refine ⟨continuous_const.mul ha, ?_⟩
    exact ha'.mul_left

variable (f f' : (AdelicGL2 (𝓞 F) F) → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
  (hfc' : Continuous f') (hfs' : HasCompactSupport f')

theorem kernel_apply (z : (AdelicGL2 (𝓞 F) F)) : rightConv F f' (fun x => f x⁻¹) z = ∫ y, f' (z * y) * f y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  rw [rightConv_apply]

include hfc hfs hfc' in

theorem exists_linear_right (w : InfinitePlace F) (W : Submodule ℂ ((AdelicGL2 (𝓞 F) F) → ℂ))
    (hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ) :
    ∃ B : W →ₗ[ℂ] ((AdelicGL2 (𝓞 F) F) → ℂ), ∀ ψ : W, (B ψ : (AdelicGL2 (𝓞 F) F) → ℂ) = fun x => ∫ y, f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hInt : ∀ ψ : W, ∀ x : (AdelicGL2 (𝓞 F) F), Integrable (fun y => f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro ψ x
    obtain ⟨hψc, hψs⟩ := hW ψ ψ.2
    exact ((hfc'.comp (continuous_const_mul x)).mul (hψc.comp continuous_inv)).integrable_of_hasCompactSupport
      ((hψs.comp_homeomorph (Homeomorph.inv _)).mul_left)
  let Bf : W → ((AdelicGL2 (𝓞 F) F) → ℂ) := fun ψ x => ∫ y, f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  have hadd : ∀ ψ₁ ψ₂ : W, Bf (ψ₁ + ψ₂) = Bf ψ₁ + Bf ψ₂ := by
    intro ψ₁ ψ₂
    funext x
    show (∫ y, f' (x * y) * ((ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) + (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ)) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (∫ y, f' (x * y) * (ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) + ∫ y, f' (x * y) * (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [← integral_add (hInt ψ₁ x) (hInt ψ₂ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, mul_add]
  have hsmul : ∀ (c : ℂ) (ψ : W), Bf (c • ψ) = c • Bf ψ := by
    intro c ψ
    funext x
    show (∫ y, f' (x * y) * (c • (ψ : (AdelicGL2 (𝓞 F) F) → ℂ)) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) = c • ∫ y, f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨{ toFun := Bf, map_add' := hadd, map_smul' := hsmul }, fun ψ => rfl⟩

include hfc hfs hfc' in

theorem exists_linear_left (w : InfinitePlace F) (W : Submodule ℂ ((AdelicGL2 (𝓞 F) F) → ℂ))
    (hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ) :
    ∃ C : W →ₗ[ℂ] ((AdelicGL2 (𝓞 F) F) → ℂ), ∀ ψ : W, (C ψ : (AdelicGL2 (𝓞 F) F) → ℂ) = fun x => ∫ v, (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hInt : ∀ ψ : W, ∀ x : (AdelicGL2 (𝓞 F) F), Integrable (fun v => (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹)) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro ψ x
    obtain ⟨hψc, hψs⟩ := hW ψ ψ.2
    exact ((hψc.comp continuous_inv).mul (hfc.comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      ((hψs.comp_homeomorph (Homeomorph.inv _)).mul_right)
  let Cf : W → ((AdelicGL2 (𝓞 F) F) → ℂ) := fun ψ x => ∫ v, (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  have hadd : ∀ ψ₁ ψ₂ : W, Cf (ψ₁ + ψ₂) = Cf ψ₁ + Cf ψ₂ := by
    intro ψ₁ ψ₂
    funext x
    show (∫ v, ((ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) + (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ)) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (∫ v, (ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) + ∫ v, (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [← integral_add (hInt ψ₁ x) (hInt ψ₂ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply, add_mul]
  have hsmul : ∀ (c : ℂ) (ψ : W), Cf (c • ψ) = c • Cf ψ := by
    intro c ψ
    funext x
    show (∫ v, (c • (ψ : (AdelicGL2 (𝓞 F) F) → ℂ)) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) = c • ∫ v, (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨{ toFun := Cf, map_add' := hadd, map_smul' := hsmul }, fun ψ => rfl⟩

theorem kernel_mul_right (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : (AdelicGL2 (𝓞 F) F)) :
    rightConv F f' (fun x => f x⁻¹) (x * rowIsometryInclAt₀ F w k) =
      ∫ y, f' (x * y) * (rTrans (rowIsometryInclAt₀ F w k) f) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set t : (AdelicGL2 (𝓞 F) F) := rowIsometryInclAt₀ F w k
  rw [kernel_apply]
  rw [← integral_mul_left_eq_self (fun y => f' (x * t * y) * f y⁻¹) t⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [rTrans_apply, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]

theorem kernel_inv_mul_right (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : (AdelicGL2 (𝓞 F) F)) :
    rightConv F f' (fun x => f x⁻¹) (x * rowIsometryInclAt₀ F w k)⁻¹ =
      ∫ v, (rTrans (rowIsometryInclAt₀ F w k) (fun u => f' u⁻¹)) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set t : (AdelicGL2 (𝓞 F) F) := rowIsometryInclAt₀ F w k
  rw [kernel_apply]
  rw [← integral_mul_left_eq_self (fun y => f' ((x * t)⁻¹ * y) * f y⁻¹) (x * t)]
  rw [← integral_mul_left_eq_self (fun v => f' ((x * t)⁻¹ * ((x * t) * v)) * f ((x * t) * v)⁻¹) t⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [rTrans_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]

end Adelic

end BIFIN
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv.BIFIN"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv.BIFIN"

open BIFIN in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hbf : IsArchBiFinite F tys f)
    (hfc' : Continuous f') (hfs' : HasCompactSupport f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F, IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) := by
  classical
  set h : AdelicGL2 (𝓞 F) F → ℂ := rightConv F f' (fun x => f x⁻¹) with hh

  have hleft : ∀ w : InfinitePlace F, ∃ (n : ℕ) (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin n → ℂ)),
      (fun x => h x⁻¹) ∈ typeSubmodule (rowIsometryInclAt₀ F w) ρ := by
    intro w
    set ι := rowIsometryInclAt₀ F w

    have hmem : (fun x => f' x⁻¹) ∈ ⨆ i, archTypeSubmoduleAt F w (tys'.rep w i) :=
      (mem_archCutSubmodule_iff F tys' _).1 hbf'.1 w
    obtain ⟨U, hU, hgU, hsU⟩ := exists_fd_stable_of_mem_iSup ι _
      (fun i g hg => exists_fd_stable_of_mem_typeSubmodule ι (tys'.rep w i).ρ hg) hmem
    haveI := hU
    set W := trSpan ι (fun x => f' x⁻¹)
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (trSpan_le ι hsU hgU)
    have hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ := fun ψ hψ =>
      continuous_and_hasCompactSupport_of_mem_trSpan F w (hfc'.comp continuous_inv)
        (hfs'.comp_homeomorph (Homeomorph.inv _)) hψ
    obtain ⟨C, hC⟩ := exists_linear_left F f f' hfc hfs hfc' w W hW

    set V := trSpan ι (fun x => h x⁻¹)
    have hVle : V ≤ LinearMap.range C := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨⟨rTrans (ι k) (fun u => f' u⁻¹), rTrans_mem_trSpan ι _ k⟩, ?_⟩
      rw [hC]
      funext x
      show _ = rTrans (ι k) (fun x => h x⁻¹) x
      rw [rTrans_apply]
      exact (kernel_inv_mul_right F f f' w k x).symm
    haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVle
    exact exists_rep_mem_typeSubmodule ι V (stable_trSpan ι _) (mem_trSpan ι _)

  have hright : ∀ w : InfinitePlace F, ∃ (n : ℕ) (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin n → ℂ)),
      h ∈ typeSubmodule (rowIsometryInclAt₀ F w) σ.dual := by
    intro w
    set ι := rowIsometryInclAt₀ F w
    have hmem : f ∈ ⨆ i, archDualTypeSubmoduleAt F w (tys.rep w i) :=
      (mem_archDualCutSubmodule_iff F tys _).1 hbf.2 w
    obtain ⟨U, hU, hgU, hsU⟩ := exists_fd_stable_of_mem_iSup ι _
      (fun i g hg => exists_fd_stable_of_mem_typeSubmodule ι (tys.rep w i).ρ.dual hg) hmem
    haveI := hU
    set W := trSpan ι f
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (trSpan_le ι hsU hgU)
    have hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ := fun ψ hψ =>
      continuous_and_hasCompactSupport_of_mem_trSpan F w hfc hfs hψ
    obtain ⟨B, hB⟩ := exists_linear_right F f f' hfc hfs hfc' w W hW
    set V := trSpan ι h
    have hVle : V ≤ LinearMap.range B := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨⟨rTrans (ι k) f, rTrans_mem_trSpan ι _ k⟩, ?_⟩
      rw [hB]
      funext x
      show _ = rTrans (ι k) h x
      rw [rTrans_apply]
      exact (kernel_mul_right F f f' w k x).symm
    haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVle
    exact exists_rep_mem_typeSubmodule_dual ι V (stable_trSpan ι _) (mem_trSpan ι _)

  choose nL ρL hρL using hleft
  choose nR σR hσR using hright
  refine ⟨⟨fun _ => 2, fun w => ![⟨nL w, ρL w⟩, ⟨nR w, σR w⟩]⟩, ?_, ?_⟩
  · rw [mem_archCutSubmodule_iff]
    intro w
    exact Submodule.mem_iSup_of_mem (0 : Fin 2) (hρL w)
  · rw [mem_archDualCutSubmodule_iff]
    intro w
    exact Submodule.mem_iSup_of_mem (1 : Fin 2) (hσR w)

end S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv
end P2MW
export P2MW.S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv (solution)
