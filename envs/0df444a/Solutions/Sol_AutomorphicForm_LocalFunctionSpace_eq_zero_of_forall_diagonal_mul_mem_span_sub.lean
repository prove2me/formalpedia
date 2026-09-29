-- Prove2me | solution 1 for AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e85f96a1-cab4-51d5-b7fb-2f32d26be2f0

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_diagonal_mul_mem_span_sub

set_option autoImplicit false

open scoped Classical

namespace KirillovInjectivityAux

open AutomorphicForm IsDedekindDomain

variable (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "Γ" => Units (WithZero (Multiplicative ℤ))

private abbrev RightSmooth (φ : G → ℂ) : Prop :=
  ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, (fun g => φ (g * k)) = φ

private def defectSet (S : Submodule ℂ (G → ℂ)) : Set (G → ℂ) :=
  {V | ∃ U ∈ S, ∃ x : F, V = (fun g => U (g * unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}

private abbrev IsRepSystem (β δ : Γ) (T : Finset F) : Prop :=
  (∀ t ∈ T, Valued.v t < (β : WithZero (Multiplicative ℤ))) ∧
    ∀ x : F, Valued.v x < (β : WithZero (Multiplicative ℤ)) →
      ∃! t, t ∈ T ∧ Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ))

private abbrev WindowSumsVanish (φ : F → ℂ) : Prop :=
  ∃ β₀ : Γ, ∀ β : Γ, β₀ ≤ β → ∃ δ₀ : Γ, ∀ δ : Γ, δ ≤ δ₀ → ∀ T : Finset F, IsRepSystem p β δ T →
    ∑ t ∈ T, NumberField.StandardAddChar.psiV p (-t) * φ t = 0

private noncomputable def diagGL2 (a : F) (ha : a ≠ 0) : G where
  val := !![a, 0; 0, 1]
  inv := !![a⁻¹, 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]

@[scoped simp] private theorem diagGL2_coe (a : F) (ha : a ≠ 0) :
    (diagGL2 p a ha : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, 1] := rfl

@[scoped simp] private theorem diagGL2_inv_coe (a : F) (ha : a ≠ 0) :
    (((diagGL2 p a ha)⁻¹ : G) : Matrix (Fin 2) (Fin 2) F) = !![a⁻¹, 0; 0, 1] := rfl

private theorem inv_diagGL2_mul_unipotent_mul_diagGL2 (a : F) (ha : a ≠ 0) (x : F) :
    (diagGL2 p a ha)⁻¹ * unipotentGL2 x * diagGL2 p a ha = unipotentGL2 (a⁻¹ * x) := by
  apply Units.ext
  simp only [Units.val_mul, diagGL2_inv_coe, unipotentGL2_coe, diagGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]

private theorem exists_unit_gt (y : F) : ∃ β₀ : Γ, Valued.v y < (β₀ : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨1, by simp⟩
  · have hv : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hy
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hv
    refine ⟨Units.mk0 ((m * Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      WithZero.coe_ne_zero, ?_⟩
    rw [← hm, Units.val_mk0, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_ofAdd]
    exact lt_add_one _

private theorem isRepSystem_image_add {β δ : Γ} {T : Finset F} (hT : IsRepSystem p β δ T) {y : F}
    (hy : Valued.v y < (β : WithZero (Multiplicative ℤ))) : IsRepSystem p β δ (T.image (· + y)) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (hT.1 t ht) hy)
  · intro x hx
    have hxy : Valued.v (x - y) < (β : WithZero (Multiplicative ℤ)) :=
      (Valuation.map_sub _ _ _).trans_lt (max_lt hx hy)
    obtain ⟨t, ⟨ht, hclose⟩, huniq⟩ := hT.2 (x - y) hxy
    refine ⟨t + y, ⟨Finset.mem_image_of_mem _ ht, ?_⟩, ?_⟩
    · have e : x - (t + y) = x - y - t := by ring
      rw [e]
      exact hclose
    · rintro s ⟨hs, hs'⟩
      obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hs
      have e : x - y - t₁ = x - (t₁ + y) := by ring
      rw [huniq t₁ ⟨ht₁, by rw [e]; exact hs'⟩]

private theorem isRepSystem_image_mul {β δ : Γ} {T : Finset F} (hT : IsRepSystem p β δ T) {a : F} (ha : a ≠ 0) :
    IsRepSystem p (Units.mk0 (Valued.v a) ((Valuation.ne_zero_iff _).mpr ha) * β)
      (Units.mk0 (Valued.v a) ((Valuation.ne_zero_iff _).mpr ha) * δ) (T.image (a * ·)) := by
  have hva : (0 : WithZero (Multiplicative ℤ)) < Valued.v a := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ha)
  have hva' : (0 : WithZero (Multiplicative ℤ)) < (Valued.v a)⁻¹ := zero_lt_iff.mpr (inv_ne_zero hva.ne')
  refine ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    simp only [Units.val_mul, Units.val_mk0, map_mul]
    exact mul_lt_mul_of_pos_left (hT.1 t ht) hva
  · intro x hx
    simp only [Units.val_mul, Units.val_mk0] at hx
    have hx' : Valued.v (a⁻¹ * x) < (β : WithZero (Multiplicative ℤ)) := by
      rw [map_mul, map_inv₀]
      have := mul_lt_mul_of_pos_left hx hva'
      rwa [inv_mul_cancel_left₀ hva.ne'] at this
    obtain ⟨t, ⟨ht, hclose⟩, huniq⟩ := hT.2 (a⁻¹ * x) hx'
    have hkey : ∀ t₁ : F, Valued.v (x - a * t₁) = Valued.v a * Valued.v (a⁻¹ * x - t₁) := by
      intro t₁
      rw [← map_mul, mul_sub, mul_inv_cancel_left₀ ha]
    refine ⟨a * t, ⟨Finset.mem_image_of_mem _ ht, ?_⟩, ?_⟩
    · simp only [Units.val_mul, Units.val_mk0]
      rw [hkey]
      exact mul_lt_mul_of_pos_left hclose hva
    · rintro s ⟨hs, hs'⟩
      obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.mp hs
      simp only [Units.val_mul, Units.val_mk0] at hs'
      rw [hkey] at hs'
      have h1 : Valued.v (a⁻¹ * x - t₁) < (δ : WithZero (Multiplicative ℤ)) := by
        have := mul_lt_mul_of_pos_left hs' hva'
        rwa [inv_mul_cancel_left₀ hva.ne', inv_mul_cancel_left₀ hva.ne'] at this
      rw [huniq t₁ ⟨ht₁, h1⟩]

private theorem sum_ite_eq_of_isRepSystem {β δ : Γ} {T : Finset F} (hT : IsRepSystem p β δ T) (φ : F → ℂ)
    (hφ : ∀ x y : F, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → φ x = φ y) {x : F}
    (hx : Valued.v x < (β : WithZero (Multiplicative ℤ))) :
    (∑ t ∈ T, if Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ)) then φ t else 0) = φ x := by
  obtain ⟨t, ⟨ht, hclose⟩, huniq⟩ := hT.2 x hx
  rw [Finset.sum_eq_single_of_mem t ht]
  · rw [if_pos hclose, hφ x t hclose]
  · intro u hu hne
    exact if_neg fun hc => hne (huniq u ⟨hu, hc⟩)

private theorem sum_eq_sum_of_isRepSystem {β δ : Γ} {T T' : Finset F} (hT : IsRepSystem p β δ T)
    (hT' : IsRepSystem p β δ T') (φ : F → ℂ)
    (hφ : ∀ x y : F, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → φ x = φ y) :
    ∑ t ∈ T, φ t = ∑ t ∈ T', φ t := by
  calc ∑ t ∈ T, φ t
      = ∑ t ∈ T, ∑ t' ∈ T', (if Valued.v (t - t') < (δ : WithZero (Multiplicative ℤ)) then φ t' else 0) :=
        Finset.sum_congr rfl fun t ht => (sum_ite_eq_of_isRepSystem p hT' φ hφ (hT.1 t ht)).symm
    _ = ∑ t' ∈ T', ∑ t ∈ T, (if Valued.v (t - t') < (δ : WithZero (Multiplicative ℤ)) then φ t' else 0) :=
        Finset.sum_comm
    _ = ∑ t' ∈ T', ∑ t ∈ T, (if Valued.v (t' - t) < (δ : WithZero (Multiplicative ℤ)) then φ t else 0) := by
        refine Finset.sum_congr rfl fun t' _ => Finset.sum_congr rfl fun t _ => ?_
        rw [Valuation.map_sub_swap]
        split_ifs with h
        · exact hφ t' t h
        · rfl
    _ = ∑ t' ∈ T', φ t' :=
        Finset.sum_congr rfl fun t' ht' => sum_ite_eq_of_isRepSystem p hT φ hφ (hT'.1 t' ht')

private theorem exists_psiV_eq_one :
    ∃ γ₀ : Γ, ∀ x : F, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) →
      NumberField.StandardAddChar.psiV p x = 1 := by
  refine ⟨1, fun x hx => NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using hx.le

private theorem continuous_unipotentGL2 : Continuous (fun x : F => (unipotentGL2 x : G)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

private theorem exists_unipotent_mem_of_isOpen (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    ∃ δ : Γ, ∀ z : F, Valued.v z < (δ : WithZero (Multiplicative ℤ)) → unipotentGL2 z ∈ K := by
  have hU : ((fun z : F => (unipotentGL2 z : G)) ⁻¹' (K : Set G)) ∈ nhds (0 : F) := by
    apply (hK.preimage (continuous_unipotentGL2 p)).mem_nhds
    show unipotentGL2 (0 : F) ∈ K
    rw [unipotentGL2_zero]
    exact K.one_mem
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation _).mp hU
  have hb : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ (0 : WithZero (Multiplicative ℤ)) := by
    intro h
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  refine ⟨Units.mk0 _ hb, fun z hz => ?_⟩
  apply hγ
  show Valued.v.restrict z < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa using hz

private theorem smooth_zero : RightSmooth p (0 : G → ℂ) :=
  ⟨⊤, by simp, fun _ _ => by ext g; rfl⟩

private theorem RightSmooth.sub {φ₁ φ₂ : G → ℂ} (h₁ : RightSmooth p φ₁) (h₂ : RightSmooth p φ₂) :
    RightSmooth p (φ₁ - φ₂) := by
  obtain ⟨K₁, hK₁, hf₁⟩ := h₁
  obtain ⟨K₂, hK₂, hf₂⟩ := h₂
  refine ⟨K₁ ⊓ K₂, by rw [Subgroup.coe_inf]; exact hK₁.inter hK₂, fun k hk => ?_⟩
  have hk' := Subgroup.mem_inf.mp hk
  funext g'
  show φ₁ (g' * k) - φ₂ (g' * k) = φ₁ g' - φ₂ g'
  have e₁' := congrFun (hf₁ k hk'.1) g'
  have e₂' := congrFun (hf₂ k hk'.2) g'
  rw [e₁', e₂']

private theorem RightSmooth.add {φ₁ φ₂ : G → ℂ} (h₁ : RightSmooth p φ₁) (h₂ : RightSmooth p φ₂) :
    RightSmooth p (φ₁ + φ₂) := by
  obtain ⟨K₁, hK₁, hf₁⟩ := h₁
  obtain ⟨K₂, hK₂, hf₂⟩ := h₂
  refine ⟨K₁ ⊓ K₂, by rw [Subgroup.coe_inf]; exact hK₁.inter hK₂, fun k hk => ?_⟩
  have hk' := Subgroup.mem_inf.mp hk
  funext g'
  show φ₁ (g' * k) + φ₂ (g' * k) = φ₁ g' + φ₂ g'
  have e₁' := congrFun (hf₁ k hk'.1) g'
  have e₂' := congrFun (hf₂ k hk'.2) g'
  rw [e₁', e₂']

private theorem RightSmooth.smul {φ : G → ℂ} (h : RightSmooth p φ) (c : ℂ) : RightSmooth p (c • φ) := by
  obtain ⟨K, hK, hf⟩ := h
  refine ⟨K, hK, fun k hk => ?_⟩
  funext g'
  show c • φ (g' * k) = c • φ g'
  have e' := congrFun (hf k hk) g'
  rw [e']

private theorem RightSmooth.rightTranslate {φ : G → ℂ} (h : RightSmooth p φ) (c : G) :
    RightSmooth p (fun g => φ (g * c)) := by
  obtain ⟨K, hK, hf⟩ := h
  refine ⟨K.comap (MulAut.conj c⁻¹).toMonoidHom, ?_, fun k hk => ?_⟩
  · have hcont : Continuous (fun k : G => c⁻¹ * k * c⁻¹⁻¹) := by fun_prop
    have hset : ((K.comap (MulAut.conj c⁻¹).toMonoidHom : Subgroup G) : Set G)
        = (fun k : G => c⁻¹ * k * c⁻¹⁻¹) ⁻¹' (K : Set G) := by
      ext k
      simp
    rw [hset]
    exact hK.preimage hcont
  · have hmem : c⁻¹ * k * c ∈ K := by
      have := Subgroup.mem_comap.mp hk
      simpa [MulAut.conj_apply] using this
    funext g'
    show φ (g' * k * c) = φ (g' * c)
    have hfix := congrFun (hf _ hmem) (g' * c)
    have hg : g' * c * (c⁻¹ * k * c) = g' * k * c := by group
    rw [hg] at hfix
    exact hfix

private theorem smooth_of_mem_span {S : Submodule ℂ (G → ℂ)} (hsm : ∀ U ∈ S, RightSmooth p U) {V : G → ℂ}
    (hV : V ∈ Submodule.span ℂ (defectSet p S)) : RightSmooth p V := by
  refine Submodule.span_induction (p := fun V _ => RightSmooth p V) ?_ (smooth_zero p) ?_ ?_ hV
  · rintro V ⟨U, hU, x, rfl⟩
    exact RightSmooth.sub p (RightSmooth.rightTranslate p (hsm U hU) (unipotentGL2 x))
      (RightSmooth.smul p (hsm U hU) _)
  · intro V₁ V₂ _ _ h₁ h₂
    exact RightSmooth.add p h₁ h₂
  · intro c V _ h
    exact RightSmooth.smul p h c

private theorem exists_forall_mul_unipotent_eq_of_smooth {W : G → ℂ} (hW : RightSmooth p W) :
    ∃ δ : Γ, ∀ (g : G) (x y : F), Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) →
      W (g * unipotentGL2 x) = W (g * unipotentGL2 y) := by
  obtain ⟨K, hK, hf⟩ := hW
  obtain ⟨δ, hδ⟩ := exists_unipotent_mem_of_isOpen p K hK
  refine ⟨δ, fun g x y hxy => ?_⟩
  have hx : unipotentGL2 x = unipotentGL2 y * unipotentGL2 (x - y) := by
    rw [← unipotentGL2_add, add_sub_cancel]
  rw [hx, ← mul_assoc]
  exact congrFun (hf _ (hδ _ hxy)) (g * unipotentGL2 y)

private theorem windowSumsVanish_of_mem_span {S : Submodule ℂ (G → ℂ)} (hsm : ∀ U ∈ S, RightSmooth p U) {V : G → ℂ}
    (hV : V ∈ Submodule.span ℂ (defectSet p S)) (h : G) :
    WindowSumsVanish p (fun x => V (h * unipotentGL2 x)) := by
  refine Submodule.span_induction (p := fun V _ => WindowSumsVanish p (fun x => V (h * unipotentGL2 x)))
    ?_ ?_ ?_ ?_ hV
  ·
    rintro V ⟨U, hU, y, rfl⟩
    obtain ⟨β₀, hβ₀⟩ := exists_unit_gt p y
    obtain ⟨δU, hδU⟩ := exists_forall_mul_unipotent_eq_of_smooth p (hsm U hU)
    obtain ⟨γ₀, hγ₀⟩ := exists_psiV_eq_one p
    refine ⟨β₀, fun β hβ => ⟨min δU γ₀, fun δ hδ T hT => ?_⟩⟩
    have hyβ : Valued.v y < (β : WithZero (Multiplicative ℤ)) := hβ₀.trans_le (Units.val_le_val.mpr hβ)
    have hδ₁ : (δ : WithZero (Multiplicative ℤ)) ≤ δU := Units.val_le_val.mpr (hδ.trans (min_le_left _ _))
    have hδ₂ : (δ : WithZero (Multiplicative ℤ)) ≤ γ₀ := Units.val_le_val.mpr (hδ.trans (min_le_right _ _))
    set Φ : F → ℂ := fun s => NumberField.StandardAddChar.psiV p (-s) * U (h * unipotentGL2 s) with hΦ
    have hΦconst : ∀ s₁ s₂ : F, Valued.v (s₁ - s₂) < (δ : WithZero (Multiplicative ℤ)) → Φ s₁ = Φ s₂ := by
      intro s₁ s₂ hs
      simp only [hΦ]
      rw [hδU h s₁ s₂ (hs.trans_le hδ₁)]
      congr 1
      have h1 : NumberField.StandardAddChar.psiV p (s₂ - s₁) = 1 := by
        apply hγ₀
        rw [Valuation.map_sub_swap]
        exact hs.trans_le hδ₂
      calc NumberField.StandardAddChar.psiV p (-s₁)
          = NumberField.StandardAddChar.psiV p (-s₂ + (s₂ - s₁)) := by congr 1; ring
        _ = NumberField.StandardAddChar.psiV p (-s₂) := by rw [AddChar.map_add_eq_mul, h1, mul_one]
    have hshift : ∑ t ∈ T, Φ (t + y) = ∑ t ∈ T, Φ t := by
      rw [← Finset.sum_image (g := (· + y)) (fun x _ x' _ hxx' => add_right_cancel hxx')]
      exact sum_eq_sum_of_isRepSystem p (isRepSystem_image_add p hT hyβ) hT Φ hΦconst
    have hterm : ∀ t : F, NumberField.StandardAddChar.psiV p (-t) *
        (((fun g => U (g * unipotentGL2 y)) - NumberField.StandardAddChar.psiV p y • U) (h * unipotentGL2 t))
        = NumberField.StandardAddChar.psiV p y * (Φ (t + y) - Φ t) := by
      intro t
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hΦ, mul_assoc, unipotentGL2_add]
      have h2 : NumberField.StandardAddChar.psiV p (-t)
          = NumberField.StandardAddChar.psiV p y * NumberField.StandardAddChar.psiV p (-(t + y)) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      rw [h2]
      ring
    simp only [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, hshift, sub_self, mul_zero]
  · exact ⟨1, fun _ _ => ⟨1, fun _ _ _ _ => by simp⟩⟩
  ·
    intro V₁ V₂ _ _ h₁ h₂
    obtain ⟨β₁, hβ₁⟩ := h₁
    obtain ⟨β₂, hβ₂⟩ := h₂
    refine ⟨max β₁ β₂, fun β hβ => ?_⟩
    obtain ⟨δ₁, hδ₁⟩ := hβ₁ β ((le_max_left _ _).trans hβ)
    obtain ⟨δ₂, hδ₂⟩ := hβ₂ β ((le_max_right _ _).trans hβ)
    refine ⟨min δ₁ δ₂, fun δ hδ T hT => ?_⟩
    have e₁ := hδ₁ δ (hδ.trans (min_le_left _ _)) T hT
    have e₂ := hδ₂ δ (hδ.trans (min_le_right _ _)) T hT
    simp only at e₁ e₂
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, e₁, e₂, add_zero]
  ·
    intro c V _ hVs
    obtain ⟨β₀, hβ₀⟩ := hVs
    refine ⟨β₀, fun β hβ => ?_⟩
    obtain ⟨δ₀, hδ₀⟩ := hβ₀ β hβ
    refine ⟨δ₀, fun δ hδ T hT => ?_⟩
    have e := hδ₀ δ hδ T hT
    simp only at e
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, e, mul_zero]

end KirillovInjectivityAux
p2m_reactivate "P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_diagonal_mul_mem_span_sub.KirillovInjectivityAux"

open AutomorphicForm IsDedekindDomain KirillovInjectivityAux in

theorem solution
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hsm : ∀ U ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => U (g * k)) = U)
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hpsi : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hD : ∀ t : GL (Fin 2) (p.adicCompletion ℚ),
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1 →
      (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) :
    W = 0 := by
  have hsm' : ∀ U ∈ S, RightSmooth p U := hsm

  have hW1 : W ∈ Submodule.span ℂ (defectSet p S) := by
    have h := hD 1 (by simp) (by simp) (by simp)
    simpa [defectSet] using h
  have hWsm : RightSmooth p W := smooth_of_mem_span p hsm' hW1

  have hslice : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), ∀ x : p.adicCompletion ℚ,
      W (g * unipotentGL2 x) = W (g * unipotentGL2 0) := by
    intro g x
    obtain ⟨δW, hδW⟩ := exists_forall_mul_unipotent_eq_of_smooth p hWsm
    refine AutomorphicForm.LocalFunctionSpace.eq_of_forall_exists_forall_sum_char_mul_eq_zero p
      (fun x => W (g * unipotentGL2 x)) ⟨δW, fun x y hxy => hδW g x y hxy⟩
      (NumberField.StandardAddChar.psiV p) (fun x y => AddChar.map_add_eq_mul _ x y) (exists_psiV_eq_one p)
      ⟨_, NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p⟩ ?_ x 0
    intro a ha

    have hFa : (fun h => W (h * diagGL2 p a ha)) ∈ Submodule.span ℂ (defectSet p S) := by
      have h := hD (diagGL2 p a ha) (by simp) (by simp) (by simp)
      simpa [defectSet] using h

    have hφ : ∀ x : p.adicCompletion ℚ,
        W (g * (diagGL2 p a ha)⁻¹ * unipotentGL2 x * diagGL2 p a ha) = W (g * unipotentGL2 (a⁻¹ * x)) := by
      intro x
      rw [mul_assoc, mul_assoc, ← mul_assoc (diagGL2 p a ha)⁻¹, inv_diagGL2_mul_unipotent_mul_diagGL2]
    have hws := windowSumsVanish_of_mem_span p hsm' hFa (g * (diagGL2 p a ha)⁻¹)
    simp only [WindowSumsVanish, hφ] at hws
    obtain ⟨β₀', hβ₀'⟩ := hws
    set ua : (WithZero (Multiplicative ℤ))ˣ := Units.mk0 (Valued.v a) ((Valuation.ne_zero_iff _).mpr ha) with hua
    refine ⟨ua⁻¹ * β₀', fun β hβ => ?_⟩
    have hβ' : β₀' ≤ ua * β := inv_mul_le_iff_le_mul.mp hβ
    obtain ⟨δ₀', hδ₀'⟩ := hβ₀' (ua * β) hβ'
    refine ⟨ua⁻¹ * δ₀', fun T hT₁ hT₂ => ?_⟩
    have hrep : IsRepSystem p (ua * β) δ₀' (T.image (a * ·)) := by
      have h := isRepSystem_image_mul p (β := β) (δ := ua⁻¹ * δ₀') (T := T) ⟨hT₁, hT₂⟩ ha
      simp only [← hua, mul_inv_cancel_left] at h
      exact h
    have hsum0 := hδ₀' δ₀' le_rfl _ hrep
    rw [Finset.sum_image (fun x _ y _ hxy => mul_left_cancel₀ ha hxy)] at hsum0
    simpa [inv_mul_cancel_left₀ ha] using hsum0

  have hfix : ∀ x : p.adicCompletion ℚ, (fun g => W (g * unipotentGL2 x)) = W := by
    intro x
    funext g
    rw [hslice g x]
    simp
  exact AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_mul_unipotent_eq p W hpsi hWsm hfix

end S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_diagonal_mul_mem_span_sub
end P2MW
export P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_diagonal_mul_mem_span_sub (solution)
