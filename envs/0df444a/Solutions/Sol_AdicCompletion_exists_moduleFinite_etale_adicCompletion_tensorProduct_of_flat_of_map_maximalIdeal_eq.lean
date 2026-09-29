-- Prove2me | solution 1 for AdicCompletion.exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bb10de7e-1908-539c-ab3d-44f95050964e

import Mathlib
import Theorems.Thm_IsLocalRing_existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
import Theorems.Thm_IsLocalRing_exists_isLocalRing_etale_free_residueField_algEquiv
import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

open IsLocalRing TensorProduct

namespace CAURed

section Generic

variable {B : Type} [CommRing B] (x : Ideal B)

theorem factor_evalₐ {m n : ℕ} (hle : m ≤ n) (s : AdicCompletion x B) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) (AdicCompletion.evalₐ x n s) =
      AdicCompletion.evalₐ x m s := by
  obtain ⟨bn, hbn⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ x n s)
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective x B s
  simp only [AdicCompletion.evalₐ_mk] at hbn ⊢
  rw [Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have := a.prop hle

  rw [SModEq, Submodule.Quotient.eq] at this
  have : (a : ℕ → B) m - (a : ℕ → B) n ∈ x ^ m := by
    simpa [smul_eq_mul, Ideal.mul_top] using this

  have := Submodule.neg_mem _ this
  rwa [neg_sub] at this

theorem exists_sub_mem_pow [IsNoetherianRing B] (s : AdicCompletion x B) (n : ℕ) :
    ∃ b : B, s - algebraMap B (AdicCompletion x B) b ∈ (x.map (algebraMap B (AdicCompletion x B))) ^ n := by
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (x ^ n • ⊤ : Submodule B B) (AdicCompletion.eval x B n s)
  refine ⟨b, ?_⟩
  have hker : s - algebraMap B (AdicCompletion x B) b ∈ LinearMap.ker (AdicCompletion.eval x B n) := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AdicCompletion.eval_of, hb, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian x)] at hker
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map]
  exact hker

end Generic

section Lift

variable {B : Type} [CommRing B] (x : Ideal B)
variable {T : Type} [CommRing T] (J : Ideal T) [IsAdicComplete J T]

theorem exists_lift_ringHom (f : B →+* T) (hf : x.map f ≤ J) :
    ∃ F : AdicCompletion x B →+* T, F.comp (algebraMap B (AdicCompletion x B)) = f ∧
      ∀ n : ℕ, ((x.map (algebraMap B (AdicCompletion x B))) ^ n).map F ≤ J ^ n := by
  have hle : ∀ n : ℕ, x ^ n ≤ (J ^ n).comap f := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono hf n
  let g : ∀ n : ℕ, AdicCompletion x B →+* T ⧸ J ^ n := fun n =>
    (Ideal.quotientMap (J ^ n) f (hle n)).comp (AdicCompletion.evalₐ x n).toRingHom
  have hg : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (g n) = g m := by
    intro m n h
    ext s
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ x n s)
    have hbm : AdicCompletion.evalₐ x m s = Ideal.Quotient.mk (x ^ m) b := by
      rw [← factor_evalₐ x h s, ← hb, Ideal.Quotient.factor_mk]
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ← hb, hbm,
      Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]
  have hg' : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp ((g n).comp
      (algebraMap B (AdicCompletion x B))) = (g m).comp (algebraMap B (AdicCompletion x B)) := by
    intro m n h; rw [← RingHom.comp_assoc, hg h]
  refine ⟨IsAdicComplete.liftRingHom J g hg, ?_, ?_⟩
  · have e1 : (IsAdicComplete.liftRingHom J g hg).comp (algebraMap B (AdicCompletion x B)) =
        IsAdicComplete.liftRingHom J _ hg' :=
      IsAdicComplete.eq_liftRingHom J _ hg' _ (fun n => by
        rw [← RingHom.comp_assoc, IsAdicComplete.mk_comp_liftRingHom])
    have e2 : f = IsAdicComplete.liftRingHom J _ hg' :=
      IsAdicComplete.eq_liftRingHom J _ hg' _ (fun n => by
        ext b
        simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalₐ_of,
          Ideal.quotientMap_mk])
    rw [e1, ← e2]
  · intro n
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, IsAdicComplete.mk_liftRingHom]
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    have : AdicCompletion.evalₐ x n s = 0 := by
      rw [← Ideal.map_pow] at hs
      have h1 := Ideal.mem_map_of_mem (AdicCompletion.evalₐ x n).toRingHom hs
      rw [Ideal.map_map] at h1
      have h2 : ((AdicCompletion.evalₐ x n).toRingHom.comp (algebraMap B (AdicCompletion x B))) =
          Ideal.Quotient.mk (x ^ n) := by
        ext b
        simp
      rw [h2, Ideal.map_quotient_self] at h1
      simpa using h1
    rw [this, map_zero]

end Lift

section LiftExt

variable {B : Type} [CommRing B] [IsNoetherianRing B] (x : Ideal B)
variable {T : Type} [CommRing T] (J : Ideal T) [IsHausdorff J T]

theorem ringHom_ext_of_le (F₁ F₂ : AdicCompletion x B →+* T)
    (h : F₁.comp (algebraMap B (AdicCompletion x B)) = F₂.comp (algebraMap B (AdicCompletion x B)))
    (h₁ : ∀ n : ℕ, ((x.map (algebraMap B (AdicCompletion x B))) ^ n).map F₁ ≤ J ^ n)
    (h₂ : ∀ n : ℕ, ((x.map (algebraMap B (AdicCompletion x B))) ^ n).map F₂ ≤ J ^ n) : F₁ = F₂ := by
  ext s
  refine IsHausdorff.eq_iff_smodEq (I := J) |>.mpr fun n => ?_
  obtain ⟨b, hb⟩ := exists_sub_mem_pow x s n
  have e1 : F₁ (algebraMap B _ b) = F₂ (algebraMap B _ b) := by
    simpa using congrArg (fun φ : B →+* T => φ b) h
  have : F₁ s - F₂ s = F₁ (s - algebraMap B _ b) - F₂ (s - algebraMap B _ b) := by
    simp [map_sub, e1]
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, this]
  exact Submodule.sub_mem _ (Ideal.map_le_iff_le_comap.mp (h₁ n) hb) (Ideal.map_le_iff_le_comap.mp (h₂ n) hb)

end LiftExt

section Residue

theorem residueField_finite_and_isSeparable
    (V : Type) [CommRing V] [IsLocalRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)]
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [Algebra V R₀] [IsLocalHom (algebraMap V R₀)]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra R₀ S] [Algebra V S] [IsScalarTower V R₀ S]
    [IsLocalHom (algebraMap R₀ S)]
    (jD : D →ₐ[V] S) [IsLocalHom jD.toRingHom]
    (hdense : ∀ s : S, ∃ t ∈ Algebra.adjoin R₀ (Set.range jD), s - t ∈ maximalIdeal S) :
    Module.Finite (ResidueField R₀) (ResidueField S) ∧
      Algebra.IsSeparable (ResidueField R₀) (ResidueField S) := by
  haveI : IsLocalHom (algebraMap V S) := by
    rw [IsScalarTower.algebraMap_eq V R₀ S]; exact RingHom.isLocalHom_comp _ _
  haveI : IsScalarTower (ResidueField V) (ResidueField R₀) (ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      obtain ⟨v, rfl⟩ := residue_surjective r
      change residue S (algebraMap V S v) = residue S (algebraMap R₀ S (algebraMap V R₀ v))
      rw [IsScalarTower.algebraMap_apply V R₀ S])

  let bD : ResidueField D →ₐ[ResidueField V] ResidueField S :=
    { toRingHom := ResidueField.map jD.toRingHom
      commutes' := fun r => by
        obtain ⟨v, rfl⟩ := residue_surjective r
        change ResidueField.map jD.toRingHom (residue D (algebraMap V D v)) = residue S (algebraMap V S v)
        rw [ResidueField.map_residue]
        simp }
  let θ : ResidueField R₀ ⊗[ResidueField V] ResidueField D →ₐ[ResidueField R₀] ResidueField S :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R₀) (ResidueField S)) bD (fun _ _ => Commute.all _ _)

  have hθ : Function.Surjective θ := by
    intro s
    obtain ⟨s, rfl⟩ := residue_surjective s
    obtain ⟨t, ht, hst⟩ := hdense s
    have hs : residue S s = residue S t := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hst
    rw [hs]

    suffices h : Algebra.adjoin R₀ (Set.range jD) ≤
        (θ.range.restrictScalars R₀ |>.comap (IsScalarTower.toAlgHom R₀ S (ResidueField S))) by
      obtain ⟨y, hy⟩ := (h ht); exact ⟨y, hy⟩
    refine Algebra.adjoin_le ?_
    rintro _ ⟨d, rfl⟩
    refine ⟨(1 : ResidueField R₀) ⊗ₜ residue D d, ?_⟩
    change θ (1 ⊗ₜ residue D d) = residue S (jD d)
    simp [θ, bD, Algebra.TensorProduct.lift_tmul, ResidueField.map_residue]
  refine ⟨Module.Finite.of_surjective θ.toLinearMap hθ, ?_⟩
  haveI : Algebra.FormallyUnramified (ResidueField V) (ResidueField D) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  haveI : Algebra.FormallyUnramified (ResidueField R₀) (ResidueField R₀ ⊗[ResidueField V] ResidueField D) :=
    inferInstance
  haveI : Algebra.FormallyUnramified (ResidueField R₀) (ResidueField S) :=
    Algebra.FormallyUnramified.of_surjective θ hθ
  haveI : Module.Finite (ResidueField R₀) (ResidueField S) := Module.Finite.of_surjective θ.toLinearMap hθ
  haveI : Algebra.EssFiniteType (ResidueField R₀) (ResidueField S) := inferInstance
  exact Algebra.FormallyUnramified.isSeparable _ _

end Residue

section Core

theorem core
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [IsAdicComplete (maximalIdeal R₀) R₀]
    [Algebra V R₀] [IsLocalHom (algebraMap V R₀)]
    (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [Algebra R₀ S] [Algebra V S] [IsScalarTower V R₀ S] [IsLocalHom (algebraMap R₀ S)]
    (jD : D →ₐ[V] S) [IsLocalHom jD.toRingHom]
    (hdense : ∀ (s : S) (n : ℕ), ∃ t ∈ Algebra.adjoin R₀ (Set.range jD), s - t ∈ maximalIdeal S ^ n)
    (hUP : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
      [Algebra R₀ T] [Algebra V T] [IsScalarTower V R₀ T] [IsLocalHom (algebraMap R₀ T)]
      (τ : ResidueField S →+* ResidueField T)
      (_hτ : ∀ r : R₀, τ (residue S (algebraMap R₀ S r)) = residue T (algebraMap R₀ T r))
      (gD : D →ₐ[V] T) (_hgD : ∀ d : D, residue T (gD d) = τ (residue S (jD d))),
      ∃ Φ : S →ₐ[R₀] T, (∀ d : D, Φ (jD d) = gD d) ∧ ∀ s : S, residue T (Φ s) = τ (residue S s)) :
    Module.Finite R₀ S ∧ Algebra.Etale R₀ S ∧
      (maximalIdeal R₀).map (algebraMap R₀ S) = maximalIdeal S := by
  classical

  obtain ⟨instFin, instSep⟩ := residueField_finite_and_isSeparable V D R₀ S jD
    (fun s => by obtain ⟨t, ht, h⟩ := hdense s 1; exact ⟨t, ht, by simpa using h⟩)

  obtain ⟨E, _instE, _instEloc, _instEalg, _instEhom, hEfin, hEfree, hEet, h𝔪E, ⟨eE⟩⟩ :=
    IsLocalRing.exists_isLocalRing_etale_free_residueField_algEquiv R₀ (ResidueField S)
  haveI := hEfin; haveI := hEfree; haveI := hEet
  haveI : IsAdicComplete (maximalIdeal E) E := IsLocalRing.isAdicComplete_of_module_finite (𝒪 := R₀) (T := E)
  letI : Algebra V E := ((algebraMap R₀ E).comp (algebraMap V R₀)).toAlgebra
  haveI : IsScalarTower V R₀ E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable (ResidueField R₀) (ResidueField E) :=
    Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField R₀)) eE.symm.toRingEquiv (by
      ext r; simp)

  obtain ⟨ψ, hψ, -⟩ :=
    IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
      R₀ E h𝔪E S (eE : ResidueField E →+* ResidueField S) (fun r => by
        change eE (residue E (algebraMap R₀ E r)) = residue S (algebraMap R₀ S r)
        have : residue E (algebraMap R₀ E r) = algebraMap (ResidueField R₀) (ResidueField E) (residue R₀ r) := rfl
        rw [this, AlgEquiv.commutes]; rfl)

  let ιD : ResidueField D →+* ResidueField E :=
    (eE.symm : ResidueField S →+* ResidueField E).comp (ResidueField.map jD.toRingHom)
  have hcompS : ∀ r : R₀, residue S (algebraMap R₀ S r) =
      algebraMap (ResidueField R₀) (ResidueField S) (residue R₀ r) := fun _ => rfl
  have hcompE : ∀ r : R₀, residue E (algebraMap R₀ E r) =
      algebraMap (ResidueField R₀) (ResidueField E) (residue R₀ r) := fun _ => rfl
  have hτ : ∀ r : R₀, (eE.symm : ResidueField S →+* ResidueField E) (residue S (algebraMap R₀ S r)) =
      residue E (algebraMap R₀ E r) := by
    intro r
    change eE.symm (residue S (algebraMap R₀ S r)) = residue E (algebraMap R₀ E r)
    rw [hcompS, hcompE, AlgEquiv.commutes]
  have hιD : ∀ v : V, ιD (residue D (algebraMap V D v)) = residue E (algebraMap V E v) := by
    intro v
    change eE.symm (ResidueField.map jD.toRingHom (residue D (algebraMap V D v))) =
      residue E (algebraMap R₀ E (algebraMap V R₀ v))
    rw [ResidueField.map_residue]
    have h1 : jD.toRingHom (algebraMap V D v) = algebraMap R₀ S (algebraMap V R₀ v) := by
      simp [IsScalarTower.algebraMap_apply V R₀ S]
    rw [h1, hcompS, hcompE, AlgEquiv.commutes]
  obtain ⟨g, hg, -⟩ :=
    IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
      V D hVD E ιD hιD

  obtain ⟨φ, hφD, hφres⟩ := hUP E (eE.symm : ResidueField S →+* ResidueField E) hτ g (fun d => by
      rw [hg]; simp [ιD, ResidueField.map_residue])

  have hφψ : φ.comp ψ = AlgHom.id R₀ E := by
    have hu := IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
      R₀ E h𝔪E E (RingHom.id (ResidueField E)) (fun r => rfl)
    refine hu.unique ?_ ?_
    · intro e
      rw [AlgHom.comp_apply, hφres, hψ]
      simp
    · intro e; rfl

  have hψloc : ∀ e ∈ maximalIdeal E, ψ e ∈ maximalIdeal S := by
    intro e he
    rw [← residue_eq_zero_iff, hψ, (residue_eq_zero_iff _).mpr he, map_zero]
  have hφloc : ∀ s ∈ maximalIdeal S, φ s ∈ maximalIdeal E := by
    intro s hs
    rw [← residue_eq_zero_iff, hφres, (residue_eq_zero_iff _).mpr hs, map_zero]
  have hψφD : ∀ d : D, ψ (φ (jD d)) = jD d := by
    let ιS : ResidueField D →+* ResidueField S := ResidueField.map jD.toRingHom
    have hu := IsLocalRing.existsUnique_algHom_residue_eq_of_flat_of_map_maximalIdeal_eq_of_isSeparable_of_isAdicComplete
      V D hVD S ιS (fun v => by
        change ResidueField.map jD.toRingHom (residue D (algebraMap V D v)) = residue S (algebraMap V S v)
        rw [ResidueField.map_residue]; simp)
    have key := hu.unique (y₁ := ((ψ.comp φ).restrictScalars V).comp jD) (y₂ := jD) ?_ ?_
    · intro d; exact congrArg (fun h : D →ₐ[V] S => h d) key
    · intro d
      change residue S (ψ (φ (jD d))) = ResidueField.map jD.toRingHom (residue D d)
      rw [hψ, hφD, hg]
      simp [ιD, ResidueField.map_residue]
    · intro d
      change residue S (jD d) = ResidueField.map jD.toRingHom (residue D d)
      rw [ResidueField.map_residue]; rfl
  have hψφ : ψ.comp φ = AlgHom.id R₀ S := by

    have hadj : Algebra.adjoin R₀ (Set.range jD) ≤ AlgHom.equalizer (ψ.comp φ) (AlgHom.id R₀ S) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨d, rfl⟩
      simpa [AlgHom.mem_equalizer] using hψφD d
    ext s
    refine IsHausdorff.eq_iff_smodEq (I := maximalIdeal S) |>.mpr fun n => ?_
    obtain ⟨t, ht, hst⟩ := hdense s n
    have e1 : ψ (φ t) = t := by simpa [AlgHom.mem_equalizer] using hadj ht
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have : (ψ.comp φ) s - (AlgHom.id R₀ S) s = ψ (φ (s - t)) - (s - t) := by
      simp [map_sub, e1]
    rw [this]
    refine Submodule.sub_mem _ ?_ hst

    have hθ : (maximalIdeal S).map ((ψ : E →+* S).comp (φ : S →+* E)) ≤ maximalIdeal S := by
      rw [Ideal.map_le_iff_le_comap]
      intro u hu; exact hψloc _ (hφloc _ hu)
    have hθn : (maximalIdeal S ^ n).map ((ψ : E →+* S).comp (φ : S →+* E)) ≤ maximalIdeal S ^ n := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono hθ n
    have := Ideal.map_le_iff_le_comap.mp hθn hst
    simpa using this

  let e : E ≃ₐ[R₀] S := AlgEquiv.ofAlgHom ψ φ hψφ hφψ
  refine ⟨Module.Finite.equiv e.toLinearEquiv, Algebra.Etale.of_equiv e, ?_⟩
  apply le_antisymm
  · exact ((IsLocalRing.local_hom_TFAE (algebraMap R₀ S)).out 0 2).mp ‹_›
  · intro s hs
    have h1 : φ s ∈ (maximalIdeal R₀).map (algebraMap R₀ E) := by rw [h𝔪E]; exact hφloc s hs
    have h2 : ψ (φ s) = s := by simpa using congrArg (fun h : S →ₐ[R₀] S => h s) hψφ
    rw [← h2]
    have : ((maximalIdeal R₀).map (algebraMap R₀ E)).map (ψ : E →+* S) =
        (maximalIdeal R₀).map (algebraMap R₀ S) := by
      rw [Ideal.map_map]; congr 1; ext r; simp
    rw [← this]
    exact Ideal.mem_map_of_mem _ h1

end Core

end CAURed

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open CAURed in
theorem solution
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (C : Type) [CommRing C] [Algebra V C] [IsNoetherianRing C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] (h𝔫 : (maximalIdeal V).map (algebraMap V C) ≤ 𝔫)
    [IsNoetherianRing (C ⊗[V] D)]
    (x : Ideal (C ⊗[V] D)) [x.IsMaximal]
    (hx : 𝔫.map (algebraMap C (C ⊗[V] D)) ≤ x) :
    ∃ (_ : IsLocalRing (AdicCompletion 𝔫 C)) (_ : IsLocalRing (AdicCompletion x (C ⊗[V] D)))
      (_ : Algebra (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)))
      (_ : IsScalarTower C (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)))
      (_ : IsLocalHom (algebraMap (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)))),
      Module.Finite (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)) ∧
      Algebra.Etale (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)) ∧
      (maximalIdeal (AdicCompletion 𝔫 C)).map (algebraMap (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D))) =
        maximalIdeal (AdicCompletion x (C ⊗[V] D)) := by
  classical

  obtain ⟨instR₀loc, instR₀noeth, instR₀cpl, h𝔪R₀, -, -, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing C 𝔫
  obtain ⟨instSloc, instSnoeth, instScpl, h𝔪S, -, hresSker, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing (C ⊗[V] D) x

  let B := C ⊗[V] D
  let R₀ := AdicCompletion 𝔫 C
  let S := AdicCompletion x (C ⊗[V] D)
  have hCS : ∀ c : C, algebraMap C S c = algebraMap B S (algebraMap C B c) := fun c => by
    simp [S, B, AdicCompletion.algebraMap_apply]

  haveI : IsAdicComplete (x.map (algebraMap B S)) S := h𝔪S ▸ instScpl
  obtain ⟨F, hF, hFcont⟩ := exists_lift_ringHom 𝔫 (x.map (algebraMap B S)) (algebraMap C S) (by
    rw [IsScalarTower.algebraMap_eq C B S, ← Ideal.map_map]; exact Ideal.map_mono hx)
  letI algR₀S : Algebra R₀ S := F.toAlgebra
  have hFC : ∀ c : C, algebraMap R₀ S (algebraMap C R₀ c) = algebraMap C S c := fun c => by
    change F (algebraMap C R₀ c) = algebraMap C S c
    exact congrArg (fun φ : C →+* S => φ c) hF
  haveI : IsScalarTower C R₀ S := IsScalarTower.of_algebraMap_eq (fun c => (hFC c).symm)
  haveI : IsScalarTower V R₀ S := IsScalarTower.of_algebraMap_eq (fun v => by
    rw [IsScalarTower.algebraMap_apply V C R₀, hFC, IsScalarTower.algebraMap_apply V C S])
  have h𝔪R₀S : (maximalIdeal R₀).map (algebraMap R₀ S) ≤ maximalIdeal S := by
    rw [h𝔪R₀, Ideal.map_map, h𝔪S]
    have : (algebraMap R₀ S).comp (algebraMap C R₀) = (algebraMap B S).comp (algebraMap C B) := by
      ext c; rw [RingHom.comp_apply, hFC, hCS]; rfl
    rw [this, ← Ideal.map_map]; exact Ideal.map_mono hx
  haveI : IsLocalHom (algebraMap R₀ S) := ((IsLocalRing.local_hom_TFAE (algebraMap R₀ S)).out 0 2).mpr h𝔪R₀S
  haveI : IsLocalHom (algebraMap V R₀) := ((IsLocalRing.local_hom_TFAE (algebraMap V R₀)).out 0 2).mpr (by
    rw [h𝔪R₀, IsScalarTower.algebraMap_eq V C R₀, ← Ideal.map_map]; exact Ideal.map_mono h𝔫)
  haveI : IsLocalHom (algebraMap V S) := by
    rw [IsScalarTower.algebraMap_eq V R₀ S]; exact RingHom.isLocalHom_comp _ _

  let jD : D →ₐ[V] S := (IsScalarTower.toAlgHom V B S).comp Algebra.TensorProduct.includeRight
  have hjD : ∀ d : D, jD d = algebraMap B S ((1 : C) ⊗ₜ d) := fun d => rfl
  haveI : IsLocalHom jD.toRingHom := ((IsLocalRing.local_hom_TFAE jD.toRingHom).out 0 2).mpr (by
    rw [← hVD, Ideal.map_map]
    have : jD.toRingHom.comp (algebraMap V D) = algebraMap V S := by ext v; simp
    rw [this]
    exact ((IsLocalRing.local_hom_TFAE (algebraMap V S)).out 0 2).mp ‹IsLocalHom (algebraMap V S)›)
  have hBgen : ∀ b : B, algebraMap B S b ∈ Algebra.adjoin R₀ (Set.range jD) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      have : (c ⊗ₜ[V] d : B) = algebraMap C B c * ((1 : C) ⊗ₜ d) := by
        change (c ⊗ₜ[V] d : C ⊗[V] D) = algebraMap C (C ⊗[V] D) c * ((1 : C) ⊗ₜ[V] d)
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, map_mul, ← hCS, ← hFC, ← hjD]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin ⟨d, rfl⟩)
    | add b₁ b₂ h₁ h₂ => rw [map_add]; exact Subalgebra.add_mem _ h₁ h₂
  have hdense : ∀ (s : S) (n : ℕ), ∃ t ∈ Algebra.adjoin R₀ (Set.range jD), s - t ∈ maximalIdeal S ^ n := by
    intro s n
    obtain ⟨b, hb⟩ := exists_sub_mem_pow x s n
    exact ⟨algebraMap B S b, hBgen b, by rw [h𝔪S]; exact hb⟩

  have hUP : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
      [Algebra R₀ T] [Algebra V T] [IsScalarTower V R₀ T] [IsLocalHom (algebraMap R₀ T)]
      (τ : ResidueField S →+* ResidueField T)
      (_hτ : ∀ r : R₀, τ (residue S (algebraMap R₀ S r)) = residue T (algebraMap R₀ T r))
      (gD : D →ₐ[V] T) (_hgD : ∀ d : D, residue T (gD d) = τ (residue S (jD d))),
      ∃ Φ : S →ₐ[R₀] T, (∀ d : D, Φ (jD d) = gD d) ∧ ∀ s : S, residue T (Φ s) = τ (residue S s) := by
    intro T _ _ _ _ _ _ _ τ hτ gD hgD
    have htmul : ∀ (c : C) (d : D), (c ⊗ₜ[V] d : B) = algebraMap C B c * ((1 : C) ⊗ₜ d) := fun c d => by
      change (c ⊗ₜ[V] d : C ⊗[V] D) = algebraMap C (C ⊗[V] D) c * ((1 : C) ⊗ₜ[V] d)
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

    let f₁ : C →ₐ[V] T := (IsScalarTower.toAlgHom V R₀ T).comp (IsScalarTower.toAlgHom V C R₀)
    let f₀ : B →ₐ[V] T := Algebra.TensorProduct.lift f₁ gD (fun _ _ => Commute.all _ _)
    have hf₀C : ∀ c : C, f₀ (algebraMap C B c) = algebraMap R₀ T (algebraMap C R₀ c) := by
      intro c
      change f₀ (c ⊗ₜ[V] (1 : D)) = algebraMap R₀ T (algebraMap C R₀ c)
      simp only [f₀]
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    have hf₀D : ∀ d : D, f₀ ((1 : C) ⊗ₜ d) = gD d := by
      intro d
      simp only [f₀]
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    have hresf₀ : ∀ b : B, residue T (f₀ b) = τ (residue S (algebraMap B S b)) := by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        rw [htmul, map_mul, map_mul, hf₀C, hf₀D, ← hτ, hgD, hjD, hFC, hCS, map_mul, map_mul, map_mul]
      | add b₁ b₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, map_add, h₁, h₂]
    have hf : x.map f₀.toRingHom ≤ maximalIdeal T := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, ← residue_eq_zero_iff]
      change residue T (f₀ b) = 0
      have : residue S (algebraMap B S b) = 0 := by
        rw [← hresSker] at hb; exact hb
      rw [hresf₀, this, map_zero]
    obtain ⟨F', hF', hF'cont⟩ := exists_lift_ringHom x (maximalIdeal T) f₀.toRingHom hf
    have hF'b : ∀ b : B, F' (algebraMap B S b) = f₀ b := fun b =>
      congrArg (fun φ : B →+* T => φ b) hF'

    have hlin : F'.comp (algebraMap R₀ S) = algebraMap R₀ T := by
      refine ringHom_ext_of_le 𝔫 (maximalIdeal T) _ _ ?_ ?_ ?_
      · ext c
        rw [RingHom.comp_apply, RingHom.comp_apply, hFC, hCS, hF'b, RingHom.comp_apply]
        exact hf₀C c
      · intro n
        have h1 : (𝔫.map (algebraMap C R₀)).map (algebraMap R₀ S) ≤ x.map (algebraMap B S) := by
          rw [Ideal.map_map]
          have : (algebraMap R₀ S).comp (algebraMap C R₀) = (algebraMap B S).comp (algebraMap C B) := by
            ext c; rw [RingHom.comp_apply, hFC, hCS]; rfl
          rw [this, ← Ideal.map_map]; exact Ideal.map_mono hx
        calc ((𝔫.map (algebraMap C R₀)) ^ n).map (F'.comp (algebraMap R₀ S))
            = (((𝔫.map (algebraMap C R₀)).map (algebraMap R₀ S)) ^ n).map F' := by
              rw [← Ideal.map_map, Ideal.map_pow]
          _ ≤ ((x.map (algebraMap B S)) ^ n).map F' := Ideal.map_mono (Ideal.pow_right_mono h1 n)
          _ ≤ maximalIdeal T ^ n := hF'cont n
      · intro n
        rw [← h𝔪R₀, Ideal.map_pow]
        exact Ideal.pow_right_mono (((IsLocalRing.local_hom_TFAE (algebraMap R₀ T)).out 0 2).mp ‹_›) n
    let Φ : S →ₐ[R₀] T :=
      { toRingHom := F'
        commutes' := fun r => congrArg (fun φ : R₀ →+* T => φ r) hlin }
    refine ⟨Φ, fun d => ?_, fun s => ?_⟩
    · change F' (jD d) = gD d
      rw [hjD, hF'b, hf₀D]
    · change residue T (F' s) = τ (residue S s)
      obtain ⟨b, hb⟩ := exists_sub_mem_pow x s 1
      have h1 : F' (s - algebraMap B S b) ∈ maximalIdeal T := by
        have := hF'cont 1
        rw [pow_one, pow_one] at this
        rw [pow_one] at hb
        exact Ideal.map_le_iff_le_comap.mp this hb
      have h2 : s - algebraMap B S b ∈ maximalIdeal S := by rw [h𝔪S]; simpa using hb
      have e1 : residue T (F' s) = residue T (F' (algebraMap B S b)) := by
        rw [← sub_eq_zero, ← map_sub, ← map_sub, residue_eq_zero_iff]; exact h1
      have e2 : residue S s = residue S (algebraMap B S b) := by
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h2
      rw [e1, e2, hF'b, hresf₀]
  obtain ⟨hfin, het, h𝔪⟩ := core V D hVD R₀ S jD hdense hUP
  exact ⟨instR₀loc, instSloc, algR₀S, inferInstance, inferInstance, hfin, het, h𝔪⟩

end S_AdicCompletion_exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
end P2MW
export P2MW.S_AdicCompletion_exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq (solution)
