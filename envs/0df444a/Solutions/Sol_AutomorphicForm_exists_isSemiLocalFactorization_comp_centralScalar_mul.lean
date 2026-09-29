-- Prove2me | solution 1 for AutomorphicForm.exists_isSemiLocalFactorization_comp_centralScalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/87a41951-c6ac-5a73-84b2-2efa27c27305

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

namespace TranslateSL

open AutomorphicForm

theorem archEntries_mul (F : Type) [Field F] (a h : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2) :
    archEntries F (a * h) i j = ∑ k : Fin 2, archEntries F a i k * archEntries F h k j := by
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

theorem isArchTestFactor_comp_mul_left (F : Type) [Field F] [NumberField F]
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (a : GL (Fin 2) (InfiniteAdeleRing F)) : IsArchTestFactor F (fun h => fa (a * h)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun X => Φ (fun i j => ∑ k : Fin 2, archEntries F a i k * X k j), ?_, ?_⟩, ?_⟩
  · exact hΦ.comp (by fun_prop)
  · intro h
    show fa (a * h) = Φ (fun i j => ∑ k : Fin 2, archEntries F a i k * archEntries F h k j)
    rw [hfaΦ]
    congr 1
    funext i j
    exact archEntries_mul F a h i j
  · exact hsupp.comp_homeomorph (Homeomorph.mulLeft a)

theorem isFinTestFactor_comp_mul_left (F : Type) [Field F] [NumberField F]
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hff : IsFinTestFactor F ff)
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : IsFinTestFactor F (fun h => ff (b * h)) :=
  ⟨hff.1.comp_continuous (continuous_const_mul b), hff.2.comp_homeomorph (Homeomorph.mulLeft b)⟩

open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isSemiLocalTestFn_comp_mul_left (v : HeightOneSpectrum (𝓞 K))
    {φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ} (h : IsSemiLocalTestFn K L v φv)
    (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : IsSemiLocalTestFn K L v (fun x => φv (b * x)) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  exact ⟨h.1.comp_continuous (continuous_const_mul b), h.2.comp_homeomorph (Homeomorph.mulLeft b)⟩

theorem isSemiLocalTestFn_indicator (v : HeightOneSpectrum (𝓞 K)) :
    IsSemiLocalTestFn K L v ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  have hopen := isOpen_semiLocalIntegralSet K L v
  have hcpt := isCompact_semiLocalIntegralSet K L v
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ semiLocalIntegralSet K L v
    · exact ⟨semiLocalIntegralSet K L v, hopen, hx, fun x' hx' => by
        rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]⟩
    · exact ⟨(semiLocalIntegralSet K L v)ᶜ, hcpt.isClosed.isOpen_compl, hx, fun x' hx' => by
        rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro hcpt fun x hx => Set.indicator_of_notMem hx _

theorem add_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K)) {a b : L ⊗[K] v.adicCompletion K}
    (ha : a ∈ semiLocalIntegers K L v) (hb : b ∈ semiLocalIntegers K L v) : a + b ∈ semiLocalIntegers K L v := by
  obtain ⟨a', rfl⟩ := ha; obtain ⟨b', rfl⟩ := hb; exact ⟨a' + b', map_add _ _ _⟩

theorem mul_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K)) {a b : L ⊗[K] v.adicCompletion K}
    (ha : a ∈ semiLocalIntegers K L v) (hb : b ∈ semiLocalIntegers K L v) : a * b ∈ semiLocalIntegers K L v := by
  obtain ⟨a', rfl⟩ := ha; obtain ⟨b', rfl⟩ := hb; exact ⟨a' * b', map_mul _ _ _⟩

theorem mul_mem_integralMatrixSet (v : HeightOneSpectrum (𝓞 K)) {M N : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hM : M ∈ integralMatrixSet (semiLocalIntegers K L v)) (hN : N ∈ integralMatrixSet (semiLocalIntegers K L v)) :
    M * N ∈ integralMatrixSet (semiLocalIntegers K L v) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_semiLocalIntegers K L v (mul_mem_semiLocalIntegers K L v (hM i 0) (hN 0 j))
    (mul_mem_semiLocalIntegers K L v (hM i 1) (hN 1 j))

theorem mul_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) (hh : h ∈ semiLocalIntegralSet K L v) :
    g * h ∈ semiLocalIntegralSet K L v := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact mul_mem_integralMatrixSet K L v hg.1 hh.1
  · rw [mul_inv_rev, Units.val_mul]; exact mul_mem_integralMatrixSet K L v hh.2 hg.2

theorem inv_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) : g⁻¹ ∈ semiLocalIntegralSet K L v :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem mul_mem_semiLocalIntegralSet_iff (v : HeightOneSpectrum (𝓞 K)) {s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hs : s ∈ semiLocalIntegralSet K L v) (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    s * x ∈ semiLocalIntegralSet K L v ↔ x ∈ semiLocalIntegralSet K L v := by
  constructor
  · intro h
    have := mul_mem_semiLocalIntegralSet K L v (inv_mem_semiLocalIntegralSet K L v hs) h
    rwa [inv_mul_cancel_left] at this
  · exact mul_mem_semiLocalIntegralSet K L v hs

theorem map_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar, RingHom.toMonoidHom_eq_coe,
    Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

end TranslateSL

open scoped TensorProduct TensorProduct.RightActions in
open TranslateSL AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      AutomorphicForm.IsSemiLocalFactorization K L S₁
        (fun g => φ (AutomorphicForm.centralScalar (𝓞 L) L z * g))
        (fun y => φa (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleArch (𝓞 L) L).toMonoidHom z) * y))
        (fun h => φf (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z) * h))
        (fun v x => (if v ∈ S then φS v
            else (AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
          (Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.map (AutomorphicForm.semiLocalEval K L v).toMonoidHom
              (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z)) * x)) := by
  classical
  obtain ⟨hφa, hφf, hφS, hprod, hzero, hsplit⟩ := hφ

  set sa : GL (Fin 2) (InfiniteAdeleRing L) :=
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (AdelicLevel.adeleArch (𝓞 L) L).toMonoidHom z) with hsa
  set sf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z) with hsf
  set sv : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) := fun v =>
    Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map (semiLocalEval K L v).toMonoidHom (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z)) with hsv
  have hglArch : AdelicLevel.glArch (𝓞 L) L (centralScalar (𝓞 L) L z) = sa := by
    simp only [hsa, AdelicLevel.glArch, centralScalar]
    exact map_scalar _ z
  have hglFin : AdelicLevel.glFin (𝓞 L) L (centralScalar (𝓞 L) L z) = sf := by
    simp only [hsf, AdelicLevel.glFin, centralScalar]
    exact map_scalar _ z
  have hcomp_sf : ∀ v, semiLocalComponent K L v sf = sv v := by
    intro v
    simp only [hsf, hsv, semiLocalComponent]
    exact map_scalar _ _
  have hcomp_mul : ∀ v (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)),
      semiLocalComponent K L v (sf * h) = sv v * semiLocalComponent K L v h := by
    intro v h; rw [map_mul, hcomp_sf]

  obtain ⟨S₀, U, hU, hS₀⟩ :=
    AutomorphicForm.exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet K L
      ((baseChangeGLEquiv K L).symm (centralScalar (𝓞 L) L z))
  have hsv_int : ∀ v ∉ S₀, sv v ∈ semiLocalIntegralSet K L v := by
    intro v hv
    have h := hS₀ _ (mem_of_mem_nhds hU) v hv
    rw [← semiLocalComponent_glFin_baseChangeGL, ← baseChangeGLEquiv_apply, ContinuousMulEquiv.apply_symm_apply,
      hglFin, hcomp_sf] at h
    exact h
  refine ⟨S ∪ S₀, Finset.subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isArchTestFactor_comp_mul_left L hφa sa
  · exact isFinTestFactor_comp_mul_left L hφf sf
  · intro v hv
    by_cases hvS : v ∈ S
    · simp only [if_pos hvS]
      exact isSemiLocalTestFn_comp_mul_left K L v (hφS v hvS) (sv v)
    · simp only [if_neg hvS]
      exact isSemiLocalTestFn_comp_mul_left K L v (isSemiLocalTestFn_indicator K L v) (sv v)
  · intro h hh
    change φf (sf * h) = ∏ v ∈ S ∪ S₀, (if v ∈ S then φS v
        else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (sv v * semiLocalComponent K L v h)

    have hh' : ∀ v ∉ S ∪ S₀, semiLocalComponent K L v (sf * h) ∈ semiLocalIntegralSet K L v := by
      intro v hv
      rw [hcomp_mul, mul_mem_semiLocalIntegralSet_iff K L v (hsv_int v fun h0 => hv (Finset.mem_union_right _ h0))]
      exact hh v hv
    by_cases hall : ∀ v ∈ S₀, v ∉ S → sv v * semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v
    ·
      have hint : ∀ v ∉ S, semiLocalComponent K L v (sf * h) ∈ semiLocalIntegralSet K L v := by
        intro v hvS
        by_cases hv0 : v ∈ S₀
        · rw [hcomp_mul]; exact hall v hv0 hvS
        · exact hh' v (by rw [Finset.mem_union, not_or]; exact ⟨hvS, hv0⟩)
      rw [hprod (sf * h) hint]
      have h1 : ∀ v ∈ S, φS v (semiLocalComponent K L v (sf * h)) = (if v ∈ S then φS v
          else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (sv v * semiLocalComponent K L v h) := by
        intro v hv; rw [if_pos hv, hcomp_mul]
      have h2 : ∀ v ∈ S ∪ S₀, v ∉ S → (if v ∈ S then φS v
          else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (sv v * semiLocalComponent K L v h) = 1 := by
        intro v hv hvS
        have hv0 : v ∈ S₀ := (Finset.mem_union.mp hv).resolve_left hvS
        rw [if_neg hvS]
        exact Set.indicator_of_mem (hall v hv0 hvS) _
      rw [Finset.prod_congr rfl h1]
      exact Finset.prod_subset Finset.subset_union_left h2
    · push Not at hall
      obtain ⟨v, hv0, hvS, hbad⟩ := hall
      rw [hzero (sf * h) ⟨v, hvS, by rwa [hcomp_mul]⟩]
      symm
      exact Finset.prod_eq_zero (Finset.mem_union_right _ hv0) (by
        rw [if_neg hvS, Set.indicator_of_notMem hbad])
  · intro h hh
    obtain ⟨v, hv, hbad⟩ := hh
    have hv0 : v ∉ S₀ := fun h0 => hv (Finset.mem_union_right _ h0)
    have hvS : v ∉ S := fun h0 => hv (Finset.mem_union_left _ h0)
    exact hzero (sf * h) ⟨v, hvS, by
      rwa [hcomp_mul, mul_mem_semiLocalIntegralSet_iff K L v (hsv_int v hv0)]⟩
  · intro g
    show φ (centralScalar (𝓞 L) L z * g) = φa (sa * AdelicLevel.glArch (𝓞 L) L g) * φf (sf * AdelicLevel.glFin (𝓞 L) L g)
    rw [hsplit, map_mul, map_mul, hglArch, hglFin]

end S_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul (solution)
