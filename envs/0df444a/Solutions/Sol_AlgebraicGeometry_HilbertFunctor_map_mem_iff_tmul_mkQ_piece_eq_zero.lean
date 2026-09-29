-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.map_mem_iff_tmul_mkQ_piece_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/21f1ad3c-2acc-553b-ae83-95e060f64db2

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero

set_option autoImplicit false
open MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

namespace P1Aux

variable {σ : Type} {R S : Type} [CommRing R] [CommRing S]

theorem homogeneousComponent_map (f : R →+* S) (p : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (MvPolynomial.map f p) = MvPolynomial.map f (homogeneousComponent d p) := by
  ext μ
  rw [coeff_homogeneousComponent, coeff_map, coeff_map, coeff_homogeneousComponent]
  split_ifs
  · rfl
  · exact (map_zero f).symm

theorem homogeneousComponent_mul_left [DecidableEq σ] {p : MvPolynomial σ R} {k : ℕ} (hp : p.IsHomogeneous k)
    (q : MvPolynomial σ R) (m : ℕ) :
    homogeneousComponent m (p * q) = if k ≤ m then p * homogeneousComponent (m - k) q else 0 := by
  classical
  ext μ
  rw [coeff_homogeneousComponent]
  have hpdeg : ∀ α : σ →₀ ℕ, coeff α p ≠ 0 → Finsupp.degree α = k := fun α hα => by
    by_contra h
    exact hα (hp.coeff_eq_zero h)
  split_ifs with hμ hk
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_homogeneousComponent]
    by_cases hα : coeff x.1 p = 0
    · rw [hα, zero_mul, zero_mul]
    · have h1 := hpdeg x.1 hα
      have h2 : Finsupp.degree x.2 = m - k := by
        have := congrArg Finsupp.degree hx
        rw [map_add, h1, hμ] at this
        omega
      rw [if_pos h2]
  · rw [coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hα : coeff x.1 p = 0
    · rw [hα, zero_mul]
    · exfalso
      have h1 := hpdeg x.1 hα
      have := congrArg Finsupp.degree hx
      rw [map_add, h1, hμ] at this
      omega
  · rw [coeff_mul]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_homogeneousComponent]
    split_ifs with h2
    · by_cases hα : coeff x.1 p = 0
      · rw [hα, zero_mul]
      · exfalso
        have h1 := hpdeg x.1 hα
        have := congrArg Finsupp.degree hx
        rw [map_add, h1, h2] at this
        omega
    · rw [mul_zero]
  · rw [coeff_zero]

end P1Aux

theorem solution
    (n : ℕ) (h : ℕ → ℕ) (B A : Type) [CommRing B] [CommRing A] (φ : B →+* A)
    (P : Point B n h) (Q : Point A n h) (hQ : Q.I = Ideal.map (MvPolynomial.map φ) P.I)
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) B) (hF : F.IsHomogeneous d) :
    MvPolynomial.map φ F ∈ Q.I ↔
      (letI : Algebra B A := φ.toAlgebra
       ((1 : A) ⊗ₜ[B] (Submodule.Quotient.mk ⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩ : piece P.I d) :
          A ⊗[B] piece P.I d) = 0) := by
  classical
  letI : Algebra B A := φ.toAlgebra
  have hφ : algebraMap B A = φ := RingHom.algebraMap_toAlgebra φ

  let ψ : MvPolynomial (Fin (n + 1)) B →ₗ[B] MvPolynomial (Fin (n + 1)) A :=
    { toFun := fun p => MvPolynomial.map φ p
      map_add' := fun p q => map_add _ p q
      map_smul' := fun b p => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, map_C,
          IsScalarTower.algebraMap_apply B A (MvPolynomial (Fin (n + 1)) A), MvPolynomial.algebraMap_eq, hφ] }
  have hψ : ∀ p, ψ p = MvPolynomial.map φ p := fun _ => rfl
  set Md := homogeneousSubmodule (Fin (n + 1)) B d with hMd
  set K : Submodule B ↥Md := Submodule.comap Md.subtype (P.I.restrictScalars B) with hKdef
  have hKmem : ∀ G : ↥Md, G ∈ K ↔ (G : MvPolynomial (Fin (n + 1)) B) ∈ P.I := fun G => by
    rw [hKdef, Submodule.mem_comap, Submodule.restrictScalars_mem]; rfl
  constructor
  ·
    intro hmem

    let S : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) := fun e =>
      Submodule.span A (MvPolynomial.map φ '' {G | G ∈ P.I ∧ G.IsHomogeneous e})
    have hSgen : ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) B), G ∈ P.I → G.IsHomogeneous e →
        MvPolynomial.map φ G ∈ S e := fun e G hG hGe => Submodule.subset_span ⟨G, ⟨hG, hGe⟩, rfl⟩

    have hSX : ∀ (i : Fin (n + 1)) (e : ℕ), S e ≤ (S (e + 1)).comap (LinearMap.mulLeft A (X i)) := by
      intro i e
      refine Submodule.span_le.2 ?_
      rintro _ ⟨G, ⟨hG, hGe⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
      have h1 : X i * MvPolynomial.map φ G = MvPolynomial.map φ (X i * G) := by rw [map_mul, map_X]
      rw [h1]
      refine hSgen (e + 1) _ (Ideal.mul_mem_left _ _ hG) ?_
      rw [← Nat.add_comm 1 e]
      exact (isHomogeneous_X B i).mul hGe

    let Tset : Set (MvPolynomial (Fin (n + 1)) A) := {F' | ∀ e : ℕ, homogeneousComponent e F' ∈ S e}
    have hT0 : (0 : MvPolynomial (Fin (n + 1)) A) ∈ Tset := fun e => by
      rw [map_zero]; exact Submodule.zero_mem _
    have hTadd : ∀ a b, a ∈ Tset → b ∈ Tset → a + b ∈ Tset := fun a b ha hb e => by
      rw [map_add]; exact Submodule.add_mem _ (ha e) (hb e)
    have hTC : ∀ (c : A) (F'), F' ∈ Tset → C c * F' ∈ Tset := fun c F' hF' e => by
      rw [C_mul', map_smul]; exact Submodule.smul_mem _ _ (hF' e)
    have hTX : ∀ (i : Fin (n + 1)) (F'), F' ∈ Tset → X i * F' ∈ Tset := fun i F' hF' e => by
      show homogeneousComponent e (X i * F') ∈ S e
      rw [P1Aux.homogeneousComponent_mul_left (isHomogeneous_X A i)]
      split_ifs with he
      · have := hSX i (e - 1) (hF' (e - 1))
        rw [Submodule.mem_comap, LinearMap.mulLeft_apply, Nat.sub_add_cancel he] at this
        exact this
      · exact Submodule.zero_mem _
    have hTmul : ∀ (c F' : MvPolynomial (Fin (n + 1)) A), F' ∈ Tset → c * F' ∈ Tset := by
      intro c
      induction c using MvPolynomial.induction_on with
      | C a => exact fun F' hF' => hTC a F' hF'
      | add p q hp hq => exact fun F' hF' => by rw [add_mul]; exact hTadd _ _ (hp F' hF') (hq F' hF')
      | mul_X p i hp => exact fun F' hF' => by rw [mul_assoc]; exact hp _ (hTX i F' hF')
    let T : Ideal (MvPolynomial (Fin (n + 1)) A) :=
      { carrier := Tset
        zero_mem' := hT0
        add_mem' := fun {a b} ha hb => hTadd a b ha hb
        smul_mem' := fun c {F'} hF' => by rw [smul_eq_mul]; exact hTmul c F' hF' }
    have hQT : Q.I ≤ T := by
      rw [hQ, Ideal.map_le_iff_le_comap]
      intro G hG e
      show homogeneousComponent e (MvPolynomial.map φ G) ∈ S e
      rw [P1Aux.homogeneousComponent_map]
      exact hSgen e _ (P.homogeneous G hG e) (homogeneousComponent_isHomogeneous e G)
    have hFS : MvPolynomial.map φ F ∈ S d := by
      have h1 : homogeneousComponent d (MvPolynomial.map φ F) ∈ S d := hQT hmem d
      rwa [homogeneousComponent_of_mem ((mem_homogeneousSubmodule d _).2 (hF.map φ)), if_pos rfl] at h1

    let π : MvPolynomial (Fin (n + 1)) B →ₗ[B] ↥Md :=
      LinearMap.codRestrict Md (homogeneousComponent d) fun p =>
        (mem_homogeneousSubmodule d _).2 (homogeneousComponent_isHomogeneous d p)
    have hπ : ∀ (G : MvPolynomial (Fin (n + 1)) B) (hG : G ∈ Md), π G = ⟨G, hG⟩ := fun G hG => by
      apply Subtype.ext
      show homogeneousComponent d G = G
      rw [homogeneousComponent_of_mem hG, if_pos rfl]
    let eA := MvPolynomial.algebraTensorAlgEquiv (σ := Fin (n + 1)) B A
    let ρ : MvPolynomial (Fin (n + 1)) A →ₗ[A] A ⊗[B] ↥Md :=
      (π.baseChange A) ∘ₗ (eA.symm : MvPolynomial (Fin (n + 1)) A →ₐ[A] A ⊗[B] MvPolynomial (Fin (n + 1)) B).toLinearMap
    have hρ : ∀ G : MvPolynomial (Fin (n + 1)) B, ρ (MvPolynomial.map φ G) = (1 : A) ⊗ₜ[B] π G := by
      intro G
      have h1 : eA ((1 : A) ⊗ₜ[B] G) = MvPolynomial.map φ G := by
        rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, hφ]
      show π.baseChange A (eA.symm (MvPolynomial.map φ G)) = _
      rw [← h1, AlgEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
    let W : Submodule A (A ⊗[B] ↥Md) := LinearMap.range (K.subtype.baseChange A)
    have hSW : S d ≤ W.comap ρ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨G, ⟨hG, hGd⟩, rfl⟩
      have hGM : G ∈ Md := (mem_homogeneousSubmodule d G).2 hGd
      rw [SetLike.mem_coe, Submodule.mem_comap, hρ, hπ G hGM]
      refine ⟨(1 : A) ⊗ₜ[B] ⟨⟨G, hGM⟩, (hKmem _).2 hG⟩, ?_⟩
      rw [LinearMap.baseChange_tmul]
      rfl
    have hFW : (1 : A) ⊗ₜ[B] (⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩ : ↥Md) ∈ W := by
      have := hSW hFS
      rw [Submodule.mem_comap, hρ, hπ F ((mem_homogeneousSubmodule d F).mpr hF)] at this
      exact this
    obtain ⟨z, hz⟩ := hFW

    have hkill : ∀ w : A ⊗[B] ↥K, (K.mkQ.baseChange A) ((K.subtype.baseChange A) w) = 0 := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul a k =>
        rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Submodule.mkQ_apply, Submodule.subtype_apply,
          (Submodule.Quotient.mk_eq_zero K).2 k.2, tmul_zero]
      | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    have : (1 : A) ⊗ₜ[B] (Submodule.Quotient.mk ⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩ : ↥Md ⧸ K) =
        (K.mkQ.baseChange A) ((1 : A) ⊗ₜ[B] (⟨F, (mem_homogeneousSubmodule d F).mpr hF⟩ : ↥Md)) := by
      rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply]
    rw [this, ← hz, hkill]
  ·
    intro h0
    let N := MvPolynomial (Fin (n + 1)) A ⧸ Q.I
    let f₀ : ↥Md →ₗ[B] N := (Ideal.Quotient.mkₐ B Q.I).toLinearMap ∘ₗ ψ ∘ₗ Md.subtype
    have hf₀ : ∀ G : ↥Md, f₀ G = Ideal.Quotient.mk Q.I (MvPolynomial.map φ (G : MvPolynomial (Fin (n + 1)) B)) :=
      fun G => rfl
    have hK : K ≤ LinearMap.ker f₀ := by
      intro G hG
      rw [LinearMap.mem_ker, hf₀, Ideal.Quotient.eq_zero_iff_mem, hQ]
      exact Ideal.mem_map_of_mem _ ((hKmem G).1 hG)
    let f : (↥Md ⧸ K) →ₗ[B] N := K.liftQ f₀ hK
    let Ψ : A ⊗[B] (↥Md ⧸ K) →ₗ[A] N := f.liftBaseChange A
    have h1 := congrArg Ψ h0
    rw [map_zero, LinearMap.liftBaseChange_tmul, one_smul, Submodule.liftQ_apply, hf₀,
      Ideal.Quotient.eq_zero_iff_mem] at h1
    exact h1

end S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_map_mem_iff_tmul_mkQ_piece_eq_zero (solution)
