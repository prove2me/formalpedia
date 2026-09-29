-- Prove2me | solution 1 for AlgebraicCurve.exists_place_ringHom_residue_eq_of_isPrime_le_of_forall_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b4b4bc26-9ab1-546c-9082-6cb9c52e0050

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_exists_of_valuationSubring_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_deg_ne_zero_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_ringHom_residue_eq_of_isPrime_le_of_forall_aeval_mem
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve

set_option maxHeartbeats 6400000 in
theorem solution
    (A₀ : Type) [CommRing A₀] [IsLocalRing A₀]
    (κ : Type) [Field κ] [IsAlgClosed κ]
    (θ : IsLocalRing.ResidueField A₀ →+* κ) (hθ : Function.Bijective θ)
    (C : Type) [CommRing C] [IsDomain C] [Algebra A₀ C] (j : C)
    (hfin : Module.Finite ↥(Algebra.adjoin A₀ ({j} : Set C)) C)
    (y : Ideal C) (hy : y.IsMaximal)
    (ψ : C →ₐ[A₀] IsLocalRing.ResidueField A₀) (hψ : ∀ c : C, ψ c = 0 ↔ c ∈ y)
    (𝔭 : Ideal C) (h𝔭 : 𝔭.IsPrime) (h𝔭y : 𝔭 ≤ y) (h𝔭ne : 𝔭 ≠ y)
    (h𝔪 : ∀ a ∈ IsLocalRing.maximalIdeal A₀, algebraMap A₀ C a ∈ 𝔭)
    (ht : ∀ f : Polynomial A₀, Polynomial.aeval j f ∈ 𝔭 → ∀ i : ℕ, f.coeff i ∈ IsLocalRing.maximalIdeal A₀) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : DecidableEq Ω) (_ : Algebra κ Ω)
      (V : Place κ Ω)
      (res : IsLocalRing.ResidueField ↥V.toValuationSubring →+* κ)
      (ρ : C →+* ↥V.toValuationSubring),
      (∀ c : κ, res (algebraMap κ (IsLocalRing.ResidueField ↥V.toValuationSubring) c) = c) ∧
      (∀ a : A₀, ((ρ (algebraMap A₀ C a) : ↥V.toValuationSubring) : Ω) =
        algebraMap κ Ω (θ (IsLocalRing.residue A₀ a))) ∧
      (∀ c : C, res (IsLocalRing.residue ↥V.toValuationSubring (ρ c)) = θ (ψ c)) ∧
      Transcendental κ ((ρ j : ↥V.toValuationSubring) : Ω) ∧
      FiniteDimensional ↥(IntermediateField.adjoin κ ({((ρ j : ↥V.toValuationSubring) : Ω)} : Set Ω)) Ω ∧
      (∀ c : C, ((ρ c : ↥V.toValuationSubring) : Ω) = 0 ↔ c ∈ 𝔭) := by
  classical

  set κ₀ := IsLocalRing.ResidueField A₀ with hκ₀
  haveI : 𝔭.IsPrime := h𝔭
  set D := C ⧸ 𝔭 with hD
  let mk : C →+* D := Ideal.Quotient.mk 𝔭

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A₀, (mk.comp (algebraMap A₀ C)) a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (h𝔪 a ha)
  let ι₀ : κ₀ →+* D := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A₀) (mk.comp (algebraMap A₀ C)) hker
  have hι₀ : ∀ a : A₀, ι₀ (IsLocalRing.residue A₀ a) = mk (algebraMap A₀ C a) := fun a => rfl

  let e : κ₀ ≃+* κ := RingEquiv.ofBijective θ hθ
  let Ω := FractionRing D
  let ιΩ : κ →+* Ω := ((algebraMap D Ω).comp ι₀).comp e.symm.toRingHom
  letI algκΩ : Algebra κ Ω := ιΩ.toAlgebra
  have halg : ∀ c : κ, algebraMap κ Ω c = algebraMap D Ω (ι₀ (e.symm c)) := fun c => rfl

  letI algA₀Ω : Algebra A₀ Ω := ((algebraMap D Ω).comp (mk.comp (algebraMap A₀ C))).toAlgebra
  let Φ : C →+* Ω := (algebraMap D Ω).comp mk
  have hΦ : ∀ c : C, Φ c = algebraMap D Ω (mk c) := fun c => rfl
  have hΦinj0 : ∀ c : C, Φ c = 0 ↔ c ∈ 𝔭 := by
    intro c
    rw [hΦ, map_eq_zero_iff _ (IsFractionRing.injective D Ω), Ideal.Quotient.eq_zero_iff_mem]
  have hΦA₀ : ∀ a : A₀, Φ (algebraMap A₀ C a) = algebraMap κ Ω (θ (IsLocalRing.residue A₀ a)) := by
    intro a
    rw [halg, hΦ]
    congr 1
    rw [← hι₀]
    congr 1
    exact (e.symm_apply_apply (IsLocalRing.residue A₀ a)).symm
  set jΩ : Ω := Φ j with hjΩ

  have htrans : Transcendental κ jΩ := by
    intro halgj
    obtain ⟨p, hp0, hp⟩ := halgj

    set p₀ : Polynomial κ₀ := p.map e.symm.toRingHom with hp₀
    obtain ⟨f, hf⟩ := Polynomial.map_surjective (IsLocalRing.residue A₀) IsLocalRing.residue_surjective p₀
    have hcomp : (algebraMap κ Ω).comp ((e : κ₀ →+* κ).comp (IsLocalRing.residue A₀)) = Φ.comp (algebraMap A₀ C) := by
      ext a; simp only [RingHom.comp_apply]; rw [hΦA₀]; rfl
    have hmap : (f.map ((e : κ₀ →+* κ).comp (IsLocalRing.residue A₀))) = p := by
      rw [← Polynomial.map_map, hf, hp₀, Polynomial.map_map]
      have : (e : κ₀ →+* κ).comp e.symm.toRingHom = RingHom.id κ := by ext x; simp
      rw [this, Polynomial.map_id]
    have heval : Φ (Polynomial.aeval j f) = Polynomial.aeval jΩ p := by
      rw [← hmap, Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, hjΩ,
        Polynomial.hom_eval₂, ← hcomp]
    have hmem : Polynomial.aeval j f ∈ 𝔭 := by
      rw [← hΦinj0, heval, hp]
    have hcoeff := ht f hmem
    apply hp0
    rw [← hmap]
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.comp_apply,
      (IsLocalRing.residue_eq_zero_iff _).mpr (hcoeff i), map_zero]

  set E := IntermediateField.adjoin κ ({jΩ} : Set Ω) with hE
  have hjE : jΩ ∈ E := IntermediateField.subset_adjoin κ _ (Set.mem_singleton jΩ)

  let S₀ : Subalgebra A₀ C := Algebra.adjoin A₀ ({j} : Set C)
  haveI : Module.Finite ↥S₀ C := hfin
  have hΦS₀ : ∀ s : ↥S₀, Φ (s : C) ∈ E := by
    intro s
    obtain ⟨s, hs⟩ := s
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx; exact hjE
    | algebraMap a => rw [hΦA₀]; exact E.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact E.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact E.mul_mem hx hy
  let φ₀ : ↥S₀ →+* ↥E :=
    { toFun := fun s => ⟨Φ (s : C), hΦS₀ s⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hcompE : (algebraMap ↥E Ω).comp φ₀ = Φ.comp (algebraMap ↥S₀ C) := by
    ext s; rfl

  have hint : ∀ c : C, IsIntegral ↥E (Φ c) := fun c =>
    (Algebra.IsIntegral.isIntegral (R := ↥S₀) c).map_of_comp_eq φ₀ Φ hcompE

  obtain ⟨s, hs⟩ := Module.finite_def.mp hfin
  set F := IntermediateField.adjoin ↥E ((fun c => Φ c) '' (s : Set C)) with hF
  haveI : FiniteDimensional ↥E ↥F := by
    rw [hF, ← Finset.coe_image]
    exact IntermediateField.finiteDimensional_adjoin (fun x hx => by
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx; exact hint c)
  have hΦF : ∀ c : C, Φ c ∈ F := by
    intro c
    have hc : c ∈ Submodule.span ↥S₀ (s : Set C) := by rw [hs]; exact Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact F.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul]
      refine F.mul_mem ?_ hx
      have : Φ (algebraMap ↥S₀ C a) = algebraMap ↥E Ω (φ₀ a) := rfl
      rw [this]; exact F.algebraMap_mem _
  have hFtop : F = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) x
    obtain ⟨ca, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨cb, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact F.div_mem (hΦF ca) (hΦF cb)
  have hfdE : FiniteDimensional ↥E Ω := by
    have e1 : ↥F ≃ₗ[↥E] Ω := (IntermediateField.equivOfEq hFtop).trans IntermediateField.topEquiv |>.toLinearEquiv
    exact LinearEquiv.finiteDimensional e1

  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  set yb : Ideal D := Ideal.map mk y with hyb
  have hcomap : Ideal.comap mk yb = y := by
    rw [hyb, Ideal.comap_map_of_surjective _ hmk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr h𝔭y]
  have hyb_ne : yb ≠ ⊤ := by
    intro h; apply hy.ne_top; rw [← hcomap, h, Ideal.comap_top]
  haveI hybmax : yb.IsMaximal := (Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hy).resolve_left hyb_ne
  have hmem_yb : ∀ c : C, mk c ∈ yb ↔ c ∈ y := by
    intro c; rw [← Ideal.mem_comap, hcomap]
  let R := Localization.AtPrime yb
  have hunits : ∀ t : yb.primeCompl, IsUnit (algebraMap D Ω (t : D)) := by
    intro t
    apply IsUnit.mk0
    rw [map_ne_zero_iff _ (IsFractionRing.injective D Ω)]
    exact fun h => t.2 (h.symm ▸ yb.zero_mem)
  let g : R →+* Ω := IsLocalization.lift (M := yb.primeCompl) hunits
  have hg : ∀ d : D, g (algebraMap D R d) = algebraMap D Ω d := fun d => IsLocalization.lift_eq hunits d
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing g

  have hΦO : ∀ c : C, Φ c ∈ O := fun c => by rw [hΦ, ← hg]; exact hO _
  have hΦnu : ∀ c ∈ y, ¬ IsUnit (⟨Φ c, hΦO c⟩ : ↥O) := by
    intro c hc hu
    have h1 : algebraMap D R (mk c) ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff R yb (mk c)).mpr ((hmem_yb c).mpr hc)
    apply (IsLocalRing.mem_maximalIdeal _).mp h1 |> mem_nonunits_iff.mp
    apply hloc.map_nonunit

    have : (g.codRestrict O.toSubring hO) (algebraMap D R (mk c)) = ⟨Φ c, hΦO c⟩ := by
      ext; show g (algebraMap D R (mk c)) = Φ c; rw [hg]; rfl
    rw [this]; exact hu
  have hOne : O ≠ ⊤ := by
    obtain ⟨c₀, hc₀y, hc₀𝔭⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h𝔭y h𝔭ne)
    intro hT
    apply hΦnu c₀ hc₀y
    have hne : Φ c₀ ≠ 0 := fun h => hc₀𝔭 ((hΦinj0 c₀).mp h)
    have hinv : (Φ c₀)⁻¹ ∈ O := by rw [hT]; exact ValuationSubring.mem_top _
    exact IsUnit.of_mul_eq_one ⟨(Φ c₀)⁻¹, hinv⟩ (by ext; exact mul_inv_cancel₀ hne)
  have hκO : ∀ c : κ, algebraMap κ Ω c ∈ O := by
    intro c
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A₀) (e.symm c)
    have : algebraMap κ Ω c = Φ (algebraMap A₀ C a) := by
      rw [hΦA₀, ha]; show algebraMap κ Ω c = algebraMap κ Ω (e (e.symm c)); rw [e.apply_symm_apply]
    rw [this]; exact hΦO _

  haveI : FiniteDimensional ↥(IntermediateField.adjoin κ ({jΩ} : Set Ω)) Ω := hfdE
  obtain ⟨V, hV⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional jΩ O hκO hOne
  have hdeg : V.deg = 1 := AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed V
    (AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin jΩ htrans V)
  have hsurj : Function.Surjective (algebraMap κ V.ResidueField) :=
    (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField V).mp hdeg
  let eV : κ ≃+* V.ResidueField := RingEquiv.ofBijective _ ⟨(algebraMap κ V.ResidueField).injective, hsurj⟩
  let res : IsLocalRing.ResidueField ↥V.toValuationSubring →+* κ := eV.symm.toRingHom
  have hres : ∀ c : κ, res (algebraMap κ _ c) = c := fun c => eV.symm_apply_apply c

  have hΦV : ∀ c : C, Φ c ∈ V.toValuationSubring := fun c => by rw [hV]; exact hΦO c
  let ρ : C →+* ↥V.toValuationSubring :=
    { toFun := fun c => ⟨Φ c, hΦV c⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hρ : ∀ c : C, ((ρ c : ↥V.toValuationSubring) : Ω) = Φ c := fun c => rfl
  have hρy : ∀ c ∈ y, ρ c ∈ IsLocalRing.maximalIdeal ↥V.toValuationSubring := by
    intro c hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu; apply hΦnu c hc

    obtain ⟨u, hu⟩ := hu
    have hmem : ∀ w : ↥V.toValuationSubring, (w : Ω) ∈ O := fun w => by rw [← hV]; exact w.2
    refine ⟨⟨⟨(u : ↥V.toValuationSubring), hmem _⟩, ⟨((u⁻¹ : (↥V.toValuationSubring)ˣ) : ↥V.toValuationSubring), hmem _⟩, ?_, ?_⟩, ?_⟩
    · ext; exact congrArg (fun z : ↥V.toValuationSubring => (z : Ω)) u.mul_inv
    · ext; exact congrArg (fun z : ↥V.toValuationSubring => (z : Ω)) u.inv_mul
    · ext; exact congrArg (fun z : ↥V.toValuationSubring => (z : Ω)) hu
  have hρalg : ∀ a : A₀, ρ (algebraMap A₀ C a) = algebraMap κ ↥V.toValuationSubring (θ (IsLocalRing.residue A₀ a)) := by
    intro a; ext
    rw [hρ, hΦA₀, AlgebraicCurve.Place.coe_algebraMap]
  refine ⟨Ω, inferInstance, inferInstance, algκΩ, V, res, ρ, hres, fun a => by rw [hρ, hΦA₀], ?_, htrans, hfdE, fun c => by rw [hρ, hΦinj0]⟩

  intro c
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A₀) (ψ c)
  have hψa : ψ (algebraMap A₀ C a) = IsLocalRing.residue A₀ a := ψ.commutes a
  have hcy : c - algebraMap A₀ C a ∈ y := by
    rw [← hψ, map_sub, hψa, ha, sub_self]
  have h1 : IsLocalRing.residue ↥V.toValuationSubring (ρ c) =
      IsLocalRing.residue ↥V.toValuationSubring (ρ (algebraMap A₀ C a)) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by rw [← map_sub]; exact hρy _ hcy)
  rw [h1, hρalg]
  show res (algebraMap κ (IsLocalRing.ResidueField ↥V.toValuationSubring) (θ (IsLocalRing.residue A₀ a))) = θ (ψ c)
  rw [hres, ← ha, ← hψa]

end S_AlgebraicCurve_exists_place_ringHom_residue_eq_of_isPrime_le_of_forall_aeval_mem
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_ringHom_residue_eq_of_isPrime_le_of_forall_aeval_mem (solution)
