-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_algEquiv_apply_eq_residue_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/875e43e9-e40b-50fb-8d0d-19764b3b4b0b

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_finrank_adjoin_residue_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental

set_option autoImplicit false

open AlgebraicCurve Polynomial

universe u v w w'

theorem solution
    {L : Type u} [Field L] (V : ValuationSubring L)
    {F' : Type v} [Field F'] [Algebra L F']
    {Fb : Type w} [Field Fb] [Algebra (IsLocalRing.ResidueField V) Fb]
    (R : RegularProlongation V F' Fb)
    (y : F') (hy : y ∈ R.integers)
    [FiniteDimensional (IntermediateField.adjoin L ({y} : Set F')) F']
    (htr : Transcendental (IsLocalRing.ResidueField V) (R.residue ⟨y, hy⟩))
    {F : Type w'} [Field F] [Algebra (IsLocalRing.ResidueField V) F]
    (Λ : Subring F') (hΛ : ∀ f : F', f ∈ Λ → f ∈ R.integers)
    (hyΛ : y ∈ Λ) (hVΛ : ∀ a : V, algebraMap L F' a ∈ Λ)
    (hint : ∀ f : Λ, ∃ P : (Polynomial V)[X], P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F').comp (algebraMap V L)) y)
        (f : F') P = 0)
    (ρ : Λ →+* F)
    (hρV : ∀ a : V, ρ ⟨algebraMap L F' a, hVΛ a⟩ =
      algebraMap (IsLocalRing.ResidueField V) F (IsLocalRing.residue V a))
    (hker : ∀ f : Λ, ρ f = 0 → R.residue ⟨f, hΛ f f.2⟩ = 0)
    (hfrac : ∀ z : F, ∃ f h : Λ, ρ h ≠ 0 ∧ z * ρ h = ρ f)
    [FiniteDimensional
      (IntermediateField.adjoin (IsLocalRing.ResidueField V) ({ρ ⟨y, hyΛ⟩} : Set F)) F]
    (hdeg : Module.finrank (IntermediateField.adjoin L ({y} : Set F')) F' ≤
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField V) ({ρ ⟨y, hyΛ⟩} : Set F)) F) :
    ∃ θ : F ≃ₐ[IsLocalRing.ResidueField V] Fb, ∀ f : Λ, θ (ρ f) = R.residue ⟨f, hΛ f f.2⟩ := by
  classical
  set k := IsLocalRing.ResidueField V
  set xb : F := ρ ⟨y, hyΛ⟩ with hxb
  set yb : Fb := R.residue ⟨y, hy⟩ with hyb

  let jR : Λ →+* R.integers :=
    { toFun := fun f => ⟨f, hΛ f f.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let res : Λ →+* Fb := R.residue.comp jR
  have hres : ∀ f : Λ, res f = R.residue ⟨f, hΛ f f.2⟩ := fun _ => rfl
  let cV : V →+* Λ :=
    { toFun := fun a => ⟨algebraMap L F' a, hVΛ a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let evΛ : V[X] →+* Λ := Polynomial.eval₂RingHom cV ⟨y, hyΛ⟩
  have hρcV : ρ.comp cV = (algebraMap k F).comp (IsLocalRing.residue V) := by
    ext a; exact hρV a
  have hrescV : res.comp cV = (algebraMap k Fb).comp (IsLocalRing.residue V) := by
    ext a
    show R.residue ⟨algebraMap L F' a, _⟩ = algebraMap k Fb (IsLocalRing.residue V a)
    rw [← R.residue_algebraMap a]

  have hρev : ∀ P : V[X], ρ (evΛ P) = Polynomial.aeval xb (P.map (IsLocalRing.residue V)) := by
    intro P
    show ρ (Polynomial.eval₂ cV ⟨y, hyΛ⟩ P) = _
    rw [Polynomial.hom_eval₂, hρcV, Polynomial.aeval_def, Polynomial.eval₂_map]
  have hresev : ∀ P : V[X], res (evΛ P) = Polynomial.aeval yb (P.map (IsLocalRing.residue V)) := by
    intro P
    show res (Polynomial.eval₂ cV ⟨y, hyΛ⟩ P) = _
    rw [Polynomial.hom_eval₂, hrescV, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hmapsurj : Function.Surjective (Polynomial.map (IsLocalRing.residue V) : V[X] → k[X]) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective

  have hevF' : Λ.subtype.comp evΛ =
      Polynomial.eval₂RingHom ((algebraMap L F').comp (algebraMap V L)) y := by
    apply Polynomial.ringHom_ext
    · intro a
      show ((Polynomial.eval₂ cV ⟨y, hyΛ⟩ (C a) : Λ) : F') = _
      simp [cV]
    · show ((Polynomial.eval₂ cV ⟨y, hyΛ⟩ X : Λ) : F') = _
      simp

  have hkerle : RingHom.ker ρ ≤ RingHom.ker res := fun f hf => hker f hf

  have hintΛ : ∀ f : Λ, ∃ P : (V[X])[X], P.Monic ∧ Polynomial.eval₂ evΛ f P = 0 := by
    intro f
    obtain ⟨P, hPm, hP⟩ := hint f
    refine ⟨P, hPm, Λ.subtype_injective ?_⟩
    rw [Polynomial.hom_eval₂, hevF', map_zero]
    exact hP

  let S : Subring F := ρ.range
  let ρ' : Λ →+* S := ρ.rangeRestrict
  have hρ' : ∀ f, ((ρ' f : S) : F) = ρ f := fun f => rfl
  have hρ'surj : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hkerρ' : RingHom.ker ρ' = RingHom.ker ρ := by
    ext f
    simp only [RingHom.mem_ker]
    constructor
    · intro h
      rw [← hρ', h]
      rfl
    · intro h
      exact Subtype.ext (by rw [hρ']; exact h)

  have hmemS : ∀ Pb : k[X], (Polynomial.aeval xb Pb : F) ∈ S := fun Pb => by
    obtain ⟨P, rfl⟩ := hmapsurj Pb
    exact ⟨evΛ P, hρev P⟩
  let φS : k[X] →+* S := (Polynomial.aeval xb : k[X] →ₐ[k] F).toRingHom.codRestrict S hmemS
  have hφS : ∀ Pb : k[X], ((φS Pb : S) : F) = Polynomial.aeval xb Pb := fun _ => rfl
  have hφScomp : φS.comp (Polynomial.mapRingHom (IsLocalRing.residue V)) = ρ'.comp evΛ := by
    apply RingHom.ext
    intro P
    apply Subtype.ext
    show Polynomial.aeval xb (P.map (IsLocalRing.residue V)) = ρ (evΛ P)
    rw [hρev]
  letI algS : Algebra k[X] S := φS.toAlgebra
  have halgS : ∀ Pb : k[X], algebraMap k[X] S Pb = φS Pb := fun _ => rfl
  haveI : Algebra.IsIntegral k[X] S := by
    refine ⟨fun z => ?_⟩
    obtain ⟨f, rfl⟩ := hρ'surj z
    obtain ⟨P, hPm, hP⟩ := hintΛ f
    refine ⟨P.map (Polynomial.mapRingHom (IsLocalRing.residue V)), hPm.map _, ?_⟩
    show Polynomial.eval₂ φS (ρ' f) (P.map (Polynomial.mapRingHom (IsLocalRing.residue V))) = 0
    rw [Polynomial.eval₂_map, hφScomp, ← Polynomial.hom_eval₂, hP, map_zero]

  have hkey : ∀ f : Λ, res f = 0 → ρ f = 0 := by
    haveI hprime : (RingHom.ker res).IsPrime := RingHom.ker_isPrime res
    let J : Ideal S := (RingHom.ker res).map ρ'
    haveI hJ : J.IsPrime :=
      Ideal.map_isPrime_of_surjective hρ'surj (I := RingHom.ker res) (by rw [hkerρ']; exact hkerle)
    have hJcomap : J.comap (algebraMap k[X] S) = ⊥ := by
      rw [eq_bot_iff]
      intro Pb hPb
      rw [Ideal.mem_comap, halgS, Ideal.mem_map_iff_of_surjective ρ' hρ'surj] at hPb
      obtain ⟨f, hf, hfP⟩ := hPb
      obtain ⟨P, rfl⟩ := hmapsurj Pb
      have h1 : φS (P.map (IsLocalRing.residue V)) = ρ' (evΛ P) := by
        have := congrArg (fun φ : V[X] →+* S => φ P) hφScomp
        simpa using this
      rw [h1] at hfP
      have h2 : evΛ P - f ∈ RingHom.ker ρ' := by
        rw [RingHom.mem_ker, map_sub, hfP, sub_self]
      rw [hkerρ'] at h2
      have h3 : res (evΛ P) = 0 := by
        have := hkerle h2
        rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
        rw [this]
        exact hf
      rw [hresev] at h3
      have h4 : P.map (IsLocalRing.residue V) = 0 := transcendental_iff.mp htr _ h3
      rw [Ideal.mem_bot, h4]
    have hJbot : J = ⊥ := Ideal.eq_bot_of_comap_eq_bot hJcomap
    intro f hf
    have hmem : ρ' f ∈ J := Ideal.mem_map_of_mem ρ' (by rwa [RingHom.mem_ker])
    rw [hJbot, Ideal.mem_bot] at hmem
    rw [← hρ', hmem]
    rfl

  haveI : IsFractionRing S F := by
    refine ⟨fun z => ?_, fun z => ?_, fun {a b} h => ⟨1, by rw [show a = b from Subtype.ext (by simpa using h)]⟩⟩
    · exact isUnit_iff_ne_zero.mpr fun h => nonZeroDivisors.coe_ne_zero z (Subtype.ext h)
    · obtain ⟨f, h, hh0, hz⟩ := hfrac z
      refine ⟨⟨⟨ρ f, f, rfl⟩, ⟨⟨ρ h, h, rfl⟩, mem_nonZeroDivisors_of_ne_zero fun h0 => hh0 ?_⟩⟩, ?_⟩
      · exact congrArg Subtype.val h0
      · simp at hz ⊢
        exact hz
  have hkerle' : RingHom.ker ρ' ≤ RingHom.ker res := by
    intro f hf
    rw [RingHom.mem_ker] at hf ⊢
    have : ρ f = 0 := by rw [← hρ', hf]; rfl
    exact hkerle (by rwa [RingHom.mem_ker])
  let θ₀ : S →+* Fb :=
    ρ'.liftOfRightInverse (Function.surjInv hρ'surj) (Function.rightInverse_surjInv hρ'surj) ⟨res, hkerle'⟩
  have hθ₀ : ∀ f : Λ, θ₀ (ρ' f) = res f := fun f =>
    ρ'.liftOfRightInverse_comp_apply (Function.surjInv hρ'surj) (Function.rightInverse_surjInv hρ'surj) _ f
  have hθ₀inj : Function.Injective θ₀ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨f, rfl⟩ := hρ'surj z
    rw [hθ₀] at hz
    exact Subtype.ext (hkey f hz)
  let θ₁ : F →+* Fb := IsFractionRing.lift hθ₀inj
  have hθ₁ρ : ∀ f : Λ, θ₁ (ρ f) = res f := by
    intro f
    have : (ρ f : F) = algebraMap S F (ρ' f) := rfl
    rw [this]
    show (IsFractionRing.lift hθ₀inj) (algebraMap S F (ρ' f)) = res f
    rw [IsFractionRing.lift_algebraMap, hθ₀]
  have hθ₁k : ∀ c : k, θ₁ (algebraMap k F c) = algebraMap k Fb c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [← hρV a, hθ₁ρ]
    exact congrArg (fun φ : V →+* Fb => φ a) hrescV
  let θa : F →ₐ[k] Fb :=
    { θ₁ with commutes' := hθ₁k }
  have hθa : ∀ z, θa z = θ₁ z := fun _ => rfl
  have hθainj : Function.Injective θa := θ₁.injective
  have hθaxb : θa xb = yb := by rw [hθa, hxb, hθ₁ρ]; rfl

  set k₀ := IntermediateField.adjoin k ({xb} : Set F) with hk₀
  set k₁ := IntermediateField.adjoin k ({yb} : Set Fb) with hk₁
  obtain ⟨hfinFb, hsumle⟩ :=
    RegularProlongation.sum_finrank_adjoin_residue_le V (fun _ : Fin 1 => Fb) (fun _ => R)
      (Function.injective_of_subsingleton _) y (fun _ => hy) (fun _ => htr)
  haveI : FiniteDimensional k₁ Fb := hfinFb 0
  have hd : Module.finrank k₁ Fb ≤ Module.finrank k₀ F := by
    have h1 : Module.finrank k₁ Fb ≤ Module.finrank (IntermediateField.adjoin L ({y} : Set F')) F' := by
      simpa using hsumle
    exact h1.trans hdeg

  have hmapk : k₀.map θa = k₁ := by
    rw [hk₀, IntermediateField.adjoin_map, Set.image_singleton, hθaxb]
  have hlift : ∀ r : k₁, ∃ r' : k₀, θa r' = r := by
    intro r
    have hr : (r : Fb) ∈ k₀.map θa := by rw [hmapk]; exact r.2
    obtain ⟨r', hr', hrr⟩ := (IntermediateField.mem_map (S := k₀) (f := θa)).mp hr
    exact ⟨⟨r', hr'⟩, hrr⟩
  set n := Module.finrank k₀ F with hn
  let bF : Module.Basis (Fin n) k₀ F := Module.finBasis k₀ F
  have hliFb : LinearIndependent k₁ (fun i => θa (bF i)) := by
    rw [Fintype.linearIndependent_iff]
    intro r hr i
    choose r' hr' using fun i => hlift (r i)
    have hsum : θa (∑ i, r' i • bF i) = 0 := by
      rw [map_sum, ← hr]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul, smul_eq_mul, map_mul, hr']
    have hzero : ∑ i, r' i • bF i = 0 := hθainj (by rw [hsum, map_zero])
    have := Fintype.linearIndependent_iff.mp bF.linearIndependent r' hzero i
    apply Subtype.ext
    rw [← hr' i, this]
    simp
  have hcard : Fintype.card (Fin n) = Module.finrank k₁ Fb := by
    have := hliFb.fintype_card_le_finrank
    rw [Fintype.card_fin] at this ⊢
    omega
  let bFb : Module.Basis (Fin n) k₁ Fb := basisOfLinearIndependentOfCardEqFinrank' _ hliFb hcard
  have hbFb : ∀ i, bFb i = θa (bF i) := fun i => by
    simp [bFb, coe_basisOfLinearIndependentOfCardEqFinrank']
  have hθasurj : Function.Surjective θa := by
    intro z
    choose r' hr' using fun i => hlift (bFb.repr z i)
    refine ⟨∑ i, r' i • bF i, ?_⟩
    conv_rhs => rw [← bFb.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul, smul_eq_mul, map_mul, hr',
      hbFb]
  let θ : F ≃ₐ[k] Fb := AlgEquiv.ofBijective θa ⟨hθainj, hθasurj⟩
  refine ⟨θ, fun f => ?_⟩
  show θa (ρ f) = _
  rw [hθa, hθ₁ρ]
  rfl

end S_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_algEquiv_apply_eq_residue_of_transcendental (solution)
