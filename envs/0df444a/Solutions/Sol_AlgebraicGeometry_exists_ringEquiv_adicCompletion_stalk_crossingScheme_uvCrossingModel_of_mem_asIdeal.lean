-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/797a81c0-450c-5fb3-8821-8710cdc15762

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
import Theorems.Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Theorems.Thm_AlgebraicGeometry_two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing MvPolynomial ModularCurve

noncomputable section

namespace VertexCompletion

section W
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)

theorem isPrecomplete_map_mk {A : Type*} [CommRing A] (I J : Ideal A) [hI : IsPrecomplete I A] :
    IsPrecomplete (I.map (Ideal.Quotient.mk J)) (A ⧸ J) := by
  constructor
  intro f hf
  have hstep : ∀ n, f (n + 1) - f n ∈ (I ^ n).map (Ideal.Quotient.mk J) := by
    intro n
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top] at h
    exact h
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  choose d hd hdq using fun n => (Ideal.mem_map_iff_of_surjective _ hsurj).mp (hstep n)
  obtain ⟨g0, hg0⟩ := hsurj (f 0)
  let g : ℕ → A := fun n => Nat.rec g0 (fun k acc => acc + d k) n
  have hg_succ : ∀ n, g (n + 1) = g n + d n := fun n => rfl
  have hgf : ∀ n, Ideal.Quotient.mk J (g n) = f n := by
    intro n
    induction n with
    | zero => exact hg0
    | succ n ih => rw [hg_succ, map_add, ih, hdq]; ring
  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem, hg_succ, smul_eq_mul, Ideal.mul_top]
      have : g n - (g n + d n) = -d n := by ring
      rw [this]
      exact Submodule.neg_mem _ (Ideal.pow_le_pow_right hmn (hd n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI hgc
  refine ⟨Ideal.Quotient.mk J L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  rw [SModEq.sub_mem, ← hgf, ← map_sub, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_map_of_mem _ h

abbrev IW : Ideal (PowerSeries O) := Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}

theorem W_facts (hϖ : Irreducible ϖ) : (IW ϖ).IsPrime ∧ IsPrincipalIdealRing (PowerSeries O ⧸ IW ϖ) ∧ IsLocalRing (PowerSeries O ⧸ IW ϖ)
    ∧ Irreducible (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) := by
  have h := PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ 1 le_rfl
  rw [pow_one] at h
  exact h

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem W_residue_surjective (hloc : IsLocalRing (PowerSeries O ⧸ IW ϖ))
    (hmax : IsLocalRing.maximalIdeal (PowerSeries O ⧸ IW ϖ) = Ideal.span {Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)}) :
    Function.Surjective ((IsLocalRing.residue (PowerSeries O ⧸ IW ϖ)).comp ((Ideal.Quotient.mk (IW ϖ)).comp (PowerSeries.C (R := O)))) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨PowerSeries.constantCoeff f, ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply]
  apply (Ideal.Quotient.eq).mpr

  rw [hmax, ← map_sub, Ideal.mem_span_singleton]
  obtain ⟨g, hg⟩ : ∃ g : PowerSeries O, f - PowerSeries.C (PowerSeries.constantCoeff f) = PowerSeries.X * g := by
    refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f, ?_⟩
    ext n
    rcases n with _ | n
    · simp
    · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), sub_zero, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
  have hX : Ideal.Quotient.mk (IW ϖ) PowerSeries.X = Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ) := by
    rw [Ideal.Quotient.eq]; exact Ideal.subset_span rfl
  refine ⟨-(Ideal.Quotient.mk (IW ϖ) g), ?_⟩
  rw [← hX, ← map_neg, ← map_mul, mul_neg, ← hg, neg_sub]

end W

section V
variable {O : Type*} [CommRing O] (a : O)

open _root_.MvPolynomial.CrossingQuotient in
theorem exists_sub_algebraMap_mem_span_U_V (q : CrossingQuotient O a) :
    ∃ c : O, q - algebraMap O (CrossingQuotient O a) c ∈ Ideal.span {CrossingQuotient.U a, CrossingQuotient.V a} := by
  classical
  obtain ⟨p, rfl⟩ := CrossingQuotient.mk_surjective a q
  refine ⟨MvPolynomial.constantCoeff p, ?_⟩
  have hmem : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
      Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2)) : Set (MvPolynomial (Fin 2) O)) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro mono hmono
    have hne : mono ≠ 0 := by
      intro h0
      subst h0
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
        ← MvPolynomial.constantCoeff_eq, sub_self] at hmono
      exact hmono rfl
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    exact ⟨i, Set.mem_univ i, hi⟩
  have hmap := Ideal.mem_map_of_mem (CrossingQuotient.mk a).toRingHom hmem
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, Ideal.map_span] at hmap
  have hC : CrossingQuotient.mk a (MvPolynomial.C (MvPolynomial.constantCoeff p)) =
      algebraMap O (CrossingQuotient O a) (MvPolynomial.constantCoeff p) := (CrossingQuotient.mk a).commutes _
  rw [hC] at hmap
  refine Ideal.span_mono ?_ hmap
  rintro _ ⟨_, ⟨i, -, rfl⟩, rfl⟩
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

abbrev vertexIdeal (ϖ : O) : Ideal (CrossingQuotient O a) :=
  Ideal.span {algebraMap O (CrossingQuotient O a) ϖ, CrossingQuotient.U a, CrossingQuotient.V a}

set_option maxHeartbeats 3200000 in
theorem vertexIdeal_isMaximal [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (E : ℕ) (hE : 1 ≤ E) (w : Oˣ) (ha : a = (w : O) * ϖ ^ E) :
    (vertexIdeal a ϖ).IsMaximal := by
  classical
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal O := by rw [hϖ]; exact Ideal.subset_span rfl

  have haI : a ∈ Ideal.span {ϖ} := Ideal.mem_span_singleton'.mpr
    ⟨(w : O) * ϖ ^ (E - 1), by rw [ha, mul_assoc, ← pow_succ, Nat.sub_add_cancel hE]⟩
  have h0 : (0 : O ⧸ Ideal.span {ϖ}) * 0 = algebraMap O (O ⧸ Ideal.span {ϖ}) a := by
    rw [zero_mul, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr haI]
  let ψ := CrossingQuotient.lift a (0 : O ⧸ Ideal.span {ϖ}) 0 h0
  rw [Ideal.isMaximal_iff]
  constructor
  ·
    intro h1
    have hle : vertexIdeal a ϖ ≤ RingHom.ker ψ.toRingHom := by
      rw [vertexIdeal, Ideal.span_le]
      rintro x (rfl | rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      · rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]; exact CrossingQuotient.lift_U a _ _ h0
      · rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]; exact CrossingQuotient.lift_V a _ _ h0
    have h1' := hle h1
    rw [RingHom.mem_ker, map_one] at h1'
    haveI : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, Ideal.span_singleton_eq_top]; exact (IsLocalRing.mem_maximalIdeal _).mp hϖm)
    exact one_ne_zero h1'
  · intro J x hJ hx hxJ
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_span_U_V a x
    have hcmem : x - algebraMap O _ c ∈ vertexIdeal a ϖ :=
      Ideal.span_mono (Set.subset_insert _ _) hc

    have hcu : IsUnit c := by
      by_contra hcu
      have hcm : c ∈ Ideal.span {ϖ} := by rw [← hϖ]; exact (IsLocalRing.mem_maximalIdeal _).mpr hcu
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hcm
      apply hx
      have : algebraMap O (CrossingQuotient O a) (d * ϖ) ∈ vertexIdeal a ϖ := by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl rfl))
      have := Ideal.add_mem _ hcmem this
      rwa [sub_add_cancel] at this
    have hunit : IsUnit (algebraMap O (CrossingQuotient O a) c) := hcu.map _
    have hcJ : algebraMap O (CrossingQuotient O a) c ∈ J := by
      have := J.sub_mem hxJ (hJ hcmem)
      rwa [sub_sub_cancel] at this
    exact J.eq_top_of_isUnit_mem hcJ hunit ▸ Submodule.mem_top

theorem vertexIdeal_le_of_mem [IsDomain O] (ϖ : O) (E : ℕ) (w : Oˣ) (ha : a = (w : O) * ϖ ^ E)
    (P : Ideal (CrossingQuotient O a)) [P.IsPrime] (hU : CrossingQuotient.U a ∈ P) (hV : CrossingQuotient.V a ∈ P) :
    vertexIdeal a ϖ ≤ P := by
  rw [vertexIdeal, Ideal.span_le]
  rintro x (rfl | rfl | rfl)
  ·
    have ha0 : algebraMap O (CrossingQuotient O a) a ∈ P := by
      rw [← CrossingQuotient.U_mul_V]; exact P.mul_mem_left _ hV
    have ha' : algebraMap O (CrossingQuotient O a) ((w : O) * ϖ ^ E) ∈ P := by rw [← ha]; exact ha0
    rw [map_mul, map_pow] at ha'
    have hpow : algebraMap O (CrossingQuotient O a) ϖ ^ E ∈ P :=
      (Ideal.unit_mul_mem_iff_mem P ((Units.map (algebraMap O (CrossingQuotient O a)).toMonoidHom w).isUnit)).mp ha'
    exact Ideal.IsPrime.mem_of_pow_mem ‹P.IsPrime› E hpow
  · exact hU
  · exact hV

end V

end VertexCompletion

open VertexCompletion in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (E : ℕ) (hE : 1 ≤ E) (w : Oˣ) (a : O) (ha : a = (w : O) * ϖ ^ E)
    (m : ↥(CrossingQuotient.crossingScheme a))
    [IsNoetherianRing ((CrossingQuotient.crossingScheme a).presheaf.stalk m)]
    (hm : CrossingQuotient.U a ∈ m.asIdeal ∧ CrossingQuotient.V a ∈ m.asIdeal) :
    letI φ : CrossingQuotient O a →+* Γ(CrossingQuotient.crossingScheme a, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O a))).inv.hom
    letI germ : Γ(CrossingQuotient.crossingScheme a, ⊤) → (CrossingQuotient.crossingScheme a).presheaf.stalk m :=
      fun t => ((CrossingQuotient.crossingScheme a).presheaf.germ ⊤ m trivial).hom t
    letI B := (CrossingQuotient.crossingScheme a).presheaf.stalk m
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : O →+* W)
      (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (_ : Function.Surjective ((IsLocalRing.residue W).comp σ))
      (ι : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W ((σ ϖ) ^ E)),
      (∀ o : O, ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (algebraMap O _ o)))) =
        UVCrossingModel.const ((σ ϖ) ^ E) (σ o)) ∧
      (∃ w' : (UVCrossingModel W ((σ ϖ) ^ E))ˣ,
        ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (CrossingQuotient.U a)))) =
          UVCrossingModel.U ((σ ϖ) ^ E) * w') ∧
      ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (CrossingQuotient.V a)))) =
        UVCrossingModel.V ((σ ϖ) ^ E) := by
  classical
  set Q := CrossingQuotient O a with hQ
  set B := (CrossingQuotient.crossingScheme a).presheaf.stalk m with hBdef

  letI algQB : Algebra Q B := StructureSheaf.stalkAlgebra Q m
  haveI locQB : IsLocalization.AtPrime B m.asIdeal := StructureSheaf.IsLocalization.to_stalk Q m
  have halg : ∀ q : Q, algebraMap Q B q =
      ((CrossingQuotient.crossingScheme a).presheaf.germ ⊤ m trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom q) :=
    fun q => rfl

  have hmax := vertexIdeal_isMaximal a ϖ hϖ E hE w ha
  haveI : m.asIdeal.IsPrime := m.isPrime
  have hle := vertexIdeal_le_of_mem a ϖ E w ha m.asIdeal hm.1 hm.2
  have hmeq : vertexIdeal a ϖ = m.asIdeal := hmax.eq_of_le Ideal.IsPrime.ne_top' hle

  letI algOB : Algebra O B := ((algebraMap Q B).comp (algebraMap O Q)).toAlgebra
  have hOB : ∀ o : O, algebraMap O B o = algebraMap Q B (algebraMap O Q o) := fun o => rfl
  set g : B := algebraMap Q B (CrossingQuotient.U a) with hg
  set h : B := algebraMap Q B (CrossingQuotient.V a) with hh
  have hmB : IsLocalRing.maximalIdeal B = Ideal.span {algebraMap O B ϖ, g, h} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m.asIdeal B, ← hmeq, Ideal.map_span,
      Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    rfl

  have hsubmem : ∀ q : Q, ∃ c : O, algebraMap Q B q - algebraMap O B c ∈ IsLocalRing.maximalIdeal B := by
    intro q
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_span_U_V a q
    refine ⟨c, ?_⟩
    rw [hOB, ← map_sub, ← IsLocalization.AtPrime.map_eq_maximalIdeal m.asIdeal B]
    apply Ideal.mem_map_of_mem
    rw [← hmeq]
    exact Ideal.span_mono (Set.subset_insert _ _) hc
  have hres : Function.Surjective ((IsLocalRing.residue B).comp (algebraMap O B)) := by
    intro r
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨⟨q, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.asIdeal.primeCompl b
    obtain ⟨cq, hcq⟩ := hsubmem q
    obtain ⟨cs, hcs⟩ := hsubmem (s : Q)

    have hsunit : IsUnit (algebraMap Q B (s : Q)) := IsLocalization.map_units B s
    have hcsu : IsUnit cs := by
      by_contra hnu
      have hcsm : algebraMap O B cs ∈ IsLocalRing.maximalIdeal B := by
        have : cs ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
        rw [hϖ, Ideal.mem_span_singleton'] at this
        obtain ⟨d, rfl⟩ := this
        rw [map_mul, hmB]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl rfl))
      have : algebraMap Q B (s : Q) ∈ IsLocalRing.maximalIdeal B := by
        have := Ideal.add_mem _ hcs hcsm
        rwa [sub_add_cancel] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hsunit
    obtain ⟨csinv, hcsinv⟩ := hcsu.exists_right_inv
    refine ⟨cq * csinv, ?_⟩
    change IsLocalRing.residue B (algebraMap O B (cq * csinv)) = IsLocalRing.residue B (IsLocalization.mk' B q s)

    have e1 : IsLocalRing.residue B (algebraMap Q B q) = IsLocalRing.residue B (algebraMap O B cq) :=
      Ideal.Quotient.eq.mpr hcq
    have e2 : IsLocalRing.residue B (algebraMap Q B (s : Q)) = IsLocalRing.residue B (algebraMap O B cs) :=
      Ideal.Quotient.eq.mpr hcs
    have e3 : IsLocalization.mk' B q s * algebraMap Q B (s : Q) = algebraMap Q B q := IsLocalization.mk'_spec B q s
    have hs0 : IsLocalRing.residue B (algebraMap O B cs) ≠ 0 := by
      rw [← e2, Ne, IsLocalRing.residue_eq_zero_iff]
      exact fun hmem => (IsLocalRing.mem_maximalIdeal _).mp hmem hsunit
    have e4 : IsLocalRing.residue B (algebraMap O B cs) * IsLocalRing.residue B (algebraMap O B csinv) = 1 := by
      rw [← map_mul, ← map_mul, hcsinv, map_one, map_one]
    apply mul_right_cancel₀ hs0
    rw [map_mul, map_mul, mul_assoc, mul_comm (IsLocalRing.residue B (algebraMap O B csinv)), e4, mul_one,
      ← e2, ← map_mul, e3, e1]

  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ

  obtain ⟨θW, θ, hθWC, hθWX, hθsurj, hθC, hθ0, hθ1⟩ :=
    IsLocalRing.exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span
      (O := O) (R := B) ϖ hϖirr g h hmB hres

  obtain ⟨hprime, hpir, hlocW, hϖW⟩ := W_facts ϖ hϖirr
  haveI := hprime
  haveI : IsDomain (PowerSeries O ⧸ IW ϖ) := Ideal.Quotient.isDomain _
  haveI := hpir
  haveI := hlocW
  set ϖW : PowerSeries O ⧸ IW ϖ := Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ) with hϖWdef
  haveI : IsDiscreteValuationRing (PowerSeries O ⧸ IW ϖ) :=
    ⟨fun h0 => hϖW.ne_zero (by
      have hmem : ϖW ∈ maximalIdeal (PowerSeries O ⧸ IW ϖ) := hϖW.not_isUnit
      rw [h0] at hmem
      exact hmem)⟩
  have hmaxW : maximalIdeal (PowerSeries O ⧸ IW ϖ) = Ideal.span {ϖW} := hϖW.maximalIdeal_eq
  have hmkX : Ideal.Quotient.mk (IW ϖ) PowerSeries.X = ϖW := by
    rw [hϖWdef, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hmaxW' : maximalIdeal (PowerSeries O ⧸ IW ϖ) = (Ideal.span {PowerSeries.X}).map (Ideal.Quotient.mk (IW ϖ)) := by
    rw [hmaxW, Ideal.map_span, Set.image_singleton, hmkX]
  haveI : IsPrecomplete (maximalIdeal (PowerSeries O ⧸ IW ϖ)) (PowerSeries O ⧸ IW ϖ) := by
    rw [hmaxW']; exact isPrecomplete_map_mk _ _
  haveI hcompl : IsAdicComplete (maximalIdeal (PowerSeries O ⧸ IW ϖ)) (PowerSeries O ⧸ IW ϖ) := { }

  set φB := algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) with hφB
  have hgh : g * h = algebraMap O B ((w : O) * ϖ ^ E) := by
    rw [hg, hh, ← map_mul, CrossingQuotient.U_mul_V, ← hOB]
    exact congrArg (algebraMap O B) ha
  let v : (AdicCompletion (IsLocalRing.maximalIdeal B) B)ˣ := Units.map (φB.comp (algebraMap O B)).toMonoidHom w
  have hv : (v : AdicCompletion (IsLocalRing.maximalIdeal B) B) = φB (algebraMap O B (w : O)) := rfl
  have hθϖ : θ (MvPowerSeries.C ϖW) = φB (algebraMap O B ϖ) := by
    rw [show θ (MvPowerSeries.C ϖW) = (θ.comp MvPowerSeries.C) ϖW from rfl, hθC, hϖWdef, hθWC]
  have hrel : θ (MvPowerSeries.X 0) * θ (MvPowerSeries.X 1) = θ (MvPowerSeries.C ϖW) ^ E * (v : AdicCompletion (IsLocalRing.maximalIdeal B) B) := by
    rw [hθ0, hθ1, ← map_mul, hgh, map_mul (algebraMap O B), map_pow, map_mul φB, map_pow, hθϖ, hv, mul_comm]

  have hdim : 2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal B) B) :=
    IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le B
      (AlgebraicGeometry.two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal O ϖ hϖ E hE w a ha m hm)

  obtain ⟨ι, hιC, hιU, hιV⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
      (R := B) ϖW hϖW E hE θ hθsurj v hrel hdim
  refine ⟨PowerSeries O ⧸ IW ϖ, inferInstance, inferInstance, inferInstance, hcompl,
    (Ideal.Quotient.mk (IW ϖ)).comp (PowerSeries.C (R := O)), hmaxW, W_residue_surjective ϖ hlocW hmaxW, ι, ?_, ?_, ?_⟩
  · intro o
    change ι (φB (algebraMap Q B (algebraMap O Q o))) = _
    rw [← hOB, ← hθWC o, ← hθC, RingHom.comp_apply]
    exact hιC _
  · refine ⟨Units.map ι.toMonoidHom v, ?_⟩
    change ι (φB g) = _
    rw [← hθ0]
    exact hιU
  · change ι (φB h) = _
    rw [← hθ1]
    exact hιV

end

end S_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal (solution)
