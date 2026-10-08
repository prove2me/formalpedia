-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoFiberConcreteBasis_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoFiberConcreteBasis_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T23:57:09.211388+00:00
-- url     : https://prove2.me/theorems/45dcbbd6-a8c0-4699-ad2e-4f0a3b0f4a0a
-- title:
--   FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CanonicalContractionQuotient_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuotientVerticalFlatness_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialQuotientBasis_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoFiberNoEscape_p0
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.LocalRing.Module

set_option autoImplicit false




/-!
# The concrete two-fibre basis for an N13 contraction

Assume only the remaining representative-level statement that the canonical
contraction reduces to the fixed special graph ideal.  The generic and special
quotient frames are then both literally `{1,x}`.  The two-fibre no-escape
theorem therefore makes the same pair an integral basis, without any prior
finiteness assumption.
-/

open Polynomial
open Module
open scoped TensorProduct

namespace MazurProof.N13TwoFiberConcreteBasis

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev k : Type :=
  N13GoodCoordinateRingTwo.K

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

abbrev SpecialQuotient : Type :=
  SpecialRing ⧸ N13SpecialQuotientBasis.specialIdeal

abbrev κ : Type :=
  IsLocalRing.ResidueField R₂

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance baseSpecialAlgebra : Algebra R₂ k :=
  N13GeneralizedMumfordReduction.reduceBase.toAlgebra

local instance baseSpecialQuotientTower :
    IsScalarTower R₂ k SpecialQuotient :=
  IsScalarTower.of_algebraMap_eq
    (R := R₂) (S := k) (A := SpecialQuotient)
    fun _ => rfl

theorem ker_baseSpecial :
    RingHom.ker (algebraMap R₂ k) =
      Ideal.span ({(2 : R₂)} : Set R₂) := by
  change RingHom.ker PadicInt.toZMod =
    Ideal.span ({(2 : R₂)} : Set R₂)
  rw [PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  congr 2

@[simp] theorem baseSpecial_two :
    algebraMap R₂ k (2 : R₂) = 0 :=
  N13GeneralizedMumfordReduction.reduceBase_two

/-- The descended reduction map respects the chosen composite
`R₂ → k → SpecialQuotient` scalar structure. -/
theorem specialQuotientMap_comp_algebraMap
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        N13SpecialQuotientBasis.specialIdeal) :
    (N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap).comp
        (algebraMap R₂ (IntegralRing ⧸ I)) =
      (algebraMap k SpecialQuotient).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk N13SpecialQuotientBasis.specialIdeal
        (N13GeneralizedMumfordReduction.reduceCoordinate
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk N13SpecialQuotientBasis.specialIdeal
        (algebraMap k SpecialRing
          (N13GeneralizedMumfordReduction.reduceBase r))
  congr 1
  change
    N13GeneralizedMumfordReduction.reduceCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C r)) =
      N13GoodCoordinateRingTwo.xClass
        (C (N13GeneralizedMumfordReduction.reduceBase r))
  rw [N13GeneralizedMumfordReduction.reduce_xClass]
  simp [N13GeneralizedMumfordReduction.reducePoly]

/-- Reduction sends the integral class of `x` to the first fixed special
basis vector. -/
theorem specialQuotientMap_x_eq_basis_one
    (I : Ideal IntegralRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        N13SpecialQuotientBasis.specialIdeal) :
    N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) =
      N13SpecialQuotientBasis.quotientBasis 1 := by
  rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
    N13CanonicalContractionQuotient.integralX,
    N13GeneralizedMumfordReduction.reduce_xClass,
    N13SpecialQuotientBasis.quotientBasis_one]
  simp [N13GeneralizedMumfordReduction.reducePoly,
    N13GeneralizedMumfordReduction.reduceBase]

/-- A literal fixed special fibre forces the integral classes `{1,x}` in
the contracted quotient to be linearly independent.  Flatness lifts the
independence from the residue-field tensor product; no generic degree
hypothesis is used. -/
theorem integralPair_linearIndependent
    (D : SexticMumford.SemiMumford Model)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    LinearIndependent R₂
      (N13TwoFiberNoEscape.pairFamily
        (1 :
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
        (Ideal.Quotient.mk
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))
          N13CanonicalContractionQuotient.integralX)) := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let g :=
    N13QuotientReduction.reduceCoordinateQuotient
      I N13SpecialQuotientBasis.specialIdeal hmap
  let e₀ : B := 1
  let e₁ : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  have hfactor :
      g.comp (algebraMap R₂ B) =
        (algebraMap κ SpecialQuotient).comp
          (IsLocalRing.residue R₂) := by
    ext r
    calc
      g (algebraMap R₂ B r) =
          algebraMap k SpecialQuotient
            (algebraMap R₂ k r) := by
        simpa only [RingHom.comp_apply, g, B] using
          DFunLike.congr_fun
            (specialQuotientMap_comp_algebraMap I hmap) r
      _ = algebraMap R₂ SpecialQuotient r :=
        (IsScalarTower.algebraMap_apply
          R₂ k SpecialQuotient r).symm
      _ = algebraMap κ SpecialQuotient
          (algebraMap R₂ κ r) :=
        IsScalarTower.algebraMap_apply
          R₂ κ SpecialQuotient r
      _ = algebraMap κ SpecialQuotient
          (IsLocalRing.residue R₂ r) := by
        rfl
  have htwo :
      (2 : R₂) ∈ IsLocalRing.maximalIdeal R₂ := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : R₂))
  let hg :
      Function.Surjective g :=
    N13QuotientReduction.reduceCoordinateQuotient_surjective
      I N13SpecialQuotientBasis.specialIdeal hmap
  let hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R₂ B (2 : R₂)} : Set B) :=
    N13QuotientReduction.ker_reduceCoordinateQuotient_eq_span_two
      I N13SpecialQuotientBasis.specialIdeal hmap
  let e :
      κ ⊗[R₂] B ≃ₗ[κ] SpecialQuotient :=
    N13TensorSpecialFiber.residueLinearEquiv
      g hfactor (2 : R₂) htwo hg hker
  have hliSpecial :
      LinearIndependent κ
        (N13SpecialQuotientBasis.quotientBasis :
          Fin 2 → SpecialQuotient) :=
    N13SpecialQuotientBasis.quotientBasis.linearIndependent
      |>.restrict_scalars' κ
  have e_tmul_one (b : B) :
      e (TensorProduct.mk R₂ κ B 1 b) = g b := by
    change
      (N13TensorSpecialFiber.residueLinearEquiv
        g hfactor (2 : R₂) htwo hg hker)
          ((1 : κ) ⊗ₜ[R₂] b) = g b
    simpa only [one_smul] using
      (N13TensorSpecialFiber.residueLinearEquiv_tmul
        (g := g) (hfactor := hfactor)
        (π := (2 : R₂)) (hπ := htwo)
        (hg := hg) (hker := hker)
        (1 : κ) b)
  have heval (i : Fin 2) :
      e
          (TensorProduct.mk R₂ κ B 1
            (N13TwoFiberNoEscape.pairFamily e₀ e₁ i)) =
        N13SpecialQuotientBasis.quotientBasis i := by
    rw [e_tmul_one]
    fin_cases i
    · simp [e₀, g]
    · simpa [e₁, g] using
        specialQuotientMap_x_eq_basis_one I hmap
  have hliTensor :
      LinearIndependent κ
        (TensorProduct.mk R₂ κ B 1 ∘
          N13TwoFiberNoEscape.pairFamily e₀ e₁) := by
    apply LinearIndependent.of_comp e.toLinearMap
    convert hliSpecial using 1
    funext i
    exact heval i
  letI : Module.Flat R₂ B :=
    N13QuotientVerticalFlatness.contractQuotient_flat
      (N13CanonicalContractionQuotient.graphIdeal D)
  exact
    IsLocalRing.linearIndependent_of_flat
      (N13TwoFiberNoEscape.pairFamily e₀ e₁) hliTensor

universe uR uK uB uG uι

/-- Clear one common denominator in a finite generic relation and descend
it through an injective integral algebra map. -/
theorem linearIndependent_map_to_fractionField
    {R : Type uR} {K : Type uK}
    [CommRing R] [Field K] [Algebra R K]
    {B : Type uB} [CommRing B] [Algebra R B]
    {G : Type uG} [CommRing G]
    [Algebra R G] [Algebra K G] [IsScalarTower R K G]
    {ι : Type uι} [Fintype ι]
    (hRK : Function.Injective (algebraMap R K))
    (q : B →ₐ[R] G) (hq : Function.Injective q)
    (v : ι → B)
    (hden :
      ∀ c : ι → K,
        ∃ d : R, d ≠ 0 ∧ ∃ a : ι → R,
          ∀ i,
            algebraMap R K (a i) =
              algebraMap R K d * c i)
    (hv : LinearIndependent R v) :
    LinearIndependent K (fun i => q (v i)) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc i
  obtain ⟨d, hd, a, ha⟩ := hden c
  have hdK : algebraMap R K d ≠ 0 := by
    simpa using hRK.ne hd
  have hscaled :
      ∑ j, algebraMap R K (a j) • q (v j) = 0 := by
    calc
      ∑ j, algebraMap R K (a j) • q (v j) =
          ∑ j, (algebraMap R K d * c j) • q (v j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [ha j]
      _ = ∑ j, algebraMap R K d •
          (c j • q (v j)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [smul_smul]
      _ = algebraMap R K d •
          ∑ j, c j • q (v j) := by
            rw [Finset.smul_sum]
      _ = 0 := by rw [hc, smul_zero]
  have hqsum :
      q (∑ j, a j • v j) = 0 := by
    calc
      q (∑ j, a j • v j) =
          ∑ j, q (a j • v j) := by simp
      _ = ∑ j, a j • q (v j) := by simp
      _ = ∑ j, algebraMap R K (a j) •
          q (v j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Algebra.smul_def, Algebra.smul_def,
              IsScalarTower.algebraMap_apply R K G]
      _ = 0 := hscaled
  have hint : ∑ j, a j • v j = 0 := by
    apply hq
    simpa only [map_zero] using hqsum
  have hai : a i = 0 := hv a hint i
  have hprod : algebraMap R K d * c i = 0 := by
    rw [← ha i, hai, map_zero]
  exact (mul_eq_zero.mp hprod).resolve_left hdK

/-- A linearly independent pair in an algebra linearly equivalent to a
monic polynomial quotient forces polynomial degree at least two. -/
theorem natDegree_ge_two_of_linearIndependent_fin_two
    {K : Type uK} [Field K]
    (u : K[X]) (hu : u.Monic)
    {B : Type uB} [AddCommGroup B] [Module K B]
    (e : B ≃ₗ[K] AdjoinRoot u)
    {v : Fin 2 → B}
    (hv : LinearIndependent K v) :
    2 ≤ u.natDegree := by
  letI : Module.Finite K (AdjoinRoot u) :=
    hu.finite_adjoinRoot
  have hv' :
      LinearIndependent K (fun i => e (v i)) := by
    change LinearIndependent K (e ∘ v)
    exact
      hv.map' e.toLinearMap
        (LinearMap.ker_eq_bot_of_injective e.injective)
  calc
    2 = Fintype.card (Fin 2) := by simp
    _ ≤ Module.finrank K (AdjoinRoot u) :=
      hv'.fintype_card_le_finrank
    _ = u.natDegree :=
      (AdjoinRoot.powerBasis' hu).finrank

/-- The literal two-dimensional special fibre itself forces the generic
Mumford polynomial to have degree two, provided only the balanced upper
bound. -/
theorem degree_eq_two_of_map_contractIdeal_eq_special
    (D : SexticMumford.SemiMumford Model)
    (hdeg_le : D.u.natDegree ≤ 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    D.u.natDegree = 2 := by
  let J :=
    N13CanonicalContractionQuotient.graphIdeal D
  let I :=
    N13IntegralModelContraction.contractIdeal J
  let B := IntegralRing ⧸ I
  let G := RationalRing ⧸ J
  let v : Fin 2 → B :=
    N13TwoFiberNoEscape.pairFamily
      1
      (Ideal.Quotient.mk I
        N13CanonicalContractionQuotient.integralX)
  let q : B →ₐ[R₂] G :=
    { toRingHom :=
        N13CanonicalContractionQuotient.genericQuotientMap J
      commutes' := fun r => by
        change
          N13CanonicalContractionQuotient.genericQuotientMap J
              (algebraMap R₂
                (IntegralRing ⧸
                  N13IntegralModelContraction.contractIdeal J) r) =
            algebraMap R₂ (RationalRing ⧸ J) r
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun
            (N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap
              J) r }
  have hvR : LinearIndependent R₂ v := by
    simpa only [J, I, B, v] using
      integralPair_linearIndependent D hmap
  have hden :
      ∀ c : Fin 2 → Q₂,
        ∃ d : R₂, d ≠ 0 ∧ ∃ a : Fin 2 → R₂,
          ∀ i,
            algebraMap R₂ Q₂ (a i) =
              algebraMap R₂ Q₂ d * c i := by
    intro c
    obtain ⟨d, hd, a₀, a₁, ha₀, ha₁⟩ :=
      N13TwoFiberNoEscape.exists_common_denominator
        (R := R₂) (K := Q₂) (c 0) (c 1)
    refine ⟨d, hd,
      N13TwoFiberNoEscape.pairFamily a₀ a₁, ?_⟩
    intro i
    fin_cases i
    · simpa using ha₀.symm
    · simpa using ha₁.symm
  have hvQ :
      LinearIndependent Q₂ (fun i => q (v i)) := by
    exact
      linearIndependent_map_to_fractionField
        (hRK := IsFractionRing.injective R₂ Q₂)
        q
        (N13CanonicalContractionQuotient.genericQuotientMap_injective J)
        v hden hvR
  have hge : 2 ≤ D.u.natDegree :=
    natDegree_ge_two_of_linearIndependent_fin_two
      D.u D.u_monic
      (SexticMumford.mumfordQuotientAlgEquiv
        Model D).toLinearEquiv
      hvQ
  exact le_antisymm hdeg_le hge

/-- Once the canonical contraction has the fixed literal special fibre, the
integral quotient has the literal basis `{1,x}`. -/
theorem exists_contractQuotient_basis
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ b : Basis (Fin 2) R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)),
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13TwoFiberNoEscape.pairFamily
          1
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            N13CanonicalContractionQuotient.integralX) := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let G :=
    RationalRing ⧸
      N13CanonicalContractionQuotient.graphIdeal D
  letI : Module.IsTorsionFree R₂ B :=
    N13QuotientVerticalFlatness.contractQuotient_isTorsionFree
      (N13CanonicalContractionQuotient.graphIdeal D)
  exact
    N13TwoFiberNoEscape.exists_basis_of_two_fibres
      (R := R₂) (k := k) (K := Q₂)
      (B := B) (C := SpecialQuotient) (G := G)
      (π := (2 : R₂))
      (hπ := PadicInt.irreducible_p)
      (g := N13QuotientReduction.reduceCoordinateQuotient
        I N13SpecialQuotientBasis.specialIdeal hmap)
      (hfactorSpecial :=
        specialQuotientMap_comp_algebraMap I hmap)
      (hπ_zero := baseSpecial_two)
      (hkerSpecial := ker_baseSpecial)
      (q := N13CanonicalContractionQuotient.genericQuotientMap
        (N13CanonicalContractionQuotient.graphIdeal D))
      (hfactorGeneric :=
        N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap
          (N13CanonicalContractionQuotient.graphIdeal D))
      (hq :=
        N13CanonicalContractionQuotient.genericQuotientMap_injective
          (N13CanonicalContractionQuotient.graphIdeal D))
      (e₀ := 1)
      (e₁ := Ideal.Quotient.mk I
        N13CanonicalContractionQuotient.integralX)
      (bC := N13SpecialQuotientBasis.quotientBasis)
      (hg₀ := by simp)
      (hg₁ := specialQuotientMap_x_eq_basis_one I hmap)
      (bG := SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg)
      (hq₀ :=
        N13CanonicalContractionQuotient.genericQuotientMap_one_eq_basis_zero
          D hdeg)
      (hq₁ :=
        N13CanonicalContractionQuotient.genericQuotientMap_x_eq_basis_one
          D hdeg)

end

end MazurProof.N13TwoFiberConcreteBasis


