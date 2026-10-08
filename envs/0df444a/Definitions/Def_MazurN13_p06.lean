-- Prove2me | Definitions.Def_MazurN13_p06
-- name    : MazurN13_p06
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T00:22:02.399635+00:00
-- url     : https://prove2.me/theorems/c5be3ea7-8633-4a45-9158-f51c5ddd6074
-- title:
--   Mazur order 13 (Huang FLT port), part 6/33
-- statement:
--   Part 6 of 33 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis`
--   - `FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery`
--   - `FLT.Assumptions.MazurProof.N13FiniteFlatBasisLift`
--   - `FLT.Assumptions.MazurProof.N13GenericQuotientLocalization`
--   - `FLT.Assumptions.MazurProof.N13TwoGeneratorFiberBasis`
--   - `FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis`
--   - `FLT.Assumptions.MazurProof.N13IntegralGraphJacobian`
--   - `FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery`
--   - `FLT.Assumptions.MazurProof.N13RankTwoVerticalIdealRecovery`
--   - `FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery`
--   - `FLT.Assumptions.MazurProof.N13VerticalGraphJacobian`
--   - `FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
import Definitions.Def_MazurN13_p05
set_option maxHeartbeats 1000000

-- module FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis
section

-- ===== FLT.Assumptions.MazurProof.N13TwoFiberConcreteBasis =====
section

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

local instance : Fact (Nat.Prime 2) :=
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

end
end

-- module FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery
section

-- ===== FLT.Assumptions.MazurProof.N13ConcreteGraphRecovery =====
section

/-!
# Recovering the integral N13 graph from the concrete two-fibre basis

The literal basis `{1,x}` turns multiplication by `x` into a monic
characteristic polynomial of degree two.  Expressing the quotient class of
`y` in that basis then recovers the canonical contraction literally as a
generalized Mumford graph ideal.
-/

open Module
open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13ConcreteGraphRecovery

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev Q₂ : Type :=
  N13IntegralModelContraction.Q₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

abbrev SmoothMumford₂ : Type :=
  N13GeneralizedMumfordReduction.SmoothMumford₂

/-- Equal graph ideals with equal infinity multiplicity define the same
oriented Picard class.  This is the literal representative-level form of
the separatedness used below. -/
theorem semiMumfordClass_eq_of_graphIdeal_eq
    (D₁ D₂ : SexticMumford.SemiMumford Model)
    (hideal :
      N13CanonicalContractionQuotient.graphIdeal D₁ =
        N13CanonicalContractionQuotient.graphIdeal D₂)
    (hnInf : D₁.nInf = D₂.nInf) :
    SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D₁ =
      SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D₂ := by
  unfold SexticMumford.semiMumfordClass
  congr 2
  apply Prod.ext
  · apply Units.ext
    change
      (N13CanonicalContractionQuotient.graphIdeal D₁ :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model)) =
        (N13CanonicalContractionQuotient.graphIdeal D₂ :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model))
    exact congrArg
      (fun I : Ideal
          (SexticMumford.CoordinateRing Model) ↦
        (I :
          FractionalIdeal
            (SexticMumford.CoordinateRing Model)⁰
            (SexticMumford.FunctionField Model)))
      hideal
  · unfold SexticMumford.semiMumfordRaw
    rw [hnInf]

/-- The integral affine `y` coordinate. -/
def integralY : IntegralRing :=
  N13GeneralizedMumfordIntegral.yClass (R := R₂)

/-- Evaluation at the integral affine `x` coordinate is the coordinate
embedding of the polynomial subring. -/
@[simp] theorem aeval_integralX (p : R₂[X]) :
    aeval N13CanonicalContractionQuotient.integralX p =
      N13GeneralizedMumfordIntegral.xClass (R := R₂) p := by
  change
    aeval
        (algebraMap R₂[X] IntegralRing X) p =
      algebraMap R₂[X] IntegralRing p
  simpa using
    aeval_algebraMap_apply IntegralRing
      (X : R₂[X]) p

/-- Polynomial evaluation commutes with passage to any quotient of the
integral affine ring. -/
theorem quotient_aeval_integralX
    (I : Ideal IntegralRing) (p : R₂[X]) :
    aeval
        (Ideal.Quotient.mk I
          N13CanonicalContractionQuotient.integralX) p =
      Ideal.Quotient.mk I
        (N13GeneralizedMumfordIntegral.xClass (R := R₂) p) := by
  rw [← aeval_integralX]
  simpa using
    (Polynomial.map_aeval_eq_aeval_map
      (R := R₂) (S := IntegralRing) (T := R₂)
      (U := IntegralRing ⧸ I)
      (φ := RingHom.id R₂)
      (ψ := Ideal.Quotient.mk I)
      (by ext; simp) p
      N13CanonicalContractionQuotient.integralX).symm

/-- The integral affine ring has polynomial normal form in `x,y`. -/
theorem integral_rankTwoPolynomialNormalForm :
    N13RankTwoIdealRecovery.HasRankTwoPolynomialNormalForm
      (R := R₂)
      N13CanonicalContractionQuotient.integralX integralY := by
  intro z
  refine
    ⟨N13GeneralizedMumfordIntegral.coeff0 z,
      N13GeneralizedMumfordIntegral.coeffY z, ?_⟩
  rw [aeval_integralX, aeval_integralX]
  exact
    (N13GeneralizedMumfordIntegral.recompose z).symm

/-- The remaining special-ideal equality forces the canonical contraction
to be a literal monic quadratic graph ideal. -/
theorem exists_integral_smoothGraph
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ E : SmoothMumford₂,
      E.u.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) E.u E.v := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let xbar : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  let ybar : B :=
    Ideal.Quotient.mk I integralY
  obtain ⟨b, hb⟩ :=
    N13TwoFiberConcreteBasis.exists_contractQuotient_basis
      D hdeg hmap
  have hb0 : b 0 = 1 := by
    have h := congrFun hb (0 : Fin 2)
    simpa [N13TwoFiberNoEscape.pairFamily] using h
  have hb1 : b 1 = xbar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13TwoFiberNoEscape.pairFamily, xbar, I] using h
  letI : Module.Free R₂ B :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ B :=
    Module.Finite.of_basis b
  letI : Nontrivial B :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, hy⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
        xbar ybar b hb0 hb1
  let u : R₂[X] :=
    (Algebra.lmul R₂ B xbar).charpoly
  let v : R₂[X] :=
    C a + C c * X
  have huMonic : u.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x xbar
  have huDegree : u.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
        xbar b hb0 hb1
  have hker :
      RingHom.ker
          ((aeval xbar : R₂[X] →ₐ[R₂] B).toRingHom) =
        Ideal.span ({u} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
          xbar b hb0 hb1
  have hyv : ybar = aeval xbar v := by
    calc
      ybar =
          algebraMap R₂ B a +
            algebraMap R₂ B c * xbar := hy
      _ = aeval xbar v := by
        simp [v]
  have hI :=
    N13RankTwoIdealRecovery.ideal_eq_span_aeval_y_sub
      (R := R₂)
      N13CanonicalContractionQuotient.integralX
      integralY I u v
      integral_rankTwoPolynomialNormalForm hker hyv
  have hIgraph :
      I =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    simpa [N13GeneralizedMumfordIntegral.mumfordIdeal,
      N13GeneralizedMumfordIntegral.ySubClass,
      integralY,
      aeval_integralX] using hI
  have hvDegree : v.natDegree ≤ 1 := by
    unfold v
    compute_degree
  let residual : R₂[X] :=
    v ^ 2 +
      N13GeneralizedMumfordIntegral.hPoly (R := R₂) * v -
      N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)
  have hresGraph :
      N13GeneralizedMumfordIntegral.xClass (R := R₂) residual ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    have hy :
        N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v ∈
          N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v :=
      N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u v
    have hprod :
        N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v *
            N13GeneralizedMumfordIntegral.ySubClass
              (R := R₂)
              (N13GeneralizedMumfordIntegral.conjugateV v) ∈
          N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v :=
      Ideal.mul_mem_right _ _ hy
    rw [N13GeneralizedMumfordIntegral.ySubClass_mul_conjugateV_raw]
      at hprod
    have hneg :=
      (N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) u v).neg_mem hprod
    simpa [residual] using hneg
  have hresI :
      N13GeneralizedMumfordIntegral.xClass (R := R₂) residual ∈ I := by
    rw [hIgraph]
    exact hresGraph
  have hresEval :
      aeval xbar residual = 0 := by
    rw [quotient_aeval_integralX]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hresI
  have hresKer :
      residual ∈
        RingHom.ker
          ((aeval xbar : R₂[X] →ₐ[R₂] B).toRingHom) :=
    RingHom.mem_ker.mpr hresEval
  rw [hker, Ideal.mem_span_singleton] at hresKer
  obtain ⟨w, hw⟩ := hresKer
  have hcurve :
      v ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂) * v -
        N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
          u * w := by
    simpa [residual] using hw
  have hmapGraph :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v) =
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hIgraph]
    exact hmap
  have hspecialGraph :
      N13GoodCoordinateRingTwo.mumfordIdeal
          (N13GeneralizedMumfordReduction.reducePoly u)
          (N13GeneralizedMumfordReduction.reducePoly v) =
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← N13GeneralizedMumfordReduction.map_mumfordIdeal]
    exact hmapGraph
  have hxmem :
      N13GoodCoordinateRingTwo.xClass
          (N13GeneralizedMumfordReduction.reducePoly u) ∈
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hspecialGraph]
    exact
      N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal
        (N13GeneralizedMumfordReduction.reducePoly u)
        (N13GeneralizedMumfordReduction.reducePoly v)
  have hxker :
      N13GoodCoordinateRingTwo.xClass
          (N13GeneralizedMumfordReduction.reducePoly u) ∈
        RingHom.ker
          (N13GoodCoordinateRingTwo.mumfordEval
            N13SpecialQuotientBasis.specialData) := by
    rw [N13GoodCoordinateRingTwo.ker_mumfordEval]
    exact hxmem
  have hbaseDvdU :=
    RingHom.mem_ker.mp hxker
  rw [N13GoodCoordinateRingTwo.mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hbaseDvdU
  have hreduceU :
      N13GeneralizedMumfordReduction.reducePoly u =
        (X ^ 2 + X : N13GeneralizedMumfordReduction.K[X]) := by
    have huReduceMonic :
        (N13GeneralizedMumfordReduction.reducePoly u).Monic :=
      huMonic.map N13GeneralizedMumfordReduction.reduceBase
    have huReduceDegree :
        (N13GeneralizedMumfordReduction.reducePoly u).natDegree = 2 := by
      change
        (u.map N13GeneralizedMumfordReduction.reduceBase).natDegree = 2
      rw [huMonic.natDegree_map, huDegree]
    have heq :
        N13GeneralizedMumfordReduction.reducePoly u =
          N13SpecialQuotientBasis.specialData.u :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        N13SpecialQuotientBasis.specialData.u_monic
        huReduceMonic hbaseDvdU
        (by
          rw [huReduceDegree,
            N13SpecialQuotientBasis.specialData_u_natDegree])
    simpa only [N13SpecialQuotientBasis.specialData_u] using heq
  have hymem :
      N13GoodCoordinateRingTwo.ySubClass
          (N13GeneralizedMumfordReduction.reducePoly v) ∈
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hspecialGraph]
    exact
      N13GoodCoordinateRingTwo.ySubClass_mem_mumfordIdeal
        (N13GeneralizedMumfordReduction.reducePoly u)
        (N13GeneralizedMumfordReduction.reducePoly v)
  have hyker :
      N13GoodCoordinateRingTwo.ySubClass
          (N13GeneralizedMumfordReduction.reducePoly v) ∈
        RingHom.ker
          (N13GoodCoordinateRingTwo.mumfordEval
            N13SpecialQuotientBasis.specialData) := by
    rw [N13GoodCoordinateRingTwo.ker_mumfordEval]
    exact hymem
  have hyzero :=
    RingHom.mem_ker.mp hyker
  have hbaseDvdNegV :
      N13SpecialQuotientBasis.specialData.u ∣
        -N13GeneralizedMumfordReduction.reducePoly v := by
    simp only [N13GoodCoordinateRingTwo.ySubClass, map_sub,
      N13GoodCoordinateRingTwo.mumfordEval_yClass,
      N13GoodCoordinateRingTwo.mumfordEval_xClass,
      N13SpecialQuotientBasis.specialData_v, map_zero,
      zero_sub] at hyzero
    change
        Ideal.Quotient.mk
            (Ideal.span
              ({N13SpecialQuotientBasis.specialData.u} :
                Set N13GeneralizedMumfordReduction.K[X]))
            (-N13GeneralizedMumfordReduction.reducePoly v) =
          0 at hyzero
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hyzero)
  have hbaseDvdV :
      N13SpecialQuotientBasis.specialData.u ∣
        N13GeneralizedMumfordReduction.reducePoly v := by
    simpa only [dvd_neg] using hbaseDvdNegV
  have hreduceV :
      N13GeneralizedMumfordReduction.reducePoly v = 0 := by
    apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hbaseDvdV
    calc
      (N13GeneralizedMumfordReduction.reducePoly v).natDegree ≤
          v.natDegree :=
        Polynomial.natDegree_map_le
      _ ≤ 1 := hvDegree
      _ < 2 := by omega
      _ =
          N13SpecialQuotientBasis.specialData.u.natDegree :=
        N13SpecialQuotientBasis.specialData_u_natDegree.symm
  let g : R₂[X] :=
    2 * v +
      N13GeneralizedMumfordIntegral.hPoly (R := R₂)
  have hgMonic : g.Monic := by
    unfold g v N13GeneralizedMumfordIntegral.hPoly
    monicity <;> norm_num
  have hreduceG :
      N13GeneralizedMumfordReduction.reducePoly g =
        N13GoodCoordinateRingTwo.hPoly := by
    change
      g.map N13GeneralizedMumfordReduction.reduceBase =
        N13GoodCoordinateRingTwo.hPoly
    unfold g
    rw [Polynomial.map_add, Polynomial.map_mul]
    have htwoPoly :
        (2 : N13GeneralizedMumfordReduction.K[X]) = 0 :=
      CharP.cast_eq_zero
        (N13GeneralizedMumfordReduction.K[X]) 2
    rw [show
        (2 : R₂[X]).map
            N13GeneralizedMumfordReduction.reduceBase =
          (2 : N13GeneralizedMumfordReduction.K[X]) by simp,
      htwoPoly, zero_mul, zero_add]
    exact N13GeneralizedMumfordReduction.reduce_hPoly
  have hcoprimeSpecial :
      IsCoprime
        (N13GeneralizedMumfordReduction.reducePoly u)
        (N13GeneralizedMumfordReduction.reducePoly g) := by
    rw [hreduceU, hreduceG]
    refine ⟨X - 1, 1, ?_⟩
    have htwoPoly :
        (2 : N13GeneralizedMumfordReduction.K[X]) = 0 :=
      CharP.cast_eq_zero
        (N13GeneralizedMumfordReduction.K[X]) 2
    calc
      (X - 1) * (X ^ 2 + X) +
          1 * N13GoodCoordinateRingTwo.hPoly =
        2 * X ^ 3 + 1 := by
          simp only [N13GoodCoordinateRingTwo.hPoly]
          ring
      _ = 1 := by rw [htwoPoly, zero_mul, zero_add]
  have hresultantSpecialUnit :
      IsUnit
        ((N13GeneralizedMumfordReduction.reducePoly u).resultant
          (N13GeneralizedMumfordReduction.reducePoly g)) :=
    (Polynomial.isUnit_resultant_iff_isCoprime
      (huMonic.map
        N13GeneralizedMumfordReduction.reduceBase)).2
      hcoprimeSpecial
  have hresultantMap :
      (N13GeneralizedMumfordReduction.reducePoly u).resultant
          (N13GeneralizedMumfordReduction.reducePoly g) =
        N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g) := by
    change
      (u.map N13GeneralizedMumfordReduction.reduceBase).resultant
          (g.map N13GeneralizedMumfordReduction.reduceBase) =
        N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g)
    simpa only [
      huMonic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase,
      hgMonic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase] using
      Polynomial.resultant_map_map
        (f := u) (g := g)
        (m := u.natDegree) (n := g.natDegree)
        N13GeneralizedMumfordReduction.reduceBase
  have hresultantReduceUnit :
      IsUnit
        (N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g)) := by
    rw [← hresultantMap]
    exact hresultantSpecialUnit
  have hresultantReduceOne :
      N13GeneralizedMumfordReduction.reduceBase
          (u.resultant g) = 1 := by
    let z :=
      N13GeneralizedMumfordReduction.reduceBase
        (u.resultant g)
    have hzFixed : z ^ 2 = z :=
      ZMod.pow_card z
    rcases
        N13GoodModelTwo.fixedTwo_eq_zero_or_one z hzFixed with
      hz | hz
    · exact
        (hresultantReduceUnit.ne_zero hz).elim
    · exact hz
  have hresultantUnit :
      IsUnit (u.resultant g) :=
    N13TwoAdicAbelChartRecover.NearBaseMumford.isUnit_of_reduceBase_eq_one
      hresultantReduceOne
  have hcoprime :
      IsCoprime u g :=
    (Polynomial.isUnit_resultant_iff_isCoprime huMonic).1
      hresultantUnit
  obtain ⟨a', b', hab⟩ := hcoprime
  let E : SmoothMumford₂ :=
    { u := u
      v := v
      w := w
      u_monic := huMonic
      curve_eq := hcurve
      bezout := ⟨a', b', 0, by simpa [g] using hab⟩ }
  refine ⟨E, huDegree, ?_⟩
  exact hIgraph

/-- The strengthened recovery already lands in the two-disk chart.  It also
recovers the original generic sextic graph after coefficient extension, so
no separate representative-existence hypothesis remains after the mapped
special-ideal equality. -/
theorem exists_integral_diskGraph
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ E : SmoothMumford₂,
      ∃ P : N13TwoAdicAbelChartData.DiskPair,
        E.u.natDegree = 2 ∧
        N13CanonicalContractionQuotient.graphIdeal D =
          N13IntegralGraphContraction.sexticIdeal E D.nInf ∧
        N13GeneralizedMumfordIntegral.mumfordIdeal E.u E.v =
          N13GeneralizedMumfordIntegral.mumfordIdeal P.u P.v := by
  obtain ⟨E, hEdeg, hE⟩ :=
    exists_integral_smoothGraph D hdeg hmap
  have hmapE :
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) E.u E.v) =
        N13SpecialQuotientBasis.specialIdeal := by
    rw [← hE]
    exact hmap
  let P :=
    N13AbelCompatibleGraphRecover.recoveredDiskPairOfMappedSpecial
      E hEdeg hmapE
  have hEP :
      N13GeneralizedMumfordIntegral.mumfordIdeal E.u E.v =
        N13GeneralizedMumfordIntegral.mumfordIdeal P.u P.v :=
    N13AbelCompatibleGraphRecover.mumfordIdeal_eq_recoveredDiskPairOfMappedSpecial
      E hEdeg hmapE
  refine ⟨E, P, hEdeg, ?_, hEP⟩
  calc
    N13CanonicalContractionQuotient.graphIdeal D =
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) :=
      (N13IntegralModelContraction.map_contractIdeal
        (N13CanonicalContractionQuotient.graphIdeal D)).symm
    _ =
        Ideal.map
          N13TwoAdicCoordinateBaseChange.integralToSextic
          (N13GeneralizedMumfordIntegral.mumfordIdeal E.u E.v) := by
      rw [hE]
    _ = N13IntegralGraphContraction.sexticIdeal E D.nInf :=
      N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        E D.nInf

/-- A balanced quadratic representative whose canonical contraction has the
selected special graph is represented by an actual pair in the two
distinguished residue disks. -/
theorem exists_diskPair_class_eq
    (D : SexticMumford.Mumford Model)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D.toSemi)) =
        N13SpecialQuotientBasis.specialIdeal) :
    ∃ P : N13TwoAdicAbelChartData.DiskPair,
      SexticMumford.classOf
          Model (N13Infinity.positiveInfinityOrder Q₂) D =
        N13TwoAdicAbelChartPic.DiskPair.pic P := by
  have hdeg : D.u.natDegree = 2 :=
    N13TwoFiberConcreteBasis.degree_eq_two_of_map_contractIdeal_eq_special
      D.toSemi (by simpa using D.deg_u) hmap
  have hnInfNat : D.nInf = 0 := by
    have hbound := D.infinity_bound
    omega
  have hnInf : D.toSemi.nInf = 0 := by
    simp [hnInfNat]
  obtain ⟨E, P, _hEdeg, hgraph, hEP⟩ :=
    exists_integral_diskGraph D.toSemi (by simpa using hdeg) hmap
  have hEPsextic :
      N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi E 0) =
        N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0) := by
    change
      SexticMumford.mumfordIdeal Model
          (N13TwoAdicMumfordTransport.sexticSemi E 0).u
          (N13TwoAdicMumfordTransport.sexticSemi E 0).v =
        SexticMumford.mumfordIdeal Model
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0).u
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0).v
    rw [
      ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        E 0,
      ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
        P.smoothMumford 0]
    exact congrArg
      (Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic)
      hEP
  have hgraphDP :
      N13CanonicalContractionQuotient.graphIdeal D.toSemi =
        N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi := by
    calc
      N13CanonicalContractionQuotient.graphIdeal D.toSemi =
          N13IntegralGraphContraction.sexticIdeal
            E D.toSemi.nInf := hgraph
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi E 0) := by
        rw [hnInf]
        rfl
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicMumfordTransport.sexticSemi
            P.smoothMumford 0) := hEPsextic
      _ = N13CanonicalContractionQuotient.graphIdeal
          (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi := rfl
  refine ⟨P, ?_⟩
  rw [← SexticMumford.semiMumfordClass_toSemi]
  change
    SexticMumford.semiMumfordClass
        Model (N13Infinity.positiveInfinityOrder Q₂) D.toSemi =
      SexticMumford.classOf
        Model (N13Infinity.positiveInfinityOrder Q₂)
          (N13TwoAdicAbelChartPic.DiskPair.mumford P)
  rw [← SexticMumford.semiMumfordClass_toSemi]
  apply semiMumfordClass_eq_of_graphIdeal_eq
    D.toSemi
      (N13TwoAdicAbelChartPic.DiskPair.mumford P).toSemi
      hgraphDP
  simp [hnInfNat]

end

end MazurProof.N13ConcreteGraphRecovery

end
end

-- module FLT.Assumptions.MazurProof.N13FiniteFlatBasisLift
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteFlatBasisLift =====
section

/-!
# Lifting the literal special-fibre basis `{1,x}`

For a finite flat algebra over a local ring, a family whose residue-field
base change is a basis is already a basis over the local ring.  This file
specializes the structural local lifting theorem to the literal family
`{1,x}` needed by the N13 quotient.
-/

open scoped TensorProduct
open Module

namespace MazurProof.N13FiniteFlatBasisLift

noncomputable section

universe uR uB

variable {R : Type uR} {B : Type uB}
variable [CommRing R] [IsLocalRing R]
variable [CommRing B] [Algebra R B]
variable [Module.Finite R B] [Module.Flat R B]


/-- The literal two-element family. -/
def oneX (x : B) : Fin 2 → B :=
  ![1, x]

@[simp] theorem oneX_zero (x : B) :
    oneX x (0 : Fin 2) = 1 := by
  simp [oneX]

@[simp] theorem oneX_one (x : B) :
    oneX x (1 : Fin 2) = x := by
  simp [oneX]

/--
If `{1,x}` becomes a supplied basis after residue-field base change, then
the same literal family is a basis over the local ring.
-/
theorem exists_basis_oneX
    (x : B)
    (b₀ : Basis (Fin 2) (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] B))
    (hb₀ : ∀ i : Fin 2,
      TensorProduct.mk R (IsLocalRing.ResidueField R) B 1 (oneX x i) = b₀ i) :
    ∃ b : Basis (Fin 2) R B,
      (b : Fin 2 → B) = oneX x := by
  have hfamily :
      (TensorProduct.mk R (IsLocalRing.ResidueField R) B 1 ∘ oneX x) =
        (b₀ : Fin 2 → (IsLocalRing.ResidueField R) ⊗[R] B) := by
    funext i
    exact hb₀ i
  have hk :
      Function.Bijective
        (Finsupp.linearCombination (IsLocalRing.ResidueField R)
          (TensorProduct.mk R (IsLocalRing.ResidueField R) B 1 ∘ oneX x)) := by
    rw [hfamily]
    exact
      ⟨b₀.linearIndependent,
        fun y => ⟨b₀.repr y, b₀.linearCombination_repr y⟩⟩
  have hR :
      Function.Bijective
        (Finsupp.linearCombination R (oneX x)) :=
    Module.IsLocalRing.linearCombination_bijective_of_flat
      (R := R) (M := B) (oneX x) hk
  have hspan :
      ⊤ ≤ Submodule.span R (Set.range (oneX x)) := by
    rw [← Finsupp.range_linearCombination]
    exact (LinearMap.range_eq_top.mpr hR.2).ge
  refine ⟨Basis.mk hR.1 hspan, ?_⟩
  exact Basis.coe_mk hR.1 hspan

end

end MazurProof.N13FiniteFlatBasisLift

end
end

-- module FLT.Assumptions.MazurProof.N13GenericQuotientLocalization
section

-- ===== FLT.Assumptions.MazurProof.N13GenericQuotientLocalization =====
section

/-!
# The generic fibre of a canonical N13 contraction

The quotient by a canonical vertical contraction becomes the original
Mumford quotient after inverting the nonzero two-adic scalars.  Consequently,
a contracted quadratic Mumford quotient has rank two over the two-adic
integers.  No preferred integral basis is used.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13GenericQuotientLocalization

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev Q₂ : Type := N13IntegralModelContraction.Q₂
abbrev IntegralRing : Type := N13IntegralModelContraction.IntegralRing
abbrev RationalRing : Type := N13IntegralModelContraction.RationalRing
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13TwoAdicCoordinateBaseChange.integralToSextic.toAlgebra

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

/-- The generic quotient map as a two-adic algebra homomorphism. -/
def genericQuotientAlgHom (J : Ideal RationalRing) :
    (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal J) →ₐ[R₂]
      (RationalRing ⧸ J) where
  toRingHom :=
    N13CanonicalContractionQuotient.genericQuotientMap J
  commutes' r :=
    DFunLike.congr_fun
      (N13CanonicalContractionQuotient.genericQuotientMap_comp_algebraMap J)
      r

/-- The generic quotient map is localization at the nonzero two-adic
scalars. -/
theorem genericQuotient_isLocalized
    (J : Ideal RationalRing) :
    IsLocalizedModule (nonZeroDivisors R₂)
      (genericQuotientAlgHom J).toLinearMap := by
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro s
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hs :
          algebraMap R₂ Q₂ (s : R₂) ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      apply_fun
        (fun z : G ↦
          (algebraMap R₂ Q₂ (s : R₂))⁻¹ • z) at hxy
      simpa [Module.algebraMap_end_apply,
        ← IsScalarTower.algebraMap_smul Q₂, hs] using hxy
    · intro y
      let c : Q₂ := algebraMap R₂ Q₂ (s : R₂)
      have hc : c ≠ 0 := by
        exact
          (IsFractionRing.injective R₂ Q₂).ne
            (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
      refine ⟨c⁻¹ • y, ?_⟩
      change c • (c⁻¹ • y) = y
      exact smul_inv_smul₀ hc y
  · intro y
    obtain ⟨z, rfl⟩ :=
      Ideal.Quotient.mk_surjective y
    obtain ⟨⟨a, s⟩, hz⟩ :=
      IsLocalization.surj
        N13IntegralModelContraction.verticalScalars z
    obtain ⟨r, hr, hs⟩ := s.property
    refine
      ⟨⟨Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a,
          ⟨r, hr⟩⟩,
        ?_⟩
    change
      r • Ideal.Quotient.mk J z =
        N13CanonicalContractionQuotient.genericQuotientMap J
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal J) a)
    rw [N13CanonicalContractionQuotient.genericQuotientMap_mk,
      Algebra.smul_def]
    change
      Ideal.Quotient.mk J
          (algebraMap R₂ RationalRing r * z) =
        Ideal.Quotient.mk J
          (N13TwoAdicCoordinateBaseChange.integralToSextic a)
    apply congrArg (Ideal.Quotient.mk J)
    rw [mul_comm]
    calc
      z * algebraMap R₂ RationalRing r =
          z *
            N13TwoAdicCoordinateBaseChange.integralToSextic
              (s : IntegralRing) := by
        rw [← hs]
        congr 1
        symm
        change
          N13GoodSexticCoordinateEquiv.toSextic
              (N13IntegralModelContraction.integralToGood
                (algebraMap R₂ IntegralRing r)) =
            algebraMap R₂ RationalRing r
        rw [N13IntegralModelContraction.integralToGood_algebraMap,
          N13GoodSexticCoordinateEquiv.toSextic_algebraMap]
        exact
          (IsScalarTower.algebraMap_apply
            R₂ Q₂ RationalRing r).symm
      _ = N13TwoAdicCoordinateBaseChange.integralToSextic a := hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [one_smul]
    exact
      N13CanonicalContractionQuotient.genericQuotientMap_injective J hxy

/-- A quadratic generic Mumford quotient forces its canonical contracted
quotient to have rank two over the two-adic integers. -/
theorem contractQuotient_finrank_eq_two
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2) :
    Module.finrank R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (SexticMumford.mumfordIdeal Model D.u D.v)) =
      2 := by
  let J : Ideal RationalRing :=
    SexticMumford.mumfordIdeal Model D.u D.v
  let B :=
    IntegralRing ⧸
      N13IntegralModelContraction.contractIdeal J
  let G := RationalRing ⧸ J
  let q : B →ₗ[R₂] G :=
    (genericQuotientAlgHom J).toLinearMap
  letI : IsLocalizedModule (nonZeroDivisors R₂) q :=
    genericQuotient_isLocalized J
  have hloc :
      Module.finrank R₂ G =
        Module.finrank R₂ B :=
    IsLocalizedModule.finrank_eq
      (nonZeroDivisors R₂) q le_rfl
  have hrank :
      Module.rank Q₂ G =
        Module.rank R₂ G :=
    IsLocalization.rank_eq
      Q₂ (nonZeroDivisors R₂) le_rfl
  have hfield :
      Module.finrank Q₂ G =
        Module.finrank R₂ G := by
    simpa only [Module.finrank] using
      congrArg Cardinal.toNat hrank
  have hgeneric :
      Module.finrank Q₂ G = 2 := by
    rw [Module.finrank_eq_card_basis
      (SexticMumfordQuotientBasis.quotientBasis
        Model D hdeg)]
    rfl
  change Module.finrank R₂ B = 2
  calc
    Module.finrank R₂ B =
        Module.finrank R₂ G := hloc.symm
    _ = Module.finrank Q₂ G := hfield.symm
    _ = 2 := hgeneric

end

end MazurProof.N13GenericQuotientLocalization

end
end

-- module FLT.Assumptions.MazurProof.N13TwoGeneratorFiberBasis
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoGeneratorFiberBasis =====
section

/-!
# A two-generator basis dichotomy in dimension two

The special N13 affine coordinate ring, and every one of its quotients, is
generated by the literal coordinates `x` and `y`.  In a two-dimensional
quotient over a field, this implies structurally that either `{1,x}` or
`{1,y}` is a basis.
-/

open Module
open Polynomial

namespace MazurProof.N13TwoGeneratorFiberBasis

noncomputable section

universe uK uB

variable {K : Type uK} {B : Type uB}
variable [Field K] [CommRing B] [Algebra K B] [Nontrivial B]

/-- If a two-dimensional algebra is generated by `x` and `y`, then one of
`{1,x}` and `{1,y}` is linearly independent. -/
theorem oneX_or_oneY_linearIndependent
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    LinearIndependent K ![1, x] ∨
      LinearIndependent K ![1, y] := by
  by_contra h
  have hxNot : ¬ LinearIndependent K ![1, x] :=
    fun hx ↦ h (Or.inl hx)
  have hyNot : ¬ LinearIndependent K ![1, y] :=
    fun hy ↦ h (Or.inr hy)
  have hx :
      ∃ a : K, algebraMap K B a = x := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hxNot
    push Not at hxNot
    obtain ⟨a, ha⟩ := hxNot
    exact ⟨a, by simpa [Algebra.smul_def] using ha⟩
  have hy :
      ∃ b : K, algebraMap K B b = y := by
    rw [LinearIndependent.pair_iff'
      (one_ne_zero : (1 : B) ≠ 0)] at hyNot
    push Not at hyNot
    obtain ⟨b, hb⟩ := hyNot
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hbot : (⊥ : Subalgebra K B) = ⊤ := by
    apply top_unique
    rw [← hgen, Algebra.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  have hsurj : Function.Surjective (algebraMap K B) := by
    intro z
    have hz : z ∈ (⊥ : Subalgebra K B) := by
      rw [hbot]
      trivial
    simpa only [Algebra.mem_bot, Set.mem_range] using hz
  have hbij :
      Function.Bijective (algebraMap K B) :=
    ⟨FaithfulSMul.algebraMap_injective K B, hsurj⟩
  have hrank :
      Module.finrank K B = 1 :=
    Module.finrank_of_bijective_algebraMap hbij
  omega

/-- Basis-valued form of `oneX_or_oneY_linearIndependent`. -/
theorem exists_basis_oneX_or_oneY
    (x y : B)
    (hfinrank : Module.finrank K B = 2)
    (hgen : Algebra.adjoin K ({x, y} : Set B) = ⊤) :
    (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, x]) ∨
      (∃ b : Basis (Fin 2) K B, (b : Fin 2 → B) = ![1, y]) := by
  rcases oneX_or_oneY_linearIndependent x y hfinrank hgen with hx | hy
  · left
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hx (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩
  · right
    let b : Basis (Fin 2) K B :=
      basisOfLinearIndependentOfCardEqFinrank hy (by simp [hfinrank])
    exact ⟨b, by simp [b]⟩

abbrev SpecialField : Type := N13GoodCoordinateRingTwo.K
abbrev SpecialRing : Type :=
  N13GoodCoordinateRingTwo.CoordinateRing

/-- Every polynomial in the special `x` coordinate lies in the subalgebra
generated by the literal `x` and `y` coordinates. -/
theorem xClass_mem_coordinateAdjoin
    (p : SpecialField[X]) :
    N13GoodCoordinateRingTwo.xClass p ∈
      Algebra.adjoin SpecialField
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) := by
  let S : Subalgebra SpecialField SpecialRing :=
    Algebra.adjoin SpecialField
      ({N13GoodCoordinateRingTwo.xClass X,
        N13GoodCoordinateRingTwo.yClass} :
        Set SpecialRing)
  change N13GoodCoordinateRingTwo.xClass p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [N13GoodCoordinateRingTwo.xClass_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial,
        N13GoodCoordinateRingTwo.xClass_mul,
        N13GoodCoordinateRingTwo.xClass_pow]
      apply S.mul_mem
      · change algebraMap SpecialField SpecialRing a ∈ S
        exact S.algebraMap_mem a
      · exact S.pow_mem
          (Algebra.subset_adjoin
            (Set.mem_insert
              (N13GoodCoordinateRingTwo.xClass X)
              {N13GoodCoordinateRingTwo.yClass}))
          n

/-- The special affine coordinate ring is generated by its literal
coordinates. -/
theorem coordinate_adjoin_eq_top :
    Algebra.adjoin SpecialField
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) =
      ⊤ := by
  apply Algebra.eq_top_iff.2
  intro z
  obtain ⟨p, rfl⟩ :=
    AdjoinRoot.mk_surjective z
  let S : Subalgebra SpecialField SpecialRing :=
    Algebra.adjoin SpecialField
      ({N13GoodCoordinateRingTwo.xClass X,
        N13GoodCoordinateRingTwo.yClass} :
        Set SpecialRing)
  change N13GoodCoordinateRingTwo.mk p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      change
        N13GoodCoordinateRingTwo.xClass a *
            N13GoodCoordinateRingTwo.yClass ^ n ∈ S
      apply S.mul_mem
      · exact xClass_mem_coordinateAdjoin a
      · exact S.pow_mem
          (Algebra.subset_adjoin
            (Set.mem_insert_iff.mpr
              (Or.inr
                (Set.mem_singleton
                  N13GoodCoordinateRingTwo.yClass))))
          n

/-- Every quotient of the special affine coordinate ring is still generated
by the images of its literal coordinates. -/
theorem quotient_coordinate_adjoin_eq_top
    (I : Ideal SpecialRing) :
    Algebra.adjoin SpecialField
        ({Ideal.Quotient.mk I
            (N13GoodCoordinateRingTwo.xClass X),
          Ideal.Quotient.mk I
            N13GoodCoordinateRingTwo.yClass} :
          Set (SpecialRing ⧸ I)) =
      ⊤ := by
  let π : SpecialRing →ₐ[SpecialField] SpecialRing ⧸ I :=
    Ideal.Quotient.mkₐ SpecialField I
  rw [show
    ({Ideal.Quotient.mk I
        (N13GoodCoordinateRingTwo.xClass X),
      Ideal.Quotient.mk I
        N13GoodCoordinateRingTwo.yClass} :
      Set (SpecialRing ⧸ I)) =
      π ''
        ({N13GoodCoordinateRingTwo.xClass X,
          N13GoodCoordinateRingTwo.yClass} :
          Set SpecialRing) by
    exact
      (Set.image_pair π
        (N13GoodCoordinateRingTwo.xClass X)
        N13GoodCoordinateRingTwo.yClass).symm]
  rw [← AlgHom.map_adjoin, coordinate_adjoin_eq_top,
    Algebra.map_top, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective

end

end MazurProof.N13TwoGeneratorFiberBasis

end
end

-- module FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis
section

-- ===== FLT.Assumptions.MazurProof.N13ContractQuotientXYBasis =====
section

open Module
open Polynomial
open scoped TensorProduct

/-!
# Coordinate bases for finite quadratic contractions

For a finite canonical contraction of a quadratic N13 Mumford quotient,
the special fibre is a two-dimensional algebra generated by the literal
coordinates `x` and `y`.  Thus either `{1,x}` or `{1,y}` is a basis on the
special fibre.  Finite flat lifting gives the same literal alternative
over the two-adic integers.
-/

namespace MazurProof.N13ContractQuotientXYBasis

noncomputable section

universe uF uK uA uι

theorem exists_basis_restrictScalars_of_surjective
    {F : Type uF} {K : Type uK} {A : Type uA} {ι : Type uι}
    [Field F] [Field K] [CommRing A]
    [Algebra F K] [Algebra F A] [Algebra K A]
    [IsScalarTower F K A] [Fintype ι]
    (hFK : Function.Surjective (algebraMap F K))
    (b : Basis ι K A) :
    ∃ bF : Basis ι F A, (bF : ι → A) = b := by
  have hli :
      LinearIndependent F (b : ι → A) :=
    b.linearIndependent.restrict_scalars' F
  have hspan :
      ⊤ ≤ Submodule.span F (Set.range (b : ι → A)) := by
    intro z _
    rw [← b.sum_repr z]
    apply Submodule.sum_mem
    intro i _
    obtain ⟨a, ha⟩ := hFK (b.repr z i)
    rw [← ha, IsScalarTower.algebraMap_smul K]
    exact
      Submodule.smul_mem _ a
        (Submodule.subset_span (Set.mem_range_self i))
  let bF : Basis ι F A :=
    Basis.mk hli hspan
  exact ⟨bF, Basis.coe_mk hli hspan⟩

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev Q₂ : Type := N13IntegralModelContraction.Q₂
abbrev k : Type := N13GoodCoordinateRingTwo.K
abbrev κ : Type := IsLocalRing.ResidueField R₂
abbrev IntegralRing : Type := N13IntegralModelContraction.IntegralRing
abbrev RationalRing : Type := N13IntegralModelContraction.RationalRing
abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing
abbrev Model : SexticMumford.Model Q₂ :=
  N13GoodSexticCoordinateEquiv.M (K := Q₂)

local instance baseSpecialAlgebra : Algebra R₂ k :=
  N13GeneralizedMumfordReduction.reduceBase.toAlgebra

def integralY : IntegralRing :=
  N13GeneralizedMumfordIntegral.yClass (R := R₂)

theorem specialQuotientMap_comp_algebraMap
    (I : Ideal IntegralRing)
    (J : Ideal SpecialRing)
    (hmap :
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate I =
        J) :
    (N13QuotientReduction.reduceCoordinateQuotient
        I J hmap).comp
        (algebraMap R₂ (IntegralRing ⧸ I)) =
      (algebraMap k (SpecialRing ⧸ J)).comp
        (algebraMap R₂ k) := by
  ext r
  change
    Ideal.Quotient.mk J
        (N13GeneralizedMumfordReduction.reduceCoordinate
          (algebraMap R₂ IntegralRing r)) =
      Ideal.Quotient.mk J
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

theorem exists_contractQuotient_basis_oneX_or_oneY
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))) :
    (∃ b : Basis (Fin 2) R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)),
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            N13CanonicalContractionQuotient.integralX)) ∨
      (∃ b : Basis (Fin 2) R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)),
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            integralY)) := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let J : Ideal SpecialRing :=
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate I
  let B := IntegralRing ⧸ I
  let C := SpecialRing ⧸ J
  let g : B →+* C :=
    N13QuotientReduction.reduceCoordinateQuotient I J rfl
  letI : Module.Finite R₂ B := hfinite
  letI : Module.Flat R₂ B :=
    N13QuotientVerticalFlatness.contractQuotient_flat
      (N13CanonicalContractionQuotient.graphIdeal D)
  letI : Module.Free R₂ B :=
    Module.free_of_flat_of_isLocalRing
  letI : IsScalarTower R₂ k C :=
    IsScalarTower.of_algebraMap_eq
      (R := R₂) (S := k) (A := C) fun _ => rfl
  have hfactor :
      g.comp (algebraMap R₂ B) =
        (algebraMap k C).comp (algebraMap R₂ k) := by
    exact specialQuotientMap_comp_algebraMap I J rfl
  have hg : Function.Surjective g :=
    N13QuotientReduction.reduceCoordinateQuotient_surjective
      I J rfl
  have hker :
      RingHom.ker g =
        Ideal.span ({algebraMap R₂ B (2 : R₂)} : Set B) :=
    N13QuotientReduction.ker_reduceCoordinateQuotient_eq_span_two
      I J rfl
  let eK : k ⊗[R₂] B ≃ₗ[k] C :=
    N13TensorSpecialFiber.tensorLinearEquiv
      (g := g)
      (hfactor := hfactor)
      (hq := ZMod.ringHom_surjective PadicInt.toZMod)
      (π := (2 : R₂))
      (hπ := N13GeneralizedMumfordReduction.reduceBase_two)
      (hg := hg)
      (hker := hker)
  have hfinB : Module.finrank R₂ B = 2 := by
    exact
      N13GenericQuotientLocalization.contractQuotient_finrank_eq_two
        D hdeg
  have hfinC : Module.finrank k C = 2 := by
    rw [← eK.finrank_eq, Module.finrank_baseChange, hfinB]
  letI : Nontrivial C :=
    Module.nontrivial_of_finrank_pos
      (R := k) (M := C) (by rw [hfinC]; decide)
  let xB : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  let yB : B :=
    Ideal.Quotient.mk I integralY
  let xC : C :=
    Ideal.Quotient.mk J
      (N13GoodCoordinateRingTwo.xClass X)
  let yC : C :=
    Ideal.Quotient.mk J
      N13GoodCoordinateRingTwo.yClass
  have hgen :
      Algebra.adjoin k ({xC, yC} : Set C) = ⊤ := by
    exact
      N13TwoGeneratorFiberBasis.quotient_coordinate_adjoin_eq_top J
  have hexC :=
    N13TwoGeneratorFiberBasis.exists_basis_oneX_or_oneY
      xC yC hfinC hgen
  have hfactorκ :
      g.comp (algebraMap R₂ B) =
        (algebraMap κ C).comp (IsLocalRing.residue R₂) := by
    ext r
    calc
      g (algebraMap R₂ B r) =
          algebraMap k C (algebraMap R₂ k r) := by
        simpa only [RingHom.comp_apply] using
          DFunLike.congr_fun hfactor r
      _ = algebraMap R₂ C r :=
        (IsScalarTower.algebraMap_apply R₂ k C r).symm
      _ = algebraMap κ C (algebraMap R₂ κ r) :=
        IsScalarTower.algebraMap_apply R₂ κ C r
      _ = algebraMap κ C
          (IsLocalRing.residue R₂ r) := by
        rfl
  have htwo :
      (2 : R₂) ∈ IsLocalRing.maximalIdeal R₂ := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (Set.mem_singleton (2 : R₂))
  let eκ : κ ⊗[R₂] B ≃ₗ[κ] C :=
    N13TensorSpecialFiber.residueLinearEquiv
      g hfactorκ (2 : R₂) htwo hg hker
  have eκ_tmul_one (b : B) :
      eκ (TensorProduct.mk R₂ κ B 1 b) = g b := by
    change
      (N13TensorSpecialFiber.residueLinearEquiv
        g hfactorκ (2 : R₂) htwo hg hker)
          ((1 : κ) ⊗ₜ[R₂] b) = g b
    simpa only [one_smul] using
      (N13TensorSpecialFiber.residueLinearEquiv_tmul
        (g := g) (hfactor := hfactorκ)
        (π := (2 : R₂))
        (hπ := htwo)
        (hg := hg) (hker := hker)
        (1 : κ) b)
  have hκk :
      Function.Surjective (algebraMap κ k) := by
    intro a
    obtain ⟨r, hr⟩ :=
      ZMod.ringHom_surjective PadicInt.toZMod a
    refine ⟨IsLocalRing.residue R₂ r, ?_⟩
    calc
      algebraMap κ k (IsLocalRing.residue R₂ r) =
          algebraMap R₂ k r := by
        exact
          (IsScalarTower.algebraMap_apply R₂ κ k r).symm
      _ = a := hr
  have ex_map :
      g xB = xC := by
    change
      N13QuotientReduction.reduceCoordinateQuotient I J rfl
          (Ideal.Quotient.mk I
            N13CanonicalContractionQuotient.integralX) =
        xC
    rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
      N13CanonicalContractionQuotient.integralX,
      N13GeneralizedMumfordReduction.reduce_xClass]
    simp [xC, N13GeneralizedMumfordReduction.reducePoly,
      N13GeneralizedMumfordReduction.reduceBase]
  have ey_map :
      g yB = yC := by
    change
      N13QuotientReduction.reduceCoordinateQuotient I J rfl
          (Ideal.Quotient.mk I integralY) =
        yC
    rw [N13QuotientReduction.reduceCoordinateQuotient_mk,
      integralY,
      N13GeneralizedMumfordReduction.reduce_yClass]
  rcases hexC with ⟨bC, hbC⟩ | ⟨bC, hbC⟩
  · left
    obtain ⟨bCκ, hbCκ⟩ :=
      exists_basis_restrictScalars_of_surjective hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX xB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, ex_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX xB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX xB) bCκ heval i
    simpa [I, B, xB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) xB b₀ hb₀
  · right
    obtain ⟨bCκ, hbCκ⟩ :=
      exists_basis_restrictScalars_of_surjective hκk bC
    let b₀ : Basis (Fin 2) κ (κ ⊗[R₂] B) :=
      N13TensorSpecialFiber.pullbackBasis eκ bCκ
    have heval (i : Fin 2) :
        eκ (TensorProduct.mk R₂ κ B 1
          (N13FiniteFlatBasisLift.oneX yB i)) =
          bCκ i := by
      rw [eκ_tmul_one]
      fin_cases i
      · simpa [N13FiniteFlatBasisLift.oneX] using
          (congrFun hbC (0 : Fin 2)).symm.trans
            (congrFun hbCκ (0 : Fin 2)).symm
      · simpa [N13FiniteFlatBasisLift.oneX, ey_map] using
          (congrFun hbC (1 : Fin 2)).symm.trans
            (congrFun hbCκ (1 : Fin 2)).symm
    have hb₀ (i : Fin 2) :
        TensorProduct.mk R₂ κ B 1
            (N13FiniteFlatBasisLift.oneX yB i) =
          b₀ i :=
      N13TensorSpecialFiber.mk_eq_pullbackBasis
        eκ (N13FiniteFlatBasisLift.oneX yB) bCκ heval i
    simpa [I, B, yB] using
      N13FiniteFlatBasisLift.exists_basis_oneX
        (R := R₂) (B := B) yB b₀ hb₀

end

end MazurProof.N13ContractQuotientXYBasis

end
end

-- module FLT.Assumptions.MazurProof.N13IntegralGraphJacobian
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphJacobian =====
section

/-!
# Integral N13 graph ideals and the affine Jacobian

This file instantiates the generic graph-Jacobian dual frame for the good
integral N13 equation.  A short resultant certificate proves that the two
relative Jacobian rows generate one globally, so every integral Mumford
graph ideal is invertible.  No fixed special graph or point classification
is used.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13IntegralGraphJacobian

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralFractionalHull.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

abbrev SemiMumford₂ : Type :=
  N13GeneralizedMumfordIntegral.SemiMumford
    (R := R₂)

local instance integralRingDomain :
    IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

open N13GeneralizedMumfordIntegral

/-- The relative `Y`-Jacobian row of
`Y² + h(X)Y - rhs(X)`. -/
def jacobianY : IntegralRing :=
  2 * yClass +
    xClass (hPoly (R := R₂))

/-- The relative `X`-Jacobian row of
`Y² + h(X)Y - rhs(X)`. -/
def jacobianX : IntegralRing :=
  xClass (derivative (hPoly (R := R₂))) *
      yClass -
    xClass (derivative (rhsPoly (R := R₂)))

theorem derivative_hPoly_explicit :
    derivative (hPoly (R := R₂)) =
      (3 : R₂[X]) * X ^ 2 + 1 := by
  simp [hPoly, derivative_add, derivative_pow]
  exact map_natCast C 3

theorem derivative_rhsPoly_explicit :
    derivative (rhsPoly (R := R₂)) =
      (5 : R₂[X]) * X ^ 4 +
        (4 : R₂[X]) * X ^ 3 := by
  simp [rhsPoly, derivative_add, derivative_pow]
  congr 1

theorem derivative_curve_eq
    (D : SemiMumford₂) :
    (C (2 : R₂) * D.v + hPoly) *
          derivative D.v +
          derivative hPoly * D.v -
        derivative rhsPoly =
      derivative D.u * D.w +
        D.u * derivative D.w := by
  have h := congrArg derivative D.curve_eq
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow] at h
  norm_num only [Nat.reduceSub, pow_one] at h
  linear_combination h

/-- The `Y`-Jacobian row is the sum of the graph function and its
hyperelliptic conjugate. -/
theorem jacobianY_eq_graph_add_conjugate
    (D : SemiMumford₂) :
    jacobianY =
      ySubClass D.v +
        ySubClass (conjugateV D.v) := by
  simp only [jacobianY, ySubClass, conjugateV,
    xClass_neg, xClass_sub]
  ring

/-- Differentiating the integral Mumford equation decomposes the
`X`-Jacobian row along the two graph generators. -/
theorem jacobianX_eq_graph_decomposition
    (D : SemiMumford₂) :
    jacobianX =
      xClass (derivative D.u) * xClass D.w +
        xClass D.u * xClass (derivative D.w) -
        xClass (derivative D.v) *
          ySubClass (conjugateV D.v) +
        (xClass (derivative hPoly) +
            xClass (derivative D.v)) *
          ySubClass D.v := by
  have h :=
    congrArg
      (xClass (R := R₂))
      (derivative_curve_eq D)
  have htwo :
      xClass (R := R₂) (C (2 : R₂)) =
        (2 : IntegralRing) := by
    rw [show C (2 : R₂) = (2 : R₂[X]) by
      exact map_natCast C 2]
    exact xClass_natCast 2
  simp only [jacobianX, ySubClass, conjugateV,
    xClass_add, xClass_sub, xClass_neg,
    xClass_mul] at h ⊢
  rw [htwo] at h
  linear_combination h

/-- The first coordinate-ring coefficient of the Jacobian Bézout
certificate. -/
def bezoutA : IntegralRing :=
  (30 * xClass X ^ 5 + 97 * xClass X ^ 4 +
      92 * xClass X ^ 3 + 50 * xClass X + 31) +
    (10 * xClass X ^ 2 + 30 * xClass X - 3) *
      yClass

/-- The second coordinate-ring coefficient of the Jacobian Bézout
certificate. -/
def bezoutB : IntegralRing :=
  (63 * xClass X ^ 5 + 153 * xClass X ^ 4 +
      98 * xClass X ^ 3 + 13 * xClass X ^ 2 -
      13 * xClass X + 13) +
    (60 * xClass X ^ 4 + 151 * xClass X ^ 3 +
      151 * xClass X ^ 2 - 63 * xClass X + 60) *
      yClass

/-- The integral resultant certificate for the two relative Jacobian
rows.  It comes from the univariate Euclidean identity between
`h² + 4 * rhs` and `h' * h + 2 * rhs'`; its right-hand side is the
optimal odd scalar `13`. -/
theorem scaled_jacobian_bezout :
    bezoutA * jacobianX + bezoutB * jacobianY =
      (13 : IntegralRing) := by
  have hcurve :=
    yClass_relation (R := R₂)
  simp only [jacobianX, derivative_hPoly_explicit,
    derivative_rhsPoly_explicit, xClass_add,
    xClass_mul, xClass_pow]
  have h3 :
      xClass (R := R₂) (3 : R₂[X]) =
        (3 : IntegralRing) :=
    xClass_natCast 3
  have h4 :
      xClass (R := R₂) (4 : R₂[X]) =
        (4 : IntegralRing) :=
    xClass_natCast 4
  have h5 :
      xClass (R := R₂) (5 : R₂[X]) =
        (5 : IntegralRing) :=
    xClass_natCast 5
  rw [h3, h4, h5]
  simp [bezoutA, bezoutB, jacobianY,
    hPoly, rhsPoly] at hcurve ⊢
  linear_combination
    (150 * xClass (R := R₂) X ^ 4 +
      392 * xClass (R := R₂) X ^ 3 +
      303 * xClass (R := R₂) X ^ 2 -
      96 * xClass (R := R₂) X + 117) * hcurve

/-- The odd resultant scalar in the Jacobian certificate is a unit in the
integral coordinate ring. -/
theorem thirteen_isUnit :
    IsUnit (13 : IntegralRing) := by
  have h : IsUnit (13 : R₂) := by
    rw [PadicInt.isUnit_iff]
    exact
      PadicInt.norm_natCast_eq_one_iff.mpr
        (by norm_num)
  convert h.map (algebraMap R₂ IntegralRing) using 1
  exact
    (map_natCast (algebraMap R₂ IntegralRing) 13).symm

/-- The two relative Jacobian rows generate the unit ideal globally over
the integral N13 model. -/
theorem exists_jacobian_bezout :
    ∃ a b : IntegralRing,
      a * jacobianX + b * jacobianY = 1 := by
  let u : IntegralRingˣ :=
    thirteen_isUnit.unit
  refine
    ⟨(u⁻¹ : IntegralRingˣ) * bezoutA,
      (u⁻¹ : IntegralRingˣ) * bezoutB, ?_⟩
  calc
    (((u⁻¹ : IntegralRingˣ) : IntegralRing) *
            bezoutA) * jacobianX +
          (((u⁻¹ : IntegralRingˣ) : IntegralRing) *
            bezoutB) * jacobianY =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) *
          (bezoutA * jacobianX +
            bezoutB * jacobianY) := by ring
    _ =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) * 13 := by
      rw [scaled_jacobian_bezout]
    _ =
        ((u⁻¹ : IntegralRingˣ) : IntegralRing) *
          (u : IntegralRing) := by
      rw [thirteen_isUnit.unit_spec]
    _ = 1 := by simp

/-! ## Graphs without a monicity hypothesis

Monicity is needed by the quotient-basis and contraction arguments, but not
by the Jacobian dual frame.  The following version isolates the exact
regularity input here: the horizontal graph equation is merely nonzero.
-/

abbrev GraphData : Type :=
  GeneralizedGraphIdealCore.SemiGraph
    (hPoly (R := R₂)) (rhsPoly (R := R₂))

theorem derivative_graphData_curve_eq
    (D : GraphData) :
    (C (2 : R₂) * D.v + hPoly) *
          derivative D.v +
          derivative hPoly * D.v -
        derivative rhsPoly =
      derivative D.u * D.w +
        D.u * derivative D.w := by
  have h := congrArg derivative D.curve_eq
  simp only [derivative_sub, derivative_add,
    derivative_mul, derivative_pow] at h
  norm_num only [Nat.reduceSub, pow_one] at h
  linear_combination h

theorem jacobianY_eq_graphData
    (D : GraphData) :
    jacobianY =
      GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v +
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV hPoly D.v) := by
  simp only [jacobianY, GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    xClassHom_apply, xClass_neg, xClass_sub]
  ring

theorem jacobianX_eq_graphData
    (D : GraphData) :
    jacobianX =
      xClass (derivative D.u) * xClass D.w +
        xClass D.u * xClass (derivative D.w) -
        xClass (derivative D.v) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass
              (GeneralizedGraphIdealCore.conjugateV hPoly D.v) +
        (xClass (derivative hPoly) +
            xClass (derivative D.v)) *
          GeneralizedGraphIdealCore.ySubClass
            xClassHom yClass D.v := by
  have h :=
    congrArg
      (xClass (R := R₂))
      (derivative_graphData_curve_eq D)
  have htwo :
      xClass (R := R₂) (C (2 : R₂)) =
        (2 : IntegralRing) := by
    rw [show C (2 : R₂) = (2 : R₂[X]) by
      exact map_natCast C 2]
    exact xClass_natCast 2
  simp only [jacobianX,
    GeneralizedGraphIdealCore.ySubClass,
    GeneralizedGraphIdealCore.conjugateV,
    xClassHom_apply, xClass_add, xClass_sub, xClass_neg,
    xClass_mul] at h ⊢
  rw [htwo] at h
  linear_combination h

/-- Every nondegenerate integral polynomial graph on the affine good model
is invertible.  Its horizontal equation need not be monic. -/
theorem graphIdeal_isUnit
    (D : GraphData)
    (hu : D.u ≠ 0) :
    IsUnit
      ((GeneralizedGraphIdealCore.graphIdeal
          xClassHom yClass D.u D.v :
          Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ := exists_jacobian_bezout
  apply
    GraphJacobianDualFrame.graphJacobian_isUnit
      (K := FunctionField)
      (U := xClass D.u)
      (G :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass D.v)
      (Gbar :=
        GeneralizedGraphIdealCore.ySubClass
          xClassHom yClass
            (GeneralizedGraphIdealCore.conjugateV hPoly D.v))
      (W := xClass D.w)
      (Fy := jacobianY)
      (Fx := jacobianX)
      (Ux := xClass (derivative D.u))
      (Wx := xClass (derivative D.w))
      (Vx := xClass (derivative D.v))
      (hx := xClass (derivative hPoly))
      (a := a) (b := b)
  · intro hzero
    apply hu
    have hcoeff :=
      congrArg (coeff0 (R := R₂)) hzero
    simpa only [coeff0_xClass, map_zero] using hcoeff
  · exact
      GeneralizedGraphIdealCore.ySubClass_mul_conjugate
        xClassHom yClass hPoly rhsPoly D
        (yClass_relation (R := R₂))
  · exact jacobianY_eq_graphData D
  · exact jacobianX_eq_graphData D
  · exact hBez

/-- A global relative-Jacobian Bézout pair makes every integral smooth
Mumford graph invertible by the explicit graph dual frame. -/
theorem mumfordIdeal_isUnit_of_jacobianBezout
    (D : SemiMumford₂)
    (a b : IntegralRing)
    (hBez :
      a * jacobianX + b * jacobianY = 1) :
    IsUnit
      ((mumfordIdeal D.u D.v :
          Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  apply
    GraphJacobianDualFrame.graphJacobian_isUnit
      (K := FunctionField)
      (U := xClass D.u)
      (G := ySubClass D.v)
      (Gbar := ySubClass (conjugateV D.v))
      (W := xClass D.w)
      (Fy := jacobianY)
      (Fx := jacobianX)
      (Ux := xClass (derivative D.u))
      (Wx := xClass (derivative D.w))
      (Vx := xClass (derivative D.v))
      (hx := xClass (derivative hPoly))
      (a := a) (b := b)
  · intro hzero
    apply D.u_monic.ne_zero
    have hcoeff :=
      congrArg (coeff0 (R := R₂)) hzero
    simpa only [coeff0_xClass, map_zero] using hcoeff
  · exact ySubClass_mul_conjugate D
  · exact jacobianY_eq_graph_add_conjugate D
  · exact jacobianX_eq_graph_decomposition D
  · exact hBez

/-- Every integral N13 Mumford graph ideal is invertible.  The proof is
the explicit graph dual frame together with the global Jacobian
certificate above. -/
theorem mumfordIdeal_isUnit
    (D : SemiMumford₂) :
    IsUnit
      ((mumfordIdeal D.u D.v :
          Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  obtain ⟨a, b, hBez⟩ :=
    exists_jacobian_bezout
  exact
    mumfordIdeal_isUnit_of_jacobianBezout
      D a b hBez

end

end MazurProof.N13IntegralGraphJacobian

end
end

-- module FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery
section

-- ===== FLT.Assumptions.MazurProof.N13RankTwoSemiGraphRecovery =====
section

/-!
# Recovering an integral semigraph from a rank-two quotient basis

The graph-recovery algebra does not need a selected special divisor until
one asks for a particular vertical smoothness certificate.  A literal
integral quotient basis `{1,x}` already recovers a monic quadratic
generalized Mumford semigraph and identifies its graph ideal with the
canonical contraction.

This is the special-class-independent core needed for arbitrary proper
specialization.
-/

open Module
open Polynomial

namespace MazurProof.N13RankTwoSemiGraphRecovery

noncomputable section

abbrev R₂ : Type :=
  N13ConcreteGraphRecovery.R₂

abbrev IntegralRing : Type :=
  N13ConcreteGraphRecovery.IntegralRing

abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13ConcreteGraphRecovery.Model

abbrev SemiMumford₂ : Type :=
  N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂

/-- A quotient basis `{1,x}` recovers the canonical contraction as a
literal integral monic quadratic graph ideal. -/
theorem exists_integral_semiGraph_of_basis
    (D : SexticMumford.SemiMumford Model)
    (b : Basis (Fin 2) R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D)))
    (hb :
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13TwoFiberNoEscape.pairFamily
          1
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            N13CanonicalContractionQuotient.integralX)) :
    ∃ E : SemiMumford₂,
      E.u.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) E.u E.v := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let xbar : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  let ybar : B :=
    Ideal.Quotient.mk I
      N13ConcreteGraphRecovery.integralY
  have hb0 : b 0 = 1 := by
    have h := congrFun hb (0 : Fin 2)
    simpa [N13TwoFiberNoEscape.pairFamily] using h
  have hb1 : b 1 = xbar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13TwoFiberNoEscape.pairFamily, xbar, I] using h
  letI : Module.Free R₂ B :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ B :=
    Module.Finite.of_basis b
  letI : Nontrivial B :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, hy⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
      xbar ybar b hb0 hb1
  let u : R₂[X] :=
    (Algebra.lmul R₂ B xbar).charpoly
  let v : R₂[X] :=
    C a + C c * X
  have huMonic : u.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x xbar
  have huDegree : u.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
      xbar b hb0 hb1
  have hker :
      RingHom.ker
          ((aeval xbar : R₂[X] →ₐ[R₂] B).toRingHom) =
        Ideal.span ({u} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
        xbar b hb0 hb1
  have hyv : ybar = aeval xbar v := by
    calc
      ybar =
          algebraMap R₂ B a +
            algebraMap R₂ B c * xbar := hy
      _ = aeval xbar v := by
        simp [v]
  have hI :=
    N13RankTwoIdealRecovery.ideal_eq_span_aeval_y_sub
      (R := R₂)
      N13CanonicalContractionQuotient.integralX
      N13ConcreteGraphRecovery.integralY I u v
      N13ConcreteGraphRecovery.integral_rankTwoPolynomialNormalForm
      hker hyv
  have hIgraph :
      I =
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    simpa [N13GeneralizedMumfordIntegral.mumfordIdeal,
      N13GeneralizedMumfordIntegral.ySubClass,
      N13ConcreteGraphRecovery.integralY,
      N13ConcreteGraphRecovery.aeval_integralX] using hI
  let residual : R₂[X] :=
    v ^ 2 +
      N13GeneralizedMumfordIntegral.hPoly (R := R₂) * v -
      N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)
  have hresGraph :
      N13GeneralizedMumfordIntegral.xClass (R := R₂) residual ∈
        N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := R₂) u v := by
    have hyMem :
        N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v ∈
          N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v :=
      N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u v
    have hprod :
        N13GeneralizedMumfordIntegral.ySubClass (R := R₂) v *
            N13GeneralizedMumfordIntegral.ySubClass
              (R := R₂)
              (N13GeneralizedMumfordIntegral.conjugateV v) ∈
          N13GeneralizedMumfordIntegral.mumfordIdeal
            (R := R₂) u v :=
      Ideal.mul_mem_right _ _ hyMem
    rw [N13GeneralizedMumfordIntegral.ySubClass_mul_conjugateV_raw]
      at hprod
    have hneg :=
      (N13GeneralizedMumfordIntegral.mumfordIdeal
        (R := R₂) u v).neg_mem hprod
    simpa [residual] using hneg
  have hresI :
      N13GeneralizedMumfordIntegral.xClass (R := R₂) residual ∈ I := by
    rw [hIgraph]
    exact hresGraph
  have hresEval :
      aeval xbar residual = 0 := by
    rw [N13ConcreteGraphRecovery.quotient_aeval_integralX]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hresI
  have hresKer :
      residual ∈
        RingHom.ker
          ((aeval xbar : R₂[X] →ₐ[R₂] B).toRingHom) :=
    RingHom.mem_ker.mpr hresEval
  rw [hker, Ideal.mem_span_singleton] at hresKer
  obtain ⟨w, hw⟩ := hresKer
  have hcurve :
      v ^ 2 +
          N13GeneralizedMumfordIntegral.hPoly (R := R₂) * v -
        N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) =
          u * w := by
    simpa [residual] using hw
  let E : SemiMumford₂ :=
    { u := u
      v := v
      w := w
      u_monic := huMonic
      curve_eq := hcurve }
  refine ⟨E, huDegree, ?_⟩
  exact hIgraph

end

end MazurProof.N13RankTwoSemiGraphRecovery

end
end

-- module FLT.Assumptions.MazurProof.N13RankTwoVerticalIdealRecovery
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13RankTwoVerticalIdealRecovery =====
section

open Polynomial

/-!
# Recovering a vertical graph from a rank-two quotient

If a quotient has basis `{1,y}`, multiplication by `y` supplies its monic
quadratic relation, while `x` is linear in `y`.  This file gives the
ideal-correspondence argument recovering the ambient ideal as
`(m(y), x-s(y))`.
-/

namespace MazurProof.N13RankTwoVerticalIdealRecovery

noncomputable section

universe uR uA

variable {R : Type uR} {A : Type uA}
variable [CommRing R] [CommRing A] [Algebra R A]

def HasVerticalPolynomialNormalForm
    (y x : A) (s : R[X]) : Prop :=
  ∀ z : A, ∃ p : R[X], ∃ q : A,
    z = aeval y p + q * (x - aeval y s)

theorem verticalNormalForm_of_rankTwoPolynomialNormalForm
    (x y : A)
    (hnormal :
      N13RankTwoIdealRecovery.HasRankTwoPolynomialNormalForm
        (R := R) x y)
    (s : R[X]) :
    HasVerticalPolynomialNormalForm (R := R) y x s := by
  intro z
  obtain ⟨p, q, hz⟩ := hnormal z
  obtain ⟨cp, hcp⟩ :=
    sub_dvd_eval_sub x (aeval y s)
      (p.map (algebraMap R A))
  obtain ⟨cq, hcq⟩ :=
    sub_dvd_eval_sub x (aeval y s)
      (q.map (algebraMap R A))
  refine
    ⟨p.comp s + (q.comp s) * X,
      cp + cq * y, ?_⟩
  have hp :
      aeval x p - aeval y (p.comp s) =
        (x - aeval y s) * cp := by
    simpa [aeval_def, aeval_comp] using hcp
  have hq :
      aeval x q - aeval y (q.comp s) =
        (x - aeval y s) * cq := by
    simpa [aeval_def, aeval_comp] using hcq
  calc
    z =
        aeval x p + aeval x q * y := hz
    _ =
        aeval y (p.comp s + (q.comp s) * X) +
          (cp + cq * y) * (x - aeval y s) := by
      simp only [map_add, map_mul, aeval_X]
      linear_combination hp + hq * y

theorem ideal_eq_span_vertical
    (y x : A)
    (I : Ideal A)
    (m s : R[X])
    (hnormal :
      HasVerticalPolynomialNormalForm (R := R) y x s)
    (hker :
      RingHom.ker
          ((aeval (Ideal.Quotient.mk I y) :
              R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({m} : Set R[X]))
    (hx :
      Ideal.Quotient.mk I x =
        aeval (Ideal.Quotient.mk I y) s) :
    I =
      Ideal.span
        ({aeval y m, x - aeval y s} : Set A) := by
  let π : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  have hker' :
      RingHom.ker
          ((aeval (π y) : R[X] →ₐ[R] A ⧸ I).toRingHom) =
        Ideal.span ({m} : Set R[X]) := by
    simpa [π] using hker
  have hx' : π x = aeval (π y) s := by
    simpa [π] using hx
  have hgraphZero :
      π (x - aeval y s) = 0 := by
    calc
      π (x - aeval y s) =
          π x - π (aeval y s) := map_sub π _ _
      _ = π x - aeval (π y) s := by
        rw [← Polynomial.aeval_algHom_apply π y s]
      _ = 0 := by rw [hx', sub_self]
  apply le_antisymm
  · intro z hz
    obtain ⟨p, q, hform⟩ := hnormal z
    have hz0 : π z = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
    have hp0 : aeval (π y) p = 0 := by
      calc
        aeval (π y) p =
            π (aeval y p) := by
          rw [Polynomial.aeval_algHom_apply]
        _ =
            π (aeval y p) +
              π q * π (x - aeval y s) := by
          rw [hgraphZero, mul_zero, add_zero]
        _ =
            π (aeval y p +
              q * (x - aeval y s)) := by
          rw [map_add, map_mul]
        _ = π z := by rw [← hform]
        _ = 0 := hz0
    have hpSpan :
        p ∈ Ideal.span ({m} : Set R[X]) := by
      rw [← hker']
      exact RingHom.mem_ker.mpr hp0
    obtain ⟨w, hw⟩ :=
      Ideal.mem_span_singleton.mp hpSpan
    refine
      (Ideal.mem_span_pair).2
        ⟨aeval y w, q, ?_⟩
    calc
      aeval y w * aeval y m +
          q * (x - aeval y s) =
        aeval y (m * w) +
          q * (x - aeval y s) := by
        simp only [map_mul]
        ring
      _ =
        aeval y p +
          q * (x - aeval y s) := by rw [← hw]
      _ = z := hform.symm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hmKer :
          m ∈
            RingHom.ker
              ((aeval (π y) :
                  R[X] →ₐ[R] A ⧸ I).toRingHom) := by
        rw [hker']
        exact Ideal.mem_span_singleton_self m
      have hzero : π (aeval y m) = 0 := by
        calc
          π (aeval y m) =
              aeval (π y) m :=
            (Polynomial.aeval_algHom_apply π y m).symm
          _ = 0 := RingHom.mem_ker.mp hmKer
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa [π] using hzero)
    · exact Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa [π] using hgraphZero)

end

end MazurProof.N13RankTwoVerticalIdealRecovery

end
end

-- module FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery
section

-- ===== FLT.Assumptions.MazurProof.N13RankTwoVerticalGraphRecovery =====
section

open Module
open Polynomial

/-!
# Vertical graph recovery from a `{1,y}` basis

A rank-two quotient basis `{1,y}` recovers a monic quadratic relation
`m(y)` and a linear equation `x=a+cy`.  Substituting the latter into the
integral curve equation shows that the vertical curve polynomial factors
as `m*w`.
-/

namespace MazurProof.N13RankTwoVerticalGraphRecovery

noncomputable section

abbrev R₂ : Type := N13ConcreteGraphRecovery.R₂
abbrev IntegralRing : Type :=
  N13ConcreteGraphRecovery.IntegralRing
abbrev Model : SexticMumford.Model
    N13IntegralModelContraction.Q₂ :=
  N13ConcreteGraphRecovery.Model

def verticalCurve (s : R₂[X]) : R₂[X] :=
  X ^ 2 +
    (N13GeneralizedMumfordIntegral.hPoly (R := R₂)).comp s * X -
    (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)).comp s

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
structure VerticalGraph where
  m : R₂[X]
  a : R₂
  c : R₂
  w : R₂[X]
  m_monic : m.Monic
  curve_eq :
    verticalCurve (C a + C c * X) = m * w

namespace VerticalGraph

def s (E : VerticalGraph) : R₂[X] :=
  C E.a + C E.c * X

def ideal (E : VerticalGraph) : Ideal IntegralRing :=
  Ideal.span
    ({aeval N13ConcreteGraphRecovery.integralY E.m,
      N13CanonicalContractionQuotient.integralX -
        aeval N13ConcreteGraphRecovery.integralY E.s} :
      Set IntegralRing)

end VerticalGraph

theorem exists_verticalGraph_of_basis
    (D : SexticMumford.SemiMumford Model)
    (b : Basis (Fin 2) R₂
      (IntegralRing ⧸
        N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D)))
    (hb :
      (b : Fin 2 →
        IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D)) =
        N13FiniteFlatBasisLift.oneX
          (Ideal.Quotient.mk
            (N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D))
            N13ConcreteGraphRecovery.integralY)) :
    ∃ E : VerticalGraph,
      E.m.natDegree = 2 ∧
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) =
        E.ideal := by
  let I :=
    N13IntegralModelContraction.contractIdeal
      (N13CanonicalContractionQuotient.graphIdeal D)
  let B := IntegralRing ⧸ I
  let xbar : B :=
    Ideal.Quotient.mk I
      N13CanonicalContractionQuotient.integralX
  let ybar : B :=
    Ideal.Quotient.mk I
      N13ConcreteGraphRecovery.integralY
  have hb0 : b 0 = 1 := by
    have h := congrFun hb (0 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX] using h
  have hb1 : b 1 = ybar := by
    have h := congrFun hb (1 : Fin 2)
    simpa [N13FiniteFlatBasisLift.oneX, ybar, I] using h
  letI : Module.Free R₂ B :=
    Module.Free.of_basis b
  letI : Module.Finite R₂ B :=
    Module.Finite.of_basis b
  letI : Nontrivial B :=
    ⟨⟨1, 0, by
      rw [← hb0]
      exact b.ne_zero 0⟩⟩
  obtain ⟨a, c, hx⟩ :=
    N13RankTwoQuotientAlgebra.exists_eq_algebraMap_add_algebraMap_mul
      ybar xbar b hb0 hb1
  let m : R₂[X] :=
    (Algebra.lmul R₂ B ybar).charpoly
  let s : R₂[X] :=
    C a + C c * X
  have hmMonic : m.Monic :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_monic_of_one_x ybar
  have hmDegree : m.natDegree = 2 :=
    N13RankTwoQuotientAlgebra.charpoly_lmul_natDegree_of_one_x
      ybar b hb0 hb1
  have hker :
      RingHom.ker
          ((aeval ybar : R₂[X] →ₐ[R₂] B).toRingHom) =
        Ideal.span ({m} : Set R₂[X]) := by
    exact
      N13RankTwoQuotientAlgebra.ker_aeval_eq_span_charpoly_of_one_x
        ybar b hb0 hb1
  have hxs : xbar = aeval ybar s := by
    calc
      xbar =
          algebraMap R₂ B a +
            algebraMap R₂ B c * ybar := hx
      _ = aeval ybar s := by simp [s]
  have hnormal :
      N13RankTwoVerticalIdealRecovery.HasVerticalPolynomialNormalForm
        (R := R₂)
        N13ConcreteGraphRecovery.integralY
        N13CanonicalContractionQuotient.integralX s :=
    N13RankTwoVerticalIdealRecovery.verticalNormalForm_of_rankTwoPolynomialNormalForm
      N13CanonicalContractionQuotient.integralX
      N13ConcreteGraphRecovery.integralY
      N13ConcreteGraphRecovery.integral_rankTwoPolynomialNormalForm
      s
  have hI :=
    N13RankTwoVerticalIdealRecovery.ideal_eq_span_vertical
      (R := R₂)
      N13ConcreteGraphRecovery.integralY
      N13CanonicalContractionQuotient.integralX
      I m s hnormal hker hxs
  have hverticalEval :
      aeval ybar (verticalCurve s) = 0 := by
    simp only [verticalCurve, map_sub, map_add, map_mul,
      map_pow, aeval_X, aeval_comp]
    rw [← hxs,
      N13ConcreteGraphRecovery.quotient_aeval_integralX,
      N13ConcreteGraphRecovery.quotient_aeval_integralX]
    change
      Ideal.Quotient.mk I
          (N13ConcreteGraphRecovery.integralY ^ 2) +
        Ideal.Quotient.mk I
            (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) *
          Ideal.Quotient.mk I
            N13ConcreteGraphRecovery.integralY -
        Ideal.Quotient.mk I
          (N13GeneralizedMumfordIntegral.xClass
            (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) =
        0
    have hcurve :=
      N13GeneralizedMumfordIntegral.yClass_relation (R := R₂)
    have hcurveQ :
        Ideal.Quotient.mk I
              ((N13GeneralizedMumfordIntegral.yClass (R := R₂)) ^ 2) +
            Ideal.Quotient.mk I
                (N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.hPoly (R := R₂))) *
              Ideal.Quotient.mk I
                (N13GeneralizedMumfordIntegral.yClass (R := R₂)) =
          Ideal.Quotient.mk I
            (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂))) := by
      simpa only [map_add, map_mul] using
        congrArg (Ideal.Quotient.mk I) hcurve
    exact sub_eq_zero.mpr
      (by
        simpa only [N13ConcreteGraphRecovery.integralY] using
          hcurveQ)
  have hverticalKer :
      verticalCurve s ∈
        RingHom.ker
          ((aeval ybar : R₂[X] →ₐ[R₂] B).toRingHom) :=
    RingHom.mem_ker.mpr hverticalEval
  rw [hker, Ideal.mem_span_singleton] at hverticalKer
  obtain ⟨w, hw⟩ := hverticalKer
  have hcurve :
      verticalCurve s = m * w := hw
  let E : VerticalGraph :=
    { m := m
      a := a
      c := c
      w := w
      m_monic := hmMonic
      curve_eq := by simpa [s] using hcurve }
  refine ⟨E, hmDegree, ?_⟩
  simpa [VerticalGraph.ideal, VerticalGraph.s, E, s] using hI

end

end MazurProof.N13RankTwoVerticalGraphRecovery

end
end

-- module FLT.Assumptions.MazurProof.N13VerticalGraphJacobian
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13VerticalGraphJacobian =====
section

open Polynomial
open scoped nonZeroDivisors

/-!
# The vertical graph Jacobian frame for the N13 integral model

A rank-two contraction with basis `{1, y}` is a vertical graph `x = s(y)`.
Dividing the curve equation by `x - s(y)` supplies the complementary factor.
Together with the differentiated vertical relation, these two factors express both
Jacobian rows in the graph frame. The global Jacobian Bezout identity then makes
the recovered graph ideal invertible.
-/

namespace MazurProof.N13VerticalGraphJacobian

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralGraphJacobian.R₂
abbrev IntegralRing : Type :=
  N13IntegralGraphJacobian.IntegralRing
abbrev RationalRing : Type :=
  N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type :=
  N13IntegralGraphJacobian.FunctionField
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
abbrev VerticalGraph : Type :=
  N13RankTwoVerticalGraphRecovery.VerticalGraph

local instance integralRingDomain :
    IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

open N13GeneralizedMumfordIntegral
open N13RankTwoVerticalGraphRecovery

def curveInX : IntegralRing[X] :=
  C (N13ConcreteGraphRecovery.integralY ^ 2) +
    (hPoly (R := R₂)).map (algebraMap R₂ IntegralRing) *
      C N13ConcreteGraphRecovery.integralY -
    (rhsPoly (R := R₂)).map (algebraMap R₂ IntegralRing)

def sValue (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.s

def U (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.m

def G (E : VerticalGraph) : IntegralRing :=
  N13CanonicalContractionQuotient.integralX - sValue E

def W (E : VerticalGraph) : IntegralRing :=
  aeval N13ConcreteGraphRecovery.integralY E.w

def complementPoly (E : VerticalGraph) : IntegralRing[X] :=
  curveInX /ₘ (X - C (sValue E))

def H (E : VerticalGraph) : IntegralRing :=
  (complementPoly E).eval
    N13CanonicalContractionQuotient.integralX

def Hx (E : VerticalGraph) : IntegralRing :=
  (derivative (complementPoly E)).eval
    N13CanonicalContractionQuotient.integralX

def fyPoly : IntegralRing[X] :=
  C (2 * N13ConcreteGraphRecovery.integralY) +
    (hPoly (R := R₂)).map (algebraMap R₂ IntegralRing)

theorem algebraMap_eq_xClass_C (r : R₂) :
    algebraMap R₂ IntegralRing r =
      xClass (R := R₂) (C r) := by
  rfl

theorem curveInX_eval_integralX :
    curveInX.eval
        N13CanonicalContractionQuotient.integralX =
      0 := by
  simp only [curveInX, eval_sub, eval_add, eval_mul,
    eval_C, eval_map]
  change
    N13ConcreteGraphRecovery.integralY ^ 2 +
        aeval N13CanonicalContractionQuotient.integralX
            (hPoly (R := R₂)) *
          N13ConcreteGraphRecovery.integralY -
      aeval N13CanonicalContractionQuotient.integralX
        (rhsPoly (R := R₂)) = 0
  rw [N13ConcreteGraphRecovery.aeval_integralX,
    N13ConcreteGraphRecovery.aeval_integralX]
  exact sub_eq_zero.mpr
    (by
      simpa only [N13ConcreteGraphRecovery.integralY] using
        (N13GeneralizedMumfordIntegral.yClass_relation
          (R := R₂)))

theorem curveInX_eval_sValue
    (E : VerticalGraph) :
    curveInX.eval (sValue E) = U E * W E := by
  have hcurve := congrArg
    (aeval N13ConcreteGraphRecovery.integralY) E.curve_eq
  simp only [verticalCurve, map_sub, map_add, map_mul,
    map_pow, aeval_X, aeval_comp] at hcurve
  have hs :
      sValue E =
        algebraMap R₂ IntegralRing E.a +
          algebraMap R₂ IntegralRing E.c *
            N13ConcreteGraphRecovery.integralY := by
    simp [sValue, VerticalGraph.s]
  rw [hs]
  simp only [curveInX, eval_sub, eval_add, eval_mul,
    eval_C, eval_map]
  change
    N13ConcreteGraphRecovery.integralY ^ 2 +
          aeval
              (algebraMap R₂ IntegralRing E.a +
                algebraMap R₂ IntegralRing E.c *
                  N13ConcreteGraphRecovery.integralY)
              (hPoly (R := R₂)) *
            N13ConcreteGraphRecovery.integralY -
        aeval
            (algebraMap R₂ IntegralRing E.a +
              algebraMap R₂ IntegralRing E.c *
                N13ConcreteGraphRecovery.integralY)
            (rhsPoly (R := R₂)) =
      U E * W E
  simpa only [U, W, Polynomial.aeval_C] using hcurve

theorem G_mul_H
    (E : VerticalGraph) :
    G E * H E = -(U E * W E) := by
  have hdiv :=
    X_sub_C_mul_divByMonic_eq_sub_modByMonic
      curveInX (sValue E)
  rw [modByMonic_X_sub_C_eq_C_eval] at hdiv
  have heval := congrArg
    (fun p : IntegralRing[X] =>
      p.eval N13CanonicalContractionQuotient.integralX) hdiv
  simp only [eval_mul, eval_sub, eval_X, eval_C] at heval
  rw [curveInX_eval_integralX, curveInX_eval_sValue E,
    zero_sub] at heval
  simpa [G, H, complementPoly] using heval

theorem jacobianX_decomposition
    (E : VerticalGraph) :
    N13IntegralGraphJacobian.jacobianX =
      U E * 0 + G E * Hx E + H E * 1 + W E * 0 := by
  have hder :=
    divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      curveInX (sValue E)
  have heval := congrArg
    (fun p : IntegralRing[X] =>
      p.eval N13CanonicalContractionQuotient.integralX) hder
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C]
    at heval
  have hcurveDerivative :
      (derivative curveInX).eval
          N13CanonicalContractionQuotient.integralX =
        N13IntegralGraphJacobian.jacobianX := by
    simp only [curveInX, derivative_add, derivative_sub,
      derivative_mul, derivative_C, zero_add,
      derivative_map, eval_sub, eval_mul,
      eval_map, eval_C, mul_zero, add_zero]
    change
      aeval N13CanonicalContractionQuotient.integralX
          (derivative (hPoly (R := R₂))) *
            N13ConcreteGraphRecovery.integralY -
          aeval N13CanonicalContractionQuotient.integralX
            (derivative (rhsPoly (R := R₂))) =
        N13IntegralGraphJacobian.jacobianX
    rw [N13ConcreteGraphRecovery.aeval_integralX,
      N13ConcreteGraphRecovery.aeval_integralX]
    rfl
  rw [hcurveDerivative] at heval
  calc
    N13IntegralGraphJacobian.jacobianX =
        H E + G E * Hx E := by
      simpa [G, H, Hx, complementPoly] using heval.symm
    _ = U E * 0 + G E * Hx E + H E * 1 + W E * 0 := by
      ring

theorem derivative_verticalCurve_linear
    (a c : R₂) :
    derivative (verticalCurve (C a + C c * X)) =
      C c *
          (((derivative (hPoly (R := R₂))).comp
              (C a + C c * X)) * X -
            (derivative (rhsPoly (R := R₂))).comp
              (C a + C c * X)) +
        (C 2 * X +
          (hPoly (R := R₂)).comp (C a + C c * X)) := by
  simp only [verticalCurve, derivative_sub, derivative_add,
    derivative_mul, derivative_pow, derivative_X,
    derivative_comp, derivative_C, zero_add, zero_mul]
  ring

theorem derivative_curveInX_eval
    (z : IntegralRing) :
    (derivative curveInX).eval z =
      aeval z (derivative (hPoly (R := R₂))) *
          N13ConcreteGraphRecovery.integralY -
        aeval z (derivative (rhsPoly (R := R₂))) := by
  simp only [curveInX, derivative_sub, derivative_add,
    derivative_mul, derivative_C, zero_add,
    derivative_map, eval_sub, eval_mul, eval_map,
    eval_C, mul_zero, add_zero]
  rfl

theorem fyPoly_eval
    (z : IntegralRing) :
    fyPoly.eval z =
      2 * N13ConcreteGraphRecovery.integralY +
        aeval z (hPoly (R := R₂)) := by
  simp [fyPoly, eval_add, eval_C, eval_map]
  rfl

theorem fyPoly_eval_integralX :
    fyPoly.eval
        N13CanonicalContractionQuotient.integralX =
      N13IntegralGraphJacobian.jacobianY := by
  rw [fyPoly_eval,
    N13ConcreteGraphRecovery.aeval_integralX]
  rfl

theorem totalDerivative_at_s
    (E : VerticalGraph) :
    algebraMap R₂ IntegralRing E.c *
          (derivative curveInX).eval (sValue E) +
        fyPoly.eval (sValue E) =
      U E *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.w) +
        W E *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.m) := by
  have hder := congrArg derivative E.curve_eq
  rw [derivative_verticalCurve_linear] at hder
  have heval := congrArg
    (aeval N13ConcreteGraphRecovery.integralY) hder
  simp only [derivative_mul, map_add, map_sub, map_mul,
    aeval_X, aeval_comp, Polynomial.aeval_C] at heval
  rw [derivative_curveInX_eval, fyPoly_eval]
  have hs :
      sValue E =
        algebraMap R₂ IntegralRing E.a +
          algebraMap R₂ IntegralRing E.c *
            N13ConcreteGraphRecovery.integralY := by
    simp [sValue, VerticalGraph.s]
  rw [hs]
  norm_num only [map_ofNat] at heval
  change
    algebraMap R₂ IntegralRing E.c *
          (aeval
                (algebraMap R₂ IntegralRing E.a +
                  algebraMap R₂ IntegralRing E.c *
                    N13ConcreteGraphRecovery.integralY)
                (derivative (hPoly (R := R₂))) *
              N13ConcreteGraphRecovery.integralY -
            aeval
                (algebraMap R₂ IntegralRing E.a +
                  algebraMap R₂ IntegralRing E.c *
                    N13ConcreteGraphRecovery.integralY)
                (derivative (rhsPoly (R := R₂)))) +
        (2 * N13ConcreteGraphRecovery.integralY +
          aeval
              (algebraMap R₂ IntegralRing E.a +
                algebraMap R₂ IntegralRing E.c *
                  N13ConcreteGraphRecovery.integralY)
              (hPoly (R := R₂))) =
      aeval N13ConcreteGraphRecovery.integralY E.m *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.w) +
        aeval N13ConcreteGraphRecovery.integralY E.w *
          aeval N13ConcreteGraphRecovery.integralY
            (derivative E.m)
  linear_combination heval

theorem complement_eval_s_eq_derivative
    (E : VerticalGraph) :
    (complementPoly E).eval (sValue E) =
      (derivative curveInX).eval (sValue E) := by
  have hder :=
    divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      curveInX (sValue E)
  have heval := congrArg
    (fun p : IntegralRing[X] => p.eval (sValue E)) hder
  simpa [complementPoly] using heval

theorem exists_jacobianY_decomposition
    (E : VerticalGraph) :
    ∃ β : IntegralRing,
      N13IntegralGraphJacobian.jacobianY =
        U E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.w) +
          G E * β +
          H E * (-algebraMap R₂ IntegralRing E.c) +
          W E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.m) := by
  obtain ⟨qFy, hqFy⟩ :=
    sub_dvd_eval_sub
      N13CanonicalContractionQuotient.integralX
      (sValue E) fyPoly
  obtain ⟨qH, hqH⟩ :=
    sub_dvd_eval_sub
      N13CanonicalContractionQuotient.integralX
      (sValue E) (complementPoly E)
  have hqFy' :
      N13IntegralGraphJacobian.jacobianY -
          fyPoly.eval (sValue E) =
        G E * qFy := by
    simpa [G, fyPoly_eval_integralX] using hqFy
  have hqH' :
      H E - (complementPoly E).eval (sValue E) =
        G E * qH := by
    simpa [G, H] using hqH
  have hHs :=
    complement_eval_s_eq_derivative E
  have htotal :=
    totalDerivative_at_s E
  refine
    ⟨qFy + algebraMap R₂ IntegralRing E.c * qH, ?_⟩
  linear_combination
    hqFy' + htotal +
      algebraMap R₂ IntegralRing E.c * hHs +
      algebraMap R₂ IntegralRing E.c * hqH'

theorem verticalIdeal_isUnit
    (E : VerticalGraph) :
    IsUnit
      ((E.ideal : Ideal IntegralRing) :
        IntegralFractionalIdeal) := by
  obtain ⟨β, hFy⟩ :=
    exists_jacobianY_decomposition E
  obtain ⟨a, b, hBez⟩ :=
    N13IntegralGraphJacobian.exists_jacobian_bezout
  have hGne : G E ≠ 0 := by
    intro hzero
    have hcoeff :=
      congrArg
        (N13GeneralizedMumfordIntegral.coeff0 (R := R₂))
        hzero
    simp only [G, sValue, VerticalGraph.s, map_add, map_mul,
      Polynomial.aeval_C, aeval_X] at hcoeff
    rw [algebraMap_eq_xClass_C E.a,
      algebraMap_eq_xClass_C E.c] at hcoeff
    simp only [map_sub, map_zero] at hcoeff
    have hcoeffOne :=
      congrArg (fun p : R₂[X] => p.coeff 1) hcoeff
    simpa [G, sValue, VerticalGraph.s,
      N13CanonicalContractionQuotient.integralX,
      N13ConcreteGraphRecovery.integralY] using hcoeffOne
  have hrelation :
      U E * W E = -(G E * H E) := by
    have h := G_mul_H E
    linear_combination h
  have hFx :
      N13IntegralGraphJacobian.jacobianX =
        G E * Hx E + U E * 0 + W E * 0 + H E * 1 := by
    have h := jacobianX_decomposition E
    linear_combination h
  have hFy' :
      N13IntegralGraphJacobian.jacobianY =
        G E * β +
          U E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.w) +
          W E *
            aeval N13ConcreteGraphRecovery.integralY
              (derivative E.m) +
          H E * (-algebraMap R₂ IntegralRing E.c) := by
    have h := hFy
    linear_combination h
  have hunit :=
    GraphJacobianDecompositionFrame.graphJacobian_isUnit_of_decompositions
      (K := FunctionField)
      (U := G E) (G := U E) (H := W E) (W := H E)
      (Fx := N13IntegralGraphJacobian.jacobianX)
      (Fy := N13IntegralGraphJacobian.jacobianY)
      (αx := Hx E) (βx := 0) (γx := 0) (δx := 1)
      (αy := β)
      (βy :=
        aeval N13ConcreteGraphRecovery.integralY
          (derivative E.w))
      (γy :=
        aeval N13ConcreteGraphRecovery.integralY
          (derivative E.m))
      (δy := -algebraMap R₂ IntegralRing E.c)
      (a := a) (b := b)
      hGne hrelation hFx hFy' hBez
  have hideal :
      E.ideal = Ideal.span ({G E, U E} : Set IntegralRing) := by
    apply congrArg Ideal.span
    ext z
    simp [U, G, sValue, or_comm]
  rw [hideal]
  exact hunit

end

end MazurProof.N13VerticalGraphJacobian

end
end

-- module FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteContractIdealInvertible =====
section

open Module
open Polynomial
open scoped nonZeroDivisors

/-!
# Invertibility of finite quadratic N13 contractions

A finite quadratic contraction admits a literal integral basis `{1,x}` or
`{1,y}`.  The first basis recovers a horizontal integral semigraph; the
second recovers a vertical graph.  The two structural Jacobian frames prove
invertibility in the respective cases.
-/

namespace MazurProof.N13FiniteContractIdealInvertible

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev R₂ : Type := N13IntegralModelContraction.R₂
abbrev IntegralRing : Type := N13IntegralModelContraction.IntegralRing
abbrev RationalRing : Type := N13IntegralFractionalHull.RationalRing
abbrev FunctionField : Type := N13IntegralGraphJacobian.FunctionField
abbrev IntegralFractionalIdeal : Type :=
  N13IntegralGraphJacobian.IntegralFractionalIdeal
abbrev Model : SexticMumford.Model N13IntegralModelContraction.Q₂ :=
  N13GoodSexticCoordinateEquiv.M

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

theorem contractIdeal_isUnit_of_finite_quadratic
    (D : SexticMumford.SemiMumford Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite R₂
        (IntegralRing ⧸
          N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal D))) :
    IsUnit
      ((N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal D) :
          Ideal IntegralRing) : IntegralFractionalIdeal) := by
  rcases
      N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
        D hdeg hfinite with hx | hy
  · obtain ⟨b, hb⟩ := hx
    have hb' :
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
      simpa [N13FiniteFlatBasisLift.oneX,
        N13TwoFiberNoEscape.pairFamily] using hb
    obtain ⟨E, _, hI⟩ :=
      N13RankTwoSemiGraphRecovery.exists_integral_semiGraph_of_basis
        D b hb'
    rw [hI]
    exact N13IntegralGraphJacobian.mumfordIdeal_isUnit E
  · obtain ⟨b, hb⟩ := hy
    have hb' :
        (b : Fin 2 →
          IntegralRing ⧸
            N13IntegralModelContraction.contractIdeal
              (N13CanonicalContractionQuotient.graphIdeal D)) =
          N13FiniteFlatBasisLift.oneX
            (Ideal.Quotient.mk
              (N13IntegralModelContraction.contractIdeal
                (N13CanonicalContractionQuotient.graphIdeal D))
              N13ConcreteGraphRecovery.integralY) := by
      simpa [N13ContractQuotientXYBasis.integralY,
        N13ConcreteGraphRecovery.integralY] using hb
    obtain ⟨E, _, hI⟩ :=
      N13RankTwoVerticalGraphRecovery.exists_verticalGraph_of_basis
        D b hb'
    rw [hI]
    exact N13VerticalGraphJacobian.verticalIdeal_isUnit E

end

end MazurProof.N13FiniteContractIdealInvertible

end
end


