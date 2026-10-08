-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianUnitSquareclasses_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianUnitSquareclasses_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:18:40.062467+00:00
-- url     : https://prove2.me/theorems/0c581412-7118-4d76-9054-3f7fe750122f
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianUnitSquareclasses source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianUnitSquareclasses

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianUnitSquareclasses
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianSignature_p0
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Tactic

set_option autoImplicit false




/-!
# Unit squareclasses in the N13 field

Dirichlet's theorem decomposes the unit group as finite cyclic torsion
times a free abelian group of rank two.  Squaring has index two on the
torsion factor and index `2^2` on the free factor, so the N13 unit
squareclass group has exactly eight elements.  No units are enumerated.
-/

open Finset Module

noncomputable section

namespace MazurProof.UnitSquareClass

/-- Transporting the range of the square map across a multiplicative
equivalence. -/
private theorem map_powTwo_range_equiv
    {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) :
    ((powMonoidHom 2 : G →* G).range).map
        e.toMonoidHom =
      (powMonoidHom 2 : H →* H).range := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz⟩, rfl⟩
    refine ⟨e z, ?_⟩
    change z ^ 2 = x at hz
    change (e z) ^ 2 = e x
    simpa only [map_pow] using congrArg e hz
  · rintro ⟨z, hz⟩
    refine ⟨(e.symm z) ^ 2, ⟨e.symm z, rfl⟩, ?_⟩
    change z ^ 2 = y at hz
    change e ((e.symm z) ^ 2) = y
    rw [map_pow, e.apply_symm_apply, hz]

/-- The square-map index is invariant under multiplicative equivalence. -/
private theorem index_powTwo_range_equiv
    {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) :
    (powMonoidHom 2 : G →* G).range.index =
      (powMonoidHom 2 : H →* H).range.index := by
  calc
    (powMonoidHom 2 : G →* G).range.index =
        (((powMonoidHom 2 : G →* G).range).map
          e.toMonoidHom).index :=
      (Subgroup.index_map_equiv
        (H := (powMonoidHom 2 : G →* G).range) e).symm
    _ = (powMonoidHom 2 : H →* H).range.index := by
      rw [map_powTwo_range_equiv e]

/-- The range of squaring on a product is the product of the two ranges. -/
private theorem powTwo_range_prod
    (A B : Type*) [CommGroup A] [CommGroup B] :
    (powMonoidHom 2 : A × B →* A × B).range =
      ((powMonoidHom 2 : A →* A).range).prod
        (powMonoidHom 2 : B →* B).range := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), ?_⟩
    exact Prod.ext ha hb

private theorem index_powTwo_range_cyclic
    (C : Type*) [CommGroup C] [Finite C] [IsCyclic C] :
    (powMonoidHom 2 : C →* C).range.index =
      (Nat.card C).gcd 2 :=
  IsCyclic.index_powMonoidHom_range C 2

private theorem index_powTwo_range_multiplicative
    (F : Type*) [AddCommGroup F]
    [Module.Free ℤ F] [Module.Finite ℤ F] :
    (powMonoidHom 2 :
        Multiplicative F →* Multiplicative F).range.index =
      2 ^ Module.finrank ℤ F := by
  rw [← Subgroup.index_toAddSubgroup]
  rw [← MonoidHom.coe_toAdditive_range]
  change
    (nsmulAddMonoidHom (α := F) 2).range.index =
      2 ^ Module.finrank ℤ F
  exact AddSubgroup.index_range_nsmul F 2

/-- Exact square-map index for a finite cyclic factor times a finite free
abelian factor. -/
theorem index_powTwo_range_eq_gcd_mul_pow
    {G C F : Type*}
    [CommGroup G]
    [CommGroup C] [Finite C] [IsCyclic C]
    [AddCommGroup F]
    [Module.Free ℤ F] [Module.Finite ℤ F]
    (e : G ≃* C × Multiplicative F) :
    (powMonoidHom 2 : G →* G).range.index =
      (Nat.card C).gcd 2 *
        2 ^ Module.finrank ℤ F := by
  calc
    (powMonoidHom 2 : G →* G).range.index =
        (powMonoidHom 2 :
          C × Multiplicative F →*
            C × Multiplicative F).range.index :=
      index_powTwo_range_equiv e
    _ = (((powMonoidHom 2 : C →* C).range).prod
          (powMonoidHom 2 :
            Multiplicative F →*
              Multiplicative F).range).index := by
      rw [powTwo_range_prod]
    _ = (powMonoidHom 2 : C →* C).range.index *
          (powMonoidHom 2 :
            Multiplicative F →*
              Multiplicative F).range.index := by
      rw [Subgroup.index_prod]
    _ = (Nat.card C).gcd 2 *
          2 ^ Module.finrank ℤ F := by
      rw [index_powTwo_range_cyclic,
        index_powTwo_range_multiplicative]

/-- Even torsion contributes one additional binary squareclass. -/
theorem index_powTwo_range_eq_pow_succ_of_even
    {G C F : Type*}
    [CommGroup G]
    [CommGroup C] [Finite C] [IsCyclic C]
    [AddCommGroup F]
    [Module.Free ℤ F] [Module.Finite ℤ F]
    (e : G ≃* C × Multiplicative F)
    (hC : Even (Nat.card C)) :
    (powMonoidHom 2 : G →* G).range.index =
      2 ^ (Module.finrank ℤ F + 1) := by
  rw [index_powTwo_range_eq_gcd_mul_pow e,
    Nat.gcd_eq_right_iff_dvd.mpr hC.two_dvd]
  simp [pow_succ']

end MazurProof.UnitSquareClass

namespace NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def dirichletCoordinatesHom :
    torsion K ×
        Multiplicative (Fin (rank K) → ℤ) →*
      (NumberField.RingOfIntegers K)ˣ where
  toFun z :=
    (z.1 : (NumberField.RingOfIntegers K)ˣ) *
      ∏ i, (fundSystem K i) ^ (z.2.toAdd i)
  map_one' := by
    simp
  map_mul' := by
    rintro ⟨ζ, a⟩ ⟨ξ, b⟩
    change
      ((ζ : (NumberField.RingOfIntegers K)ˣ) *
          (ξ : (NumberField.RingOfIntegers K)ˣ)) *
          ∏ i, (fundSystem K i) ^
            (a.toAdd i + b.toAdd i) =
        ((ζ : (NumberField.RingOfIntegers K)ˣ) *
            ∏ i, (fundSystem K i) ^
              (a.toAdd i)) *
          ((ξ : (NumberField.RingOfIntegers K)ˣ) *
            ∏ i, (fundSystem K i) ^
              (b.toAdd i))
    simp_rw [zpow_add, Finset.prod_mul_distrib]
    ac_rfl

private theorem dirichletCoordinatesHom_surjective :
    Function.Surjective (dirichletCoordinatesHom K) := by
  intro x
  obtain ⟨⟨ζ, f⟩, hx, _⟩ :=
    exist_unique_eq_mul_prod K x
  refine ⟨⟨ζ, Multiplicative.ofAdd f⟩, ?_⟩
  simpa [dirichletCoordinatesHom] using hx.symm

private theorem dirichletCoordinatesHom_injective :
    Function.Injective (dirichletCoordinatesHom K) := by
  rintro ⟨ζ, a⟩ ⟨ξ, b⟩ hab
  have hcoords :
      (ζ, a.toAdd) = (ξ, b.toAdd) := by
    apply
      (exist_unique_eq_mul_prod K
        (dirichletCoordinatesHom K (ζ, a))).unique
    · rfl
    · simpa [dirichletCoordinatesHom] using hab
  refine Prod.ext (congrArg Prod.fst hcoords) ?_
  exact Multiplicative.ext
    (congrArg Prod.snd hcoords)

/-- Bundled multiplicative form of Dirichlet's unique unit coordinates. -/
noncomputable def dirichletMulEquiv :
    torsion K ×
        Multiplicative (Fin (rank K) → ℤ) ≃*
      (NumberField.RingOfIntegers K)ˣ :=
  MulEquiv.ofBijective (dirichletCoordinatesHom K)
    ⟨dirichletCoordinatesHom_injective K,
      dirichletCoordinatesHom_surjective K⟩

/-- Exact square-map index for the unit group of a number field. -/
theorem unit_powTwo_range_index :
    (powMonoidHom 2 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range.index =
      2 ^ (rank K + 1) := by
  classical

  letI : Module.Free ℤ (Fin (rank K) → ℤ) :=
    Module.Free.of_basis
      (Pi.basisFun ℤ (Fin (rank K)))
  letI : Module.Finite ℤ (Fin (rank K) → ℤ) :=
    Module.Finite.of_basis
      (Pi.basisFun ℤ (Fin (rank K)))

  have hfinrank :
      Module.finrank ℤ (Fin (rank K) → ℤ) =
        rank K := by
    simpa using
      Module.finrank_eq_card_basis
        (Pi.basisFun ℤ (Fin (rank K)))

  have hEven :
      Even (Nat.card (torsion K)) := by
    simpa only [torsionOrder] using even_torsionOrder K

  have h :=
    MazurProof.UnitSquareClass.index_powTwo_range_eq_pow_succ_of_even
        (e := (dirichletMulEquiv K).symm) hEven
  simpa [hfinrank] using h

/-- Cardinality of the quotient of units by squares. -/
theorem natCard_unit_quotient_squares :
    Nat.card
      (((NumberField.RingOfIntegers K)ˣ) ⧸
        (powMonoidHom 2 :
          (NumberField.RingOfIntegers K)ˣ →*
            (NumberField.RingOfIntegers K)ˣ).range) =
      2 ^ (rank K + 1) := by
  change
    (powMonoidHom 2 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range.index =
      2 ^ (rank K + 1)
  exact unit_powTwo_range_index K

end NumberField.Units

namespace MazurProof.N13GaussianUnitSquareclasses

abbrev L : Type :=
  N13GaussianNumberField.L

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField

/-- The N13 unit squareclass group has exactly eight elements. -/
theorem unit_squareclass_natCard :
    Nat.card
      (((NumberField.RingOfIntegers L)ˣ) ⧸
        (powMonoidHom 2 :
          (NumberField.RingOfIntegers L)ˣ →*
            (NumberField.RingOfIntegers L)ˣ).range) =
      8 := by
  rw [NumberField.Units.natCard_unit_quotient_squares L,
    N13GaussianSignature.units_rank_eq_two]
  norm_num

end MazurProof.N13GaussianUnitSquareclasses


