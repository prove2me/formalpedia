-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticIrreducible_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SexticIrreducible_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:10:58.939872+00:00
-- url     : https://prove2.me/theorems/7f1813e2-2ef4-4189-b89a-6ea31e68189f
-- title:
--   FLT.Assumptions.MazurProof.N13SexticIrreducible source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SexticIrreducible

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SexticIrreducible
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SexticSquareclass_p0
import Mathlib.FieldTheory.Finite.Extension

set_option autoImplicit false




/-!
# Irreducibility of the N13 sextic

The sextic defining the fake two-descent algebra is irreducible over `ℚ`.
We prove this structurally by reduction modulo three.  An irreducible
degree-`d` factor over `𝔽₃` divides `X ^ (3 ^ d) - X`, by applying finite-field
Frobenius in its adjoin-root field.  Three short Bézout identities exclude
degrees one through three, which is the full Rabin test for a sextic.  No
finite-field polynomials are enumerated.
-/

open Polynomial

namespace MazurProof.N13SexticIrreducible

noncomputable section

def fInt : ℤ[X] :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 1

def fModThree : (ZMod 3)[X] :=
  fInt.map (Int.castRingHom (ZMod 3))

theorem fInt_monic : fInt.Monic := by
  unfold fInt
  monicity!

theorem fInt_natDegree : fInt.natDegree = 6 := by
  unfold fInt
  compute_degree!

theorem fModThree_eq :
    fModThree = X ^ 6 + X ^ 5 - X ^ 3 + X ^ 2 - X + 1 := by
  simp [fModThree, fInt]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination (X ^ 5 + 2 * X ^ 4 + X ^ 3 + X) * hthree

theorem fModThree_monic : fModThree.Monic := by
  rw [fModThree_eq]
  monicity!

theorem fModThree_natDegree : fModThree.natDegree = 6 := by
  rw [fModThree_eq]
  compute_degree!

private theorem irreducible_dvd_own_frobenius
    {p : (ZMod 3)[X]} (hp : Irreducible p) :
    p ∣ X ^ (3 ^ p.natDegree) - X := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : Module.Finite (ZMod 3) (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis hp.ne_zero).finite
  letI : Finite (AdjoinRoot p) :=
    Module.finite_of_finite (ZMod 3)
  letI : Fintype (AdjoinRoot p) :=
    Fintype.ofFinite (AdjoinRoot p)
  have hcard :
      Fintype.card (AdjoinRoot p) = 3 ^ p.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod 3) (V := AdjoinRoot p),
      (AdjoinRoot.powerBasis hp.ne_zero).finrank, ZMod.card,
      AdjoinRoot.powerBasis_dim]
  have hroot :
      (AdjoinRoot.root p) ^ (3 ^ p.natDegree) =
        AdjoinRoot.root p := by
    rw [← hcard]
    exact FiniteField.pow_card _
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X]
  exact sub_eq_zero.mpr hroot

private def bezoutOneA : (ZMod 3)[X] :=
  -X ^ 2 - X + 1

private def bezoutOneB : (ZMod 3)[X] :=
  X ^ 5 - X ^ 4 + X ^ 3 + X + 1

private theorem bezout_one :
    bezoutOneA * fModThree + bezoutOneB * (X ^ 3 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutOneA, bezoutOneB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (-X ^ 7 + X ^ 5 - X) * hthree

private def bezoutTwoA : (ZMod 3)[X] :=
  X ^ 8 - X ^ 6 + X ^ 5 - X ^ 3 - X ^ 2 - X + 1

private def bezoutTwoB : (ZMod 3)[X] :=
  -X ^ 5 - X ^ 4 + X ^ 3 + X ^ 2 + X + 1

private theorem bezout_two :
    bezoutTwoA * fModThree + bezoutTwoB * (X ^ 9 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutTwoA, bezoutTwoB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (X * (X ^ 9 - X ^ 7 + X ^ 4 - X ^ 2 - 1)) * hthree

private def bezoutThreeA : (ZMod 3)[X] :=
  -X ^ 25 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 19 - X ^ 18 - X ^ 17 +
    X ^ 16 - X ^ 12 - X ^ 10 + X ^ 8 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 + 1

private def bezoutThreeB : (ZMod 3)[X] :=
  X ^ 4 + X ^ 3 + X - 1

private theorem bezout_three :
    bezoutThreeA * fModThree + bezoutThreeB * (X ^ 27 - X) = 1 := by
  rw [fModThree_eq]
  simp [bezoutThreeA, bezoutThreeB]
  have hthree : (3 : (ZMod 3)[X]) = 0 :=
    CharP.cast_eq_zero ((ZMod 3)[X]) 3
  linear_combination
    (X ^ 4 * (X ^ 24 + X ^ 22 - X ^ 19 + X ^ 17 - X ^ 13 +
      X ^ 9 - X ^ 8 + X ^ 3 - X ^ 2 + X - 1)) * hthree

private theorem coprime_frobenius_one :
    IsCoprime fModThree (X ^ 3 - X) :=
  ⟨bezoutOneA, bezoutOneB, bezout_one⟩

private theorem coprime_frobenius_two :
    IsCoprime fModThree (X ^ 9 - X) :=
  ⟨bezoutTwoA, bezoutTwoB, bezout_two⟩

private theorem coprime_frobenius_three :
    IsCoprime fModThree (X ^ 27 - X) :=
  ⟨bezoutThreeA, bezoutThreeB, bezout_three⟩

/-- The reduction of the N13 sextic modulo three is irreducible. -/
theorem fModThree_irreducible : Irreducible fModThree := by
  have hf1 : fModThree ≠ 1 := by
    intro h
    have := fModThree_natDegree
    rw [h] at this
    norm_num at this
  rw [fModThree_monic.irreducible_iff_lt_natDegree_lt hf1]
  intro q hq hdeg hqf
  rw [fModThree_natDegree] at hdeg
  have hdeg' : 0 < q.natDegree ∧ q.natDegree ≤ 3 := by
    simpa using (Finset.mem_Ioc.mp hdeg)
  obtain ⟨r, _hrm, hri, hrq⟩ :=
    Polynomial.exists_monic_irreducible_factor q
      (not_isUnit_of_natDegree_pos q hdeg'.1)
  have hrf : r ∣ fModThree :=
    dvd_trans hrq hqf
  have hrle : r.natDegree ≤ 3 :=
    (natDegree_le_of_dvd hrq hq.ne_zero).trans hdeg'.2
  have hrpos : 0 < r.natDegree :=
    hri.natDegree_pos
  have hcases :
      r.natDegree = 1 ∨ r.natDegree = 2 ∨ r.natDegree = 3 := by
    omega
  rcases hcases with hdegree | hdegree | hdegree
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_one.isUnit_of_dvd' hrf hrfrob)
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_two.isUnit_of_dvd' hrf hrfrob)
  · have hrfrob := irreducible_dvd_own_frobenius hri
    rw [hdegree] at hrfrob
    norm_num at hrfrob
    exact hri.not_isUnit
      (coprime_frobenius_three.isUnit_of_dvd' hrf hrfrob)

/-- The integral N13 sextic is irreducible by its irreducible reduction
modulo three. -/
theorem fInt_irreducible : Irreducible fInt := by
  apply fInt_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 3)) fInt
  simpa [fModThree] using fModThree_irreducible

theorem fInt_map_rat :
    fInt.map (algebraMap ℤ ℚ) = N13Mumford.f ℚ := by
  simp [fInt, N13Mumford.f]

/-- The sextic defining the N13 Mumford model is irreducible over `ℚ`. -/
theorem n13Mumford_f_irreducible :
    Irreducible (N13Mumford.f ℚ) := by
  rw [← fInt_map_rat]
  exact
    fInt_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mp
      fInt_irreducible

theorem f_irreducible :
    Irreducible (N13Mumford.f ℚ) :=
  n13Mumford_f_irreducible

/-- The same irreducibility statement in the notation used by the fake
square-class target. -/
theorem squareclass_f_irreducible :
    Irreducible N13SexticSquareclass.f := by
  simpa [N13SexticSquareclass.f] using n13Mumford_f_irreducible

/-- An explicit, opt-in `Fact` for clients that need the field structure on
the sextic algebra.  Use `letI := sexticIrreducibleFact`; it is deliberately
not a global instance. -/
@[reducible] def sexticIrreducibleFact :
    Fact (Irreducible N13SexticSquareclass.f) :=
  ⟨squareclass_f_irreducible⟩

/-- The field structure on the sextic algebra, exported without installing a
global instance. -/
@[reducible] noncomputable def sexticAlgebraField :
    Field N13SexticSquareclass.SexticAlgebra := by
  letI := sexticIrreducibleFact
  infer_instance

end

end MazurProof.N13SexticIrreducible


