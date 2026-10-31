-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06
-- name    : QAlgorithms_Papers_Independent_Intake100_P06
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:44:26.236599+00:00
-- url     : https://prove2.me/theorems/b94c4b76-b494-4860-8ea9-8b72aa1cc674
-- title:
--   Definitions for Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras
-- statement:
--   The objects the formalized statements of *Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras* (arXiv:math/0612064) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HeckeLetter`: Signed generators of Definition 6.3, PDF pp.39--42. g indices are zero based. The affine x_1=beta_0 is absent when affine=false or n=0.
--   - `heckeFreeG`: Free g_(i+1) or inverse, with unused out-of-range value zero, PDF p.42.
--   - `heckeFreeX`: Free x_1 or inverse, when the generator exists, PDF p.42.
--   - `NormalizedBraidHeckeRel`: Complete invertibility, Artin and normalized Hecke relations, Definition 6.3, PDF pp.39--42. There is no quadratic relation on x_1 and no BMW data. This ordinary/affine presentation differs from the imported Support21.P14.HeckeRel, which includes a cyclotomic relation and requires GroundParameters.
--   - `NormalizedBraidHecke`: H(q^2) of Definition 6.3, PDF pp.41--42, as the complete invertible-letter presentation of the group-algebra quotient. No geometry is asserted by def. The frozen Renew46.P26.Hecke is degenerate and has complex coefficients; Support21.P14.MultiplicativeCyclotomicHecke already imposes a root polynomial. Neither is this unrestricted ordinary/affine algebra of Definition 6.3.
--   - `heckeMap`: Canonical presentation quotient, PDF pp.41--42.
--   - `heckeG`: Normalized g_(i+1) or its specified inverse, PDF p.42.
--   - `heckeX`: Affine x_1 or its specified inverse, PDF p.42.
--   - `heckeWinding`: x'_(j+1) or its inverse: g_j...g_1 x_1^a g_1^-1...g_j^-1, where a is 1 or -1, PDF p.42. The inverse flag changes x_1 only.
--   - `heckeWindingPower`: Integer powers use the explicit inverse conjugate, never ring division, PDF pp.42--43. Only j<n is used by the displayed basis families.
--   - `heckeLaurentWord`: The ordered word (x'_n)^a_n ... (x'_1)^a_1, PDF pp.42--43.
--   - `adjacentSwap`: Adjacent transposition on positions i,i+1. The unused out-of-range helper is the identity; the reduced-word construction uses valid indices, PDF p.43.
--   - `permutationReducedWord`: Explicit reduced expression for alpha, fixing the choice allowed on PDF p.43. Sort one-line notation: at stage i move value i from k to i using s_(k-1),...,s_i. Reverse the sorting word to express alpha. Each swap removes one inversion. This constructs the lift without assuming a normal-form result.
--   - `heckePermutationLift`: T_alpha uses INVERSE g generators in a reduced expression, PDF p.43.
--   - `heckeNormalWord`: The specified Sigma-prime words, PDF p.43. Integer labels are indexed by upper (initial) vertices and T_alpha is to the left of the winding word.
--   - `heckeCyclotomicPolynomial`: The full cyclotomic polynomial in x_1, Definition 6.10, PDF p.44.
--   - `heckeCyclotomicRel`: Actual polynomial relation, PDF p.44; absent at scalar level zero.
--   - `CyclotomicHecke`: The cyclotomic Hecke quotient, Definition 6.10, PDF p.44.
--   - `heckeCyclotomicMap`: Canonical cyclotomic quotient map, PDF p.44.
--   - `boundedHeckeNormalWord`: Sigma-prime-r is the quotient image of the specified words with each exponent in 0,...,r-1, PDF p.44.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, https://arxiv.org/abs/math/0612064v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

/-! Statement draft for arXiv:math/0612064v5. Geometric targets are inventoried
in HARD.md. Compilation is pending the requested batch handoff. -/

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Signed generators of Definition 6.3, PDF pp.39--42. g indices are zero
based. The affine x_1=beta_0 is absent when affine=false or n=0. -/
inductive HeckeLetter (n : ℕ) (affine : Bool)
  | g : Fin (n - 1) → Bool → HeckeLetter n affine
  | x : Fin (if affine then min n 1 else 0) → Bool → HeckeLetter n affine

/-- Free g_(i+1) or inverse, with unused out-of-range value zero, PDF p.42. -/
def heckeFreeG (S : Type*) [CommRing S] (n : ℕ) (affine : Bool)
    (i : ℕ) (inverse : Bool) : FreeAlgebra S (HeckeLetter n affine) :=
  if h : i < n - 1 then FreeAlgebra.ι S (.g ⟨i, h⟩ inverse) else 0

/-- Free x_1 or inverse, when the generator exists, PDF p.42. -/
def heckeFreeX (S : Type*) [CommRing S] (n : ℕ) (affine : Bool)
    (inverse : Bool) : FreeAlgebra S (HeckeLetter n affine) :=
  if h : 0 < (if affine then min n 1 else 0) then
    FreeAlgebra.ι S (.x ⟨0, h⟩ inverse) else 0

/-- Complete invertibility, Artin and normalized Hecke relations, Definition
6.3, PDF pp.39--42. There is no quadratic relation on x_1 and no BMW data.
This ordinary/affine presentation differs from the imported Support21.P14.HeckeRel,
which includes a cyclotomic relation and requires GroundParameters. -/
inductive NormalizedBraidHeckeRel {S : Type*} [CommRing S] (q : Sˣ) (n : ℕ) (affine : Bool) :
    FreeAlgebra S (HeckeLetter n affine) → FreeAlgebra S (HeckeLetter n affine) → Prop
  | inverseL (i : ℕ) (hi : i + 1 < n) : NormalizedBraidHeckeRel q n affine
      (heckeFreeG S n affine i false * heckeFreeG S n affine i true) 1
  | inverseR (i : ℕ) (hi : i + 1 < n) : NormalizedBraidHeckeRel q n affine
      (heckeFreeG S n affine i true * heckeFreeG S n affine i false) 1
  | braid (i : ℕ) (hi : i + 2 < n) : NormalizedBraidHeckeRel q n affine
      (heckeFreeG S n affine i false * heckeFreeG S n affine (i+1) false * heckeFreeG S n affine i false)
      (heckeFreeG S n affine (i+1) false * heckeFreeG S n affine i false * heckeFreeG S n affine (i+1) false)
  | far (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hd : i + 1 < j ∨ j + 1 < i) : NormalizedBraidHeckeRel q n affine
      (heckeFreeG S n affine i false * heckeFreeG S n affine j false)
      (heckeFreeG S n affine j false * heckeFreeG S n affine i false)
  | xInverseL (ha : affine = true) (hn : 1 ≤ n) : NormalizedBraidHeckeRel q n affine
      (heckeFreeX S n affine false * heckeFreeX S n affine true) 1
  | xInverseR (ha : affine = true) (hn : 1 ≤ n) : NormalizedBraidHeckeRel q n affine
      (heckeFreeX S n affine true * heckeFreeX S n affine false) 1
  | typeB (ha : affine = true) (hn : 2 ≤ n) : NormalizedBraidHeckeRel q n affine
      (heckeFreeX S n affine false * heckeFreeG S n affine 0 false *
        heckeFreeX S n affine false * heckeFreeG S n affine 0 false)
      (heckeFreeG S n affine 0 false * heckeFreeX S n affine false *
        heckeFreeG S n affine 0 false * heckeFreeX S n affine false)
  | xFar (ha : affine = true) (i : ℕ) (hi : i + 1 < n) (hpos : 1 ≤ i) :
      NormalizedBraidHeckeRel q n affine
        (heckeFreeX S n affine false * heckeFreeG S n affine i false)
        (heckeFreeG S n affine i false * heckeFreeX S n affine false)
  | skein (i : ℕ) (hi : i + 1 < n) : NormalizedBraidHeckeRel q n affine
      (heckeFreeG S n affine i false - heckeFreeG S n affine i true)
      (algebraMap S _ ((q : S) - (↑q⁻¹ : S)))

/-- H(q^2) of Definition 6.3, PDF pp.41--42, as the complete invertible-letter
presentation of the group-algebra quotient. No geometry is asserted by def.
The frozen Renew46.P26.Hecke is degenerate and has complex coefficients;
Support21.P14.MultiplicativeCyclotomicHecke already imposes a root polynomial.
Neither is this unrestricted ordinary/affine algebra of Definition 6.3. -/
abbrev NormalizedBraidHecke (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) (affine : Bool) :=
  RingQuot (NormalizedBraidHeckeRel q n affine)

/-- Canonical presentation quotient, PDF pp.41--42. -/
def heckeMap (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) (affine : Bool) :
    FreeAlgebra S (HeckeLetter n affine) →ₐ[S] NormalizedBraidHecke S q n affine :=
  RingQuot.mkAlgHom S (NormalizedBraidHeckeRel q n affine)

/-- Normalized g_(i+1) or its specified inverse, PDF p.42. -/
def heckeG (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) (affine : Bool)
    (i : ℕ) (inverse : Bool) : NormalizedBraidHecke S q n affine :=
  heckeMap S q n affine (heckeFreeG S n affine i inverse)

/-- Affine x_1 or its specified inverse, PDF p.42. -/
def heckeX (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ)
    (inverse : Bool) : NormalizedBraidHecke S q n true :=
  heckeMap S q n true (heckeFreeX S n true inverse)

/-- x'_(j+1) or its inverse: g_j...g_1 x_1^a g_1^-1...g_j^-1,
where a is 1 or -1, PDF p.42. The inverse flag changes x_1 only. -/
def heckeWinding (S : Type*) [CommRing S] (q : Sˣ) (n j : ℕ)
    (inverse : Bool) : NormalizedBraidHecke S q n true :=
  ((List.range j).reverse.map fun i => heckeG S q n true i false).prod *
    heckeX S q n inverse *
    ((List.range j).map fun i => heckeG S q n true i true).prod

/-- Integer powers use the explicit inverse conjugate, never ring division,
PDF pp.42--43. Only j<n is used by the displayed basis families. -/
def heckeWindingPower (S : Type*) [CommRing S] (q : Sˣ) (n j : ℕ)
    (a : ℤ) : NormalizedBraidHecke S q n true :=
  if 0 ≤ a then heckeWinding S q n j false ^ a.toNat
  else heckeWinding S q n j true ^ (-a).toNat

/-- The ordered word (x'_n)^a_n ... (x'_1)^a_1, PDF pp.42--43. -/
def heckeLaurentWord (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ)
    (a : Fin n → ℤ) : NormalizedBraidHecke S q n true :=
  ((List.finRange n).reverse.map fun j => heckeWindingPower S q n j.val (a j)).prod

/-- Adjacent transposition on positions i,i+1. The unused out-of-range helper
is the identity; the reduced-word construction uses valid indices, PDF p.43. -/
def adjacentSwap (n i : ℕ) : Equiv.Perm (Fin n) :=
  if h : i + 1 < n then Equiv.swap ⟨i, by omega⟩ ⟨i+1, h⟩ else 1

/-- Explicit reduced expression for alpha, fixing the choice allowed on PDF
p.43. Sort one-line notation: at stage i move value i from k to i using
s_(k-1),...,s_i. Reverse the sorting word to express alpha. Each swap removes
one inversion. This constructs the lift without assuming a normal-form result. -/
def permutationReducedWord {n : ℕ} (alpha : Equiv.Perm (Fin n)) : List ℕ :=
  (((List.finRange n).foldl (fun (state : Equiv.Perm (Fin n) × List ℕ) i =>
    let steps := ((List.range ((state.1.symm i).val)).drop i.val).reverse
    (state.1 * (steps.map (adjacentSwap n)).prod, state.2 ++ steps))
    (alpha, [])).2).reverse

/-- T_alpha uses INVERSE g generators in a reduced expression, PDF p.43. -/
def heckePermutationLift (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ)
    (alpha : Equiv.Perm (Fin n)) : NormalizedBraidHecke S q n true :=
  ((permutationReducedWord alpha).map fun i => heckeG S q n true i true).prod

/-- The specified Sigma-prime words, PDF p.43. Integer labels are indexed by
upper (initial) vertices and T_alpha is to the left of the winding word. -/
def heckeNormalWord (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ)
    (d : Equiv.Perm (Fin n) × (Fin n → ℤ)) : NormalizedBraidHecke S q n true :=
  heckePermutationLift S q n d.1 * heckeLaurentWord S q n d.2

/-- The full cyclotomic polynomial in x_1, Definition 6.10, PDF p.44. -/
def heckeCyclotomicPolynomial (S : Type*) [CommRing S] (q : Sˣ) (n r : ℕ)
    (u : Fin r → Sˣ) : NormalizedBraidHecke S q n true :=
  (List.ofFn fun j : Fin r => heckeX S q n false - algebraMap S _ (u j : S)).prod

/-- Actual polynomial relation, PDF p.44; absent at scalar level zero. -/
def heckeCyclotomicRel (S : Type*) [CommRing S] (q : Sˣ) (n r : ℕ)
    (u : Fin r → Sˣ) (a b : NormalizedBraidHecke S q n true) : Prop :=
  1 ≤ n ∧ a = heckeCyclotomicPolynomial S q n r u ∧ b = 0

/-- The cyclotomic Hecke quotient, Definition 6.10, PDF p.44. -/
abbrev CyclotomicHecke (S : Type*) [CommRing S] (q : Sˣ) (n r : ℕ)
    (u : Fin r → Sˣ) := RingQuot (heckeCyclotomicRel S q n r u)

/-- Canonical cyclotomic quotient map, PDF p.44. -/
def heckeCyclotomicMap (S : Type*) [CommRing S] (q : Sˣ) (n r : ℕ)
    (u : Fin r → Sˣ) : NormalizedBraidHecke S q n true →ₐ[S] CyclotomicHecke S q n r u :=
  RingQuot.mkAlgHom S (heckeCyclotomicRel S q n r u)

/-- Sigma-prime-r is the quotient image of the specified words with each
exponent in 0,...,r-1, PDF p.44. -/
def boundedHeckeNormalWord (S : Type*) [CommRing S] (q : Sˣ) (n r : ℕ)
    (u : Fin r → Sˣ) (d : Equiv.Perm (Fin n) × (Fin n → Fin r)) :
    CyclotomicHecke S q n r u :=
  heckeCyclotomicMap S q n r u
    (heckeNormalWord S q n (d.1, fun j => (d.2 j).val))

/-- Sanity: the ordinary presentation has no affine letter. -/
example (S : Type*) [CommRing S] (n : ℕ) (inverse : Bool) :
    heckeFreeX S n false inverse = 0 := by
  simp [heckeFreeX]

/-- Sanity: source normalized skein constant at two strands. -/
example (S : Type*) [CommRing S] (q : Sˣ) (affine : Bool) :
    heckeG S q 2 affine 0 false - heckeG S q 2 affine 0 true =
      algebraMap S (NormalizedBraidHecke S q 2 affine) ((q : S) - (↑q⁻¹ : S)) := by
  have h := RingQuot.mkAlgHom_rel S
    (NormalizedBraidHeckeRel.skein (q := q) (n := 2) (affine := affine) 0 (by decide))
  simpa only [heckeG, heckeMap, map_sub, AlgHom.commutes] using h

/-- Sanity: the first conjugate has no surrounding braid generators. -/
example (S : Type*) [CommRing S] (q : Sˣ) (n : ℕ) (inverse : Bool) :
    heckeWinding S q n 0 inverse = heckeX S q n inverse := by
  simp [heckeWinding]

/-- Sanity: the zero exponent gives 1, including in the zero ring. -/
example (S : Type*) [CommRing S] (q : Sˣ) (n j : ℕ) :
    heckeWindingPower S q n j 0 = 1 := by
  simp [heckeWindingPower]

/-- Sanity: the empty permutation has the empty reduced word. -/
example (alpha : Equiv.Perm (Fin 0)) : permutationReducedWord alpha = [] := by
  simp [permutationReducedWord]

/-- Sanity: empty monomials give the empty-product value 1. -/
example (S : Type*) [CommRing S] (q : Sˣ) (a : Fin 0 → ℤ) :
    heckeLaurentWord S q 0 a = 1 := by
  simp [heckeLaurentWord]

/-- Sanity: the imposed polynomial has its full constant term, PDF p.44. -/
example (S : Type*) [CommRing S] (q : Sˣ) (n r : ℕ) (hn : 1 ≤ n)
    (u : Fin r → Sˣ) :
    heckeCyclotomicMap S q n r u (heckeCyclotomicPolynomial S q n r u) = 0 := by
  have h := RingQuot.mkAlgHom_rel S
    (s := heckeCyclotomicRel S q n r u) (x := heckeCyclotomicPolynomial S q n r u)
    (y := 0) ⟨hn, rfl, rfl⟩
  simpa only [heckeCyclotomicMap, map_zero] using h

end QAlgorithms.Papers.Independent.Intake100.P06


