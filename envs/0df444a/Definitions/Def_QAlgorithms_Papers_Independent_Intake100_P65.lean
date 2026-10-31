-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65
-- name    : QAlgorithms_Papers_Independent_Intake100_P65
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:11:12.616666+00:00
-- url     : https://prove2.me/theorems/351d7049-9070-4a28-b672-215bd76fd048
-- title:
--   Definitions for Cyclotomic Nazarov-Wenzl algebras
-- statement:
--   The objects the formalized statements of *Cyclotomic Nazarov-Wenzl algebras* (arXiv:math/0506467) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `OmegaAdmissible`: Ordinary scalar admissibility, Definition 2.10, PDF p.8. The equation is multiplied by 2; all uses assume that 2 is invertible.
--   - `SplitMatrixAlgebra`: Split semisimplicity means an actual finite product of full matrix algebras over the ground field, rather than a parameter criterion.
--   - `affineCyclotomicProjection`: Canonical affine-to-cyclotomic projection at positive rank, PDF pp.2,9. The accepted tower is R at rank zero; the raw affine presentation is used only at positive rank. Splitting on the rank exposes their definitional equality.
--   - `topEndpoint`: Boundary embedding of the top row, Definition 2.6, PDF p.6.
--   - `bottomEndpoint`: Boundary embedding of the bottom row, Definition 2.6, PDF p.6.
--   - `TopLeft`: A left endpoint of a top horizontal edge, Definition 2.9, PDF p.7.
--   - `BottomLeft`: A left endpoint of a bottom horizontal edge, Definition 2.9, PDF p.7.
--   - `BrauerRegular`: The precise affine regularity test, Definition 2.9, PDF p.7.
--   - `RegularIndex`: Affine regular indices, including all unbounded nonnegative exponents. This is an index type, not yet an evaluated monomial family.
--   - `RRegularIndex`: Bounded r-regular indices, Definition 2.14, PDF p.9. Both exponent bounds are part of Fin r, and the top/bottom tests are retained.
--   - `HorizontalRegularIndex`: Horizontal-edge subfamily of r-regular indices, PDF pp.44--45.
--   - `Node`: Nodes are (component,row,column), with all three coordinates zero based; column minus row is unchanged by this convention, PDF pp.17--18.
--   - `LowerClosed`: A finite Young diagram is closed toward the upper left in each component, which is exactly the partition condition in PDF p.17.
--   - `MultipartitionShape`: An r-multipartition as its actual finite node diagram, PDF p.17.
--   - `emptyShape`: The empty multipartition at time zero, PDF p.17.
--   - `Addable`: Addable nodes, requiring both absence and a valid enlarged partition.
--   - `RemovableNode`: RemovableNode nodes, requiring membership and a valid remaining partition.
--   - `BoundaryNodes`: All addable AND removable nodes, with the two directions distinguished.
--   - `ShapeStep`: One genuine box addition or removal, PDF p.17. In particular the box cannot be inserted twice or removed from a diagram that does not contain it.
--   - `Updown`: The exact finite updown paths from empty to lambda, PDF pp.17--18.
--   - `pathAt`: Time evaluation. The helper outside 0..n is empty and is never used in a source formula without its time-range guard.
--   - `KEquivalent`: k-equivalence fixes all shapes at times other than k, Definition 4.1.
--   - `content`: The signed content of the unique changed box at time k, PDF p.18. Finite differences avoid an arbitrary choice of a box or a proof parameter. Source p.17 prints the old row length for an added box; the actual differing cell uses the new row length, as required by the add-box definition and p.18.
--   - `WGeneric`: W-genericity, Definition 4.3, PDF p.18: all signed inter-component collisions and the doubles are tested against small integers.
--   - `HeckeGeneric`: Hecke-genericity, Definition 6.4, PDF p.41, corrected by the proof on p.44: only DISTINCT component indices are compared. Printed: all i,j. Changed: i != j, because i=j,d=0 would make the printed predicate impossible at positive n, and the converse proof explicitly uses distinct indices.
--   - `TerminalPathPairs`: The pairs counted by the sum of squares in Corollary 5.2, PDF p.36. The sigma type binds BOTH the contraction number and the terminal shape.
--   - `HLetter`: Source Hecke generators, PDF p.10; there is no contraction or Omega.
--   - `freeHT`: Free T_(i+1), with the out-of-range helper zero.
--   - `freeHY`: Free Y_(j+1), with the out-of-range helper zero.
--   - `HRel`: Every relation of the degenerate cyclotomic Hecke presentation, PDF p.10. Both skein equations and all valid-index guards are included.
--   - `CyclotomicHeckeAlgebra`: The actual presented degenerate cyclotomic Hecke algebra, PDF p.10.
--   - `hMap`: Its canonical presentation map.
--   - `hT`: The source T_(i+1) in the quotient.
--   - `hY`: The source Y_(j+1) in the quotient.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, https://arxiv.org/abs/math/0506467v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

/-!
Ariki--Mathas--Rui, Cyclotomic Nazarov--Wenzl algebras, math/0506467v5.
Only statements are admitted. All local definitions have complete bodies.
Generator indices are zero based; tableau time and row/column coordinates are
explicit. Missing concrete interfaces are recorded in the unit's HARD.md.
-/

noncomputable section

open scoped BigOperators TensorProduct
open QAlgorithms.Papers.Independent.Renew46.P16
open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)
open QAlgorithms.Papers.Independent.Support21.P12
open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Ordinary scalar admissibility, Definition 2.10, PDF p.8.
The equation is multiplied by 2; all uses assume that 2 is invertible. -/
def OmegaAdmissible {R : Type*} [CommRing R] (omega : ℕ → R) : Prop :=
  ∀ a : ℕ, 2 * omega (2*a+1) = -omega (2*a) +
    ∑ b ∈ Finset.range (2*a+1), (-1 : R)^b * omega b * omega (2*a-b)

/-- Zero parameters satisfy every scalar admissibility equation. -/
example (R : Type*) [CommRing R] : OmegaAdmissible (fun _ => (0 : R)) := by
  intro a
  simp

/-- The a=0 equation has the loop-square term, not a cancelled E_1. -/
example {R : Type*} [CommRing R] {omega : ℕ → R} (h : OmegaAdmissible omega) :
    2 * omega 1 = -omega 0 + omega 0 * omega 0 := by
  simpa using h 0

/-- In particular, the zero vector space is excluded from irreducibility. -/
example {R A V : Type u} [Field R] [Ring A] [Algebra R A]
    [AddCommGroup V] [Module R V] [Subsingleton V]
    (rho : A →ₐ[R] Module.End R V) : ¬ IrreducibleRepresentation rho := by
  intro h
  rcases h.1 with ⟨x, hx⟩
  exact hx (Subsingleton.elim x 0)

/-- Split semisimplicity means an actual finite product of full matrix
algebras over the ground field, rather than a parameter criterion. -/
def SplitMatrixAlgebra (R A : Type u) [Field R] [Ring A] [Algebra R A] : Prop :=
  ∃ (q : ℕ) (d : Fin q → ℕ), (∀ i, 0 < d i) ∧
    Nonempty (A ≃ₐ[R] ((i : Fin q) → Matrix (Fin (d i)) (Fin (d i)) R))

/-- An algebra already given as a matrix product satisfies the definition. -/
example (R : Type u) [Field R] (q : ℕ) (d : Fin q → ℕ)
    (hd : ∀ i, 0 < d i) :
    SplitMatrixAlgebra R ((i : Fin q) → Matrix (Fin (d i)) (Fin (d i)) R) :=
  ⟨q, d, hd, ⟨AlgEquiv.refl⟩⟩

/-- Canonical affine-to-cyclotomic projection at positive rank, PDF pp.2,9.
The accepted tower is R at rank zero; the raw affine presentation is used only
at positive rank. Splitting on the rank exposes their definitional equality. -/
def affineCyclotomicProjection (R : Type*) [CommRing R] (omega : ℕ → R)
    (n r : ℕ) (roots : Fin r → R) (hn : 1 ≤ n) :
    AffineBMW R omega n →ₐ[R] Cyclotomic R omega .degenerate r roots n := by
  cases n with
  | zero => omega
  | succ k => exact toCycl R omega .degenerate r roots (k+1)

/-- At rank one the projection is the accepted quotient, without a new map. -/
example (R : Type*) [CommRing R] (omega : ℕ → R) (r : ℕ) (roots : Fin r → R) :
    affineCyclotomicProjection R omega 1 r roots (by decide) =
      toCycl R omega .degenerate r roots 1 := rfl

/-- Boundary embedding of the top row, Definition 2.6, PDF p.6. -/
def topEndpoint {n : ℕ} (i : Fin n) : Fin (2*n) := ⟨i.val, by omega⟩

/-- Boundary embedding of the bottom row, Definition 2.6, PDF p.6. -/
def bottomEndpoint {n : ℕ} (i : Fin n) : Fin (2*n) := ⟨n+i.val, by omega⟩

/-- A left endpoint of a top horizontal edge, Definition 2.9, PDF p.7. -/
def TopLeft {n : ℕ} (g : BrauerPairing n) (i : Fin n) : Prop :=
  ∃ j : Fin n, i < j ∧ g.val (topEndpoint i) = topEndpoint j

/-- A left endpoint of a bottom horizontal edge, Definition 2.9, PDF p.7. -/
def BottomLeft {n : ℕ} (g : BrauerPairing n) (i : Fin n) : Prop :=
  ∃ j : Fin n, i < j ∧ g.val (bottomEndpoint i) = bottomEndpoint j

/-- The precise affine regularity test, Definition 2.9, PDF p.7. -/
def BrauerRegular {n : ℕ} (g : BrauerPairing n) (alpha beta : Fin n → ℕ) : Prop :=
  (∀ i, TopLeft g i → alpha i = 0) ∧
  (∀ i, beta i ≠ 0 → BottomLeft g i)

/-- Affine regular indices, including all unbounded nonnegative exponents.
This is an index type, not yet an evaluated monomial family. -/
def RegularIndex (n : ℕ) :=
  {z : (Fin n → ℕ) × BrauerPairing n × (Fin n → ℕ) // BrauerRegular z.2.1 z.1 z.2.2}

/-- Bounded r-regular indices, Definition 2.14, PDF p.9. Both exponent bounds
are part of Fin r, and the top/bottom tests are retained. -/
def RRegularIndex (n r : ℕ) :=
  {z : (Fin n → Fin r) × BrauerPairing n × (Fin n → Fin r) //
    BrauerRegular z.2.1 (fun i => (z.1 i).val) (fun i => (z.2.2 i).val)}

/-- Horizontal-edge subfamily of r-regular indices, PDF pp.44--45. -/
def HorizontalRegularIndex (n r : ℕ) :=
  {z : RRegularIndex n r // ∃ i, TopLeft z.val.2.1 i}

/-- At zero strands regularity imposes no condition; no endpoint exists. -/
example (g : BrauerPairing 0) (alpha beta : Fin 0 → ℕ) : BrauerRegular g alpha beta := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

/-- Top and bottom endpoint numbering at two strands. -/
example : (topEndpoint (0 : Fin 2)).val = 0 ∧
    (bottomEndpoint (0 : Fin 2)).val = 2 := by decide

/-- Nodes are (component,row,column), with all three coordinates zero based;
column minus row is unchanged by this convention, PDF pp.17--18. -/
abbrev Node (r : ℕ) := Fin r × ℕ × ℕ

/-- A finite Young diagram is closed toward the upper left in each component,
which is exactly the partition condition in PDF p.17. -/
def LowerClosed {r : ℕ} (s : Finset (Node r)) : Prop :=
  ∀ a ∈ s, ∀ i ≤ a.2.1, ∀ j ≤ a.2.2, (a.1,i,j) ∈ s

/-- An r-multipartition as its actual finite node diagram, PDF p.17. -/
def MultipartitionShape (r : ℕ) := {s : Finset (Node r) // LowerClosed s}

/-- The empty multipartition at time zero, PDF p.17. -/
def emptyShape (r : ℕ) : MultipartitionShape r := ⟨∅, by simp [LowerClosed]⟩

/-- Addable nodes, requiring both absence and a valid enlarged partition. -/
def Addable {r : ℕ} (lambda : MultipartitionShape r) (a : Node r) : Prop :=
  a ∉ lambda.val ∧ LowerClosed (insert a lambda.val)

/-- RemovableNode nodes, requiring membership and a valid remaining partition. -/
def RemovableNode {r : ℕ} (lambda : MultipartitionShape r) (a : Node r) : Prop :=
  a ∈ lambda.val ∧ LowerClosed (lambda.val.erase a)

/-- All addable AND removable nodes, with the two directions distinguished. -/
def BoundaryNodes {r : ℕ} (lambda : MultipartitionShape r) :=
  Sum {a : Node r // Addable lambda a} {a : Node r // RemovableNode lambda a}

/-- One genuine box addition or removal, PDF p.17. In particular the box
cannot be inserted twice or removed from a diagram that does not contain it. -/
def ShapeStep {r : ℕ} (lambda mu : MultipartitionShape r) : Prop :=
  (∃ a, Addable lambda a ∧ mu.val = insert a lambda.val) ∨
  (∃ a, RemovableNode lambda a ∧ mu.val = lambda.val.erase a)

/-- The exact finite updown paths from empty to lambda, PDF pp.17--18. -/
def Updown (r n : ℕ) (lambda : MultipartitionShape r) :=
  {t : Fin (n+1) → MultipartitionShape r // t 0 = emptyShape r ∧ t (Fin.last n) = lambda ∧
    ∀ k : Fin n, ShapeStep (t k.castSucc) (t k.succ)}

/-- Time evaluation. The helper outside 0..n is empty and is never used in
a source formula without its time-range guard. -/
def pathAt {r n : ℕ} {lambda : MultipartitionShape r} (t : Updown r n lambda) (k : ℕ) : MultipartitionShape r :=
  if h : k < n+1 then t.val ⟨k,h⟩ else emptyShape r

/-- k-equivalence fixes all shapes at times other than k, Definition 4.1. -/
def KEquivalent {r n : ℕ} {lambda : MultipartitionShape r} (k : ℕ)
    (s t : Updown r n lambda) : Prop :=
  ∀ j : Fin (n+1), j.val ≠ k → s.val j = t.val j

/-- The signed content of the unique changed box at time k, PDF p.18.
Finite differences avoid an arbitrary choice of a box or a proof parameter.
Source p.17 prints the old row length for an added box; the actual differing
cell uses the new row length, as required by the add-box definition and p.18. -/
def content {R : Type*} [CommRing R] {r n : ℕ} (roots : Fin r → R)
    {lambda : MultipartitionShape r} (t : Updown r n lambda) (k : ℕ) : R :=
  (∑ a ∈ ((pathAt t k).val \ (pathAt t (k-1)).val),
    (roots a.1 + (a.2.2 : R) - (a.2.1 : R))) -
  (∑ a ∈ ((pathAt t (k-1)).val \ (pathAt t k).val),
    (roots a.1 + (a.2.2 : R) - (a.2.1 : R)))

/-- W-genericity, Definition 4.3, PDF p.18: all signed inter-component
collisions and the doubles are tested against small integers. -/
def WGeneric {R : Type*} [CommRing R] {r : ℕ} (n : ℕ) (roots : Fin r → R) : Prop :=
  (∀ i j : Fin r, i ≠ j → ∀ d : ℤ,
    (roots i + roots j = (d : R) ∨ roots i - roots j = (d : R)) → 2*n ≤ d.natAbs) ∧
  (∀ i : Fin r, ∀ d : ℤ, 2 * roots i = (d : R) → 2*n ≤ d.natAbs)

/-- Hecke-genericity, Definition 6.4, PDF p.41, corrected by the proof on
p.44: only DISTINCT component indices are compared. Printed: all i,j.
Changed: i != j, because i=j,d=0 would make the printed predicate impossible
at positive n, and the converse proof explicitly uses distinct indices. -/
def HeckeGeneric {R : Type*} [CommRing R] {r : ℕ} (n : ℕ) (roots : Fin r → R) : Prop :=
  ∀ i j : Fin r, i ≠ j → ∀ d : ℤ, roots i - roots j = (d : R) → n ≤ d.natAbs

/-- The empty partition has no removable box. -/
example (r : ℕ) (a : Node r) : ¬ RemovableNode (emptyShape r) a := by
  simp [RemovableNode, emptyShape]

/-- Equivalence of paths does not introduce a choice of action or coefficients. -/
example {r n : ℕ} {lambda : MultipartitionShape r} (t : Updown r n lambda) (k : ℕ) :
    KEquivalent k t t := by
  intro j hj
  rfl

/-- One Hecke parameter imposes no inter-component genericity restriction. -/
example {R : Type*} [CommRing R] (n : ℕ) (roots : Fin 1 → R) : HeckeGeneric n roots := by
  intro i j h
  exact False.elim (h (Subsingleton.elim i j))

/-- The pairs counted by the sum of squares in Corollary 5.2, PDF p.36.
The sigma type binds BOTH the contraction number and the terminal shape. -/
def TerminalPathPairs (r n : ℕ) :=
  (m : Fin (n/2+1)) ×
    (lambda : {s : MultipartitionShape r // s.val.card = n-2*m.val}) ×
      (Updown r n lambda.val × Updown r n lambda.val)

/-- At n=0 the time domain has exactly its initial/terminal time. -/
example : Fin.last 0 = (0 : Fin 1) := rfl

/-- Source Hecke generators, PDF p.10; there is no contraction or Omega. -/
inductive HLetter (n : ℕ)
  | t : Fin (n-1) → HLetter n
  | y : Fin n → HLetter n

/-- Free T_(i+1), with the out-of-range helper zero. -/
def freeHT (R : Type*) [CommRing R] (n i : ℕ) : FreeAlgebra R (HLetter n) :=
  if h : i < n-1 then FreeAlgebra.ι R (.t ⟨i,h⟩) else 0

/-- Free Y_(j+1), with the out-of-range helper zero. -/
def freeHY (R : Type*) [CommRing R] (n j : ℕ) : FreeAlgebra R (HLetter n) :=
  if h : j < n then FreeAlgebra.ι R (.y ⟨j,h⟩) else 0

/-- Every relation of the degenerate cyclotomic Hecke presentation, PDF p.10.
Both skein equations and all valid-index guards are included. -/
inductive HRel (R : Type*) [CommRing R] (n r : ℕ) (roots : Fin r → R) :
    FreeAlgebra R (HLetter n) → FreeAlgebra R (HLetter n) → Prop
  | square (i : ℕ) (hi : i+1 < n) : HRel R n r roots (freeHT R n i ^ 2) 1
  | far (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n) (hd : i + 1 < j ∨ j + 1 < i) :
      HRel R n r roots (freeHT R n i * freeHT R n j) (freeHT R n j * freeHT R n i)
  | braid (i : ℕ) (hi : i + 2 < n) :
      HRel R n r roots (freeHT R n i * freeHT R n (i+1) * freeHT R n i)
        (freeHT R n (i+1) * freeHT R n i * freeHT R n (i+1))
  | yy (i j : ℕ) (hi : i < n) (hj : j < n) :
      HRel R n r roots (freeHY R n i * freeHY R n j) (freeHY R n j * freeHY R n i)
  | ty (i j : ℕ) (hi : i + 1 < n) (hj : j < n) (hji : j ≠ i) (hji1 : j ≠ i + 1) :
      HRel R n r roots (freeHT R n i * freeHY R n j) (freeHY R n j * freeHT R n i)
  | skeinLeft (i : ℕ) (hi : i + 1 < n) :
      HRel R n r roots (freeHT R n i * freeHY R n i - freeHY R n (i+1) * freeHT R n i) (-1)
  | skeinRight (i : ℕ) (hi : i + 1 < n) :
      HRel R n r roots (freeHY R n i * freeHT R n i - freeHT R n i * freeHY R n (i+1)) (-1)
  | cyclotomic (hn : 1 ≤ n) :
      HRel R n r roots
        ((List.ofFn fun j : Fin r => freeHY R n 0 - algebraMap R _ (roots j)).prod) 0

/-- The actual presented degenerate cyclotomic Hecke algebra, PDF p.10. -/
abbrev CyclotomicHeckeAlgebra (R : Type*) [CommRing R] (n r : ℕ) (roots : Fin r → R) :=
  RingQuot (HRel R n r roots)

/-- Its canonical presentation map. -/
def hMap (R : Type*) [CommRing R] (n r : ℕ) (roots : Fin r → R) :
    FreeAlgebra R (HLetter n) →ₐ[R] CyclotomicHeckeAlgebra R n r roots :=
  RingQuot.mkAlgHom R (HRel R n r roots)

/-- The source T_(i+1) in the quotient. -/
def hT (R : Type*) [CommRing R] (n r : ℕ) (roots : Fin r → R) (i : ℕ) :
    CyclotomicHeckeAlgebra R n r roots := hMap R n r roots (freeHT R n i)

/-- The source Y_(j+1) in the quotient. -/
def hY (R : Type*) [CommRing R] (n r : ℕ) (roots : Fin r → R) (j : ℕ) :
    CyclotomicHeckeAlgebra R n r roots := hMap R n r roots (freeHY R n j)

/-- Two-strand presentation sanity: T_1 is an involution. -/
example (R : Type*) [CommRing R] (r : ℕ) (roots : Fin r → R) :
    hT R 2 r roots 0 ^ 2 = 1 := by
  have h := RingQuot.mkAlgHom_rel R
    (HRel.square (R := R) (n := 2) (r := r) (roots := roots) 0 (by decide))
  simpa only [hT, hMap, map_pow, map_one] using h

end QAlgorithms.Papers.Independent.Intake100.P65


