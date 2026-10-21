-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16
-- name    : QAlgorithms_Papers_Independent_Renew46_P16
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:18:36.138182+00:00
-- url     : https://prove2.me/theorems/e3bfc40f-4a91-43b8-88fa-552374bd3d79
-- title:
--   Definitions for On Cellular Algebras with Jucys Murphy Elements
-- statement:
--   The objects the formalized statements of *On Cellular Algebras with Jucys Murphy Elements* (arXiv:0907.3459) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BMWLetter`: Generator set of Definition 6.7, PDF p.23; indices are zero based.
--   - `freeS`: Free generator s_(i+1), with zero outside the generator range (PDF p.23).
--   - `freeE`: Free generator e_(i+1), with zero outside the generator range (PDF p.23).
--   - `freeX`: Free generator x_(i+1), with zero outside the generator range (PDF p.23).
--   - `BMWRel`: All nine groups of defining relations in Definition 6.7, PDF p.23. Each printed pair of equalities is included in both directions as needed; no admissibility, characteristic, or freeness assumption is imposed.
--   - `AffineBMW`: The actual degenerate affine BMW algebra, by generators and relations, Definition 6.7, PDF p.23. At level zero the generator set is empty.
--   - `affineBMWQuotientMap`: Canonical presentation map for Definition 6.7, PDF p.23.
--   - `affineS`: Image of s_(i+1) in the affine algebra, PDF p.23.
--   - `affineE`: Image of e_(i+1) in the affine algebra, PDF p.23.
--   - `affineX`: Image of x_(i+1) in the affine algebra, PDF p.23.
--   - `cyclotomicPolynomial`: The cyclotomic polynomial in x_1 of Definition 6.8, PDF p.23. The product order is the displayed parameter order.
--   - `cyclotomicRel`: The relation imposing the cyclotomic polynomial, Definition 6.8, PDF p.23.
--   - `CyclotomicBMW`: The degenerate cyclotomic BMW algebra, Definition 6.8, PDF p.23. Only positive r and positive n are used below.
--   - `cyclotomicMap`: Affine-to-cyclotomic quotient map, Definition 6.8, PDF p.23.
--   - `cyclotomicS`: Images of s_(i+1) in the cyclotomic quotient, PDF p.23.
--   - `cyclotomicE`: Images of e_(i+1) in the cyclotomic quotient, PDF p.23.
--   - `cyclotomicX`: Images of x_(i+1) in the cyclotomic quotient, PDF p.23.
--   - `levelImage`: Image of the rank m generator algebra in an ambient algebra (PDF pp.24--25). This uses canonical generator images rather than an assumed inclusion.
--   - `affineLevel`: The canonical image of W_m^aff in W_n^aff, PDF p.24; used for m ≤ n.
--   - `cyclotomicLevel`: The canonical image of W_m in W_n, PDF p.25; used for 1 ≤ m ≤ n.
--   - `rightProductSpan`: S-linear span of U e, interpreting the corner notation on PDF pp.24--25.
--   - `cornerSpan`: S-linear span of e U e, interpreting the corner notation on PDF p.24.
--   - `middleFactors`: The permitted middle factors in Lemma 6.11, PDF p.24. At n=1 only positive powers of x_1 occur.
--   - `CellIndex`: Pairs of cell indices together with their shape, Definition 2.1, PDF p.3.
--   - `higherCellSpan`: Strictly higher cell span of Definition 2.1, PDF p.3.
--   - `IsWeakCellularBasis`: The weaker cellular basis axioms, Definition 2.1, PDF p.3. In particular, the involution swaps indices only modulo the strictly higher cell span. Finiteness of shapes is a standing binder of the theorem using this predicate.
--   - `cellOrderSpan`: The cell order-ideal span A(Gamma), Lemma 6.19, PDF p.28. The closure toward higher labels is imposed explicitly in that theorem.
--   - `CellQuotient`: Quotient by the relations a-b in A(Gamma), Lemma 6.19, PDF p.28. Under the cellular and order-closure hypotheses, this is exactly A/A(Gamma).
--   - `cellQuotientMap`: Canonical quotient map in Lemma 6.19, PDF p.28.
--   - `quotientCells`: The displayed quotient basis, indexed by the complement of Gamma, Lemma 6.19, PDF p.28.
-- source:
--   On Cellular Algebras with Jucys Murphy Elements, arXiv:0907.3459v2, https://arxiv.org/abs/0907.3459v2

import Mathlib

/-!
Statements from Goodman--Graber, arXiv:0907.3459v2.
The presentation below is Definition 6.7 in full. Generator indices in Lean are
zero based: `affineS ... i`, `affineE ... i`, `affineX ... i` mean the source's
s_(i+1), e_(i+1), x_(i+1). Out-of-range helper values are zero and are never
used as source generators in a theorem. Lower-level algebras are represented
by their canonical generator images, without assuming those maps injective.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P16

/-- Generator set of Definition 6.7, PDF p.23; indices are zero based. -/
inductive BMWLetter (n : ℕ)
  | s : Fin (n - 1) → BMWLetter n
  | e : Fin (n - 1) → BMWLetter n
  | x : Fin n → BMWLetter n

/-- Free generator s_(i+1), with zero outside the generator range (PDF p.23). -/
def freeS (S : Type*) [CommRing S] (n i : ℕ) : FreeAlgebra S (BMWLetter n) :=
  if h : i < n - 1 then FreeAlgebra.ι S (.s ⟨i, h⟩) else 0

/-- Free generator e_(i+1), with zero outside the generator range (PDF p.23). -/
def freeE (S : Type*) [CommRing S] (n i : ℕ) : FreeAlgebra S (BMWLetter n) :=
  if h : i < n - 1 then FreeAlgebra.ι S (.e ⟨i, h⟩) else 0

/-- Free generator x_(i+1), with zero outside the generator range (PDF p.23). -/
def freeX (S : Type*) [CommRing S] (n i : ℕ) : FreeAlgebra S (BMWLetter n) :=
  if h : i < n then FreeAlgebra.ι S (.x ⟨i, h⟩) else 0

section Presentation

variable (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ)

local notation "ss" => freeS S n
local notation "ee" => freeE S n
local notation "xx" => freeX S n
local notation "scalar" => algebraMap S (FreeAlgebra S (BMWLetter n))

/-- All nine groups of defining relations in Definition 6.7, PDF p.23.
Each printed pair of equalities is included in both directions as needed;
no admissibility, characteristic, or freeness assumption is imposed. -/
inductive BMWRel (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ) : FreeAlgebra S (BMWLetter n) → FreeAlgebra S (BMWLetter n) → Prop
  | involution (i : ℕ) (hi : i + 1 < n) : BMWRel S omega n (freeS S n i ^ 2) 1
  | braidFar (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hd : i + 1 < j ∨ j + 1 < i) : BMWRel S omega n (freeS S n i * freeS S n j) (freeS S n j * freeS S n i)
  | braidNear (i : ℕ) (hi : i + 2 < n) :
      BMWRel S omega n (freeS S n i * freeS S n (i + 1) * freeS S n i) (freeS S n (i + 1) * freeS S n i * freeS S n (i + 1))
  | sx (i j : ℕ) (hi : i + 1 < n) (hj : j < n)
      (hji : j ≠ i) (hji1 : j ≠ i + 1) : BMWRel S omega n (freeS S n i * freeX S n j) (freeX S n j * freeS S n i)
  | idempotent (i : ℕ) (hi : i + 1 < n) : BMWRel S omega n (freeE S n i ^ 2) (algebraMap S (FreeAlgebra S (BMWLetter n)) (omega 0) * freeE S n i)
  | seFar (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hd : i + 1 < j ∨ j + 1 < i) : BMWRel S omega n (freeS S n i * freeE S n j) (freeE S n j * freeS S n i)
  | eeFar (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n)
      (hd : i + 1 < j ∨ j + 1 < i) : BMWRel S omega n (freeE S n i * freeE S n j) (freeE S n j * freeE S n i)
  | ex (i j : ℕ) (hi : i + 1 < n) (hj : j < n)
      (hji : j ≠ i) (hji1 : j ≠ i + 1) : BMWRel S omega n (freeE S n i * freeX S n j) (freeX S n j * freeE S n i)
  | xxCommute (i j : ℕ) (hi : i < n) (hj : j < n) : BMWRel S omega n (freeX S n i * freeX S n j) (freeX S n j * freeX S n i)
  | skeinLeft (i : ℕ) (hi : i + 1 < n) :
      BMWRel S omega n (freeS S n i * freeX S n i - freeX S n (i + 1) * freeS S n i) (freeE S n i - 1)
  | skeinRight (i : ℕ) (hi : i + 1 < n) :
      BMWRel S omega n (freeX S n i * freeS S n i - freeS S n i * freeX S n (i + 1)) (freeE S n i - 1)
  | unwrap (a : ℕ) (ha : 0 < a) (hn : 2 ≤ n) :
      BMWRel S omega n (freeE S n 0 * freeX S n 0 ^ a * freeE S n 0) (algebraMap S (FreeAlgebra S (BMWLetter n)) (omega a) * freeE S n 0)
  | es (i : ℕ) (hi : i + 1 < n) : BMWRel S omega n (freeE S n i * freeS S n i) (freeE S n i)
  | se (i : ℕ) (hi : i + 1 < n) : BMWRel S omega n (freeS S n i * freeE S n i) (freeE S n i)
  | tangleLeft (i : ℕ) (hi : i + 2 < n) :
      BMWRel S omega n (freeS S n i * freeE S n (i + 1) * freeE S n i) (freeS S n (i + 1) * freeE S n i)
  | tangleRight (i : ℕ) (hi : i + 2 < n) :
      BMWRel S omega n (freeE S n i * freeE S n (i + 1) * freeS S n i) (freeE S n i * freeS S n (i + 1))
  | tangleLeftReverse (i : ℕ) (hi : i + 2 < n) :
      BMWRel S omega n (freeE S n (i + 1) * freeE S n i * freeS S n (i + 1)) (freeE S n (i + 1) * freeS S n i)
  | tangleRightReverse (i : ℕ) (hi : i + 2 < n) :
      BMWRel S omega n (freeS S n (i + 1) * freeE S n i * freeE S n (i + 1)) (freeS S n i * freeE S n (i + 1))
  | untwistLeft (i : ℕ) (hi : i + 2 < n) :
      BMWRel S omega n (freeE S n (i + 1) * freeE S n i * freeE S n (i + 1)) (freeE S n (i + 1))
  | untwistRight (i : ℕ) (hi : i + 2 < n) : BMWRel S omega n (freeE S n i * freeE S n (i + 1) * freeE S n i) (freeE S n i)
  | antisymLeft (i : ℕ) (hi : i + 1 < n) : BMWRel S omega n (freeE S n i * (freeX S n i + freeX S n (i + 1))) 0
  | antisymRight (i : ℕ) (hi : i + 1 < n) : BMWRel S omega n ((freeX S n i + freeX S n (i + 1)) * freeE S n i) 0

/-- The actual degenerate affine BMW algebra, by generators and relations,
Definition 6.7, PDF p.23. At level zero the generator set is empty. -/
abbrev AffineBMW := RingQuot (BMWRel S omega n)

/-- Canonical presentation map for Definition 6.7, PDF p.23. -/
def affineBMWQuotientMap : FreeAlgebra S (BMWLetter n) →ₐ[S] AffineBMW S omega n :=
  RingQuot.mkAlgHom S (BMWRel S omega n)

/-- Image of s_(i+1) in the affine algebra, PDF p.23. -/
def affineS (i : ℕ) : AffineBMW S omega n := affineBMWQuotientMap S omega n (ss i)

/-- Image of e_(i+1) in the affine algebra, PDF p.23. -/
def affineE (i : ℕ) : AffineBMW S omega n := affineBMWQuotientMap S omega n (ee i)

/-- Image of x_(i+1) in the affine algebra, PDF p.23. -/
def affineX (i : ℕ) : AffineBMW S omega n := affineBMWQuotientMap S omega n (xx i)

end Presentation

/-- The cyclotomic polynomial in x_1 of Definition 6.8, PDF p.23.
The product order is the displayed parameter order. -/
def cyclotomicPolynomial (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) : AffineBMW S omega n :=
  (List.ofFn fun j : Fin r => affineX S omega n 0 - algebraMap S _ (u j)).prod

/-- The relation imposing the cyclotomic polynomial, Definition 6.8, PDF p.23. -/
def cyclotomicRel (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) (a b : AffineBMW S omega n) : Prop :=
  a = cyclotomicPolynomial S omega n r u ∧ b = 0

/-- The degenerate cyclotomic BMW algebra, Definition 6.8, PDF p.23.
Only positive r and positive n are used below. -/
abbrev CyclotomicBMW (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) := RingQuot (cyclotomicRel S omega n r u)

/-- Affine-to-cyclotomic quotient map, Definition 6.8, PDF p.23. -/
def cyclotomicMap (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) : AffineBMW S omega n →ₐ[S] CyclotomicBMW S omega n r u :=
  RingQuot.mkAlgHom S (cyclotomicRel S omega n r u)

/-- Images of s_(i+1) in the cyclotomic quotient, PDF p.23. -/
def cyclotomicS (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) (i : ℕ) : CyclotomicBMW S omega n r u :=
  cyclotomicMap S omega n r u (affineS S omega n i)

/-- Images of e_(i+1) in the cyclotomic quotient, PDF p.23. -/
def cyclotomicE (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) (i : ℕ) : CyclotomicBMW S omega n r u :=
  cyclotomicMap S omega n r u (affineE S omega n i)

/-- Images of x_(i+1) in the cyclotomic quotient, PDF p.23. -/
def cyclotomicX (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) (i : ℕ) : CyclotomicBMW S omega n r u :=
  cyclotomicMap S omega n r u (affineX S omega n i)

/-- Image of the rank m generator algebra in an ambient algebra (PDF pp.24--25).
This uses canonical generator images rather than an assumed inclusion. -/
def levelImage (S : Type*) [CommRing S] {A : Type*} [Ring A] [Algebra S A]
    (s e x : ℕ → A) (m : ℕ) : Subalgebra S A :=
  Algebra.adjoin S {z | (∃ i, i + 1 < m ∧ (z = s i ∨ z = e i)) ∨
    (∃ i, i < m ∧ z = x i)}

/-- The canonical image of W_m^aff in W_n^aff, PDF p.24; used for m ≤ n. -/
def affineLevel (S : Type*) [CommRing S] (omega : ℕ → S) (n m : ℕ) :
    Subalgebra S (AffineBMW S omega n) :=
  levelImage S (affineS S omega n) (affineE S omega n) (affineX S omega n) m

/-- The canonical image of W_m in W_n, PDF p.25; used for 1 ≤ m ≤ n. -/
def cyclotomicLevel (S : Type*) [CommRing S] (omega : ℕ → S)
    (n r : ℕ) (u : Fin r → S) (m : ℕ) : Subalgebra S (CyclotomicBMW S omega n r u) :=
  levelImage S (cyclotomicS S omega n r u) (cyclotomicE S omega n r u)
    (cyclotomicX S omega n r u) m

/-- S-linear span of U e, interpreting the corner notation on PDF pp.24--25. -/
def rightProductSpan (S : Type*) [CommRing S] {A : Type*} [Ring A] [Algebra S A]
    (U : Set A) (e : A) : Submodule S A :=
  Submodule.span S ((fun a : A => a * e) '' U)

/-- S-linear span of e U e, interpreting the corner notation on PDF p.24. -/
def cornerSpan (S : Type*) [CommRing S] {A : Type*} [Ring A] [Algebra S A]
    (U : Set A) (e : A) : Submodule S A :=
  Submodule.span S ((fun a : A => e * a * e) '' U)

/-- The permitted middle factors in Lemma 6.11, PDF p.24.
At n=1 only positive powers of x_1 occur. -/
def middleFactors (S : Type*) [CommRing S] (omega : ℕ → S) (n : ℕ) :
    Set (AffineBMW S omega n) :=
  {z | (2 ≤ n ∧ (z = affineE S omega n (n - 2) ∨ z = affineS S omega n (n - 2))) ∨
    (∃ a : ℕ, 1 ≤ a ∧ z = affineX S omega n (n - 1) ^ a)}

/-- Presentation sanity check: at two strands the first s generator squares to one. -/
example (S : Type*) [CommRing S] (omega : ℕ → S) :
    affineS S omega 2 0 ^ 2 = 1 := by
  have h := RingQuot.mkAlgHom_rel S (BMWRel.involution (S := S) (omega := omega) (n := 2) 0 (by decide))
  simpa only [affineS, affineBMWQuotientMap, map_pow, map_one] using h

/-- Pairs of cell indices together with their shape, Definition 2.1, PDF p.3. -/
abbrev CellIndex (L : Type*) (T : L → Type*) := Σ l, T l × T l

/-- Strictly higher cell span of Definition 2.1, PDF p.3. -/
def higherCellSpan {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    [PartialOrder L] {T : L → Type*} (c : CellIndex L T → A) (l : L) : Submodule R A :=
  Submodule.span R {a | ∃ m, l < m ∧ ∃ s t : T m, a = c ⟨m, (s, t)⟩}

/-- The weaker cellular basis axioms, Definition 2.1, PDF p.3. In particular,
the involution swaps indices only modulo the strictly higher cell span.
Finiteness of shapes is a standing binder of the theorem using this predicate. -/
def IsWeakCellularBasis {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    [PartialOrder L] {T : L → Type*} [∀ l, Fintype (T l)]
    (c : CellIndex L T → A) (i : A →ₗ[R] A) : Prop :=
  Function.Involutive i ∧ (∀ a b, i (a * b) = i b * i a) ∧
  LinearIndependent R c ∧ Submodule.span R (Set.range c) = ⊤ ∧
  (∀ l (s : T l) (a : A), ∃ r : T l → R, ∀ t : T l,
    a * c ⟨l, (s, t)⟩ - ∑ v : T l, r v • c ⟨l, (v, t)⟩ ∈ higherCellSpan (R := R) c l) ∧
  (∀ l (s t : T l), i (c ⟨l, (s, t)⟩) - c ⟨l, (t, s)⟩ ∈ higherCellSpan (R := R) c l)

/-- The cell order-ideal span A(Gamma), Lemma 6.19, PDF p.28.
The closure toward higher labels is imposed explicitly in that theorem. -/
def cellOrderSpan {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    {T : L → Type*} (c : CellIndex L T → A) (Gamma : L → Prop) : Submodule R A :=
  Submodule.span R {a | ∃ l, Gamma l ∧ ∃ s t : T l, a = c ⟨l, (s, t)⟩}

/-- Quotient by the relations a-b in A(Gamma), Lemma 6.19, PDF p.28.
Under the cellular and order-closure hypotheses, this is exactly A/A(Gamma). -/
abbrev CellQuotient {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    {T : L → Type*} (c : CellIndex L T → A) (Gamma : L → Prop) :=
  RingQuot (fun a b : A => a - b ∈ cellOrderSpan (R := R) c Gamma)

/-- Canonical quotient map in Lemma 6.19, PDF p.28. -/
def cellQuotientMap {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    {T : L → Type*} (c : CellIndex L T → A) (Gamma : L → Prop) :
    A →ₐ[R] CellQuotient (R := R) c Gamma :=
  RingQuot.mkAlgHom R (fun a b : A => a - b ∈ cellOrderSpan (R := R) c Gamma)

/-- The displayed quotient basis, indexed by the complement of Gamma,
Lemma 6.19, PDF p.28. -/
def quotientCells {R A L : Type*} [CommRing R] [Ring A] [Algebra R A]
    {T : L → Type*} (c : CellIndex L T → A) (Gamma : L → Prop) :
    CellIndex {l : L // ¬ Gamma l} (fun l => T l.val) → CellQuotient (R := R) c Gamma :=
  fun z => cellQuotientMap (R := R) c Gamma (c ⟨z.1.val, z.2⟩)

/-- Sanity check on the weaker axiom: a single shape has no strictly higher cells. -/
example {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (c : CellIndex Unit (fun _ => Unit) → A) : higherCellSpan (R := R) c () = ⊥ := by
  simp [higherCellSpan]

end QAlgorithms.Papers.Independent.Renew46.P16


