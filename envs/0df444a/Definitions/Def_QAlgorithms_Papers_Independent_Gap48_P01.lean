-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01
-- name    : QAlgorithms_Papers_Independent_Gap48_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:41:13.33799+00:00
-- url     : https://prove2.me/theorems/2753a73a-a2c0-4b6d-8c8e-84153c749a0b
-- title:
--   Definitions for On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras
-- statement:
--   The objects the formalized statements of *On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras* (arXiv:0911.5284) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NonsplitParameters`: Ground data of Definition 2.1, PDF pp.4--5, including its sole scalar relation.
--   - `skeinDelta`: skeinDelta=q-q inverse, Definition 2.1, PDF p.4.
--   - `loopZero`: A_0, which is an arbitrary scalar rather than a unit, PDF p.4.
--   - `CyclotomicLetter`: Letters for Definition 2.1, PDF pp.4--5. There are no letters at level zero.
--   - `nonsplitFreeX`: Free X_i or its inverse. Zero is only an out-of-range helper, PDF p.4.
--   - `nonsplitFreeE`: Free e_i, with zero outside the source generator range, PDF p.4.
--   - `nonsplitFreeY`: Free Y or its inverse, absent at level zero, PDF pp.4--5,20.
--   - `NonsplitBMWRel`: All of relations (1)--(15), with both inverse identities and both sides of chained equalities. Adjacent indices are ordered. Definition 2.1, PDF pp.4--5.
--   - `NonsplitBMW`: The actual presented cyclotomic NonsplitBMW algebra, Definition 2.1, PDF pp.4--5.
--   - `presentationMap`: Canonical presentation homomorphism, PDF pp.4--5.
--   - `X`: X_i (or X_i inverse), PDF p.4.
--   - `E`: e_i, PDF p.4.
--   - `Y`: Y (or its inverse), PDF pp.4--5.
--   - `JM`: Y'_i or its explicit inverse word, PDF p.6. The value at i=0 is unused.
--   - `JPower`: Integer powers of Y'_i, using the explicit inverse word for negative powers, PDF pp.6--7. This never uses a default ring inverse.
--   - `intervalProduct`: Ordered product a_s ... a_(t-1), including the empty product 1, PDF p.11.
--   - `alphaChain`: alphaChain^p_(i,j,l)=Y'_i^p X_i...X_(j-1)e_j...e_l, PDF p.11. Used only for 1≤i≤j≤l+1 and l<n; the possible empty e-tail is explicit.
--   - `level`: Canonical smaller-algebra image as its generator subalgebra, PDF p.11. In particular level 0 consists of scalars and injectivity is not assumed.
--   - `alphaSpan`: The span <alphaChain^p_(i,j,l) Btilde_(l-1)> with a filter on indices and p, PDF pp.12,16. Bounds on valid alphaChain chains are intrinsic to the set.
--   - `IsLeftIdealIn`: A submodule is a left ideal of the indicated canonical image, PDF pp.16,19.
--   - `exponentRange`: The centered exponent interval P, PDF p.16.
--   - `chainWords`: General and ordered alphaChain-chain word sets of PDF p.19, including m=0; sets are empty when 2m>l. Indices f are zero-based positions in the product.
--   - `productSpan`: Product notation U V means the R-span of products, PDF p.19.
--   - `NonsplitHeckeRel`: Independent Ariki--Koike presentation with T_0=Y and T_i represented by nonsplitFreeX i. The auxiliary e letters are killed, not given NonsplitBMW relations. Definition 3.1, PDF pp.10--11. SOURCE CORRECTION: its printed quadratic upper index n-2 is n-1, as required by the quotient calculation on p.11. Independent moderation pending.
--   - `NonsplitHecke`: The Ariki--Koike algebra for qprime=q^2, Definition 3.1, PDF pp.10--11.
--   - `eIdeal`: Two-sided ideal spanned by all a e_i b, PDF p.11.
--   - `HeckeQuotient`: The quotient by the actual e-generated ideal, PDF p.11.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, https://arxiv.org/abs/0911.5284v1

import Mathlib

/-!
Statements from Wilcox--Yu, arXiv:0911.5284v1.
All indices are the source's one-based indices. This is the nonsplit presentation:
A_0 need not be invertible and skeinDelta may be zero or a zero divisor.
Theorems are statement targets, with proofs deliberately omitted.
Compilation is pending the batch compilation handoff.
-/

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

/-- Ground data of Definition 2.1, PDF pp.4--5, including its sole scalar relation. -/
structure NonsplitParameters (R : Type*) [CommRing R] (k : ℕ) where
  positive : 0 < k
  q : Rˣ
  lam : Rˣ
  constant : Rˣ
  coeff : Fin k → R
  constant_eq : coeff ⟨0, positive⟩ = (constant : R)
  loop : Fin k → R
  ground : (lam : R) - ↑lam⁻¹ = ((q : R) - ↑q⁻¹) * (1 - loop ⟨0, positive⟩)

/-- skeinDelta=q-q inverse, Definition 2.1, PDF p.4. -/
def skeinDelta {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) : R :=
  (P.q : R) - ↑P.q⁻¹

/-- A_0, which is an arbitrary scalar rather than a unit, PDF p.4. -/
def loopZero {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) : R :=
  P.loop ⟨0, P.positive⟩

/-- Letters for Definition 2.1, PDF pp.4--5. There are no letters at level zero. -/
inductive CyclotomicLetter (n : ℕ)
  | x : {i : ℕ // 1 ≤ i ∧ i < n} → Bool → CyclotomicLetter n
  | e : {i : ℕ // 1 ≤ i ∧ i < n} → CyclotomicLetter n
  | y : Fin (min n 1) → Bool → CyclotomicLetter n

/-- Free X_i or its inverse. Zero is only an out-of-range helper, PDF p.4. -/
def nonsplitFreeX (R : Type*) [CommRing R] (n i : ℕ) (inv : Bool) : FreeAlgebra R (CyclotomicLetter n) :=
  if h : 1 ≤ i ∧ i < n then FreeAlgebra.ι R (.x ⟨i, h⟩ inv) else 0

/-- Free e_i, with zero outside the source generator range, PDF p.4. -/
def nonsplitFreeE (R : Type*) [CommRing R] (n i : ℕ) : FreeAlgebra R (CyclotomicLetter n) :=
  if h : 1 ≤ i ∧ i < n then FreeAlgebra.ι R (.e ⟨i, h⟩) else 0

/-- Free Y or its inverse, absent at level zero, PDF pp.4--5,20. -/
def nonsplitFreeY (R : Type*) [CommRing R] (n : ℕ) (inv : Bool) : FreeAlgebra R (CyclotomicLetter n) :=
  if h : 0 < min n 1 then FreeAlgebra.ι R (.y ⟨0, h⟩ inv) else 0

/-- All of relations (1)--(15), with both inverse identities and both sides of
chained equalities. Adjacent indices are ordered. Definition 2.1, PDF pp.4--5. -/
inductive NonsplitBMWRel {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :
    FreeAlgebra R (CyclotomicLetter n) → FreeAlgebra R (CyclotomicLetter n) → Prop
  | invL (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitBMWRel P n (nonsplitFreeX R n i false * nonsplitFreeX R n i true) 1
  | invR (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitBMWRel P n (nonsplitFreeX R n i true * nonsplitFreeX R n i false) 1
  | yInvL (hn : 0 < n) : NonsplitBMWRel P n (nonsplitFreeY R n false * nonsplitFreeY R n true) 1
  | yInvR (hn : 0 < n) : NonsplitBMWRel P n (nonsplitFreeY R n true * nonsplitFreeY R n false) 1
  | skein (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitBMWRel P n
      (nonsplitFreeX R n i false - nonsplitFreeX R n i true)
      (algebraMap R _ (skeinDelta P) * (1 - nonsplitFreeE R n i))
  | xFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i + 1 < j ∨ j + 1 < i) : NonsplitBMWRel P n
      (nonsplitFreeX R n i false * nonsplitFreeX R n j false) (nonsplitFreeX R n j false * nonsplitFreeX R n i false)
  | braid (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) : NonsplitBMWRel P n
      (nonsplitFreeX R n i false * nonsplitFreeX R n (i+1) false * nonsplitFreeX R n i false)
      (nonsplitFreeX R n (i+1) false * nonsplitFreeX R n i false * nonsplitFreeX R n (i+1) false)
  | xeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i + 1 < j ∨ j + 1 < i) : NonsplitBMWRel P n
      (nonsplitFreeX R n i false * nonsplitFreeE R n j) (nonsplitFreeE R n j * nonsplitFreeX R n i false)
  | eeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i + 1 < j ∨ j + 1 < i) : NonsplitBMWRel P n
      (nonsplitFreeE R n i * nonsplitFreeE R n j) (nonsplitFreeE R n j * nonsplitFreeE R n i)
  | xe (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitBMWRel P n
      (nonsplitFreeX R n i false * nonsplitFreeE R n i) (algebraMap R _ (P.lam : R) * nonsplitFreeE R n i)
  | ex (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitBMWRel P n
      (nonsplitFreeE R n i * nonsplitFreeX R n i false) (algebraMap R _ (P.lam : R) * nonsplitFreeE R n i)
  | nearL (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i + 1 = j ∨ j + 1 = i) : NonsplitBMWRel P n
      (nonsplitFreeX R n i false * nonsplitFreeX R n j false * nonsplitFreeE R n i) (nonsplitFreeE R n j * nonsplitFreeE R n i)
  | nearR (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i + 1 = j ∨ j + 1 = i) : NonsplitBMWRel P n
      (nonsplitFreeE R n j * nonsplitFreeX R n i false * nonsplitFreeX R n j false) (nonsplitFreeE R n j * nonsplitFreeE R n i)
  | tripleE (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i + 1 = j ∨ j + 1 = i) : NonsplitBMWRel P n
      (nonsplitFreeE R n i * nonsplitFreeE R n j * nonsplitFreeE R n i) (nonsplitFreeE R n i)
  | squareE (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitBMWRel P n
      (nonsplitFreeE R n i ^ 2) (algebraMap R _ (loopZero P) * nonsplitFreeE R n i)
  | cyclotomic (hn : 0 < n) : NonsplitBMWRel P n (nonsplitFreeY R n false ^ k)
      (∑ j : Fin k, algebraMap R _ (P.coeff j) * nonsplitFreeY R n false ^ j.val)
  | affine (hn : 2 ≤ n) : NonsplitBMWRel P n
      (nonsplitFreeX R n 1 false * nonsplitFreeY R n false * nonsplitFreeX R n 1 false * nonsplitFreeY R n false)
      (nonsplitFreeY R n false * nonsplitFreeX R n 1 false * nonsplitFreeY R n false * nonsplitFreeX R n 1 false)
  | yx (i : ℕ) (hi : 1 < i ∧ i < n) : NonsplitBMWRel P n
      (nonsplitFreeY R n false * nonsplitFreeX R n i false) (nonsplitFreeX R n i false * nonsplitFreeY R n false)
  | ye (i : ℕ) (hi : 1 < i ∧ i < n) : NonsplitBMWRel P n
      (nonsplitFreeY R n false * nonsplitFreeE R n i) (nonsplitFreeE R n i * nonsplitFreeY R n false)
  | unwrapL (hn : 2 ≤ n) : NonsplitBMWRel P n
      (nonsplitFreeY R n false * nonsplitFreeX R n 1 false * nonsplitFreeY R n false * nonsplitFreeE R n 1)
      (algebraMap R _ (↑P.lam⁻¹ : R) * nonsplitFreeE R n 1)
  | unwrapR (hn : 2 ≤ n) : NonsplitBMWRel P n
      (nonsplitFreeE R n 1 * nonsplitFreeY R n false * nonsplitFreeX R n 1 false * nonsplitFreeY R n false)
      (algebraMap R _ (↑P.lam⁻¹ : R) * nonsplitFreeE R n 1)
  | loop (m : Fin k) (hn : 2 ≤ n) : NonsplitBMWRel P n
      (nonsplitFreeE R n 1 * nonsplitFreeY R n false ^ m.val * nonsplitFreeE R n 1)
      (algebraMap R _ (P.loop m) * nonsplitFreeE R n 1)

/-- The actual presented cyclotomic NonsplitBMW algebra, Definition 2.1, PDF pp.4--5. -/
abbrev NonsplitBMW {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :=
  RingQuot (NonsplitBMWRel P n)

/-- Canonical presentation homomorphism, PDF pp.4--5. -/
def presentationMap {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :
    FreeAlgebra R (CyclotomicLetter n) →ₐ[R] NonsplitBMW P n := RingQuot.mkAlgHom R (NonsplitBMWRel P n)

/-- X_i (or X_i inverse), PDF p.4. -/
def X {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n i : ℕ) (inv : Bool := false) : NonsplitBMW P n :=
  presentationMap P n (nonsplitFreeX R n i inv)

/-- e_i, PDF p.4. -/
def E {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n i : ℕ) : NonsplitBMW P n :=
  presentationMap P n (nonsplitFreeE R n i)

/-- Y (or its inverse), PDF pp.4--5. -/
def Y {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) (inv : Bool := false) : NonsplitBMW P n :=
  presentationMap P n (nonsplitFreeY R n inv)

/-- Y'_i or its explicit inverse word, PDF p.6. The value at i=0 is unused. -/
def JM {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) (inv : Bool) : ℕ → NonsplitBMW P n
  | 0 => 0
  | 1 => Y P n inv
  | i+2 => X P n (i+1) inv * JM P n inv (i+1) * X P n (i+1) inv

/-- Integer powers of Y'_i, using the explicit inverse word for negative powers,
PDF pp.6--7. This never uses a default ring inverse. -/
def JPower {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n i : ℕ) (p : ℤ) : NonsplitBMW P n :=
  if 0 ≤ p then JM P n false i ^ p.toNat else JM P n true i ^ (-p).toNat

/-- Ordered product a_s ... a_(t-1), including the empty product 1, PDF p.11. -/
def intervalProduct {A : Type*} [Monoid A] (a : ℕ → A) (s t : ℕ) : A :=
  ((List.range (t-s)).map fun j => a (s+j)).prod

/-- alphaChain^p_(i,j,l)=Y'_i^p X_i...X_(j-1)e_j...e_l, PDF p.11.
Used only for 1≤i≤j≤l+1 and l<n; the possible empty e-tail is explicit. -/
def alphaChain {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n i j l : ℕ) (p : ℤ) : NonsplitBMW P n :=
  JPower P n i p * intervalProduct (fun t => X P n t false) i j *
    intervalProduct (E P n) j (l+1)

/-- Canonical smaller-algebra image as its generator subalgebra, PDF p.11.
In particular level 0 consists of scalars and injectivity is not assumed. -/
def level {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n l : ℕ) : Subalgebra R (NonsplitBMW P n) :=
  Algebra.adjoin R {z | (1 ≤ l ∧ (z = Y P n false ∨ z = Y P n true)) ∨
    ∃ i, 1 ≤ i ∧ i < l ∧ (z = X P n i false ∨ z = X P n i true ∨ z = E P n i)}

/-- The span <alphaChain^p_(i,j,l) Btilde_(l-1)> with a filter on indices and p,
PDF pp.12,16. Bounds on valid alphaChain chains are intrinsic to the set. -/
def alphaSpan {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n l : ℕ)
    (filter : ℕ → ℤ → Prop) : Submodule R (NonsplitBMW P n) :=
  Submodule.span R {z | ∃ i j : ℕ, ∃ p : ℤ,
    1 ≤ i ∧ i ≤ j ∧ j ≤ l ∧ filter i p ∧
    ∃ b ∈ level P n (l-1), z = alphaChain P n i j l p * b}

/-- A submodule is a left ideal of the indicated canonical image, PDF pp.16,19. -/
def IsLeftIdealIn {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (B : Subalgebra R A) (L : Submodule R A) : Prop :=
  (∀ z ∈ L, z ∈ B) ∧ ∀ a ∈ B, ∀ z ∈ L, a * z ∈ L

/-- The centered exponent interval P, PDF p.16. -/
def exponentRange (k : ℕ) (p : ℤ) : Prop :=
  -(((k-1)/2 : ℕ) : ℤ) ≤ p ∧ p ≤ (k/2 : ℕ)

/-- General and ordered alphaChain-chain word sets of PDF p.19, including m=0;
sets are empty when 2m>l. Indices f are zero-based positions in the product. -/
def chainWords {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n l m : ℕ)
    (ordered : Bool) : Set (NonsplitBMW P n) :=
  {z | 2*m ≤ l ∧ ∃ i j : Fin m → ℕ, ∃ p : Fin m → ℤ,
    (∀ f, 1 ≤ i f ∧ i f ≤ j f ∧ j f ≤ l-2*f.val-1 ∧ exponentRange k (p f)) ∧
    (ordered = true → ∀ f g, f < g → i g < i f) ∧
    z = (List.ofFn fun f : Fin m => alphaChain P n (i f) (j f) (l-2*f.val-1) (p f)).prod}

/-- Product notation U V means the R-span of products, PDF p.19. -/
def productSpan {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (U V : Set A) : Submodule R A :=
  Submodule.span R {z | ∃ a ∈ U, ∃ b ∈ V, z = a*b}

/-- Sanity: the JM element at index one is Y, PDF p.6. -/
example {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :
    JM P n false 1 = Y P n false := by rfl

/-- Sanity: integer exponent zero is the identity, PDF p.7. -/
example {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n i : ℕ) :
    JPower P n i 0 = 1 := by simp [JPower]

/-- Sanity: an empty interval product is 1, PDF p.11. -/
example {A : Type*} [Monoid A] (a : ℕ → A) (i : ℕ) : intervalProduct a i i = 1 := by
  simp [intervalProduct]

/-- Sanity: the presentation really imposes (9) at two strands, PDF p.5. -/
example {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) :
    E P 2 1 ^ 2 = algebraMap R _ (loopZero P) * E P 2 1 := by
  have h := RingQuot.mkAlgHom_rel R (NonsplitBMWRel.squareE (P := P) (n := 2) 1 (by omega))
  simpa only [E, presentationMap, map_pow, map_mul, AlgHom.commutes] using h

/-- Sanity: no source generator exists at level zero, PDF p.20. -/
example (a : CyclotomicLetter 0) : False := by
  cases a with
  | x i inv => have := i.property; omega
  | e i => have := i.property; omega
  | y i inv => have := i.isLt; omega

section Statements

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

end Statements

/-- Independent Ariki--Koike presentation with T_0=Y and T_i represented by
nonsplitFreeX i. The auxiliary e letters are killed, not given NonsplitBMW relations.
Definition 3.1, PDF pp.10--11. SOURCE CORRECTION: its printed quadratic
upper index n-2 is n-1, as required by the quotient calculation on p.11.
Independent moderation pending. -/
inductive NonsplitHeckeRel {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :
    FreeAlgebra R (CyclotomicLetter n) → FreeAlgebra R (CyclotomicLetter n) → Prop
  | invL (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitHeckeRel P n (nonsplitFreeX R n i false * nonsplitFreeX R n i true) 1
  | invR (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitHeckeRel P n (nonsplitFreeX R n i true * nonsplitFreeX R n i false) 1
  | yInvL (hn : 0 < n) : NonsplitHeckeRel P n (nonsplitFreeY R n false * nonsplitFreeY R n true) 1
  | yInvR (hn : 0 < n) : NonsplitHeckeRel P n (nonsplitFreeY R n true * nonsplitFreeY R n false) 1
  | braid (i : ℕ) (hi : 1 ≤ i ∧ i+1 < n) : NonsplitHeckeRel P n
      (nonsplitFreeX R n i false * nonsplitFreeX R n (i+1) false * nonsplitFreeX R n i false)
      (nonsplitFreeX R n (i+1) false * nonsplitFreeX R n i false * nonsplitFreeX R n (i+1) false)
  | far (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i+1 < j ∨ j+1 < i) : NonsplitHeckeRel P n
      (nonsplitFreeX R n i false * nonsplitFreeX R n j false) (nonsplitFreeX R n j false * nonsplitFreeX R n i false)
  | affine (hn : 2 ≤ n) : NonsplitHeckeRel P n
      (nonsplitFreeY R n false * nonsplitFreeX R n 1 false * nonsplitFreeY R n false * nonsplitFreeX R n 1 false)
      (nonsplitFreeX R n 1 false * nonsplitFreeY R n false * nonsplitFreeX R n 1 false * nonsplitFreeY R n false)
  | yFar (i : ℕ) (hi : 1 < i ∧ i < n) : NonsplitHeckeRel P n
      (nonsplitFreeY R n false * nonsplitFreeX R n i false) (nonsplitFreeX R n i false * nonsplitFreeY R n false)
  | cyclotomic (hn : 0 < n) : NonsplitHeckeRel P n (nonsplitFreeY R n false ^ k)
      (∑ j : Fin k, algebraMap R _ (P.coeff j) * nonsplitFreeY R n false ^ j.val)
  | quadratic (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitHeckeRel P n (nonsplitFreeX R n i false ^ 2)
      (algebraMap R _ ((P.q : R)^2 - 1) * nonsplitFreeX R n i false + algebraMap R _ ((P.q : R)^2))
  | killE (i : ℕ) (hi : 1 ≤ i ∧ i < n) : NonsplitHeckeRel P n (nonsplitFreeE R n i) 0

/-- The Ariki--Koike algebra for qprime=q^2, Definition 3.1, PDF pp.10--11. -/
abbrev NonsplitHecke {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :=
  RingQuot (NonsplitHeckeRel P n)

/-- Two-sided ideal spanned by all a e_i b, PDF p.11. -/
def eIdeal {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) : Submodule R (NonsplitBMW P n) :=
  Submodule.span R {z | ∃ i, 1 ≤ i ∧ i < n ∧ ∃ a b : NonsplitBMW P n, z = a * E P n i * b}

/-- The quotient by the actual e-generated ideal, PDF p.11. -/
abbrev HeckeQuotient {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :=
  RingQuot (fun a b : NonsplitBMW P n => a-b ∈ eIdeal P n)

/-- Sanity: the independent NonsplitHecke presentation includes the last quadratic
relation, already at n=2. Definition 3.1 corrected as on PDF p.11. -/
example {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) :
    (RingQuot.mkAlgHom R (NonsplitHeckeRel P 2)) (nonsplitFreeX R 2 1 false ^ 2) =
    (RingQuot.mkAlgHom R (NonsplitHeckeRel P 2))
      (algebraMap R _ ((P.q : R)^2 - 1) * nonsplitFreeX R 2 1 false + algebraMap R _ ((P.q : R)^2)) := by
  exact RingQuot.mkAlgHom_rel R (NonsplitHeckeRel.quadratic (P := P) (n := 2) 1 (by omega))

end QAlgorithms.Papers.Independent.Gap48.P01


