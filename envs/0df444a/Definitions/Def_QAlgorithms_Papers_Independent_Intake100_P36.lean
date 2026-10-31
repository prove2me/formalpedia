-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36
-- name    : QAlgorithms_Papers_Independent_Intake100_P36
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:53:25.17231+00:00
-- url     : https://prove2.me/theorems/79be2108-16ad-4143-918b-3c1b7c00d0be
-- title:
--   Definitions for The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras
-- statement:
--   The objects the formalized statements of *The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras* (arXiv:math/0204025) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AKFree`: The free algebra on exactly T_0,...,T_(n-1), PDF p.4.
--   - `akFreeGenerator`: A helper for generators; out-of-range indices return zero and never enter a relation.
--   - `AKRel`: Corrected Definition 2.1, PDF p.4. Each relation is guarded by its degree domain. The ordered cyclotomic product keeps repeated and zero parameters.
--   - `ArikiKoike`: The presented algebra H, not an algebra equipped with a presumed basis (PDF p.4).
--   - `akT`: The quotient images of the generators, PDF p.4.
--   - `jmNat`: L_(k+1), with zero-based helper k; the q^(-1) factor is essential (PDF p.4).
--   - `cyclotomicJM`: The n genuine JM elements, L_1,...,L_n (PDF p.4).
--   - `reducedWord`: Choose a reduced expression using the accepted Coxeter predicate (PDF p.4). Reverse the word for right actions: the first written letter acts first. Adjacent transpositions generate S_n, so this choice predicate is inhabited for every w.
--   - `tw`: T_w computed by a reduced word. No independence or spanning assertion is a field (PDF p.4).
--   - `jmPowers`: Ordered product L_1^a_1...L_n^a_n, including the empty product 1 (PDF p.4).
--   - `arikiKoikeMonomial`: The explicit family of Theorem 2.2 (PDF p.4).
--   - `jmEval`: Finite ordered evaluation makes sense before commutativity is proved (PDF p.4). Once the JM theorem is used it is ordinary multivariate polynomial evaluation.
--   - `qInteger`: The quantum integer 1+q+...+q^(m-1), PDF p.11.
--   - `semisimplicityPolynomial`: The exact semisimplicity polynomial P_H, PDF p.11. Integer powers are powers of the unit q, not total division by an arbitrary element.
--   - `MultiPartition`: Multipartitions of n as decreasing rows, padded by zero to n rows (PDF p.11). Every part is at most n. Fin 0 represents the unique empty component at degree zero.
--   - `Node`: Nodes (component,row,column), all zero-based; source nodes add one to each index (PDF p.11).
--   - `StandardMultiTableau`: A standard tableau is a bijective labeling increasing in rows and columns (PDF p.11).
--   - `rowNumber`: Count the nodes strictly before x in component/row/column reading order (PDF p.16).
--   - `tableauPermutation`: d(t) is the unique permutation carrying row reading labels to t (PDF p.16). The predicate computes d(t) from the bijection, not from an assumed H-action.
--   - `rowStabilizer`: The row-stabilizer of the row reading tableau (PDF p.16).
--   - `precedingSize`: Size of components strictly preceding s (PDF p.16).
--   - `rowSymmetrizer`: x_lambda=sum_(w in S_lambda) T_w; there are no q-weights here (PDF p.16).
--   - `uPlus`: u_lambda^+, preserving both product orders before JM commutativity is used (PDF p.16).
--   - `murphyGenerator`: m_lambda=x_lambda u_lambda^+, computed in the presented algebra (PDF p.16).
--   - `murphy`: The literal m_st=T_(d(s)^(-1)) m_lambda T_(d(t)), Definition 3.7, PDF p.16.
--   - `MurphyIndex`: The dependent index set keeps the common shape (PDF p.16).
--   - `murphyFamily`: The computed Murphy family, not an arbitrary cellular basis (PDF p.16).
--   - `dominancePrefix`: Dominance prefix: earlier components, then the first i rows of component s (PDF p.11).
--   - `ShapeDominates`: Shape dominance, including every row prefix (PDF p.11).
--   - `higherMurphySpan`: H^lambda is the R-span of strictly higher SHAPES (PDF p.17).
--   - `tableauDominancePrefixCount`: Prefix count in the restriction of a tableau to labels 1,...,k (PDF p.19).
--   - `TableauDominates`: Tableau dominance compares the shapes of ALL initial subtableaux (PDF p.19).
--   - `tableauResidue`: Residue of the node carrying label k+1, with possibly negative column-row content (PDF p.11).
--   - `AffineFree`: Free affine algebra: T_1,...,T_(n-1) and two formal signs of each X_j (PDF p.7).
--   - `affineFreeT`: T_i with the source's one-based index; invalid helper values are zero (PDF p.7).
--   - `affineFreeX`: X_(j+1) or its formal inverse; valid j is zero-based (PDF p.7).
--   - `AffineRel`: Corrected affine presentation from PDF p.7. Polynomial RHS is zero; ALL X's commute, and T_i commutes with X_j for j≠i,i+1. The printed shared distance guard cannot apply to the X-X commutation relation.
--   - `AffineHecke`: The actual affine Hecke algebra, PDF p.7.
--   - `affineT`: The affine T generator image (PDF p.7).
--   - `affineHeckeX`: The affine X generator or inverse image, with zero-based j (PDF p.7).
--   - `Laurent`: Laurent polynomials in n variables, as the group algebra of Z^n (PDF p.37).
--   - `IsSymmetricLaurent`: Symmetric Laurent polynomials: coefficients are invariant under every variable permutation (PDF p.37).
--   - `affineLaurentEval`: Ordered Laurent evaluation using the explicit inverse generators (PDF p.37).
--   - `affineCyclotomicRel`: The only extra affine relation for the cyclotomic quotient (PDF p.7).
--   - `AffineCyclotomic`: Hhat modulo the two-sided ideal generated by the cyclotomic polynomial (PDF p.7).
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, https://arxiv.org/abs/math/0204025v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P06

/-!
Mathas, arXiv:math/0204025v1. Local, literal Ariki--Koike presentation.
The two polynomial relations on PDF p.4 are corrected from 1 to 0, as
required by the quotient ideal on p.6 and normalized relation on p.41.
No basis, cellular datum, representation, or JM axiom is assumed.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)
open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The free algebra on exactly T_0,...,T_(n-1), PDF p.4. -/
abbrev AKFree (R : Type*) [CommRing R] (n : ℕ) := FreeAlgebra R (Fin n)

/-- A helper for generators; out-of-range indices return zero and never enter a relation. -/
def akFreeGenerator (R : Type*) [CommRing R] (n i : ℕ) : AKFree R n :=
  if h : i < n then FreeAlgebra.ι R ⟨i, h⟩ else 0

/-- Corrected Definition 2.1, PDF p.4. Each relation is guarded by its degree domain.
The ordered cyclotomic product keeps repeated and zero parameters. -/
inductive AKRel {R : Type*} [CommRing R] {r : ℕ}
    (q : Rˣ) (Q : Fin r → R) (n : ℕ) : AKFree R n → AKFree R n → Prop
  | cyclotomic (h : 0 < n) : AKRel q Q n
      (List.ofFn (fun s : Fin r => akFreeGenerator R n 0 - algebraMap R (AKFree R n) (Q s))).prod 0
  | quadratic (i : ℕ) (hi : 1 ≤ i) (hn : i < n) : AKRel q Q n
      ((akFreeGenerator R n i - algebraMap R (AKFree R n) (q : R)) * (akFreeGenerator R n i + 1)) 0
  | specialBraid (hn : 2 ≤ n) : AKRel q Q n
      (akFreeGenerator R n 0 * akFreeGenerator R n 1 * akFreeGenerator R n 0 * akFreeGenerator R n 1)
      (akFreeGenerator R n 1 * akFreeGenerator R n 0 * akFreeGenerator R n 1 * akFreeGenerator R n 0)
  | distant (i j : ℕ) (hi : i < n) (hj : j < n) (hij : i + 1 < j) : AKRel q Q n
      (akFreeGenerator R n i * akFreeGenerator R n j) (akFreeGenerator R n j * akFreeGenerator R n i)
  | braid (i : ℕ) (hi : 1 ≤ i) (hn : i + 1 < n) : AKRel q Q n
      (akFreeGenerator R n i * akFreeGenerator R n (i + 1) * akFreeGenerator R n i)
      (akFreeGenerator R n (i + 1) * akFreeGenerator R n i * akFreeGenerator R n (i + 1))

/-- The presented algebra H, not an algebra equipped with a presumed basis (PDF p.4). -/
abbrev ArikiKoike {R : Type*} [CommRing R] {r : ℕ}
    (q : Rˣ) (Q : Fin r → R) (n : ℕ) := RingQuot (AKRel q Q n)

/-- The quotient images of the generators, PDF p.4. -/
def akT {R : Type*} [CommRing R] {r : ℕ} (q : Rˣ) (Q : Fin r → R)
    (n i : ℕ) : ArikiKoike q Q n := RingQuot.mkAlgHom R (AKRel q Q n) (akFreeGenerator R n i)

/-- L_(k+1), with zero-based helper k; the q^(-1) factor is essential (PDF p.4). -/
def jmNat {R : Type*} [CommRing R] {r : ℕ} (q : Rˣ) (Q : Fin r → R)
    (n : ℕ) : ℕ → ArikiKoike q Q n
  | 0 => akT q Q n 0
  | k + 1 => algebraMap R (ArikiKoike q Q n) (↑(q⁻¹) : R) *
      akT q Q n (k + 1) * jmNat q Q n k * akT q Q n (k + 1)

/-- The n genuine JM elements, L_1,...,L_n (PDF p.4). -/
def cyclotomicJM {R : Type*} [CommRing R] {r n : ℕ} (q : Rˣ) (Q : Fin r → R)
    (k : Fin n) : ArikiKoike q Q n := jmNat q Q n k.val

/-- Normalization check L_2=q^(-1)T_1 T_0 T_1 (PDF p.4). -/
example {R : Type*} [CommRing R] {r : ℕ} (q : Rˣ) (Q : Fin r → R) :
    jmNat q Q 2 1 = algebraMap R (ArikiKoike q Q 2) (↑(q⁻¹) : R) *
      akT q Q 2 1 * akT q Q 2 0 * akT q Q 2 1 := by rfl

/-- The imported adjacent permutation swaps zero-based positions i and i+1 (PDF p.4).
The corresponding source generator is T_(i+1). -/
example {n : ℕ} (i : Adjacent n) :
    adjacentPerm i = Equiv.swap i.val (nextPosition i) := by rfl

/-- Choose a reduced expression using the accepted Coxeter predicate (PDF p.4).
Reverse the word for right actions: the first written letter acts first.
Adjacent transpositions generate S_n, so this choice predicate is inhabited for every w. -/
def reducedWord {n : ℕ} (w : Equiv.Perm (Fin n)) : List (Adjacent n) :=
  Classical.epsilon (fun l : List (Adjacent n) => IsReducedWord w l.reverse)

/-- T_w computed by a reduced word. No independence or spanning assertion is a field (PDF p.4). -/
def tw {R : Type*} [CommRing R] {r n : ℕ} (q : Rˣ) (Q : Fin r → R)
    (w : Equiv.Perm (Fin n)) : ArikiKoike q Q n :=
  ((reducedWord w).map (fun i => akT q Q n (i.val.val + 1))).prod

/-- Ordered product L_1^a_1...L_n^a_n, including the empty product 1 (PDF p.4). -/
def jmPowers {R : Type*} [CommRing R] {r n : ℕ} (q : Rˣ) (Q : Fin r → R)
    (a : Fin n → ℕ) : ArikiKoike q Q n :=
  (List.ofFn (fun i : Fin n => cyclotomicJM q Q i ^ a i)).prod

/-- The explicit family of Theorem 2.2 (PDF p.4). -/
def arikiKoikeMonomial {R : Type*} [CommRing R] {r n : ℕ} (q : Rˣ) (Q : Fin r → R)
    (z : (Fin n → Fin r) × Equiv.Perm (Fin n)) : ArikiKoike q Q n :=
  jmPowers q Q (fun i => (z.1 i).val) * tw q Q z.2

/-- Finite ordered evaluation makes sense before commutativity is proved (PDF p.4).
Once the JM theorem is used it is ordinary multivariate polynomial evaluation. -/
def jmEval {R : Type*} [CommRing R] {r n : ℕ} (q : Rˣ) (Q : Fin r → R)
    (p : MvPolynomial (Fin n) R) : ArikiKoike q Q n :=
  ∑ d ∈ p.support, (p.coeff d) • jmPowers q Q (fun i => d i)

/-- The quantum integer 1+q+...+q^(m-1), PDF p.11. -/
def qInteger {R : Type*} [CommRing R] (q : Rˣ) (m : ℕ) : R :=
  ∑ k ∈ Finset.range m, (q : R) ^ k

/-- The exact semisimplicity polynomial P_H, PDF p.11.
Integer powers are powers of the unit q, not total division by an arbitrary element. -/
def semisimplicityPolynomial {R : Type*} [CommRing R] {r : ℕ}
    (q : Rˣ) (Q : Fin r → R) (n : ℕ) : R :=
  (∏ k : Fin n, qInteger q (k.val + 1)) *
  ∏ s : Fin r, ∏ t ∈ Finset.univ.filter (fun t : Fin r => s < t),
    ∏ d ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((↑(q ^ d) : R) * Q s - Q t)

/-- P_H=1 in degree zero even with repeated or zero parameters (PDF pp.2,11). -/
example {R : Type*} [CommRing R] {r : ℕ} (q : Rˣ) (Q : Fin r → R) :
    semisimplicityPolynomial q Q 0 = 1 := by
  simp [semisimplicityPolynomial]

/-- Multipartitions of n as decreasing rows, padded by zero to n rows (PDF p.11).
Every part is at most n. Fin 0 represents the unique empty component at degree zero. -/
abbrev MultiPartition (r n : ℕ) :=
  {a : Fin r → Fin n → Fin (n + 1) //
    (∑ s : Fin r, ∑ i : Fin n, (a s i).val) = n ∧
      ∀ s, Antitone (fun i : Fin n => (a s i).val)}

/-- Nodes (component,row,column), all zero-based; source nodes add one to each index (PDF p.11). -/
abbrev Node {r n : ℕ} (lam : MultiPartition r n) :=
  {x : Fin r × Fin n × Fin n // x.2.2.val < (lam.val x.1 x.2.1).val}

/-- A standard tableau is a bijective labeling increasing in rows and columns (PDF p.11). -/
abbrev StandardMultiTableau {r n : ℕ} (lam : MultiPartition r n) :=
  {t : Node lam ≃ Fin n //
    (∀ x y : Node lam, x.val.1 = y.val.1 → x.val.2.1 = y.val.2.1 →
      x.val.2.2 < y.val.2.2 → t x < t y) ∧
    (∀ x y : Node lam, x.val.1 = y.val.1 → x.val.2.2 = y.val.2.2 →
      x.val.2.1 < y.val.2.1 → t x < t y)}

/-- Count the nodes strictly before x in component/row/column reading order (PDF p.16). -/
def rowNumber {r n : ℕ} {lam : MultiPartition r n} (x : Node lam) : ℕ :=
  (Finset.univ.filter (fun y : Node lam =>
    y.val.1 < x.val.1 ∨
    (y.val.1 = x.val.1 ∧ y.val.2.1 < x.val.2.1) ∨
    (y.val.1 = x.val.1 ∧ y.val.2.1 = x.val.2.1 ∧ y.val.2.2 < x.val.2.2))).card

/-- d(t) is the unique permutation carrying row reading labels to t (PDF p.16).
The predicate computes d(t) from the bijection, not from an assumed H-action. -/
def tableauPermutation {r n : ℕ} {lam : MultiPartition r n} (t : StandardMultiTableau lam) :
    Equiv.Perm (Fin n) :=
  Classical.epsilon (fun w => ∀ (x : Node lam) (k : Fin n),
    k.val = rowNumber x → w k = t.val x)

/-- The row-stabilizer of the row reading tableau (PDF p.16). -/
def rowStabilizer {r n : ℕ} (lam : MultiPartition r n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun w => ∀ (x : Node lam) (k : Fin n),
    k.val = rowNumber x → ∃ y : Node lam,
      y.val.1 = x.val.1 ∧ y.val.2.1 = x.val.2.1 ∧ rowNumber y = (w k).val)

/-- Size of components strictly preceding s (PDF p.16). -/
def precedingSize {r n : ℕ} (lam : MultiPartition r n) (s : Fin r) : ℕ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin r => t < s),
    ∑ i : Fin n, (lam.val t i).val

/-- x_lambda=sum_(w in S_lambda) T_w; there are no q-weights here (PDF p.16). -/
def rowSymmetrizer {R : Type*} [CommRing R] {r n : ℕ}
    (q : Rˣ) (Q : Fin r → R) (lam : MultiPartition r n) : ArikiKoike q Q n :=
  ∑ w ∈ rowStabilizer lam, tw q Q w

/-- u_lambda^+, preserving both product orders before JM commutativity is used (PDF p.16). -/
def uPlus {R : Type*} [CommRing R] {r n : ℕ}
    (q : Rˣ) (Q : Fin r → R) (lam : MultiPartition r n) : ArikiKoike q Q n :=
  (List.ofFn (fun s : Fin r =>
    (((List.finRange n).filter (fun k => k.val < precedingSize lam s)).map
      (fun k => cyclotomicJM q Q k - algebraMap R (ArikiKoike q Q n) (Q s))).prod)).prod

/-- m_lambda=x_lambda u_lambda^+, computed in the presented algebra (PDF p.16). -/
def murphyGenerator {R : Type*} [CommRing R] {r n : ℕ}
    (q : Rˣ) (Q : Fin r → R) (lam : MultiPartition r n) : ArikiKoike q Q n :=
  rowSymmetrizer q Q lam * uPlus q Q lam

/-- The literal m_st=T_(d(s)^(-1)) m_lambda T_(d(t)), Definition 3.7, PDF p.16. -/
def murphy {R : Type*} [CommRing R] {r n : ℕ}
    (q : Rˣ) (Q : Fin r → R) {lam : MultiPartition r n}
    (s t : StandardMultiTableau lam) : ArikiKoike q Q n :=
  tw q Q (tableauPermutation s)⁻¹ * murphyGenerator q Q lam * tw q Q (tableauPermutation t)

/-- The dependent index set keeps the common shape (PDF p.16). -/
abbrev MurphyIndex (r n : ℕ) := Σ lam : MultiPartition r n, StandardMultiTableau lam × StandardMultiTableau lam

/-- The computed Murphy family, not an arbitrary cellular basis (PDF p.16). -/
def murphyFamily {R : Type*} [CommRing R] {r n : ℕ}
    (q : Rˣ) (Q : Fin r → R) (z : MurphyIndex r n) : ArikiKoike q Q n :=
  murphy q Q z.2.1 z.2.2

/-- Dominance prefix: earlier components, then the first i rows of component s (PDF p.11). -/
def dominancePrefix {r n : ℕ} (lam : MultiPartition r n) (s : Fin r) (i : ℕ) : ℕ :=
  precedingSize lam s + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i),
    (lam.val s j).val

/-- Shape dominance, including every row prefix (PDF p.11). -/
def ShapeDominates {r n : ℕ} (lam mu : MultiPartition r n) : Prop :=
  ∀ s i, dominancePrefix mu s i ≤ dominancePrefix lam s i

/-- H^lambda is the R-span of strictly higher SHAPES (PDF p.17). -/
def higherMurphySpan {R : Type*} [CommRing R] {r n : ℕ}
    (q : Rˣ) (Q : Fin r → R) (lam : MultiPartition r n) : Submodule R (ArikiKoike q Q n) :=
  Submodule.span R {z | ∃ (mu : MultiPartition r n) (s t : StandardMultiTableau mu),
    ShapeDominates mu lam ∧ mu ≠ lam ∧ z = murphy q Q s t}

/-- Prefix count in the restriction of a tableau to labels 1,...,k (PDF p.19). -/
def tableauDominancePrefixCount {r n : ℕ} {lam : MultiPartition r n}
    (t : StandardMultiTableau lam) (k : ℕ) (s : Fin r) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Node lam => (t.val x).val < k ∧
    (x.val.1 < s ∨ (x.val.1 = s ∧ x.val.2.1.val < i)))).card

/-- Tableau dominance compares the shapes of ALL initial subtableaux (PDF p.19). -/
def TableauDominates {r n : ℕ} {lam : MultiPartition r n}
    (s t : StandardMultiTableau lam) : Prop :=
  ∀ k, k ≤ n → ∀ c i, tableauDominancePrefixCount t k c i ≤ tableauDominancePrefixCount s k c i

/-- Residue of the node carrying label k+1, with possibly negative column-row content (PDF p.11). -/
def tableauResidue {R : Type*} [CommRing R] {r n : ℕ}
    (q : Rˣ) (Q : Fin r → R) {lam : MultiPartition r n}
    (t : StandardMultiTableau lam) (k : Fin n) : R :=
  let x := t.val.symm k
  (↑(q ^ ((x.val.2.2.val : ℤ) - (x.val.2.1.val : ℤ))) : R) * Q x.val.1

/-- At degree zero there is no node or JM index (PDF p.2). -/
example {r : ℕ} (lam : MultiPartition r 0) (x : Node lam) : False := by
  exact Fin.elim0 x.val.2.1

/-- Free affine algebra: T_1,...,T_(n-1) and two formal signs of each X_j (PDF p.7). -/
abbrev AffineFree (R : Type*) [CommRing R] (n : ℕ) :=
  FreeAlgebra R (Sum (Fin (n - 1)) (Fin n × Bool))

/-- T_i with the source's one-based index; invalid helper values are zero (PDF p.7). -/
def affineFreeT (R : Type*) [CommRing R] (n i : ℕ) : AffineFree R n :=
  if h : 1 ≤ i ∧ i < n then FreeAlgebra.ι R (Sum.inl ⟨i - 1, by omega⟩) else 0

/-- X_(j+1) or its formal inverse; valid j is zero-based (PDF p.7). -/
def affineFreeX (R : Type*) [CommRing R] (n j : ℕ) (inverse : Bool) : AffineFree R n :=
  if h : j < n then FreeAlgebra.ι R (Sum.inr (⟨j, h⟩, inverse)) else 0

/-- Corrected affine presentation from PDF p.7.
Polynomial RHS is zero; ALL X's commute, and T_i commutes with X_j for j≠i,i+1.
The printed shared distance guard cannot apply to the X-X commutation relation. -/
inductive AffineRel {R : Type*} [CommRing R] (q : Rˣ) (n : ℕ) :
    AffineFree R n → AffineFree R n → Prop
  | quadratic (i : ℕ) (hi : 1 ≤ i) (hn : i < n) : AffineRel q n
      ((affineFreeT R n i - algebraMap R (AffineFree R n) (q : R)) *
        (affineFreeT R n i + 1)) 0
  | braid (i : ℕ) (hi : 1 ≤ i) (hn : i + 1 < n) : AffineRel q n
      (affineFreeT R n i * affineFreeT R n (i + 1) * affineFreeT R n i)
      (affineFreeT R n (i + 1) * affineFreeT R n i * affineFreeT R n (i + 1))
  | distant (i j : ℕ) (hi : 1 ≤ i) (hj : j < n) (hij : i + 1 < j) : AffineRel q n
      (affineFreeT R n i * affineFreeT R n j) (affineFreeT R n j * affineFreeT R n i)
  | inverseRight (j : ℕ) (hj : j < n) : AffineRel q n
      (affineFreeX R n j false * affineFreeX R n j true) 1
  | inverseLeft (j : ℕ) (hj : j < n) : AffineRel q n
      (affineFreeX R n j true * affineFreeX R n j false) 1
  | commutingX (i j : ℕ) (hi : i < n) (hj : j < n) (b c : Bool) : AffineRel q n
      (affineFreeX R n i b * affineFreeX R n j c)
      (affineFreeX R n j c * affineFreeX R n i b)
  | mixed (i : ℕ) (hi : 1 ≤ i) (hn : i < n) : AffineRel q n
      (affineFreeT R n i * affineFreeX R n (i - 1) false * affineFreeT R n i)
      (algebraMap R (AffineFree R n) (q : R) * affineFreeX R n i false)
  | distantX (i j : ℕ) (hi : 1 ≤ i) (hn : i < n) (hj : j < n)
      (h1 : j + 1 ≠ i) (h2 : j + 1 ≠ i + 1) (b : Bool) : AffineRel q n
      (affineFreeT R n i * affineFreeX R n j b)
      (affineFreeX R n j b * affineFreeT R n i)

/-- The actual affine Hecke algebra, PDF p.7. -/
abbrev AffineHecke {R : Type*} [CommRing R] (q : Rˣ) (n : ℕ) := RingQuot (AffineRel q n)

/-- The affine T generator image (PDF p.7). -/
def affineT {R : Type*} [CommRing R] (q : Rˣ) (n i : ℕ) : AffineHecke q n :=
  RingQuot.mkAlgHom R (AffineRel q n) (affineFreeT R n i)

/-- The affine X generator or inverse image, with zero-based j (PDF p.7). -/
def affineHeckeX {R : Type*} [CommRing R] {n : ℕ} (q : Rˣ) (j : Fin n) (b : Bool) :
    AffineHecke q n := RingQuot.mkAlgHom R (AffineRel q n) (affineFreeX R n j.val b)

/-- Laurent polynomials in n variables, as the group algebra of Z^n (PDF p.37). -/
abbrev Laurent (R : Type*) [CommRing R] (n : ℕ) := AddMonoidAlgebra R (Fin n → ℤ)

/-- Symmetric Laurent polynomials: coefficients are invariant under every variable permutation (PDF p.37). -/
def IsSymmetricLaurent {R : Type*} [CommRing R] {n : ℕ} (p : Laurent R n) : Prop :=
  ∀ (w : Equiv.Perm (Fin n)) (a : Fin n → ℤ), p.coeff (fun i => a (w i)) = p.coeff a

/-- Ordered Laurent evaluation using the explicit inverse generators (PDF p.37). -/
def affineLaurentEval {R : Type*} [CommRing R] {n : ℕ} (q : Rˣ) (p : Laurent R n) :
    AffineHecke q n :=
  ∑ a ∈ p.coeff.support, (p.coeff a) •
    (List.ofFn (fun i : Fin n =>
      if 0 ≤ a i then affineHeckeX q i false ^ (a i).toNat
      else affineHeckeX q i true ^ (-a i).toNat)).prod

/-- The only extra affine relation for the cyclotomic quotient (PDF p.7). -/
def affineCyclotomicRel {R : Type*} [CommRing R] {r : ℕ}
    (q : Rˣ) (Q : Fin r → R) (n : ℕ) (x y : AffineHecke q n) : Prop :=
  0 < n ∧ x = (List.ofFn (fun s : Fin r =>
    RingQuot.mkAlgHom R (AffineRel q n) (affineFreeX R n 0 false) -
      algebraMap R (AffineHecke q n) (Q s))).prod ∧ y = 0

/-- Hhat modulo the two-sided ideal generated by the cyclotomic polynomial (PDF p.7). -/
abbrev AffineCyclotomic {R : Type*} [CommRing R] {r : ℕ}
    (q : Rˣ) (Q : Fin r → R) (n : ℕ) := RingQuot (affineCyclotomicRel q Q n)

/-- Negative exponents really use inverse generators; -1 does not become zero (PDF p.37). -/
example : (-(-1 : ℤ)).toNat = 1 := by rfl

end QAlgorithms.Papers.Independent.Intake100.P36


