-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40
-- name    : QAlgorithms_Papers_Independent_Intake100_P40
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:12:53.636892+00:00
-- url     : https://prove2.me/theorems/f4b05c9d-11a9-44ef-85ec-a14fd3251eae
-- title:
--   Definitions for Centers of degenerate cyclotomic Hecke algebras and parabolic category O
-- statement:
--   The objects the formalized statements of *Centers of degenerate cyclotomic Hecke algebras and parabolic category O* (arXiv:math/0607717) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DegenerateHeckeLetter`: Polynomial and permutation letters, source PDF pp.1,4.
--   - `degenerateFreeX`: Free polynomial letter, PDF pp.1,4.
--   - `freeW`: Free permutation letter, PDF pp.1,4.
--   - `GradedRel`: Presentation of T ⋊ R S_d: polynomial commutativity, group multiplication, variable permutation, and x_i^l=0. This is the actual algebra of PDF p.4.
--   - `GradedAlgebra`: Truncated polynomial skew group algebra, PDF p.4.
--   - `gradedMap`: Canonical presentation map, PDF p.4.
--   - `gradedX`: The variable x_(i+1) in the graded algebra, PDF p.4.
--   - `gradedW`: Permutation in the graded algebra, PDF p.4.
--   - `orderedMonomial`: Source-ordered monomial, meaningful also in a noncommutative ambient ring. The empty product at d=0 is 1 (PDF pp.4,12).
--   - `hElement`: The h_r(I) of PDF p.4, inside its faithful skew-group ambient algebra. Only exponents on I contribute; exponents outside I are required to be zero. The source uses this definition for nonempty I; lemma_2_1 ensures that domain.
--   - `IsMarkedCycle`: A cycle with its actual nonempty letter set, including marked 1-cycles. Lists differing by rotation give the same pair; singleton labels are retained. PDF p.5.
--   - `MarkedCycle`: Canonical cycle data modulo cyclic rotation, PDF p.5.
--   - `coloredCycle`: A^(r)=h_r(A)A, with r any natural color, PDF p.5.
--   - `ColoredProduct`: Canonical disjoint product data. Every letter is covered exactly once, so the otherwise removable color-zero singletons have a unique presentation. This implements the equivalence of presentations on PDF pp.6--7.
--   - `disjointColoredProductElement`: Product of all colored factors in a canonical finite-set ordering. Disjoint factors commute; no summation over their reorderings is used. PDF pp.6--7.
--   - `polynomialCentralizer`: The polynomial centralizer Q_d, PDF p.4. Commuting with all variables is equivalent to commuting with the subalgebra they generate.
--   - `IsBasisFor`: A specified family is a basis of a specified ambient submodule. This asserts both linear independence and exact span, without choosing membership proofs or imposing the nonzero-ring convention for `Module.rank`. PDF pp.6--12.
--   - `IsPartition`: An ordinary partition is its multiset of strictly positive parts. An empty multiset is the empty partition (PDF p.7).
--   - `Multipartition`: M_d(l), using source colors 0,...,l-1 as component indices, PDF p.7.
--   - `quotientSize`: Sum of the quotients floor(mu_i/l), PDF p.9.
--   - `PartitionIndex`: P_d(l), PDF p.9. Positive parts only; padding zeros is done separately.
--   - `partitionPhi`: The explicitly given phi of PDF p.9. A part a in color r gives (a-1)l+r; zero outputs are omitted from the ordinary partition.
--   - `partitionInverse`: The source inverse formula (PDF p.9): restore exactly the lost color-zero singletons using total size d, then separate by residue modulo l.
--   - `cycleType`: Cycle type, with all fixed points and their colors counted, PDF pp.7--8.
--   - `orbitSum`: z_d(lambda): each distinct canonical colored product is included once. In particular no stabilizer multiplicity or division by d! occurs. PDF p.8.
--   - `centralizerIndexCount`: The rank formula of Theorem 2.3, PDF p.6, computed in Q, not N. The finite tuple m records the multiplicity of cycles of size a+1. The empty product and sum at d=0 give rank 1.
--   - `singleCycleSum`: The sum of all a-cycles of color r, with marked singletons, PDF p.8.
--   - `murphyY`: y_i(k), summing ordered distinct choices of k/l earlier letters. The last letter is i, and the color is k mod l (PDF p.8).
--   - `rearrangements`: All distinct rearrangements of a partition padded to d entries by zeros. The bound mu.sum+1 accommodates every part, including the empty partition. PDF pp.9,12.
--   - `symmetricMonomial`: Monomial symmetric sum for an explicitly given family, PDF pp.9,12. Each exponent tuple occurs once, even if its entries repeat.
--   - `murphyM`: m_d(mu), the second central basis in the graded algebra, PDF p.9.
--   - `murphyErrorProducts`: Error products in Lemma 2.6: the head cycle contains i, every cycle lies in S_(i+1), factors have the uniform color l-1, and the total number of letters is at most p. The set is empty at p=0. PDF pp.8--9.
--   - `DegenerateAffineHeckeRel`: All relations of the degenerate affine Hecke algebra, PDF p.1. The sign is s_i x_(i+1) = x_i s_i + 1.
--   - `CyclotomicRel`: The cyclotomic relation for the monic polynomial f(X)=X^l+sum_(a<l)c_a X^a. At d=0 there is no first variable and no extra relation, giving H_0^f=R. PDF pp.1,21.
--   - `CyclotomicAlgebra`: Literal presented degenerate cyclotomic Hecke algebra, PDF p.1.
--   - `degenerateCyclotomicQuotientMap`: Canonical quotient map, PDF p.1.
--   - `degenerateCyclotomicVariable`: x_(i+1) in H_d^f; separate from the graded variable, PDF pp.1,10--11.
--   - `cyclotomicP`: p_d(mu), with distinct rearrangements, PDF p.12.
--   - `IsSymmetricPolynomial`: Symmetry under the usual permutation of variables, PDF pp.1--2.
--   - `cyclotomicEvaluate`: Evaluation at the commuting cyclotomic variables, expressed as the finite coefficient sum of ordered monomials to allow a noncommutative ambient algebra. PDF pp.1--2.
--   - `cyclotomicPowerSum`: Source-prescribed power sums, PDF p.12.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, https://arxiv.org/abs/math/0607717v3

import Mathlib

/-!
Statements from Brundan, arXiv:math/0607717v3.
All new objects in this file are local to this paper. The algebra presentations
use a letter for every permutation, with the full group multiplication table.
Indices in `Fin d` are zero based; index i represents the source letter i+1.
No nonzero-ring, characteristic, or splitting assumption is imposed in §§2--3.
The representation-theoretic and filtered-symbol nodes are explicitly deferred
in the unit's GAPS.json; no abstract surrogate for those objects is assumed.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Polynomial and permutation letters, source PDF pp.1,4. -/
inductive DegenerateHeckeLetter (d : ℕ)
  | x : Fin d → DegenerateHeckeLetter d
  | w : Equiv.Perm (Fin d) → DegenerateHeckeLetter d

/-- Free polynomial letter, PDF pp.1,4. -/
def degenerateFreeX (R : Type*) [CommRing R] (d : ℕ) (i : Fin d) :
    FreeAlgebra R (DegenerateHeckeLetter d) := FreeAlgebra.ι R (.x i)

/-- Free permutation letter, PDF pp.1,4. -/
def freeW (R : Type*) [CommRing R] (d : ℕ) (w : Equiv.Perm (Fin d)) :
    FreeAlgebra R (DegenerateHeckeLetter d) := FreeAlgebra.ι R (.w w)

/-- Presentation of T ⋊ R S_d: polynomial commutativity, group multiplication,
variable permutation, and x_i^l=0. This is the actual algebra of PDF p.4. -/
inductive GradedRel (R : Type*) [CommRing R] (l d : ℕ) :
    FreeAlgebra R (DegenerateHeckeLetter d) → FreeAlgebra R (DegenerateHeckeLetter d) → Prop
  | unit : GradedRel R l d (freeW R d 1) 1
  | group (u v : Equiv.Perm (Fin d)) : GradedRel R l d
      (freeW R d u * freeW R d v) (freeW R d (u * v))
  | commute (i j : Fin d) : GradedRel R l d
      (degenerateFreeX R d i * degenerateFreeX R d j) (degenerateFreeX R d j * degenerateFreeX R d i)
  | permute (w : Equiv.Perm (Fin d)) (i : Fin d) : GradedRel R l d
      (freeW R d w * degenerateFreeX R d i) (degenerateFreeX R d (w i) * freeW R d w)
  | truncate (i : Fin d) : GradedRel R l d (degenerateFreeX R d i ^ l) 0

/-- Truncated polynomial skew group algebra, PDF p.4. -/
abbrev GradedAlgebra (R : Type*) [CommRing R] (l d : ℕ) :=
  RingQuot (GradedRel R l d)

/-- Canonical presentation map, PDF p.4. -/
def gradedMap (R : Type*) [CommRing R] (l d : ℕ) :
    FreeAlgebra R (DegenerateHeckeLetter d) →ₐ[R] GradedAlgebra R l d :=
  RingQuot.mkAlgHom R (GradedRel R l d)

/-- The variable x_(i+1) in the graded algebra, PDF p.4. -/
def gradedX (R : Type*) [CommRing R] (l d : ℕ) (i : Fin d) :
    GradedAlgebra R l d := gradedMap R l d (degenerateFreeX R d i)

/-- Permutation in the graded algebra, PDF p.4. -/
def gradedW (R : Type*) [CommRing R] (l d : ℕ) (w : Equiv.Perm (Fin d)) :
    GradedAlgebra R l d := gradedMap R l d (freeW R d w)

/-- Source-ordered monomial, meaningful also in a noncommutative ambient ring.
The empty product at d=0 is 1 (PDF pp.4,12). -/
def orderedMonomial {A : Type*} [Monoid A] {d : ℕ}
    (x : Fin d → A) (e : Fin d → ℕ) : A :=
  (List.ofFn fun i : Fin d => x i ^ e i).prod

/-- The h_r(I) of PDF p.4, inside its faithful skew-group ambient algebra.
Only exponents on I contribute; exponents outside I are required to be zero.
The source uses this definition for nonempty I; lemma_2_1 ensures that domain. -/
def hElement (R : Type*) [CommRing R] (l d : ℕ) (I : Finset (Fin d))
    (r : ℕ) : GradedAlgebra R l d :=
  ∑ e ∈ (Finset.univ : Finset (Fin d → Fin l)).filter
      (fun e => (∀ i, i ∉ I → (e i).val = 0) ∧
        ∑ i ∈ I, (e i).val = (I.card - 1) * (l - 1) + r),
    orderedMonomial (gradedX R l d) (fun i => (e i).val)

/-- A cycle with its actual nonempty letter set, including marked 1-cycles.
Lists differing by rotation give the same pair; singleton labels are retained.
PDF p.5. -/
def IsMarkedCycle {d : ℕ}
    (p : Finset (Fin d) × Equiv.Perm (Fin d)) : Prop :=
  ∃ t : List (Fin d), t.Nodup ∧ t ≠ [] ∧ t.toFinset = p.1 ∧ t.formPerm = p.2

/-- Canonical cycle data modulo cyclic rotation, PDF p.5. -/
abbrev MarkedCycle (d : ℕ) :=
  {p : Finset (Fin d) × Equiv.Perm (Fin d) // IsMarkedCycle p}

instance markedCycleFintype (d : ℕ) : Fintype (MarkedCycle d) := Fintype.ofFinite _

/-- A^(r)=h_r(A)A, with r any natural color, PDF p.5. -/
def coloredCycle (R : Type*) [CommRing R] (l d : ℕ)
    (A : MarkedCycle d) (r : ℕ) : GradedAlgebra R l d :=
  hElement R l d A.val.1 r * gradedW R l d A.val.2

/-- Canonical disjoint product data. Every letter is covered exactly once,
so the otherwise removable color-zero singletons have a unique presentation.
This implements the equivalence of presentations on PDF pp.6--7. -/
abbrev ColoredProduct (l d : ℕ) :=
  {s : Finset (MarkedCycle d × Fin l) //
    (s : Set (MarkedCycle d × Fin l)).Pairwise
      (fun a b => Disjoint a.1.val.1 b.1.val.1) ∧
      s.biUnion (fun a => a.1.val.1) = Finset.univ}

instance coloredProductFintype (l d : ℕ) : Fintype (ColoredProduct l d) :=
  Fintype.ofFinite _

/-- Product of all colored factors in a canonical finite-set ordering.
Disjoint factors commute; no summation over their reorderings is used.
PDF pp.6--7. -/
def disjointColoredProductElement (R : Type*) [CommRing R] (l d : ℕ)
    (C : ColoredProduct l d) : GradedAlgebra R l d :=
  (C.val.toList.map fun a => coloredCycle R l d a.1 a.2.val).prod

/-- The polynomial centralizer Q_d, PDF p.4. Commuting with all variables
is equivalent to commuting with the subalgebra they generate. -/
def polynomialCentralizer (R : Type*) [CommRing R] (l d : ℕ) :
    Subalgebra R (GradedAlgebra R l d) :=
  Subalgebra.centralizer R (Set.range (gradedX R l d))

/-- A specified family is a basis of a specified ambient submodule.
This asserts both linear independence and exact span, without choosing
membership proofs or imposing the nonzero-ring convention for `Module.rank`.
PDF pp.6--12. -/
def IsBasisFor {R A J : Type*} [CommRing R] [Ring A] [Algebra R A]
    (b : J → A) (M : Submodule R A) : Prop :=
  LinearIndependent R b ∧ Submodule.span R (Set.range b) = M

/-- An ordinary partition is its multiset of strictly positive parts.
An empty multiset is the empty partition (PDF p.7). -/
def IsPartition (mu : Multiset ℕ) : Prop := ∀ a ∈ mu, 0 < a

/-- M_d(l), using source colors 0,...,l-1 as component indices, PDF p.7. -/
abbrev Multipartition (l d : ℕ) :=
  {lam : Fin l → Multiset ℕ //
    (∀ r, IsPartition (lam r)) ∧ ∑ r : Fin l, (lam r).sum = d}

/-- Sum of the quotients floor(mu_i/l), PDF p.9. -/
def quotientSize (l : ℕ) (mu : Multiset ℕ) : ℕ :=
  (mu.map fun a => a / l).sum

/-- P_d(l), PDF p.9. Positive parts only; padding zeros is done separately. -/
abbrev PartitionIndex (l d : ℕ) :=
  {mu : Multiset ℕ // IsPartition mu ∧ mu.card + quotientSize l mu ≤ d}

/-- The explicitly given phi of PDF p.9. A part a in color r gives
(a-1)l+r; zero outputs are omitted from the ordinary partition. -/
def partitionPhi (l : ℕ) (lam : Fin l → Multiset ℕ) : Multiset ℕ :=
  ∑ r : Fin l, ((lam r).map fun a => (a - 1) * l + r.val).filter (fun b => 0 < b)

/-- The source inverse formula (PDF p.9): restore exactly the lost color-zero
singletons using total size d, then separate by residue modulo l. -/
def partitionInverse (l d : ℕ) (mu : Multiset ℕ) : Fin l → Multiset ℕ :=
  fun r => ((mu + Multiset.replicate (d - quotientSize l mu - mu.card) 0).filter
    (fun a => a % l = r.val)).map (fun a => a / l + 1)

/-- Cycle type, with all fixed points and their colors counted, PDF pp.7--8. -/
def cycleType {l d : ℕ} (C : ColoredProduct l d) : Fin l → Multiset ℕ :=
  fun r => ((C.val.filter fun a => a.2 = r).val.map fun a => a.1.val.1.card)

/-- z_d(lambda): each distinct canonical colored product is included once.
In particular no stabilizer multiplicity or division by d! occurs. PDF p.8. -/
def orbitSum (R : Type*) [CommRing R] (l d : ℕ)
    (lam : Multipartition l d) : GradedAlgebra R l d :=
  ∑ C ∈ (Finset.univ : Finset (ColoredProduct l d)).filter
    (fun C => cycleType C = lam.val), disjointColoredProductElement R l d C

/-- The rank formula of Theorem 2.3, PDF p.6, computed in Q, not N.
The finite tuple m records the multiplicity of cycles of size a+1.
The empty product and sum at d=0 give rank 1. -/
def centralizerIndexCount (l d : ℕ) : ℚ :=
  ∑ m ∈ (Finset.univ : Finset (Fin d → Fin (d + 1))).filter
      (fun m => ∑ a : Fin d, (a.val + 1) * (m a).val = d),
    ((Nat.factorial d : ℚ) / ∏ a : Fin d, (Nat.factorial (m a).val : ℚ)) *
      ∏ a : Fin d, ((l : ℚ) / (a.val + 1 : ℕ)) ^ (m a).val

/-- The sum of all a-cycles of color r, with marked singletons, PDF p.8. -/
def singleCycleSum (R : Type*) [CommRing R] (l d a r : ℕ) :
    GradedAlgebra R l d :=
  ∑ A ∈ (Finset.univ : Finset (MarkedCycle d)).filter
    (fun A => A.val.1.card = a), coloredCycle R l d A r

/-- y_i(k), summing ordered distinct choices of k/l earlier letters.
The last letter is i, and the color is k mod l (PDF p.8). -/
def murphyY (R : Type*) [CommRing R] (l d : ℕ) (i : Fin d) (k : ℕ) :
    GradedAlgebra R l d :=
  ∑ e ∈ (Finset.univ : Finset (Fin (k / l) → Fin d)).filter
      (fun e => Function.Injective e ∧ ∀ j, (e j).val < i.val),
    hElement R l d (List.ofFn e ++ [i]).toFinset (k % l) *
      gradedW R l d (List.ofFn e ++ [i]).formPerm

/-- All distinct rearrangements of a partition padded to d entries by zeros.
The bound mu.sum+1 accommodates every part, including the empty partition.
PDF pp.9,12. -/
def rearrangements (d : ℕ) (mu : Multiset ℕ) :
    Finset (Fin d → Fin (mu.sum + 1)) :=
  Finset.univ.filter fun e =>
    (((List.ofFn fun i : Fin d => (e i).val) : Multiset ℕ).filter (fun a => 0 < a)) = mu

/-- Monomial symmetric sum for an explicitly given family, PDF pp.9,12.
Each exponent tuple occurs once, even if its entries repeat. -/
def symmetricMonomial {A : Type*} [Ring A] {d : ℕ}
    (x : Fin d → ℕ → A) (mu : Multiset ℕ) : A :=
  ∑ e ∈ rearrangements d mu, (List.ofFn fun i : Fin d => x i (e i).val).prod

/-- m_d(mu), the second central basis in the graded algebra, PDF p.9. -/
def murphyM (R : Type*) [CommRing R] (l d : ℕ) (mu : Multiset ℕ) :
    GradedAlgebra R l d := symmetricMonomial (murphyY R l d) mu

/-- Error products in Lemma 2.6: the head cycle contains i, every cycle lies
in S_(i+1), factors have the uniform color l-1, and the total number of
letters is at most p. The set is empty at p=0. PDF pp.8--9. -/
def murphyErrorProducts (R : Type*) [CommRing R] (l d : ℕ)
    (i : Fin d) (p : ℕ) : Set (GradedAlgebra R l d) :=
  {z | ∃ (A : MarkedCycle d) (t : List (MarkedCycle d)),
    i ∈ A.val.1 ∧
    (A :: t).Pairwise (fun B C => Disjoint B.val.1 C.val.1) ∧
    (∀ B ∈ A :: t, ∀ j ∈ B.val.1, j.val ≤ i.val) ∧
    ((A :: t).foldl (fun (S : Finset (Fin d)) (B : MarkedCycle d) => S ∪ B.val.1) ∅).card ≤ p ∧
    z = ((A :: t).map fun B => coloredCycle R l d B (l - 1)).prod}

/-- All relations of the degenerate affine Hecke algebra, PDF p.1.
The sign is s_i x_(i+1) = x_i s_i + 1. -/
inductive DegenerateAffineHeckeRel (R : Type*) [CommRing R] (d : ℕ) :
    FreeAlgebra R (DegenerateHeckeLetter d) → FreeAlgebra R (DegenerateHeckeLetter d) → Prop
  | unit : DegenerateAffineHeckeRel R d (freeW R d 1) 1
  | group (u v : Equiv.Perm (Fin d)) : DegenerateAffineHeckeRel R d
      (freeW R d u * freeW R d v) (freeW R d (u * v))
  | commute (i j : Fin d) : DegenerateAffineHeckeRel R d
      (degenerateFreeX R d i * degenerateFreeX R d j) (degenerateFreeX R d j * degenerateFreeX R d i)
  | adjacent (i j : Fin d) (hj : j.val = i.val + 1) : DegenerateAffineHeckeRel R d
      (freeW R d (Equiv.swap i j) * degenerateFreeX R d j)
      (degenerateFreeX R d i * freeW R d (Equiv.swap i j) + 1)
  | far (i j k : Fin d) (hj : j.val = i.val + 1) (hki : k ≠ i) (hkj : k ≠ j) :
      DegenerateAffineHeckeRel R d (freeW R d (Equiv.swap i j) * degenerateFreeX R d k)
        (degenerateFreeX R d k * freeW R d (Equiv.swap i j))

/-- The cyclotomic relation for the monic polynomial
f(X)=X^l+sum_(a<l)c_a X^a. At d=0 there is no first variable and no
extra relation, giving H_0^f=R. PDF pp.1,21. -/
inductive CyclotomicRel (R : Type*) [CommRing R] (l d : ℕ) (c : Fin l → R) :
    FreeAlgebra R (DegenerateHeckeLetter d) → FreeAlgebra R (DegenerateHeckeLetter d) → Prop
  | hecke {a b} (h : DegenerateAffineHeckeRel R d a b) : CyclotomicRel R l d c a b
  | cyclotomic (i : Fin d) (hi : i.val = 0) : CyclotomicRel R l d c
      (degenerateFreeX R d i ^ l + ∑ a : Fin l,
        algebraMap R _ (c a) * degenerateFreeX R d i ^ a.val) 0

/-- Literal presented degenerate cyclotomic Hecke algebra, PDF p.1. -/
abbrev CyclotomicAlgebra (R : Type*) [CommRing R] (l d : ℕ) (c : Fin l → R) :=
  RingQuot (CyclotomicRel R l d c)

/-- Canonical quotient map, PDF p.1. -/
def degenerateCyclotomicQuotientMap (R : Type*) [CommRing R] (l d : ℕ) (c : Fin l → R) :
    FreeAlgebra R (DegenerateHeckeLetter d) →ₐ[R] CyclotomicAlgebra R l d c :=
  RingQuot.mkAlgHom R (CyclotomicRel R l d c)

/-- x_(i+1) in H_d^f; separate from the graded variable, PDF pp.1,10--11. -/
def degenerateCyclotomicVariable (R : Type*) [CommRing R] (l d : ℕ) (c : Fin l → R) (i : Fin d) :
    CyclotomicAlgebra R l d c := degenerateCyclotomicQuotientMap R l d c (degenerateFreeX R d i)

/-- p_d(mu), with distinct rearrangements, PDF p.12. -/
def cyclotomicP (R : Type*) [CommRing R] (l d : ℕ) (c : Fin l → R)
    (mu : Multiset ℕ) : CyclotomicAlgebra R l d c :=
  symmetricMonomial (fun i k => degenerateCyclotomicVariable R l d c i ^ k) mu

/-- Symmetry under the usual permutation of variables, PDF pp.1--2. -/
def IsSymmetricPolynomial {R : Type*} [CommRing R] {d : ℕ}
    (p : MvPolynomial (Fin d) R) : Prop :=
  ∀ w : Equiv.Perm (Fin d), MvPolynomial.rename w p = p

/-- Evaluation at the commuting cyclotomic variables, expressed as the finite
coefficient sum of ordered monomials to allow a noncommutative ambient algebra.
PDF pp.1--2. -/
def cyclotomicEvaluate (R : Type*) [CommRing R] (l d : ℕ) (c : Fin l → R)
    (p : MvPolynomial (Fin d) R) : CyclotomicAlgebra R l d c :=
  ∑ e ∈ p.support, p.coeff e • orderedMonomial (degenerateCyclotomicVariable R l d c) (fun i => e i)

/-- Source-prescribed power sums, PDF p.12. -/
def cyclotomicPowerSum (R : Type*) [CommRing R] (l d : ℕ) (c : Fin l → R)
    (r : ℕ) : CyclotomicAlgebra R l d c := ∑ i : Fin d, degenerateCyclotomicVariable R l d c i ^ r

/-- Sanity: a marked singleton has its letter even though its permutation is 1. -/
example {d : ℕ} (i : Fin d) :
    IsMarkedCycle ({i}, (1 : Equiv.Perm (Fin d))) := by
  exact ⟨[i], by simp, by simp, by simp, by simp⟩

/-- Sanity: the d=0 monomial is the empty product 1. -/
example {A : Type*} [Monoid A] (x : Fin 0 → A) (e : Fin 0 → ℕ) :
    orderedMonomial x e = 1 := by
  simp [orderedMonomial]

/-- Sanity: the presentation really kills x_1^l, including l=1. -/
example (R : Type*) [CommRing R] (l : ℕ) :
    gradedX R l 1 (0 : Fin 1) ^ l = 0 := by
  have h := RingQuot.mkAlgHom_rel R (GradedRel.truncate (R := R) (l := l)
    (d := 1) (0 : Fin 1))
  simpa only [gradedX, gradedMap, map_pow, map_zero] using h

/-- Sanity: the Hecke sign is the printed plus sign, on two letters. -/
example (R : Type*) [CommRing R] (l : ℕ) (c : Fin l → R) :
    degenerateCyclotomicQuotientMap R l 2 c (freeW R 2 (Equiv.swap (0 : Fin 2) 1)) *
        degenerateCyclotomicVariable R l 2 c 1 =
      degenerateCyclotomicVariable R l 2 c 0 *
        degenerateCyclotomicQuotientMap R l 2 c (freeW R 2 (Equiv.swap (0 : Fin 2) 1)) + 1 := by
  have h := RingQuot.mkAlgHom_rel R
    (CyclotomicRel.hecke (l := l) (c := c)
      (DegenerateAffineHeckeRel.adjacent (R := R) (d := 2) (0 : Fin 2) 1 (by decide)))
  simpa only [degenerateCyclotomicVariable, degenerateCyclotomicQuotientMap, map_mul, map_add, map_one] using h

/-- Sanity: all three lost color-zero singleton parts are restored at d=3. -/
example : partitionInverse 1 3 0 (0 : Fin 1) = {1, 1, 1} := by
  simp [partitionInverse, quotientSize, Multiset.filter_singleton]

/-- Sanity: the rational rank expression has the correct empty value. -/
example (l : ℕ) : centralizerIndexCount l 0 = 1 := by
  simp [centralizerIndexCount]

end QAlgorithms.Papers.Independent.Intake100.P40


