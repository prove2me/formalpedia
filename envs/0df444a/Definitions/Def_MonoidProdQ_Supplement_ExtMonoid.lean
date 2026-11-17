-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_ExtMonoid
-- name    : MonoidProdQ_Supplement_ExtMonoid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:09:14.108507+00:00
-- url     : https://prove2.me/theorems/5a3c52a8-2f07-4648-97f4-c209228aa45a
-- title:
--   Extension monoid $M_f$
-- statement:
--   The **extension monoid** of $f:2^U\to O$ is the quotient of the union monoid of subsets of $U$ by equivalence under extensions:
--
--   $$M_f=2^U/\!\sim_f,\qquad [S][T]=[S\cup T],\qquad 1=[\emptyset].$$
--
--   The relation $\sim_f$ is a congruence for union (if $S\sim_f T$ then $S\cup D\sim_f T\cup D$), so $M_f$ is a finite commutative idempotent monoid. Theorem 29 identifies its product breadth with the worst-case size of a smallest strong certificate.
--
--   **Formalization Note** The quotient type of finite subsets of $U$ by $\sim_f$, with the commutative monoid structure induced by union (well-definedness is proved), and finiteness and decidable equality for finite $U$ and $O$ with decidable equality.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 3, p.41

import Definitions.Def_MonoidProdQ_Supplement_extEquiv

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Definition 3 (Extension monoid), p.41:
"The extension monoid of f is M_f = 2^U/∼_f, [S][T] = [S ∪ T], 1 = [∅]", the quotient of the
union monoid of subsets of `U` by equivalence under extensions (`extEquiv`).

**Formalization Note.** The quotient type `Quotient (extEquiv f)`. The commutative monoid
structure (product induced by union, identity the class of `∅`; well defined because `∼_f` is a
congruence: "if S ∼_f T, then S ∪ D ∼_f T ∪ D"), the finite-type instance and decidable equality
are defined in this module. -/
def ExtMonoid {U O : Type*} [DecidableEq U] (f : Finset U → O) : Type _ :=
  Quotient (extEquiv f)

namespace ExtMonoid

variable {U O : Type*} [DecidableEq U] {f : Finset U → O}

/-- `∼_f` is a congruence for union. -/
theorem union_congr {S S' T T' : Finset U} (hS : (extEquiv f).r S S')
    (hT : (extEquiv f).r T T') : (extEquiv f).r (S ∪ T) (S' ∪ T') := by
  intro K
  calc f (S ∪ T ∪ K) = f (S ∪ (T ∪ K)) := by rw [Finset.union_assoc]
    _ = f (S' ∪ (T ∪ K)) := hS _
    _ = f (T ∪ (S' ∪ K)) := by rw [← Finset.union_assoc, Finset.union_comm S' T, Finset.union_assoc]
    _ = f (T' ∪ (S' ∪ K)) := hT _
    _ = f (S' ∪ T' ∪ K) := by rw [← Finset.union_assoc, Finset.union_comm T' S']

/-- The product `[S][T] = [S ∪ T]` and the identity `[∅]`. -/
instance : CommMonoid (ExtMonoid f) where
  mul := Quotient.map₂ (· ∪ ·) (fun _ _ hS _ _ hT => union_congr hS hT)
  one := Quotient.mk _ ∅
  mul_assoc a b c := by
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (Finset.union_assoc _ _ _)
  one_mul a := by
    induction a using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (Finset.empty_union _)
  mul_one a := by
    induction a using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (Finset.union_empty _)
  mul_comm a b := by
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact congrArg (Quotient.mk _) (Finset.union_comm _ _)

variable [Fintype U] [DecidableEq O]

instance : DecidableEq (ExtMonoid f) :=
  @Quotient.decidableEq _ (extEquiv f) (fun S T => extEquiv.decRel f S T)

instance : Fintype (ExtMonoid f) :=
  @Quotient.fintype _ _ (extEquiv f) (fun S T => extEquiv.decRel f S T)

end ExtMonoid

end MonoidProdQ.Supplement


