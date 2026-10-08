-- Prove2me | Definitions.Def_DegreeRigidity
-- name    : DegreeRigidity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.250593+00:00
-- url     : https://prove2.me/theorems/c3b1e589-cb73-4f86-90c3-b5b76fac6b74
-- statement:
--   An oracle is a Boolean-valued function A on the natural numbers, represented for computation by the total partial function that returns 1 when A(n) is true and 0 otherwise. An oracle A reduces to B when this characteristic function of A is Turing reducible to the characteristic function of B, meaning that A can be computed with access to B as an oracle. Reflexivity and transitivity of Turing reducibility make this relation a preorder. A Turing degree is an equivalence class of oracles under mutual Turing reducibility; the induced reducibility relation on these classes is a partial order. MainTheorem is the defined proposition that this ordered set is rigid: every order isomorphism π from the set of Turing degrees to itself fixes every degree a, so π(a) = a. The block defines this proposition but does not establish it.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DegreeRigidity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DegreeRigidity.lean; bytes 16..1127
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace TuringRigidity

abbrev Oracle := ℕ → Bool

def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)

def Reduces (A B : Oracle) : Prop := TuringReducible (oracleFunction A) (oracleFunction B)

instance : IsPreorder Oracle Reduces where
  refl A := TuringReducible.refl (oracleFunction A)
  trans _ _ _ h k := TuringReducible.trans h k

def Degree := Antisymmetrization Oracle Reduces

instance : PartialOrder Degree :=
  @instPartialOrderAntisymmetrization Oracle
    { le := Reduces
      lt A B := Reduces A B ∧ ¬ Reduces B A
      lt_iff_le_not_ge _ _ := Iff.rfl
      le_refl A := TuringReducible.refl (oracleFunction A)
      le_trans _ _ _ h k := TuringReducible.trans h k }

private instance oraclePreorder : Preorder Oracle where
  le := Reduces
  lt A B := Reduces A B ∧ ¬ Reduces B A
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl A := TuringReducible.refl (oracleFunction A)
  le_trans _ _ _ h k := TuringReducible.trans h k

def MainTheorem : Prop := ∀ π : Degree ≃o Degree, ∀ a : Degree, π a = a

namespace ManuscriptMain



end ManuscriptMain
end TuringRigidity
end OAI


