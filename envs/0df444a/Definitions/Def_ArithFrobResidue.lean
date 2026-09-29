-- Prove2me | Definitions.Def_ArithFrobResidue
-- name    : ArithFrobResidue
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/013493a4-b1e3-5627-8077-c05b190e73d0
-- title:
--   Arithmetic Frobenius elements as residue-field Frobenius generators
-- statement:
--   The module works in the following standing setting: commutative rings $A$ and $B$ with an $A$-algebra structure on $B$, a group $G$ acting on $B$ by ring automorphisms in a way compatible with the $A$-action, and a maximal ideal $P \subseteq B$ whose contraction $\mathfrak p =$ `P.under A` to $A$ is maximal, with $A/\mathfrak p$ finite and $B/P$ finite; the residue rings are treated as fields. It contains no new definitions, only comparison statements identifying the residue automorphism attached to an arithmetic Frobenius element with Mathlib's canonical Frobenius generator of a finite-field extension.
--
--   The principal statement, `stabilizerHom_eq_frobenius`, takes $\sigma$ in the stabiliser of $P$ in $G$ satisfying `IsArithFrobAt A (σ : G) P` (that is, $\sigma b \equiv b^{\#(A/\mathfrak p)} \pmod P$ for all $b \in B$) and asserts that its image under `Ideal.Quotient.stabilizerHom P (P.under A) G`, an $A/\mathfrak p$-algebra automorphism of $B/P$, is exactly `FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P)`, the automorphism $y \mapsto y^{q}$ with $q = \#(A/\mathfrak p)$; `stabilizerHom_apply_pow` records the same fact pointwise. `exists_stabilizerHom_eq_frobenius` adds the hypotheses that $G$ is finite and $A$ is the ring of $G$-invariants of $B$ (`Algebra.IsInvariant A B G`) and produces some element of the stabiliser of $P$ whose residue automorphism is that Frobenius. From the identification follow `orderOf_stabilizerHom_eq_finrank`, that the order of the residue automorphism equals the residue degree $[B/P : A/\mathfrak p]$, and `exists_pow_stabilizerHom_eq`, that every $A/\mathfrak p$-algebra automorphism of $B/P$ is a power of it. Finally `stabilizerHom_injective_of_inertia_eq_bot` states that vanishing of the inertia subgroup `P.inertia G` makes `Ideal.Quotient.stabilizerHom` injective on the whole stabiliser (this statement drops the maximality and finiteness instances), and `orderOf_arithFrob_eq_finrank_of_inertia_eq_bot` concludes that in that case an arithmetic Frobenius element has order $[B/P : A/\mathfrak p]$ in $G$ itself.
--
--   **Relation to Mathlib.** All the ingredients are Mathlib's: the predicate `IsArithFrobAt`, the map `Ideal.Quotient.stabilizerHom` from the stabiliser of $P$ to the residue algebra automorphisms, the canonical generator `FiniteField.frobeniusAlgEquivOfAlgebraic`, and `Ideal.inertia`. What this module provides is the dictionary between them, together with the resulting order and generation statements.
--
--   **Where it is used.** These lemmas are used to compute the permutation action of an arithmetic Frobenius element on the roots of a polynomial upstairs, giving Dedekind's description of its cycle type in terms of the degrees of the irreducible factors of the reduced polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ArithFrobResidue.lean

import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

namespace ArithFrobResidue

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
  {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
  [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]

theorem stabilizerHom_eq_frobenius
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    Ideal.Quotient.stabilizerHom P (P.under A) G σ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P) := by
  ext x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hL : Ideal.Quotient.stabilizerHom P (P.under A) G σ (Ideal.Quotient.mk P b)
      = (Ideal.Quotient.mk P b) ^ Nat.card (A ⧸ P.under A) := by
    rw [Ideal.Quotient.stabilizerHom_apply, MulAction.subgroup_smul_def]
    exact hσ.mk_apply b
  have hR : FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P)
        (Ideal.Quotient.mk P b)
      = (Ideal.Quotient.mk P b) ^ Fintype.card (A ⧸ P.under A) :=
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) _
  rw [hL, hR, Nat.card_eq_fintype_card]

theorem stabilizerHom_apply_pow
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) (y : B ⧸ P) :
    Ideal.Quotient.stabilizerHom P (P.under A) G σ y = y ^ Fintype.card (A ⧸ P.under A) := by
  rw [stabilizerHom_eq_frobenius σ hσ]
  exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic _ _) y

theorem exists_stabilizerHom_eq_frobenius [Finite G] [Algebra.IsInvariant A B G] :
    ∃ σ : MulAction.stabilizer G P,
      Ideal.Quotient.stabilizerHom P (P.under A) G σ =
        FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P) := by
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant A G P
  exact ⟨⟨σ, hσ.mem_stabilizer⟩, stabilizerHom_eq_frobenius _ hσ⟩

theorem orderOf_stabilizerHom_eq_finrank
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (Ideal.Quotient.stabilizerHom P (P.under A) G σ) =
      Module.finrank (A ⧸ P.under A) (B ⧸ P) := by
  rw [stabilizerHom_eq_frobenius σ hσ]
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (A ⧸ P.under A) (B ⧸ P)

theorem exists_pow_stabilizerHom_eq
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P)
    (τ : (B ⧸ P) ≃ₐ[A ⧸ P.under A] (B ⧸ P)) :
    ∃ n : ℕ, (Ideal.Quotient.stabilizerHom P (P.under A) G σ) ^ n = τ := by
  rw [stabilizerHom_eq_frobenius σ hσ]
  obtain ⟨m, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (A ⧸ P.under A) (B ⧸ P)).surjective τ
  exact ⟨m.1, hn⟩

omit [P.IsMaximal] [(P.under A).IsMaximal] [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)] in

theorem stabilizerHom_injective_of_inertia_eq_bot (hP : P.inertia G = ⊥) :
    Function.Injective (Ideal.Quotient.stabilizerHom P (P.under A) G) := by
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom, Ideal.inertia,
    ← AddSubgroup.subgroupOf_inertia, ← Ideal.inertia, hP, Subgroup.bot_subgroupOf]

theorem orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
    (hP : P.inertia G = ⊥)
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (σ : G) = Module.finrank (A ⧸ P.under A) (B ⧸ P) := by
  have hinj := stabilizerHom_injective_of_inertia_eq_bot (A := A) (P := P) (G := G) hP
  rw [Subgroup.orderOf_coe σ,
    ← orderOf_injective (Ideal.Quotient.stabilizerHom P (P.under A) G) hinj σ,
    orderOf_stabilizerHom_eq_finrank σ hσ]

end ArithFrobResidue


