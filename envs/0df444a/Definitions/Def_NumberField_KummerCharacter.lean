-- Prove2me | Definitions.Def_NumberField_KummerCharacter
-- name    : NumberField_KummerCharacter
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/83598f9e-4c07-5c0a-86b7-e964da5b7349
-- title:
--   Kummer character of a unit via a chosen p-th root
-- statement:
--   Throughout, $p$ is a prime, $\zeta$ is an element of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `hζ : IsPrimitiveRoot ζ p`, and $F$ is an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$. For a unit $x$ of $F$, `kummerRoot p F x` is an element of $\overline{\mathbb{Q}}$ chosen, by the classical choice operator applied to Mathlib's solvability of $y^{n} = a$ over an algebraically closed field, so as to satisfy `kummerRoot_pow`: its $p$-th power is the image of $x$ in $\overline{\mathbb{Q}}$. Thus the root is one arbitrary $p$-th root of $x$, not a canonical one, and statements about it are only pinned down by the defining equation. Two elementary companions follow: `kummerRoot_ne_zero` says the chosen root is non-zero, and `div_kummerRoot_pow_eq_one` says that for $\sigma$ in `F.fixingSubgroup`, i.e. in the subgroup of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ fixing $F$ pointwise, the ratio $\sigma(y)/y$ with $y =$ `kummerRoot p F x` is a $p$-th root of unity (the proof uses that $\sigma$ fixes $x$ and that $x \neq 0$).
--
--   Since $\zeta$ is a primitive $p$-th root of unity, `exists_kummerExp` produces an exponent $i < p$ with $\zeta^{i} = \sigma(y)/y$. The definition `kummerChar p ζ hζ F x σ : ZMod p` is the class modulo $p$ of such a chosen exponent; as data it is simply a function $F$-fixing automorphisms $\to \mathbb{Z}/p$, depending on the chosen root $y$, with no homomorphism property or multiplicativity in $x$ asserted in this module. Its characterising property is `kummerChar_spec`: $\sigma(y) = \zeta^{n} y$, where $n$ is the canonical representative `(kummerChar p ζ hζ F x σ).val` in $\{0,\dots,p-1\}$. The module therefore supplies the data of the Kummer cocycle together with its defining equation, and nothing more.
--
--   **Relation to Mathlib.** The constructions rest on Mathlib's `IsAlgClosed.exists_pow_nat_eq`, `IsPrimitiveRoot` and `IntermediateField.fixingSubgroup`; the Kummer character in this explicit, choice-based form is the project's own packaging rather than a Mathlib notion.
--
--   **Where it is used.** These definitions provide the vocabulary for the Kummer-theoretic descent computations used in the arithmetic of levels: the character attached to a class in $F^{\times}/(F^{\times})^{p}$, on which the later ramification and equivariance statements of the tree are phrased.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_KummerCharacter.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

section KummerChar

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ))

def kummerRoot (x : (↥F)ˣ) : AlgebraicClosure ℚ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

theorem kummerRoot_pow (x : (↥F)ˣ) : kummerRoot p F x ^ p = ((x : ↥F) : AlgebraicClosure ℚ) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

theorem kummerRoot_ne_zero (x : (↥F)ˣ) : kummerRoot p F x ≠ 0 := fun h => by
  have := kummerRoot_pow p F x
  rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at this
  exact (Units.ne_zero x) (Subtype.ext (by exact_mod_cast this.symm))

theorem div_kummerRoot_pow_eq_one (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) / kummerRoot p F x) ^ p = 1 := by
  rw [div_pow, ← map_pow, kummerRoot_pow, div_eq_one_iff_eq]
  · exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ (x : ↥F).2
  · exact_mod_cast (Units.ne_zero x : (x : ↥F) ≠ 0)

include hζ in
theorem exists_kummerExp (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    ∃ i < p, ζ ^ i = (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) / kummerRoot p F x :=
  hζ.eq_pow_of_pow_eq_one (div_kummerRoot_pow_eq_one p F x σ)

def kummerChar (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) : ZMod p :=
  (Classical.choose (exists_kummerExp p ζ hζ F x σ) : ℕ)

theorem kummerChar_spec (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) = ζ ^ (kummerChar p ζ hζ F x σ).val * kummerRoot p F x := by
  obtain ⟨hi, h⟩ := Classical.choose_spec (exists_kummerExp p ζ hζ F x σ)
  rw [kummerChar, ZMod.val_natCast_of_lt hi, h, div_mul_cancel₀ _ (kummerRoot_ne_zero p F x)]

end KummerChar

end NumberField.LevelArith

end


