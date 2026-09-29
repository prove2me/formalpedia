-- Prove2me | Definitions.Def_AlgebraicCurve_RegularProlongation
-- name    : AlgebraicCurve_RegularProlongation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/e569c5f1-ac8b-5a7a-8582-3132e3f94293
-- title:
--   Regular prolongations of a valuation ring to a function field
-- statement:
--   Throughout, $L$ is a field, $A \subseteq L$ a valuation subring with residue field $k = A/\mathfrak m_A$, $F$ a field extension of $L$, and $\bar F$ a field extension of $k$. The structure [`AlgebraicCurve.RegularProlongation A F Fbar`](../def/AlgebraicCurve_RegularProlongation.html#L16) bundles the data of a regular prolongation of $A$ to $F$ with residue field $\bar F$: a valuation subring $\mathcal O \subseteq F$ (`integers`); a ring homomorphism $\varrho \colon \mathcal O \to \bar F$ (`residue`); the condition that $\mathcal O$ lies over $A$ in the strong sense that for every $x \in L$ one has $\mathrm{alg}_{L \to F}(x) \in \mathcal O$ if and only if $x \in A$, i.e. $\mathcal O \cap L = A$ (`algebraMap_mem_iff`); surjectivity of $\varrho$ together with $\ker \varrho = \mathfrak m_{\mathcal O}$, so that $\varrho$ identifies $\mathcal O/\mathfrak m_{\mathcal O}$ with $\bar F$ (`residue_surjective`, `ker_residue`); compatibility on constants, $\varrho(a) = \mathrm{alg}_{k \to \bar F}(a \bmod \mathfrak m_A)$ for $a \in A$, so the identification is one of $k$-algebras (`residue_algebraMap`); and a regularity clause (`exists_smul_mem`) asserting that every $f \in F$, $f \neq 0$, admits $c \in L$ with $c \cdot f \in \mathcal O$ and $\varrho(c \cdot f) \neq 0$ — that is, $F^{\times}$ is exhausted by constants times units of $\mathcal O$, expressing that the value group of $\mathcal O$ is that of $A$.
--
--   Three small lemmas record the basic consequences: an element of $\mathcal O$ is a unit exactly when its residue is nonzero (`isUnit_of_residue_ne_zero`, `residue_ne_zero_of_isUnit`, from locality of $\mathcal O$ and $\ker \varrho = \mathfrak m_{\mathcal O}$), and the scalar produced by the regularity clause is necessarily nonzero (`smul_const_ne_zero`). Finally, [`AlgebraicCurve.ConstantReduction.toRegularProlongation`](../def/AlgebraicCurve_RegularProlongation.html#L65) is the forgetful passage from the project's `ConstantReduction` structure, whose first seven fields are precisely the fields above, discarding the reduction map on places and its two compatibility clauses; two lemmas identify the ring of integers and the residue map of the result with those of the original.
--
--   **Relation to Mathlib.** Built on Mathlib's `ValuationSubring` and `IsLocalRing.ResidueField`, but the notion itself — a valuation subring of $F$ contracting to a prescribed valuation subring of $L$, with a prescribed $k$-algebra identification of its residue field and with value group equal to that of $A$ — is the project's own; Mathlib has no such structure.
--
--   **Where it is used.** This is the carrier for statements about several prolongations of one valuation ring of the constants to a single function field, where the individual prolongations carry no divisor-compatible reduction of places and so are not constant reductions in the sense of the project's `ConstantReduction`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_RegularProlongation.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

structure RegularProlongation where

  integers : ValuationSubring F

  residue : integers →+* Fbar

  algebraMap_mem_iff : ∀ x : L, algebraMap L F x ∈ integers ↔ x ∈ A

  residue_surjective : Function.Surjective residue

  ker_residue : RingHom.ker residue = maximalIdeal integers

  residue_algebraMap : ∀ a : A,
    residue ⟨algebraMap L F a, (algebraMap_mem_iff a).mpr a.2⟩ =
      algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a)

  exists_smul_mem : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ integers, residue ⟨c • f, h⟩ ≠ 0

namespace RegularProlongation

variable {A F Fbar}
variable (R : RegularProlongation A F Fbar)

theorem isUnit_of_residue_ne_zero {f : R.integers} (hf : R.residue f ≠ 0) : IsUnit f := by
  by_contra h
  apply hf
  have hmem : f ∈ maximalIdeal R.integers := (IsLocalRing.mem_maximalIdeal f).mpr h
  rw [← R.ker_residue] at hmem
  exact hmem

theorem residue_ne_zero_of_isUnit {f : R.integers} (hf : IsUnit f) : R.residue f ≠ 0 := by
  intro h0
  have hmem : f ∈ RingHom.ker R.residue := h0
  rw [R.ker_residue] at hmem
  exact (IsLocalRing.mem_maximalIdeal f).mp hmem hf

theorem smul_const_ne_zero {f : F} {c : L} (hc : c • f ∈ R.integers)
    (hres : R.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

end RegularProlongation

namespace ConstantReduction

variable {A F Fbar}

@[reducible] def toRegularProlongation (R : ConstantReduction A F Fbar) : RegularProlongation A F Fbar where
  integers := R.integers
  residue := R.residue
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem

@[simp] theorem toRegularProlongation_integers (R : ConstantReduction A F Fbar) :
    R.toRegularProlongation.integers = R.integers := rfl

@[simp] theorem toRegularProlongation_residue (R : ConstantReduction A F Fbar) :
    R.toRegularProlongation.residue = R.residue := rfl

end ConstantReduction

end AlgebraicCurve

end


