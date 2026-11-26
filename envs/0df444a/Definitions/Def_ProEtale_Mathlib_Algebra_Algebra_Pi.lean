-- Prove2me | Definitions.Def_ProEtale_Mathlib_Algebra_Algebra_Pi
-- name    : ProEtale_Mathlib_Algebra_Algebra_Pi
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:36:41.173495+00:00
-- url     : https://prove2.me/theorems/37a02385-8ac6-4c9e-bbf9-0bf0910fd372
-- title:
--   Algebra maps from a finite product of algebras to a local algebra factor through a single factor
-- statement:
--   Let $A$ be a commutative semiring and $R_0, R_1$ semirings that are $A$-algebras. The file first gives the $A$-algebra isomorphism
--   $$\prod_{i \in \{0,1\}} R_i \;\cong\; R_0 \times R_1.$$
--
--   Next let $k$ be a commutative semiring, $I$ a finite index set, $(A_i)_{i\in I}$ commutative rings that are $k$-algebras, $B$ a commutative $k$-algebra, and $\psi : \prod_i A_i \to B$ a $k$-algebra homomorphism. Write $e_i$ for the idempotent with $1$ in position $i$ and $0$ elsewhere.
--
--   Principal results:
--   1. If $B$ is a local ring, there exists $j \in I$ with $\psi(e_j) = 1$ and $\psi(e_i) = 0$ for all $i \ne j$.
--   2. Given such $j$ (for arbitrary $B$), the map $\psi_j : A_j \to B$, $y \mapsto \psi(\text{the element with } y \text{ in position } j \text{ and } 0 \text{ elsewhere})$, is a $k$-algebra homomorphism.
--   3. With $I$ finite, $\psi(x) = \psi_j(x_j)$ for every $x \in \prod_i A_i$; thus $\psi$ factors through the projection to $A_j$.
--
--   These lemmas are used to analyse homomorphisms from étale algebras over a field (finite products of finite separable field extensions) to local rings.
--
--   **Formalization Note** Declarations: `AlgEquiv.piFinTwo`, `AlgHom.exists_pi_single_eq_one_of_isLocalRing`, `AlgHom.piFactor` (with simp lemma `piFactor_apply`) and `AlgHom.eq_piFactor_apply`. The idempotents are `Pi.single i 1`; `I` carries `DecidableEq`, and finiteness is `_root_.Finite I`. `piFactor` itself requires neither finiteness of `I` nor locality of `B`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Algebra/Pi.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Ring.Fin
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Definitions.Def_ProEtale_Mathlib_RingTheory_Idempotents

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Algebra equivalences for Pi types

In this file we provide the algebra version of `RingEquiv.piFinTwo`, and lemmas about algebra
homomorphisms out of a finite product of algebras to a local algebra.
-/

/-- The product over `Fin 2` of some algebras is the Cartesian product of these algebras. -/
def AlgEquiv.piFinTwo (A : Type*) [CommSemiring A] (R : Fin 2 → Type*)
    [∀ i, Semiring (R i)] [∀ i, Algebra A (R i)] :
    (∀ i : Fin 2, R i) ≃ₐ[A] R 0 × R 1 :=
  { RingEquiv.piFinTwo R with
    commutes' := fun _ => rfl }

-- `_root_.Finite` is required below because `AlgHom.Finite` is in scope inside this namespace.
namespace AlgHom

variable {k : Type*} [CommSemiring k] {I : Type*} [DecidableEq I]
  {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
  {B : Type*} [CommRing B] [Algebra k B]

/-- An algebra homomorphism from a finite product of commutative rings to a nontrivial local
algebra factors through one of the factors: there exists `j : I` with `ψ (Pi.single j 1) = 1`
and `ψ (Pi.single i 1) = 0` for every `i ≠ j`. -/
lemma exists_pi_single_eq_one_of_isLocalRing [_root_.Finite I] [IsLocalRing B]
    (ψ : (∀ i, A i) →ₐ[k] B) :
    ∃ j : I, ψ (Pi.single j 1) = 1 ∧ ∀ i, i ≠ j → ψ (Pi.single i 1) = 0 := by
  have : Fintype I := Fintype.ofFinite I
  have hcoi : CompleteOrthogonalIdempotents
      (fun i : I ↦ Pi.single (M := fun i ↦ A i) i (1 : A i)) :=
    CompleteOrthogonalIdempotents.single _
  have hidem (i : I) : IsIdempotentElem (ψ (Pi.single i 1)) :=
    (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.idem i
  have h01 (i : I) : ψ (Pi.single i 1) = 0 ∨ ψ (Pi.single i 1) = 1 :=
    (hidem i).eq_zero_or_one_of_isLocalRing
  have hsum : ∑ i : I, ψ (Pi.single i 1) = 1 := by
    rw [← map_sum]
    simp [hcoi.complete]
  have hortho (i j : I) (hij : i ≠ j) :
      ψ (Pi.single i 1) * ψ (Pi.single j 1) = 0 := by
    simpa [Function.comp_def] using
      (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.ortho hij
  have hex : ∃ j, ψ (Pi.single j 1) = 1 := by
    by_contra hall
    push Not at hall
    have hzero : ∀ i, ψ (Pi.single i 1) = 0 := fun i ↦ (h01 i).resolve_right (hall i)
    simp [hzero] at hsum
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, fun i hi ↦ ?_⟩
  have := hortho i j hi
  rwa [hj, mul_one] at this

/-- The algebra homomorphism `A j →ₐ[k] B` factoring `ψ : (∀ i, A i) →ₐ[k] B` through the
`j`-th factor, given that `ψ (Pi.single j 1) = 1` and `ψ (Pi.single i 1) = 0` for every
`i ≠ j`. Note that `B` is not required to be local; the hypotheses subsume that. -/
def piFactor (ψ : (∀ i, A i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1) (_hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0) :
    A j →ₐ[k] B where
  toFun y := ψ (Pi.single j y)
  map_one' := hj
  map_mul' y₁ y₂ := by simp [Pi.single_mul]
  map_zero' := by simp
  map_add' y₁ y₂ := by simp [Pi.single_add]
  commutes' c := by
    have heq : Pi.single j (algebraMap k (A j) c) =
        (algebraMap k (∀ i, A i) c) * Pi.single j 1 := by
      ext i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Pi.single_eq_of_ne hij]
    rw [heq, map_mul, AlgHom.commutes, hj, mul_one]

@[simp]
lemma piFactor_apply (ψ : (∀ i, A i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1) (hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0) (y : A j) :
    piFactor ψ j hj hothers y = ψ (Pi.single j y) := rfl

/-- An algebra homomorphism `ψ : (∀ i, A i) →ₐ[k] B` to a local algebra is recovered from its
factor through the unique component `A j` selected by the unit idempotents. -/
lemma eq_piFactor_apply [_root_.Finite I] (ψ : (∀ i, A i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1) (hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0)
    (x : ∀ i, A i) : ψ x = piFactor ψ j hj hothers (x j) := by
  have : Fintype I := Fintype.ofFinite I
  rw [piFactor_apply]
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_eq_single_of_mem j (Finset.mem_univ _) fun i _ hi ↦ ?_
  have : Pi.single (M := fun i ↦ A i) i (x i) = Pi.single i 1 * x := by
    rw [← Pi.single_mul_left]
    simp
  rw [this, map_mul, hothers i hi, zero_mul]

end AlgHom


