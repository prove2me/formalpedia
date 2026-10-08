-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13QuotientFiniteness_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13QuotientFiniteness_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:32:36.92698+00:00
-- url     : https://prove2.me/theorems/6722b52c-385f-4d4f-802f-ce7e0fc74f16
-- title:
--   FLT.Assumptions.MazurProof.N13QuotientFiniteness source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13QuotientFiniteness

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13QuotientFiniteness
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Basic

set_option autoImplicit false




/-!
# Finiteness from one monic affine relation

This file isolates the algebraic finiteness step in the explicit N13
no-escape argument.  If an affine algebra has a rank-two polynomial normal
form `P(x) + Q(x) * y`, then one monic relation in `x` contained in an ideal
already makes the corresponding quotient finite over the base ring.

The proof factors the quotient through two copies of `AdjoinRoot m`.  It
therefore uses the structural finite basis of a monic polynomial quotient,
without choosing a degree bound or enumerating polynomial coefficients.
-/

open Polynomial

namespace MazurProof.N13QuotientFiniteness

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]

/--
A rank-two polynomial normal form together with one monic relation in the
first coordinate makes every ideal quotient finite over the base ring.
-/
theorem quotient_finite_of_monic_relation_of_rankTwoNormalForm
    (x y : A)
    (normalForm :
      ∀ a : A,
        ∃ P Q : R[X],
          a = aeval x P + aeval x Q * y)
    (I : Ideal A)
    {m : R[X]}
    (hm : m.Monic)
    (hmI : aeval x m ∈ I) :
    Module.Finite R (A ⧸ I) := by
  let xq : A ⧸ I := Ideal.Quotient.mk I x
  let yq : A ⧸ I := Ideal.Quotient.mk I y
  have aeval_mk (p : R[X]) :
      aeval xq p =
        Ideal.Quotient.mk I (aeval x p) := by
    simp only [aeval_def, xq]
    exact
      (Polynomial.hom_eval₂ p
        (algebraMap R A) (Ideal.Quotient.mk I) x).symm
  have hmRoot : aeval xq m = 0 := by
    calc
      aeval xq m =
          Ideal.Quotient.mk I (aeval x m) := aeval_mk m
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmI
  let φ : AdjoinRoot m →ₐ[R] A ⧸ I :=
    AdjoinRoot.liftAlgHom m (Algebra.ofId R (A ⧸ I)) xq hmRoot
  let L : (AdjoinRoot m × AdjoinRoot m) →ₗ[R] A ⧸ I := {
    toFun z := φ z.1 + φ z.2 * yq
    map_add' p q := by
      change
        φ (p.1 + q.1) + φ (p.2 + q.2) * yq =
          (φ p.1 + φ p.2 * yq) + (φ q.1 + φ q.2 * yq)
      rw [map_add, map_add]
      ring
    map_smul' r p := by
      rw [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
        map_smul, map_smul, smul_add, Algebra.smul_mul_assoc]
  }
  letI : Module.Finite R (AdjoinRoot m) :=
    hm.finite_adjoinRoot
  refine Module.Finite.of_surjective L ?_
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨P, Q, hPQ⟩ := normalForm a
  refine ⟨(AdjoinRoot.mk m P, AdjoinRoot.mk m Q), ?_⟩
  change
    φ (AdjoinRoot.mk m P) +
        φ (AdjoinRoot.mk m Q) * yq =
      Ideal.Quotient.mk I a
  have hφ (p : R[X]) : φ (AdjoinRoot.mk m p) = aeval xq p :=
    AdjoinRoot.liftAlgHom_mk m (Algebra.ofId R (A ⧸ I)) xq hmRoot p
  rw [hφ P, hφ Q]
  rw [aeval_mk P, aeval_mk Q]
  dsimp only [yq]
  rw [← map_mul, ← map_add, hPQ]

end

end MazurProof.N13QuotientFiniteness


