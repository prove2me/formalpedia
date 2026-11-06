-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
-- name    : OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:21:21.556938+00:00
-- url     : https://prove2.me/theorems/036d97ff-bcbb-454c-bf99-d3b966ddad25
-- title:
--   Quadratic Trace
-- statement:
--   Definitions and structural lemmas for Quadratic Trace, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
section
open ActualEisensteinCoordinates ShortDraftLatticeCount
end
section
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
theorem rational_modulus_card (m : ℕ) (_hm : m ≠ 0) :
    Nat.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
  have hnorm : Algebra.norm ℤ (m : O) = (m : ℤ) ^ 2 := by
    have h := Algebra.norm_algebraMap_of_basis
      EisensteinEmbedding.pb.basis (m : ℤ)
    simpa [EisensteinEmbedding.pb_dim] using h
  calc
    Nat.card (O ⧸ Ideal.span {(m : O)}) =
        Ideal.absNorm (Ideal.span {(m : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Algebra.norm ℤ (m : O)).natAbs :=
      Ideal.absNorm_span_singleton (m : O)
    _ = m ^ 2 := by rw [hnorm]; simp
theorem mk_eval_congr_mod (m : ℕ) (a b c d : ℤ)
    (ha : (a : ZMod m) = c) (hb : (b : ZMod m) = d) :
    Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval a b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval c d) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have hda : (m : ℤ) ∣ a - c :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub c a m).mp ha.symm
  have hdb : (m : ℤ) ∣ b - d :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d b m).mp hb.symm
  obtain ⟨r, hr⟩ := hda
  obtain ⟨s, hs⟩ := hdb
  apply (Ideal.mem_span_singleton).mpr
  refine ⟨ActualEisensteinCoordinates.eval r s, ?_⟩
  dsimp [ActualEisensteinCoordinates.eval]
  rw [show a = c + m*r by omega, show b = d + m*s by omega]
  push_cast
  ring
noncomputable def rationalCoordMap (m : ℕ) :
    ZMod m × ZMod m → (O ⧸ Ideal.span {(m : O)}) :=
  fun ab => Ideal.Quotient.mk (Ideal.span {(m : O)})
    (ActualEisensteinCoordinates.eval (ZMod.cast ab.1) (ZMod.cast ab.2))
theorem rationalCoordMap_surjective (m : ℕ) :
    Function.Surjective (rationalCoordMap m) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, b, hab⟩ := ActualEisensteinCoordinates.exists_coordinates z
  refine ⟨((a : ZMod m), (b : ZMod m)), ?_⟩
  change Ideal.Quotient.mk (Ideal.span {(m : O)})
      (ActualEisensteinCoordinates.eval (ZMod.cast (a : ZMod m))
        (ZMod.cast (b : ZMod m))) = _
  rw [hab]
  apply mk_eval_congr_mod
  · exact ZMod.intCast_zmod_cast _
  · exact ZMod.intCast_zmod_cast _
noncomputable def rationalCoordEquiv (m : ℕ) (hm : m ≠ 0) :
    ZMod m × ZMod m ≃ (O ⧸ Ideal.span {(m : O)}) := by
  letI : NeZero m := ⟨hm⟩
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  refine Equiv.ofBijective (rationalCoordMap m) ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · exact rationalCoordMap_surjective m
  · have hq : Fintype.card (O ⧸ Ideal.span {(m : O)}) = m ^ 2 := by
      simpa only [Nat.card_eq_fintype_card] using rational_modulus_card m hm
    simp [hq, Fintype.card_prod, sq]
noncomputable def quadraticGammaRational (m : ℕ) (hm : m ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {(m : O)}) :=
    finite_quotient_span (by exact_mod_cast hm)
  letI : Fintype (O ⧸ Ideal.span {(m : O)}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates
    (m : O) (by exact_mod_cast hm)
  exact (∑ x : O ⧸ Ideal.span {(m : O)}, ψ (x ^ 2)) /
    (‖eisEmbedding (m : O)‖ : ℂ)
end
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
end ActualEisensteinCubic
end
end OAI


