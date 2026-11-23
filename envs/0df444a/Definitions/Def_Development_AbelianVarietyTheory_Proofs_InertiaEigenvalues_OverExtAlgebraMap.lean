-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:28.113606+00:00
-- url     : https://prove2.me/theorems/7689f45d-580c-443a-a70d-deaf24e90f76
-- title:
--   Over Ext Algebra Map
-- statement:
--   Definitions and structural lemmas for Over Ext Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/OverExtAlgebraMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
def IsUnrExt (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) : Prop :=
  K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧
    @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d
variable {K K' : UQ}
def overExt (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) : InvAlg K' :=
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := by
    obtain ⟨S, hS⟩ := B.fd.fg_top
    refine ⟨⟨S, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.E (S : Set B.A) := hS ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  { A := B.A
    σ := B.σ
    σ_σ := B.σ_σ
    σ_alg := hσ
    g := B.g }
end GlobalTheory.UnitLemma.Unr


