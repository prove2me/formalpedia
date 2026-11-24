-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:10.14275+00:00
-- url     : https://prove2.me/theorems/a7bd9655-d909-4550-862a-10a329fa4a60
-- title:
--   Prod Minors Mem Inv
-- statement:
--   Definitions and structural lemmas for Prod Minors Mem Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.MinorFrame
abbrev Var (ι : Type) (d a : ℕ) : Type := ι × Fin d × Fin a
abbrev Pol (ι : Type) (d a : ℕ) : Type := MvPolynomial (Var ι d a) ℂ
abbrev Tup (ι : Type) (a d : ℕ) (n : ι → ℕ) : Type := ∀ τ, Fin (n τ) → {s : Fin a → Fin d // StrictMono s}
variable {ι : Type}
def minorAt (τ : ι) {a d : ℕ} (s : Fin a → Fin d) : Pol ι d a :=
  (Matrix.of fun i i' : Fin a => (X (τ, s i, i') : Pol ι d a)).det
variable [Fintype ι]
def prodMinors {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : Pol ι d a := ∏ τ, ∏ j, minorAt τ (T τ j).1
def rowSub {d a : ℕ} (κ : ι → Matrix (Fin d) (Fin d) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ i' : Fin d, C (κ y.1 i' y.2.1) * X (y.1, i', y.2.2)
def colSub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Pol ι d a →ₐ[ℂ] Pol ι d a :=
  aeval fun y => ∑ j' : Fin a, C (g y.1 j' y.2.2) * X (y.1, y.2.1, j')
def detChar {a : ℕ} (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) : ℂ := ∏ τ, (g τ).det ^ n τ
def inv (a d : ℕ) (n : ι → ℕ) : Submodule ℂ (Pol ι d a) where
  carrier := {P | ∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ,
    colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P = detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • P}
  add_mem' := by
    intro P Q hP hQ g
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, hP g, hQ g, smul_add]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c P hP g
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, hP g, smul_comm]
end GlobalTheory.MinorFrame
namespace GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
end GlobalTheory.MinorFrame
namespace GlobalTheory.MinorFrame
open Classical
variable {ι : Type} [Fintype ι]
end GlobalTheory.MinorFrame


