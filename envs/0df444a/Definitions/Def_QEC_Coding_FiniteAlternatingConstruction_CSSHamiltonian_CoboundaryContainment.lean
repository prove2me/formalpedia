-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T02:00:22.325029+00:00
-- url     : https://prove2.me/theorems/49e791b8-083d-44c4-82a6-521b162d41f1
-- title:
--   Coboundary Containment
-- statement:
--   Definitions and structural lemmas for Coboundary Containment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
local instance imageFintype (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) :
    Fintype (LinearMap.range P) := Fintype.ofFinite _
def shift (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ s : LinearMap.range P) : LinearMap.range P := s+τ
theorem shift_involutive (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Function.Involutive (shift P τ) := by
  intro s
  apply Subtype.ext
  funext j
  change (s.val j+τ.val j)+τ.val j=s.val j
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
def shiftEquiv (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : LinearMap.range P ≃ LinearMap.range P where
  toFun := shift P τ
  invFun := shift P τ
  left_inv := shift_involutive P τ
  right_inv := shift_involutive P τ
def containment (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Finset (LinearMap.range P) :=
  Finset.univ.filter fun s => hammingSupport τ.val ⊆ hammingSupport s.val
def translated (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Finset (LinearMap.range P) :=
  (containment P τ).map (shiftEquiv P τ).toEmbedding
def mass (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (A : Finset (LinearMap.range P)) : ℝ :=
  ∑ s ∈ A, CSSGibbs.rowProbability P t s
def familyEvent (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (W : Finset (LinearMap.range P)) : Finset (LinearMap.range P) :=
  W.biUnion (containment P)
end QEC.Coding.FixedCoboundaryGibbs
namespace QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
local instance xImageFintype (S : OddScale) (n : Nat) : Fintype (XImage S n) := Fintype.ofFinite _
local instance zImageFintype (S : OddScale) (n : Nat) : Fintype (ZImage S n) := Fintype.ofFinite _
def xContainment (S : OddScale) (n : Nat) (τ : XImage S n) :=
  FixedCoboundaryGibbs.containment (zSyndrome S n) τ
def zContainment (S : OddScale) (n : Nat) (τ : ZImage S n) :=
  FixedCoboundaryGibbs.containment (xSyndrome S n) τ
def xFamily (S : OddScale) (n : Nat) (W : Finset (XImage S n)) :=
  FixedCoboundaryGibbs.familyEvent (zSyndrome S n) W
def zFamily (S : OddScale) (n : Nat) (W : Finset (ZImage S n)) :=
  FixedCoboundaryGibbs.familyEvent (xSyndrome S n) W
def xSelected (S : OddScale) (n : Nat) (A : Finset (XImage S n)) :
    Operator (Qubit.QubitRegister (Physical S n)) := selected S n (A ×ˢ Finset.univ)
def zSelected (S : OddScale) (n : Nat) (A : Finset (ZImage S n)) :
    Operator (Qubit.QubitRegister (Physical S n)) := selected S n (Finset.univ ×ˢ A)
end QEC.Coding.BDL26CoboundaryContainment


