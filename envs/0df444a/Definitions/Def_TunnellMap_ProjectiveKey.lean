-- Prove2me | Definitions.Def_TunnellMap_ProjectiveKey
-- name    : TunnellMap_ProjectiveKey
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:20:17.17245+00:00
-- url     : https://prove2.me/theorems/4a0508de-606f-5320-82e6-eed7042581c8
-- title:
--   Projective Key
-- statement:
--   Definitions and structural lemmas for Projective Key, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


set_option autoImplicit true
namespace TunnellMap
def qBilinear (p q : Triple) : ℤ :=
  2 * p.x * q.x + p.y * q.y + 2 * p.z * q.z
def vsub (p q : Triple) : Triple :=
  ⟨p.x - q.x, p.y - q.y, p.z - q.z⟩
@[simp] theorem qBilinear_self (p : Triple) : qBilinear p p = qForm p := by
  simp [qBilinear, qForm]
  ring
structure DirectionKey where
  /-- The value of the quadratic form on the primitive direction. -/
  form : ℤ
  /-- The first coordinate of the primitive direction. -/
  x : ℤ
  /-- The second coordinate of the primitive direction. -/
  y : ℤ
  /-- The third coordinate of the primitive direction. -/
  z : ℤ
deriving DecidableEq
namespace DirectionKey
def toLexKey (k : DirectionKey) : ℤ ×ₗ (ℤ ×ₗ (ℤ ×ₗ ℤ)) :=
  toLex (k.form, toLex (k.x, toLex (k.y, k.z)))
theorem toLexKey_injective : Function.Injective toLexKey := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  simp only [toLexKey, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp_all
def blt (a b : DirectionKey) : Bool :=
  a.form < b.form || (a.form == b.form &&
    (a.x < b.x || (a.x == b.x && (a.y < b.y || (a.y == b.y && a.z < b.z)))))
def ble (a b : DirectionKey) : Bool := !blt b a
theorem blt_iff_lex (a b : DirectionKey) :
    blt a b = true ↔ toLexKey a < toLexKey b := by
  simp only [blt, toLexKey, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Prod.Lex.toLex_lt_toLex]
theorem ble_iff_lex (a b : DirectionKey) :
    ble a b = true ↔ toLexKey a ≤ toLexKey b := by
  rw [ble, Bool.not_eq_true', ← Bool.not_eq_true, blt_iff_lex, not_lt]
instance instLinearOrder : LinearOrder DirectionKey where
  le a b := toLexKey a ≤ toLexKey b
  lt a b := toLexKey a < toLexKey b
  le_refl _ := le_refl _
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
  le_antisymm _ _ h₁ h₂ := toLexKey_injective (le_antisymm h₁ h₂)
  le_total _ _ := le_total _ _
  toDecidableLE a b := decidable_of_iff (ble a b = true) (ble_iff_lex a b)
  toDecidableLT a b := decidable_of_iff (blt a b = true) (blt_iff_lex a b)
  toDecidableEq := instDecidableEqDirectionKey
end DirectionKey
noncomputable def directionKey (v : Triple) : DirectionKey :=
  ⟨qForm (primitiveDirection v), (primitiveDirection v).x,
    (primitiveDirection v).y, (primitiveDirection v).z⟩
def residualSourceLift {n : ℤ} (s : BResidual n) : Triple := bLift s.1
def residualTargetLift {n : ℤ} (t : AResidual n) : Triple := aLift t.1
def plusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  vadd (residualSourceLift s) (residualTargetLift t)
def minusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  vsub (residualSourceLift s) (residualTargetLift t)
noncomputable def representativeEdgeKey {n : ℤ} (s : BResidual n) (t : AResidual n) :
    DirectionKey :=
  min (directionKey (plusVector s t)) (directionKey (minusVector s t))
noncomputable def preferredVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then
    plusVector s t
  else
    minusVector s t
end TunnellMap


