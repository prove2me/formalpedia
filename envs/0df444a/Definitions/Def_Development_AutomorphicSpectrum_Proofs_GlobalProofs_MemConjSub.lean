-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:34.851674+00:00
-- url     : https://prove2.me/theorems/e74a7238-1c78-4c60-a5d8-8ebbd4b97284
-- title:
--   Mem Conj Sub
-- statement:
--   Definitions and structural lemmas for Mem Conj Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemConjSub.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.QIndex
variable {F : Type} [Field F]
def Lvl {n : ℕ} (O : Subring F) (c : F) (X : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, ∃ o ∈ O, X a b = c * o
theorem Lvl.add {n : ℕ} {O : Subring F} {c : F} {X Y : Matrix (Fin n) (Fin n) F} (hX : Lvl O c X)
    (hY : Lvl O c Y) : Lvl O c (X + Y) := fun a b => by
  obtain ⟨o, ho, h⟩ := hX a b
  obtain ⟨o', ho', h'⟩ := hY a b
  exact ⟨o + o', O.add_mem ho ho', by simp [h, h', mul_add]⟩
theorem Lvl.neg {n : ℕ} {O : Subring F} {c : F} {X : Matrix (Fin n) (Fin n) F} (hX : Lvl O c X) :
    Lvl O c (-X) := fun a b => by
  obtain ⟨o, ho, h⟩ := hX a b
  exact ⟨-o, O.neg_mem ho, by simp [h]⟩
theorem Lvl.int_mul {n : ℕ} {O : Subring F} {c : F} {X Y : Matrix (Fin n) (Fin n) F}
    (hY : IsInt O Y) (hX : Lvl O c X) : Lvl O c (Y * X) := fun a b => by
  choose f hf hf' using hX
  refine ⟨∑ k, Y a k * f k b, O.sum_mem fun k _ => O.mul_mem (hY a k) (hf k b), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hf' k b]; ring
def congGL (O : Subring F) (c : F) (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {g | g ∈ GLint O n ∧ Lvl O c ((g : Matrix (Fin n) (Fin n) F) - 1)}
  one_mem' := ⟨(GLint O n).one_mem, fun a b => ⟨0, O.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(GLint O n).mul_mem hx hy, ?_⟩
    have : ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
        (x : Matrix (Fin n) (Fin n) F) * ((y : Matrix (Fin n) (Fin n) F) - 1) +
          ((x : Matrix (Fin n) (Fin n) F) - 1) := by
      simp [Matrix.mul_sub]
    rw [this]
    exact (Lvl.int_mul hx.1 hy').add hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨(GLint O n).inv_mem hx, ?_⟩
    have : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
        -(((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((x : Matrix (Fin n) (Fin n) F) - 1)) := by
      rw [Matrix.mul_sub, ← Units.val_mul]
      simp
    rw [this]
    exact (Lvl.int_mul hx.2 hx').neg
def boxAdd (O : Subring F) {n : ℕ} (β : Fin n → ℕ) (c : Fin n → Fin n → F) :
    AddSubgroup (Matrix (Fin n) (Fin n) F) where
  carrier := {x | x.BlockTriangular β ∧ ∀ a b, ∃ o ∈ O, x a b = c a b * o}
  zero_mem' := ⟨fun _ _ _ => rfl, fun a b => ⟨0, O.zero_mem, by simp⟩⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun i j h => by simp [hx h, hy h], fun a b => ?_⟩
    obtain ⟨o, ho, h⟩ := hx' a b
    obtain ⟨o', ho', h'⟩ := hy' a b
    exact ⟨o + o', O.add_mem ho ho', by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨fun i j h => by simp [hx h], fun a b => ?_⟩
    obtain ⟨o, ho, h⟩ := hx' a b
    exact ⟨-o, O.neg_mem ho, by simp [h]⟩
def conjSub {G : Type} [Group G] (H : Subgroup G) (d : G) : Subgroup G :=
  H.map (MulAut.conj d⁻¹).toMonoidHom
def lev (ϖ : F) (T : ℕ) {n : ℕ} (dd : Fin n → F) : Fin n → Fin n → F :=
  fun a b => ϖ ^ (2 * T) * ((dd a)⁻¹ * dd b)
end GlobalTheory.CompanionTheory.QL.QIndex


