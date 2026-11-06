-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
-- name    : OAI_NumberTheory_DirichletL_EisensteinTheta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:58.739665+00:00
-- url     : https://prove2.me/theorems/fc83ebff-ede7-4880-8370-0395c2352f83
-- title:
--   Eisenstein Theta
-- statement:
--   Definitions and structural lemmas for Eisenstein Theta, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EisensteinTheta.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SevenEighths.EisensteinTheta
open ThetaProduct
def normForm (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2
def shearEquiv : (ℤ × (ℤ × Fin 2)) ≃ (Fin 2 × (ℤ × ℤ)) where
  toFun n := (n.2.2, (n.1 - n.2.1, n.2.1))
  invFun p := (p.2.1 + p.2.2, (p.2.2, p.1))
  left_inv n := by simp
  right_inv p := by simp
def parityEquiv : (ℤ × ℤ) ≃ (Fin 2 × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Equiv.refl ℤ) (Int.divModEquiv 2)).trans shearEquiv
def xShift (a b L : ℝ) (e : Fin 2) : ℝ := (2 * a - b - L * e) / (2 * L)
def yShift (b L : ℝ) (e : Fin 2) : ℝ := (b + L * e) / (2 * L)
def cosetTheta (a b L t : ℝ) : ℂ :=
  ∑' n : ℤ × ℤ,
    (Real.exp (-Real.pi * normForm (a + L * n.1) (b + L * n.2) * t) : ℂ)
def parityPair (a b L : ℝ) (hL : 0 < L) (e : Fin 2) : WeakFEPair ℂ :=
  rectangularPair (xShift a b L e) (yShift b L e) (L ^ 2) (3 * L ^ 2)
    (sq_pos_of_pos hL) (mul_pos (by norm_num) (sq_pos_of_pos hL))
def cosetConstant (a b L : ℝ) (hL : 0 < L) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).f₀
def completedCoset (a b L : ℝ) (hL : 0 < L) (s : ℂ) : ℂ :=
  ∑ e : Fin 2, (parityPair a b L hL e).Λ s
end SevenEighths.EisensteinTheta
end
end OAI


