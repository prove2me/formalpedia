-- Prove2me | Definitions.Def_ReciprocityTheory_ThetaSummability_RealCoinvariants_Numbers
-- name    : ReciprocityTheory_ThetaSummability_RealCoinvariants_Numbers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:33.612822+00:00
-- url     : https://prove2.me/theorems/4a991e6d-e820-4059-b6ad-6103dfbf42bc
-- title:
--   Numbers
-- statement:
--   Definitions and structural lemmas for Numbers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaSummability/RealCoinvariants/Numbers.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ThetaSummability.Real
structure RealData where
  a : ℕ
  a' : ℕ
  p : ℕ
  q : ℕ
  κ : ℕ
structure RealData.Hyp (D : RealData) : Prop where
  a_gt : D.a' < D.a
  a'_pos : 1 ≤ D.a'
  even_im_hermitian_sub : (D.a - D.a') % 2 = 0
  h1a : 2 * D.p + 1 ≤ D.a
  h1b : 2 * D.q + 1 ≤ D.a'
  h2 : D.a + D.a' < D.κ
  h3 : D.κ % 2 = 0
  h5 : 2 * (D.p + D.q) < D.a'
  h4 : 2 * D.p + D.a' < D.a
namespace RealData
variable (D : RealData)
def d : ℕ := D.a + D.a'
def y : ℕ := D.p + D.q
def R : ℕ := D.d - D.y
def S : ℕ := D.y
def P : ℕ := D.a - D.p
def Q : ℕ := D.p
def P' : ℕ := D.q
def Q' : ℕ := D.a' - D.q
def e : ℝ := ((D.a : ℝ) - D.a') / 2
def c₁ : ℝ := ((D.R : ℝ) - D.S) / 2
def c₂ : ℝ := ((D.P : ℝ) - D.Q) / 2
def c₂' : ℝ := ((D.P' : ℝ) - D.Q') / 2
def x₁ : ℝ := (D.κ : ℝ) / 2 - D.c₁ + D.c₂
def x₂ : ℝ := D.c₂
def y₁ : ℝ := (D.κ : ℝ) / 2 + D.c₁ - D.c₂
def y₂ : ℝ := -D.c₂
def ω : ℝ := D.x₁ - D.y₂
def ω' : ℝ := D.y₁ - D.x₂
end RealData
def exampleData : RealData := ⟨9, 5, 1, 1, 16⟩
end ReciprocityTheory.ThetaSummability.Real


