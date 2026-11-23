-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:38.936952+00:00
-- url     : https://prove2.me/theorems/cd0e61e7-10aa-4f73-abb6-dac4728dc08d
-- title:
--   Exists Torus Coordinates
-- statement:
--   Definitions and structural lemmas for Exists Torus Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsTorusCoordinates.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_conj_conj_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
namespace GlobalTheory
namespace TorusCoord
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open Classical in

def dimOf (X : Data E r) (σ : E →+* ℂ) : ℕ := if σ ∈ X.Ψ then X.p0 else r - X.p0
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.conj_mem (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {σ : E →+* ℂ} (h : σ ∉ X.Ψ) :
    ComplexEmbedding.conjugate σ ∈ X.Ψ :=
  (X.cmType _).mpr (by rwa [_root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.conj_conj_X])
def pr (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (b : Fin r) : ℂ :=
  (Real.sqrt (X.c τ) : ℂ) * hermC τ.1 X.Gm (y τ) (e τ b)
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.pr_add (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y y' : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
    (b : Fin r) : _root_.GlobalTheory.TorusCoord.pr X e (y + y') τ b = _root_.GlobalTheory.TorusCoord.pr X e y τ b + _root_.GlobalTheory.TorusCoord.pr X e y' τ b := by
  simp only [_root_.GlobalTheory.TorusCoord.pr, Pi.add_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left]
  ring
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.pr_real_smul (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (t : ℝ) (y : X.Ψ → Fin r → ℂ)
    (τ : X.Ψ) (b : Fin r) : _root_.GlobalTheory.TorusCoord.pr X e (t • y) τ b = (t : ℂ) * _root_.GlobalTheory.TorusCoord.pr X e y τ b := by
  simp only [_root_.GlobalTheory.TorusCoord.pr, Pi.smul_apply, ← Complex.coe_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left]
  ring
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.lt_pos (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {σ : E →+* ℂ} (h : σ ∈ X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X σ)) : a.1 < r := by
  have ha : a.1 < X.p0 := lt_of_lt_of_eq a.2 (if_pos h)
  have := X.p0_le
  omega
open NumberField in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.TorusCoord.lt_neg (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {σ : E →+* ℂ} (h : σ ∉ X.Ψ) (a : Fin (_root_.GlobalTheory.TorusCoord.dimOf X σ)) :
    X.p0 + a.1 < r := by
  have ha : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (if_neg h)
  have := X.p0_le
  omega
open Classical in

def coord (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) (y : X.Ψ → Fin r → ℂ)
    (i : Idx (dimOf X)) : ℂ :=
  if h : i.1 ∈ X.Ψ then pr X e y ⟨i.1, h⟩ ⟨i.2.1, lt_pos X h i.2⟩
  else - conj (pr X e y ⟨ComplexEmbedding.conjugate i.1, conj_mem X h⟩ ⟨X.p0 + i.2.1, lt_neg X h i.2⟩)
def coordMap (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) :
    (X.Ψ → Fin r → ℂ) →ₗ[ℝ] Vsp (dimOf X) where
  toFun y := WithLp.toLp 2 (coord X e y)
  map_add' y y' := by
    ext i
    simp only [PiLp.add_apply, coord]
    split_ifs
    · rw [pr_add]
    · rw [pr_add, map_add]; ring
  map_smul' t y := by
    ext i
    simp only [PiLp.smul_apply, coord, RingHom.id_apply, Complex.real_smul]
    split_ifs
    · rw [pr_real_smul]
    · rw [pr_real_smul, map_mul, Complex.conj_ofReal]; ring
end
end TorusCoord
end GlobalTheory


