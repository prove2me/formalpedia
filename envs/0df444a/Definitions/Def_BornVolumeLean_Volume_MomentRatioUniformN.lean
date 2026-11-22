-- Prove2me | Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
-- name    : BornVolumeLean_Volume_MomentRatioUniformN
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:34.225345+00:00
-- url     : https://prove2.me/theorems/fc97d302-6464-43df-8764-26d1f59b2fa0
-- title:
--   Moment Ratio Uniform N
-- statement:
--   Definitions and structural lemmas for Moment Ratio Uniform N, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentRatioUniformN.lean

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Real Set
open scoped ENNReal
namespace BornVolume
variable {M : ℕ}
noncomputable def psiMat (S : ℝ) (t : Fin M → ℝ) : Matrix (Fin (M + 1)) (Fin (M + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.lastCases
      -- last row (i = last): −S on castSucc columns, 1−∑t on the last column
      (Fin.lastCases (1 - ∑ k, t k) (fun _ => -S) j)
      -- row i = castSucc a
      (fun a => Fin.lastCases (t a) (fun b => if a = b then S else 0) j)
      i
noncomputable def PsiN (y : Fin (M + 1) → ℝ) : Fin (M + 1) → ℝ :=
  Fin.lastCases ((1 - ∑ k, y (Fin.castSucc k)) * y (Fin.last M))
    (fun k => y (Fin.castSucc k) * y (Fin.last M))
noncomputable def psiFDerivN (y : Fin (M + 1) → ℝ) : (Fin (M + 1) → ℝ) →L[ℝ] (Fin (M + 1) → ℝ) :=
  (Matrix.toLin' (psiMat (y (Fin.last M)) (fun k => y (Fin.castSucc k)))).toContinuousLinearMap
def domainN : Set (Fin (M + 1) → ℝ) :=
  {y | (∀ k, 0 < y (Fin.castSucc k)) ∧ (∑ k, y (Fin.castSucc k) < 1) ∧ 0 < y (Fin.last M)}
def posQuadrant : Set (Fin (M + 1) → ℝ) := {s | ∀ i, 0 < s i}
noncomputable def ratioN (s : Fin (M + 1) → ℝ) : Fin M → ℝ :=
  fun k => s (Fin.castSucc k) / (∑ i, s i)
def openSimplexFree : Set (Fin M → ℝ) := {t | (∀ k, 0 < t k) ∧ ∑ k, t k < 1}
noncomputable def dExp (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0)
end BornVolume


