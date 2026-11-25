-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:59.714734+00:00
-- url     : https://prove2.me/theorems/fc0c8049-fe46-4d73-addb-59dd3c943c83
-- title:
--   Real Covolume
-- statement:
--   Definitions and structural lemmas for Real Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/RealCovolume.lean

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
open MeasureTheory
open scoped Matrix
namespace Formalism.L2.SG.Pf.RealCovolume
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def reCo : (ι → κ → ℂ) ≃ₗ[ℝ] (ι × κ × Fin 2 → ℝ) where
  toFun a p := if p.2.2 = 0 then (a p.1 p.2.1).re else (a p.1 p.2.1).im
  invFun x i c := ⟨x (i, c, 0), x (i, c, 1)⟩
  map_add' a b := by funext p; by_cases h : p.2.2 = 0 <;> simp [h]
  map_smul' r a := by funext p; by_cases h : p.2.2 = 0 <;> simp [h]
  left_inv a := by funext i c; apply Complex.ext <;> simp
  right_inv x := by
    funext p
    obtain ⟨i, c, t⟩ := p
    fin_cases t <;> simp
def bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ) := (Pi.basisFun ℝ (ι × κ × Fin 2)).map reCo.symm
def Qf (g : κ → ℝ) (a b : ι → κ → ℂ) : ℝ := ∑ i, ∑ c, (a i c * star (b i c)).re * g c
def boxC : Set ℂ := {z | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1}
end Formalism.L2.SG.Pf.RealCovolume


