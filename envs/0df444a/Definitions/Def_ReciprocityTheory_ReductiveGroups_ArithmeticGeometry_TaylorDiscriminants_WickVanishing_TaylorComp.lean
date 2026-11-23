-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:33.731281+00:00
-- url     : https://prove2.me/theorems/3fc7c7ca-0d90-4272-82ff-2e490f76fcef
-- title:
--   Taylor Comp
-- statement:
--   Definitions and structural lemmas for Taylor Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
section Chain
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
end Chain
section Uniq
variable {σ : Type}
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
def IsTayF (Θ : W → ℂ) (w : σ → W) (F : MvPowerSeries σ ℂ) : Prop :=
  ∀ l : List σ, constantCoeff (l.foldr (fun q H => pderiv ℂ q H) F) = mD Θ 0 ((l.map w : List W) : Multiset W)
end Uniq
section Fam
variable {g : ℕ}
variable {n : ℕ}
def tayNs (Θ : (Fin n × Fin g → ℂ) → ℂ) (s : Multiset (Fin n × Fin g → ℂ)) : MvPowerSeries (Fin n × Fin g) ℂ :=
  fun k => mD Θ 0 (dirsN k + s) / fctN k
end Fam
section Main
variable {g : ℕ}
def diagCLM (c : Fin g → ℂ) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun i => c i • ContinuousLinearMap.proj i
def addCLM (g : ℕ) : (Fin 2 × Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 × Fin g => ℂ) ((0 : Fin 2), i) +
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 × Fin g => ℂ) ((1 : Fin 2), i)
end Main
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf


