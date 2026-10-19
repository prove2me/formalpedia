-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
-- name    : OAI_Combinatorics_HoneycombCorridor_RaySeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T11:24:51.625631+00:00
-- url     : https://prove2.me/theorems/4d961dc8-228c-4826-84de-0141266ff1c5
-- title:
--   Positive and phased word masses and the ray contraction constant
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Word masses.** For a finite set $S$ of words, the positive mass is $\sum_{w\in S}\lambda^{|w|}$ and the phased mass is $\sum_{w\in S}\mathrm{wordWeight}(w)$.
--   2. **Phases.** $\mathrm{phase}(a)=e^{ia}$ has modulus one, and $|\mathrm{wordWeight}(w)|=\lambda^{|w|}$, so the phased mass is bounded by the positive mass.
--   3. **Ray contraction.** The constant
--   $$
--   \rho=\frac1{1+\cos(3\pi/8)\sin(\pi/8)}\in(0,1)
--   $$
--   is the factor by which the positive mass of walks contracts each time they must cross a further separating ray; it drives the exponential decay of lateral masses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/RaySeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/RaySeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def positiveWordMass (S : Finset (List Bool)) : ℝ :=
  ∑ w ∈ S, criticalActivity ^ w.length
noncomputable def phasedWordMass (S : Finset (List Bool)) : ℂ :=
  ∑ w ∈ S, wordWeight w
noncomputable def phase (a : ℝ) : ℂ := Complex.exp ((a : ℂ) * Complex.I)

@[simp] theorem phase_norm (a : ℝ) : ‖phase a‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I a

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] theorem wordWeight_norm (w : List Bool) :
    ‖wordWeight w‖ = criticalActivity ^ w.length := by
  rw [wordWeight_turnUnits,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos criticalActivity_pos]

noncomputable def rayContraction : ℝ :=
  (1 + Real.cos (3*Real.pi/8) * Real.sin (Real.pi/8))⁻¹

end PolynomialVacuumBridge.Corridor

end

end OAI


