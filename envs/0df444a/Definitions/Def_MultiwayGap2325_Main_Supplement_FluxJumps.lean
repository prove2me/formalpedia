-- Prove2me | Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps
-- name    : MultiwayGap2325_Main_Supplement_FluxJumps
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T22:42:39.525913+00:00
-- url     : https://prove2.me/theorems/dfc5ba42-db1c-474c-b232-ba82561f93f7
-- title:
--   Selected flux jumps and real-valued cost components
-- statement:
--   For a flow instance and a realized non-opposite cut $C$, this module defines the selected flux jump on each truncated face,
--   $$
--   \Lambda_S(C)=\int_{\partial\Omega_S}\nu_{\Omega_S}(F^S_{C})\,d\sigma-\int_{\Omega_S}\operatorname{div}F^S_{C}\,dx,
--   $$
--   using the actual labels on terminal and coordinate facets. It also defines the sum $\sum_S\Lambda_S(C)$ and the real-valued interior and terminal cost components.
--
--   The coordinate-facet sum is empty on an interval, and all measures are the matched measures from the geometry module. These are definitions only: finiteness, measurability, and the inequalities involving these quantities are separate theorem obligations.
--
--   **Formalization Note** Extended nonnegative interior and terminal costs are converted to real numbers only in separate functions; the original extended cost remains unchanged.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), equation (10), p.7; boundary sign conventions (12)–(13), p.12; Definition 5.4, p.15.

import Definitions.Def_MultiwayGap2325_Main_Supplement_CrossingCost
import Definitions.Def_MultiwayGap2325_Main_Supplement_Flows

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace MultiwayGap2325.Main.Supplement

attribute [local instance] Classical.propDecidable

/-- The coordinate facets of a face, absent in dimension one. The dependent
`if` records that erasing a coordinate leaves a genuine source face. -/
def coordinateFlux {q : ℕ} (T : ℝ) (D : FlowData q) (S : Face q)
    (C : Simplex q → CutLabel q) : ℝ :=
  ∑ j ∈ S.val, if h : 2 ≤ (S.val.erase j).card then
    ∫ x, flowAt D S (ambientCut C x) x j
      ∂faceVolume T (⟨S.val.erase j, h⟩ : Face q)
  else 0

/-- Equation (10): selected outward flux through terminal and coordinate
facets, minus the selected divergence in the interior. -/
def fluxJump {q : ℕ} (T : ℝ) (D : FlowData q) (S : Face q)
    (C : Simplex q → CutLabel q) : ℝ :=
  (∑ i ∈ S.val, ∫ y, flowAt D S (ambientCut C y) y i ∂facetMeasure T S i) -
    coordinateFlux T D S C -
    ∫ x, divergenceAt D S (ambientCut C x) x ∂faceVolume T S

/-- All face flux jumps of one realization. -/
def totalFluxJump {q : ℕ} (T : ℝ) (D : FlowData q)
    (C : Simplex q → CutLabel q) : ℝ :=
  ∑ S : Face q, fluxJump T D S C

/-- Real-valued interior cost, used only after almost-sure finiteness has
been established. -/
def realFaceCost {q : ℕ} (T : ℝ) (W : Weighting q) (S : Face q)
    (C : Simplex q → CutLabel q) : ℝ :=
  (faceCost T W S C).toReal

/-- Sum of the real-valued interior costs over all faces. -/
def totalRealFaceCost {q : ℕ} (T : ℝ) (W : Weighting q)
    (C : Simplex q → CutLabel q) : ℝ :=
  ∑ S : Face q, realFaceCost T W S C

/-- Real-valued terminal cost. -/
def realTerminalCost {q : ℕ} (T : ℝ) (W : Weighting q)
    (C : Simplex q → CutLabel q) : ℝ :=
  (terminalCost T W C).toReal

end MultiwayGap2325.Main.Supplement


