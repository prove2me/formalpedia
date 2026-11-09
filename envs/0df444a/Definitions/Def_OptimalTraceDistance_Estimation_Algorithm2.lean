-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2
-- name    : OptimalTraceDistance_Estimation_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:42:42.319228+00:00
-- url     : https://prove2.me/theorems/6d51a39c-a31f-464f-8150-c8856730d02c
-- title:
--   Fixed construction parameters and the two-stage estimator
-- statement:
--   This module fixes universal construction choices $A=2^{30}$ and $C_0=2^{40}$. The former exceeds the explicit coarse and fine dyadic error requirements on p.27; the latter exceeds the scalar bias and tomography threshold requirements on pp.12,21. The sample-rate multiplier $C$ and dimension threshold remain theorem witnesses, not numerical choices.
--
--   For the bounded-dimension branch the per-state budget is $\lceil C_0d^2/\varepsilon^2\rceil$. Otherwise the two budgets are $m_0=\lceil C_0d\log^2d\rceil$ and $n=\lceil CR(d,\varepsilon)\rceil$. The projector is the spectral indicator of $[0,1/(2\log d))$ in the tomography report. The expression $f$ includes the entire correction and uses the univariate branch when $\varepsilon\log d\le1$. The computed event weights integrate the clipped fresh spectral outcome over the Keyl tomography report law; the bounded branch uses independent tomography of both inputs. Measurability and realization by a lawful POVM are stated separately, so the computed expression is not assumed to be a probability law.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Algorithm 2 and §5, pp.11–12,21; construction estimates pp.25–27.

import Definitions.Def_OptimalTraceDistance_Estimation_Fourier
import Definitions.Def_QAlgorithms_Defs_KeylTomography

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal
noncomputable section

namespace OptimalTraceDistance.Estimation

/-- A fixed choice sufficient for the explicit dyadic bias estimates on p.27:
2^16·8/A ≤ 1/4, and the fine-scale geometric sum is absorbed by the same A. -/
def constructionA : ℝ := 2^30
/-- One fixed construction constant: 32/C₀ ≤ 1/8, 256/C₀ ≤ 1/8;
4d/m tomography and the threshold 1/(4 log d) require C₀ ≥ 256. -/
def constructionC₀ : ℝ := 2^40

def F (d : ℕ) (ε : ℝ) : TraceExpression d := multiscale constructionA d ε
def f (d : ℕ) (ε : ℝ) (Q : Mat d) : TraceExpression d :=
  estimatorExpression constructionA constructionC₀ d ε Q

def tomographyCount (d : ℕ) : ℕ := ⌈constructionC₀*d*(Real.log d)^2⌉₊
def boundedCount (d : ℕ) (ε : ℝ) : ℕ := ⌈constructionC₀*(d : ℝ)^2/ε^2⌉₊
def freshCount (C : ℝ) (d : ℕ) (ε : ℝ) : ℕ := ⌈C * rate d ε⌉₊
def algorithmCost (C : ℝ) (d₀ d : ℕ) (ε : ℝ) : ℕ :=
  if d < d₀ then boundedCount d ε else tomographyCount d + freshCount C d ε

def reportProjector (d : ℕ) (report : Mat d) : Mat d :=
  cfc (fun x : ℝ => if 0 ≤ x ∧ x < 1/(2*Real.log d) then (1 : ℝ) else 0) report

def clip (x : ℝ) : ℝ := min 1 (max 0 x)

/-- The exact computed Keyl report law; output matrices have their ambient Borel σ-algebra.
The physical POVM and risk bound remain the existing Open reference. -/
def tomographyLaw {d : ℕ} (m : ℕ) (ρ : Mat d) (hρ : Density ρ) : Measure (Mat d) :=
  if h : 0 < d ∧ 0 < m then
    Measure.map (fun o : QAlgorithms.Schur.Partition d m × Matrix.unitaryGroup (Fin d) ℂ =>
      QAlgorithms.Schur.estimate h.1 h.2 o.1 o.2)
      (QAlgorithms.Tomography.keylJointLaw h.1 h.2 ρ hρ)
  else 0

/-- Event weights of the two-stage algorithm, with an independent fresh spectral batch.
A realization/measurement theorem must establish lawfulness; no measurability or accuracy
certificate is placed in this definition. The source goal only asserts existence of a POVM. -/
def algorithm2Weight {d : ℕ} (C : ℝ) (d₀ : ℕ) (ε : ℝ)
    (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) (B : Set ℝ) : ℝ≥0∞ :=
  if d < d₀ then
    ∫⁻ a : Mat d, ∫⁻ b : Mat d, if distance a b ∈ B then 1 else 0
      ∂tomographyLaw (boundedCount d ε) σ hσ
      ∂tomographyLaw (boundedCount d ε) ρ hρ
  else
    let n := freshCount C d ε
    let mixture := plus ρ σ
    -- S₊ is a density matrix by the structural convex-combination identity.
    if hm : Density mixture then
      ∫⁻ report, spectralLaw (observable (f d ε (reportProjector d report)) n)
          (powerState (labelledState ρ σ) n) (clip ⁻¹' B)
        ∂tomographyLaw (tomographyCount d) mixture hm
    else 0

end OptimalTraceDistance.Estimation


