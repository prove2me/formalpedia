-- Prove2me | Definitions.Def_WalkTreeCluster_TrialDecision
-- name    : WalkTreeCluster_TrialDecision
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:42:02.589513+00:00
-- url     : https://prove2.me/theorems/0a7558d1-2a98-4325-8ad6-251ef663d879
-- title:
--   One uncapped trial of Cluster (Algorithm 7, lines 8–18)
-- statement:
--   Fix the values returned by the calls to ComputeCorrelation in one depth-$h$ trial of Cluster$(u,v)$: for each stage $i$, the norm estimates $\langle F_i\mathbb 1_z,F_i\mathbb 1_z\rangle_{w,h}$ for $z\in\{u,v\}$ (line 9) and the three fresh estimates $\langle F_i\mathbb 1_u,F_i\mathbb 1_u\rangle_{w,h}$, $\langle F_i\mathbb 1_v,F_i\mathbb 1_v\rangle_{w,h}$, $\langle F_i\mathbb 1_u,F_i\mathbb 1_v\rangle_{w,h}$ (lines 11–13). The trial scans $i=1,\dots,h$ for the first stage $j$ at which the norm condition (120)
--   $$\alpha^i\max_{z\in\{u,v\}}\langle F_i\mathbb 1_z,F_i\mathbb 1_z\rangle_{w,h}\ge\frac{a^{10}}{4\alpha}$$
--   holds, and there sets $A_r=\textit{same}$ if
--   $$\langle F_j\mathbb 1_u,F_j\mathbb 1_u\rangle_{w,h}+\langle F_j\mathbb 1_v,F_j\mathbb 1_v\rangle_{w,h}-2\langle F_j\mathbb 1_u,F_j\mathbb 1_v\rangle_{w,h}<\frac{a^{10}}{64\alpha^{j+1}}$$
--   and $A_r=\textit{different}$ otherwise (line 14); if no stage passes, the trial is unfinished.
--
--   **Formalization Note.** This is the trial without its work cap (line 7), as a deterministic function of its estimates; a trial that does not exceed the cap runs as this function.
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Algorithm 7, p.63; Eq. (120), p.62

import Mathlib
import Definitions.Def_WalkTreeCluster_Params

open scoped Classical

namespace WalkTreeCluster

/-!
# One uncapped trial of Cluster (Algorithm 7, lines 8–18)

Kapralov–Kochetkova, *Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027
submission (manuscript sha256 638eeef1…), Algorithm 7, p.63; the norm condition (120), p.62.

Given the values returned by the calls to ComputeCorrelation in one depth-`h` trial of
`Cluster(u, v)`, the trial is the following deterministic function of them. At stage
`i = 1, …, h` it reads `⟨F_i 1_z, F_i 1_z⟩_{w,h}` for `z ∈ {u, v}` (line 9) and tests the norm
condition (120), `α^i max_z ⟨F_i 1_z, F_i 1_z⟩_{w,h} ≥ a^{10}/(4α)` (line 10). At the first stage
`j` where it holds, it reads three fresh estimates (lines 11–13) and sets `A_r = same` iff
`⟨F_j1_u, F_j1_u⟩_{w,h} + ⟨F_j1_v, F_j1_v⟩_{w,h} − 2⟨F_j1_u, F_j1_v⟩_{w,h} < a^{10}/(64α^{j+1})`
(lines 14–15); if no stage passes, the trial is unfinished.

**Formalization Note.**
* The estimates are functions of the stage: `normEst i false`, `normEst i true` (line 9, for `u` and
  `v`), and `uuEst i`, `vvEst i`, `uvEst i` (lines 11–13). Values at stages the trial does not read
  are ignored.
* `testStage` is the stage of line 14 (`none`: unfinished); `trialOutcome` returns that stage with
  the decision `true` = same, `false` = different.
* This is the trial without its work cap (line 7): "the trial does not exceed the work cap" is the
  case in which the trial runs as this function.
-/

/-- The norm condition (120) at stage `i`. -/
def normPasses (ϵ ϕ : ℝ) (normEst : ℕ → Bool → ℝ) (i : ℕ) : Prop :=
  aParam ϵ ϕ ^ 10 / (4 * alphaParam ϵ ϕ) ≤
    alphaParam ϵ ϕ ^ i * max (normEst i false) (normEst i true)

/-- The first stage `j ∈ [1, h]` at which (120) holds (line 14 is reached there), if any. -/
noncomputable def testStage (ϵ ϕ : ℝ) (h : ℕ) (normEst : ℕ → Bool → ℝ) : Option ℕ :=
  if hne : ((Finset.Icc 1 h).filter (normPasses ϵ ϕ normEst)).Nonempty then
    some (((Finset.Icc 1 h).filter (normPasses ϵ ϕ normEst)).min' hne)
  else none

/-- The outcome of the uncapped trial: the stage `j` of line 14 and the decision of line 15
(`true` = same), or `none` (unfinished). -/
noncomputable def trialOutcome (ϵ ϕ : ℝ) (h : ℕ) (normEst : ℕ → Bool → ℝ)
    (uuEst vvEst uvEst : ℕ → ℝ) : Option (ℕ × Bool) :=
  (testStage ϵ ϕ h normEst).map (fun j =>
    (j, decide (uuEst j + vvEst j - 2 * uvEst j <
      aParam ϵ ϕ ^ 10 / (64 * alphaParam ϵ ϕ ^ (j + 1)))))

end WalkTreeCluster


