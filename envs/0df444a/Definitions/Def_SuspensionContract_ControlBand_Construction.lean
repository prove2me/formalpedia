-- Prove2me | Definitions.Def_SuspensionContract_ControlBand_Construction
-- name    : SuspensionContract_ControlBand_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:20.50165+00:00
-- url     : https://prove2.me/theorems/2d623930-b855-4aba-96c9-3ac3e51cf2de
-- title:
--   EC.3.9, pp. ec34–ec39 — the construction of Proposition 6: w̃(θ̲), C(θ̲) (Lemmas EC.4, EC.8), θ̲⁰ (EC.5, EC.9), θ̲̆, θ̄(θ̲) (EC.74) and ψ(θ̲) (EC.75)
-- statement:
--   The proof of Proposition 6 constructs the parameters in four steps; this file defines the objects of those steps.
--
--   1. For $\underline\theta$, a pair $(\tilde w,C)$ is **matching** at $\underline\theta$ if $\tilde w\in(\underline\theta,\bar w)$ and value matching and smooth pasting hold there: $\mathcal V_{\tilde w}(\underline\theta)=V_C(\underline\theta)$ and $\mathcal V_{\tilde w}'(\underline\theta)=V_C'(\underline\theta)$. The functions $\tilde w(\underline\theta)$, $C(\underline\theta)$ are a matching pair when one exists (Lemmas EC.4, EC.8 assert it exists and is unique).
--   2. $\underline\theta^0=\inf\{\underline\theta\in(0,\bar w):\tilde w'(\underline\theta)\ge0\}$ (Lemma EC.5, Condition 1 case) and, under Condition 2, $\underline\theta^0=\inf\{\underline\theta\in(\breve{\underline\theta},\bar w):\tilde w'(\underline\theta)\ge0\}$ (Lemma EC.9), where
--   $$\breve{\underline\theta}=\frac{(\bar V-\underline v)(\rho-r-\mu)-(\rho-r)\bar w}{\mu(\rho/r-1)}.$$
--   3. The upper threshold (EC.74)
--   $$\bar\theta(\underline\theta)=\inf\{w>\underline\theta:\mathcal V_{\tilde w(\underline\theta)}'(w)\le1+C(\underline\theta)\tfrac r\rho w^{r/\rho-1}\}.$$
--   4. The gap function (EC.75)
--   $$\psi(\underline\theta)=\mathcal V_{\tilde w(\underline\theta)}(\bar\theta(\underline\theta))-\big[\underline v+\bar\theta(\underline\theta)+C(\underline\theta)\,\bar\theta(\underline\theta)^{r/\rho}\big].$$
--
--   The parameters of Proposition 6 are $\hat{\mathbf w}=\tilde w(\underline\vartheta)$, $\mathsf c=C(\underline\vartheta)$, $\bar\vartheta=\bar\theta(\underline\vartheta)$ for the root $\underline\vartheta$ of $\psi=K$.
--
--   **Formalization Note.** $\tilde w$, $C$ are chosen with `Classical.choose` and are junk $(0,0)$ when no matching pair exists. In the definitions of $\underline\theta^0$ only points where $\tilde w$ has a derivative are counted. Lemma EC.9 prints $\tilde w'(\underline\theta^0)\ge0$ inside the set; it is read as $\tilde w'(\underline\theta)\ge0$, as in Lemma EC.5. Infima of empty sets take Lean's junk value $0$; the paper's Lemmas EC.5, EC.6, EC.9, EC.10 assert they are well defined.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, EC.3.9, pp. ec34–ec39, Lemmas EC.4, EC.5, (EC.74), (EC.75), EC.3.9.2 (p. ec38), Lemmas EC.8, EC.9

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_DelayODE

namespace SuspensionContract.ControlBand

namespace Params

variable (P : Params)

/-- Step 1 of EC.3.9 (Lemmas EC.4, EC.8, pp. ec34, ec38): the pairs `(w̃, C)` with `w̃ ∈ (θ̲, w̄)`
satisfying value matching (42) and smooth pasting (43) at `ϑ̲ = θ̲`:
`𝒱_w̃(θ̲) = V_C(θ̲)` and `𝒱′_w̃(θ̲) = V′_C(θ̲)`. -/
def MatchPair (θ : ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 ∈ Set.Ioo θ P.wbar ∧ P.calV p.1 θ = P.Vc p.2 θ ∧ d1 (P.calV p.1) θ = deriv (P.Vc p.2) θ

open Classical in
/-- The chosen pair `(w̃(θ̲), C(θ̲))` (unique by Lemmas EC.4, EC.8), junk `(0, 0)` if none exists. -/
noncomputable def matchPair (θ : ℝ) : ℝ × ℝ :=
  if h : ∃ p, P.MatchPair θ p then Classical.choose h else (0, 0)

/-- `w̃(θ̲)` of Lemmas EC.4/EC.8. -/
noncomputable def wtil (θ : ℝ) : ℝ := (P.matchPair θ).1

/-- `C(θ̲)` of Lemmas EC.4/EC.8. -/
noncomputable def Cof (θ : ℝ) : ℝ := (P.matchPair θ).2

/-- `θ̲⁰ := inf {θ̲ ∈ (0, w̄) | w̃′(θ̲) ≥ 0}` (Lemma EC.5, p. ec35; Condition 1 case). Points where
`w̃` is not differentiable are not counted. -/
noncomputable def theta0 : ℝ :=
  sInf {θ | θ ∈ Set.Ioo 0 P.wbar ∧ ∃ d, HasDerivAt P.wtil d θ ∧ 0 ≤ d}

/-- `θ̲̆ := ((V̄ − v̲)(ρ − r − µ) − (ρ − r)w̄)/(µ(ρ/r − 1))` (EC.3.9.2, p. ec38). -/
noncomputable def thetaBreve : ℝ :=
  ((P.Vbar - P.vlow) * (P.ρ - P.r - P.μ) - (P.ρ - P.r) * P.wbar) / (P.μ * (P.ρ / P.r - 1))

/-- `θ̲⁰ := inf {θ̲ ∈ (θ̲̆, w̄) | w̃′(θ̲) ≥ 0}` (Lemma EC.9, p. ec39; Condition 2 case; the printed
`w̃′(θ̲⁰)` inside the set is read as `w̃′(θ̲)`). -/
noncomputable def theta0C2 : ℝ :=
  sInf {θ | θ ∈ Set.Ioo P.thetaBreve P.wbar ∧ ∃ d, HasDerivAt P.wtil d θ ∧ 0 ≤ d}

/-- `θ̄(θ̲) := inf {w > θ̲ | 𝒱′_{w̃(θ̲)}(w) ≤ 1 + C(θ̲)(r/ρ)w^{r/ρ−1}}` (EC.74), p. ec36. -/
noncomputable def thetaBar (θ : ℝ) : ℝ :=
  sInf {w | θ < w ∧
    d1 (P.calV (P.wtil θ)) w ≤ 1 + P.Cof θ * (P.r / P.ρ) * w ^ (P.r / P.ρ - 1)}

/-- `ψ(θ̲) := 𝒱_{w̃(θ̲)}(θ̄(θ̲)) − [v̲ + θ̄(θ̲) + C(θ̲)(θ̄(θ̲))^{r/ρ}]` (EC.75), p. ec37. -/
noncomputable def psi (θ : ℝ) : ℝ :=
  P.calV (P.wtil θ) (P.thetaBar θ)
    - (P.vlow + P.thetaBar θ + P.Cof θ * P.thetaBar θ ^ (P.r / P.ρ))

end Params

end SuspensionContract.ControlBand


