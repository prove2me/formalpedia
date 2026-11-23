-- Prove2me | Definitions.Def_SuspensionContract_HighCostC2_Supplement_Verification
-- name    : SuspensionContract_HighCostC2_Supplement_Verification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:59:30.789599+00:00
-- url     : https://prove2.me/theorems/d9e2d1e7-09f6-456a-ad85-129b9901fb8b
-- title:
--   Promise keeping, full verification pairs and all five attainment equalities
-- statement:
--   For a contract and effort process, promise keeping is the integrated stochastic equation (PK) on $(0,T]$, with predictable arrival and random-switch jump coefficients $H,H^q$. Its initialization is the conditional-expectation identity $E[W_0+\Delta L_0]=u$, interpreted in extended values when the initial transfer has infinite expectation. Jump bounds use $W_{0-}=u$ and the ordinary left limit at positive times.
--
--   A verification pair consists of continuous, concave, nondecreasing functions $V_I,V_\emptyset$ on $\mathbb R_+$ satisfying the published optimality condition:
--   $$\mathcal A_I V_I\ge0,\qquad\mathcal A_\emptyset V_\emptyset\ge0,\qquad 0\le V_I-V_\emptyset\le K,\qquad V_I(0),V_\emptyset(0)\ge\underline v.$$
--   The generator inequalities use positive utility; the remaining bounds include zero. The definition of $\phi(w,E)=V_E(w)-w$ and all five equations (EC.47)–(EC.51) are recorded separately for the attainment proposition. Drift equalities are interpreted almost everywhere in time, and jump equalities pathwise up to null sample paths. No utility conclusion is included in the equality predicate. A separate initial-switch equality is bound explicitly in the corrected Proposition EC.3, because (EC.49) is printed only at positive times while the utility charges the start at zero.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, pp.10,15–16, (PK), (5), (18)–(22); ec19–ec21, (EC.44), (EC.47)–(EC.51)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Contracts

namespace SuspensionContract.HighCostC2.Supplement

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

/-- Continuation immediately before a positive time; W_{0-}=u by the source's convention. -/
noncomputable def promisedBefore (P : Params) (G : Contract) (ν : ℝ≥0 → G.Ω → ℝ) :=
  preValue (promised P G ν) (fun _ => (agentUtility P G ν).toReal)

open Classical in
/-- The integrated PK equation on (0,T]. Initialization is handled separately: initial public
randomization satisfies E[W₀+ΔL₀]=u, not a pathwise equality W₀+ΔL₀=u (ec19, EC.44). -/
def PromiseKeeping (P : Params) (G : Contract) (ν H Hq : ℝ≥0 → G.Ω → ℝ) : Prop :=
  IsStronglyPredictable G.data.F H ∧ IsStronglyPredictable G.data.F Hq ∧
  (∀ᵐ ω ∂G.data.law ν, ∀ T : ℝ≥0,
    IntegrableOn (fun t => P.ρ * promisedBefore P G ν t ω +
      (if rateBefore ν t ω = P.μ then P.b else 0) - H t ω * rateBefore ν t ω + G.data.q t ω * Hq t ω)
      (Ioc 0 T) timeMeasure ∧
    promised P G ν T ω = promised P G ν 0 ω +
      (∫ t in Ioc 0 T, P.ρ * promisedBefore P G ν t ω +
        (if rateBefore ν t ω = P.μ then P.b else 0) - H t ω * rateBefore ν t ω + G.data.q t ω * Hq t ω
        ∂timeMeasure) - (G.data.payment ω (Ioc 0 T)).toReal +
      (∫ t in Ioc 0 T, H t ω ∂G.data.N.measure ω) -
      ∫ t in Ioc 0 T, Hq t ω ∂G.data.Q.measure ω) ∧
  (((∫ ω, promised P G ν 0 ω ∂G.data.law ν) : ℝ) : EReal) +
    ((∫⁻ ω, G.data.payment ω {0} ∂G.data.law ν) : EReal) = agentUtility P G ν

open Classical in
/-- Nonnegative jump utility as in (5), up to null sets of sample paths. -/
def JumpBounds (P : Params) (G : Contract) (ν H Hq : ℝ≥0 → G.Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂G.data.law ν, ∀ t,
    let wm : EReal := if t = 0 then agentUtility P G ν else (promisedBefore P G ν t ω : EReal);
    -wm ≤ (H t ω : EReal) ∧ (Hq t ω : EReal) ≤ wm

/-- The incentive inequality uses the predictable state, with the dt-a.e. convention of endnote 6. -/
def IncentiveInequality (P : Params) (G : Contract) (H : ℝ≥0 → G.Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂G.data.law (complying P G), ∀ᵐ t ∂timeMeasure,
    workingBefore G.data t ω → P.β ≤ H t ω

/-- Theorem 1 includes regularity of BOTH functions, beyond the bare QVI certificate. -/
def VerificationPair (P : Params) (VI V0 : ℝ → ℝ) : Prop :=
  ContinuousOn VI (Ici 0) ∧ ContinuousOn V0 (Ici 0) ∧
  ConcaveOn ℝ (Ici 0) VI ∧ ConcaveOn ℝ (Ici 0) V0 ∧
  MonotoneOn VI (Ici 0) ∧ MonotoneOn V0 (Ici 0) ∧ P.OptCond VI V0

open Classical in
/-- φ(w,E)=V_E(w)-w, EC.2.3. -/
noncomputable def phi (VI V0 : ℝ → ℝ) (w : ℝ) (e : Prop) : ℝ :=
  (if e then VI w else V0 w) - w

open Classical in
/-- The left derivative of V_E, including interior kinks, as on p.15. -/
noncomputable def stateDerivative (VI V0 : ℝ → ℝ) (w : ℝ) (e : Prop) : ℝ :=
  derivWithin (if e then VI else V0) (Iic w) w

open Classical in
/-- All five equality conditions EC.47–EC.51. Conditions at jumps are pathwise, the drift
conditions hold dt-a.e.; no terminal payoff or desired utility identity is included. -/
def AttainmentEqualities (P : Params) (G : Contract) (VI V0 : ℝ → ℝ)
    (H Hq : ℝ≥0 → G.Ω → ℝ) : Prop :=
  let ν := complying P G
  let W := promised P G ν
  let Wm := promisedBefore P G ν
  (∀ᵐ ω ∂G.data.law ν, ∀ᵐ t ∂timeMeasure,
    let e := workingBefore G.data t ω
    let w := Wm t ω
    (P.ρ * w + (if rateBefore ν t ω = P.μ then P.b else 0) - H t ω * rateBefore ν t ω - G.data.flow t ω) *
      (stateDerivative VI V0 w e - 1) - P.r * phi VI V0 w e +
      (phi VI V0 (w + H t ω) e - phi VI V0 w e) * rateBefore ν t ω =
      G.data.flow t ω - (P.R * rateBefore ν t ω -
        (if rateBefore ν t ω = P.μ then P.c - P.b else 0))) ∧
  (∀ᵐ ω ∂G.data.law ν, ∀ t : ℝ≥0, 0 < t →
    let e := workingBefore G.data t ω
    let z := Wm t ω + H t ω * G.data.N.jump t ω - Hq t ω * G.data.Q.jump t ω
    phi VI V0 (z - (G.data.payment ω {t}).toReal) e - phi VI V0 z e =
      (G.data.payment ω {t}).toReal) ∧
  (∀ᵐ ω ∂G.data.law ν, ∀ t : ℝ≥0, 0 < t →
    phi VI V0 (W t ω) (working G.data t ω) - phi VI V0 (W t ω) (workingBefore G.data t ω) =
      (if ¬workingBefore G.data t ω ∧ working G.data t ω then P.K else 0)) ∧
  (∀ᵐ ω ∂G.data.law ν, ∀ᵐ t ∂timeMeasure,
    let e := workingBefore G.data t ω
    let w := Wm t ω
    G.data.q t ω * (Hq t ω * (stateDerivative VI V0 w e - 1) +
      phi VI V0 (w - Hq t ω) e - phi VI V0 w e) = 0) ∧
  (∫ ω, phi VI V0 (W 0 ω) False ∂G.data.law ν) -
      phi VI V0 (agentUtility P G ν).toReal False =
    ∫ ω, (G.data.payment ω {0}).toReal ∂G.data.law ν


open Classical in
/-- The equality version of the time-zero switching inequality in the verification proof.
EC.49 is printed only for t>0; its time-zero counterpart is needed as an explicit repair
of Proposition EC.3 because (6) charges the initial restart as well. -/
def InitialSwitchEquality (P : Params) (G : Contract) (VI V0 : ℝ → ℝ) : Prop :=
  ∀ᵐ ω ∂G.data.law (complying P G),
    let w := promised P G (complying P G) 0 ω
    phi VI V0 w (working G.data 0 ω) - phi VI V0 w False =
      (if working G.data 0 ω then P.K else 0)

end SuspensionContract.HighCostC2.Supplement


