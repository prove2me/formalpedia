-- Prove2me | Definitions.Def_TransparencyTeamContracts_Submodular_Information
-- name    : TransparencyTeamContracts_Submodular_Information
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:54.762149+00:00
-- url     : https://prove2.me/theorems/d3240af0-8656-48a7-936a-f7a8aa0d0575
-- title:
--   Public signaling, favorable contract schemes, and disclosure benchmarks
-- statement:
--   Let $\Omega=[m]$ be the finite state set and $D\in\Delta(\Omega)$ its prior, with zero coordinates allowed. For a belief $\mu$, put
--   $$f_\mu(S)=\sum_{\omega}\mu_\omega f_\omega(S),\quad U_P^N(D)=V(f_D,c),\quad U_P^F(D)=\sum_\omega D_\omega V(f_\omega,c).$$
--   A public scheme has an arbitrary compact Borel signal space, a joint probability law of state and signal with state marginal $D$, and a measurable Bayes posterior. It also has a measurable signal-dependent contract in the full share cube and a measurable effort team which is a principal-favorable pure equilibrium almost everywhere under the signal marginal. Its ex ante payoff is the expectation of $(1-\sum_i\alpha_i(\sigma)) f_\omega(S(\sigma))$. The joint optimum is
--   $$\operatorname{OPT}(D)=\sup\{\mathbb E[U_P(S(\sigma),\alpha(\sigma),\omega)]:\text{admissible public schemes}\}.$$
--   The posterior is specified by the published integral form of Bayes' rule, without dividing by zero prior or signal probabilities. Signals may have arbitrary support. The joint-law representation describes the same state-conditional public signaling problem: condition the joint law on each positive-prior state; on a zero-prior state the kernel is arbitrary. Integrability is explicit and follows from measurable bounded payoffs on a probability space. This operational definition avoids replacing the joint problem by an unproved posterior-value formula.
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), §2, printed pp.5–8 (PDF pp.7–10); §3 disclosure benchmarks, printed p.8 (PDF p.10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1292.pdf; PDF SHA-256 0aa8b61daf25346bcfca67a178c55762d05abe3f79b2b66a6d2ad6dfed9b3321

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Game
import Definitions.Def_RiskPersuasion_Convex_Signaling

open Finset MeasureTheory

namespace TransparencyTeamContracts.Submodular

/-- The finite-state probability simplex, including zero coordinates. -/
abbrev Belief (m : ℕ) := RiskPersuasion.Convex.Belief (Fin m)

/-- The posterior expected technology, §2, printed p.7 (PDF 9). -/
def posteriorReward {n m : ℕ} (M : Model n m) (μ : Belief m) (S : Finset (Fin n)) : ℝ :=
  ∑ ω, (μ : Fin m → ℝ) ω * M.f ω S

/-- No-information benchmark: the stateless optimum at the prior, §3, p.8. -/
noncomputable def noInformation {n m : ℕ} (M : Model n m) (D : Belief m) : ℝ :=
  V (posteriorReward M D) M.c

/-- Full disclosure with a separate optimal contract at every state, §3, p.8. -/
noncomputable def fullInformation {n m : ℕ} (M : Model n m) (D : Belief m) : ℝ :=
  ∑ ω, (D : Fin m → ℝ) ω * V (M.f ω) M.c

/-- A joint public information-and-contract scheme, §2, printed pp.6–8 (PDF 8–10).
The joint law is equivalent to a state-conditional signaling kernel for finite states;
zero-prior states can be assigned any conditional law. The published posterior
identity encodes Bayes' rule without division. Favorable pure NE selection is explicit.
Measurable strategies and integrability express meaningful expectations, not finite support. -/
structure PublicScheme {n m : ℕ} (M : Model n m) (D : Belief m)
    (Signal : Type) [MeasurableSpace Signal] where
  joint : Measure (Fin m × Signal)
  signaling : RiskPersuasion.Convex.IsSignalingScheme (D : Fin m → ℝ) joint
  posterior : Signal → Belief m
  bayes : RiskPersuasion.Convex.IsPosterior joint (fun s => (posterior s : Fin m → ℝ))
  contract : Signal → Fin n → ℝ
  contract_bounds : ∀ s, IsContract (contract s)
  contract_measurable : ∀ i, Measurable (fun s => contract s i)
  team : Signal → Finset (Fin n)
  team_measurable : RiskPersuasion.Convex.IsMeasurableStrategy team
  favorable : ∀ᵐ s ∂(joint.map Prod.snd),
    IsBestEquilibrium (posteriorReward M (posterior s)) M.c (contract s) (team s)
  payoff_integrable : Integrable
    (fun p => principalUtility (M.f p.1) (contract p.2) (team p.2)) joint

/-- Operational ex ante payoff, §2, p.7: expectation over state and public signal. -/
noncomputable def PublicScheme.value {n m : ℕ} {M : Model n m} {D : Belief m}
    {Signal : Type} [MeasurableSpace Signal] (A : PublicScheme M D Signal) : ℝ :=
  ∫ p, principalUtility (M.f p.1) (A.contract p.2) (A.team p.2) ∂A.joint

/-- Every compact Borel public signal space is allowed. The supremum is over
joint signaling and contract schemes, not just finitely supported posterior laws. -/
def publicPayoffs {n m : ℕ} (M : Model n m) (D : Belief m) : Set ℝ :=
  {u | ∃ (Signal : Type) (t : TopologicalSpace Signal) (ms : MeasurableSpace Signal),
    @CompactSpace Signal t ∧ @BorelSpace Signal t ms ∧
    ∃ A : @PublicScheme n m M D Signal ms, u = A.value}

/-- OPT(D), §2, p.7–8. Its payoff set is nonempty and bounded above by one.
No maximizing scheme is asserted by the curated results; this least upper bound
therefore expresses the same optimal value without adding an attainment claim. -/
noncomputable def optimalInformation {n m : ℕ} (M : Model n m) (D : Belief m) : ℝ :=
  sSup (publicPayoffs M D)

end TransparencyTeamContracts.Submodular


