-- Prove2me | Definitions.Def_WangGreenTech_Regulation_Model
-- name    : WangGreenTech_Regulation_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:39.848777+00:00
-- url     : https://prove2.me/theorems/f6d8413a-155c-4089-b567-9379f74a4040
-- title:
--   Three-period green-technology model, signals, payoffs, and adoption equilibrium
-- statement:
--   Let $p=(\epsilon,b,q,r,f_1,f_L,f_H,m_L,m_H)$ satisfy $\epsilon>0$, $b\ge0$, $0\le q<1$, $r>0$, $f_1,f_L>0$, $f_H\ge f_L$, and $m_L\le m_H\le0$. Signals and the common fundamental are real. Conditional on signal $x$, the specified posterior is uniform on $[x-\epsilon,x+\epsilon]$. Followers form a unit-mass population on $[0,1)$; the leader has zero population mass. Both choose action 1 at indifference.
--
--   The posterior measure is $(2\epsilon)^{-1}$ times Lebesgue measure restricted to $[x-\epsilon,x+\epsilon]$. Conditional signals use the same kernel centered at $\theta$; every finite collection uses its product measure. A profile $\sigma(i,x)\in\{0,1\}$ is jointly measurable. Its aggregate adoption mass integrates the conditional adoption probability over follower indices:
--   $$\alpha_\sigma(\theta)=\int_{[0,1)}\int\sigma(i,x)\,dK_\theta(x)\,di.$$
--   Regulation has probability $R(\alpha)=q+(1-q)\alpha^r$. A follower choosing 1 earns $-f_L+\theta-b\alpha+R(\alpha)m_H+(1-R(\alpha))m_L$, while action 0 earns $R(\alpha)(m_H-f_H)$. The leader choosing development earns $\lambda-f_1+\theta-b\alpha+R(\alpha)m_H+(1-R(\alpha))m_L$; declining development ends the game at payoff zero. Thus the gain functions are
--   $$g_F=\theta-b\alpha+(1-q)(f_H-m_L)\alpha^r-(1-q)(f_H-m_L)+f_H-f_L,$$
--   $$g_L=\lambda-f_1+m_L+\theta-b\alpha+R(\alpha)(m_H-m_L).$$
--   Fixed regulation replaces $R$ by the constant $\widehat q$ in the action payoffs; its follower gain is $\theta-b\alpha-f_L+(1-\widehat q)m_L+\widehat q f_H$. An adoption equilibrium compares both actions at every real signal of each follower and chooses adoption when their interim payoffs are equal; it also requires the payoff integrals to exist. Threshold profiles adopt exactly when $x\ge t$. The bundle defines $A_t(\theta)=\min\{1,\max\{0,(\theta+\epsilon-t)/(2\epsilon)\}\}$, $t=b/2+f_L-f_H+\frac r{r+1}(1-q)(f_H-m_L)$, and $\widehat t=b/2+f_L-(1-\widehat q)m_L-\widehat q f_H$.
--
--   These objects specify the three-period decision model independently of the claims about its equilibria.
--
--   **Formalization Note** Validity is a separate predicate on real primitives; no equilibrium conclusion is a structure field. Profiles extend to all real indices but are integrated and tested only on $[0,1)$. The product signal laws describe finite-dimensional conditional independence. Aggregate mass is the integral of adoption probabilities, not an asserted sample-path law of large numbers. The posterior after development is stipulated, without a claim that it updates on the leader's public action (finding F3).
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, body pp. 9–13 (PDF 9–13), equations (1)–(2); Appendix A p. 1 (PDF 34), equation (4); body p. 24, Lemma 2

import Mathlib

set_option autoImplicit false

namespace WangGreenTech.Regulation

/-- Primitives fixed before the first-mover advantage is varied. -/
structure Model where
  ε : ℝ
  b : ℝ
  q : ℝ
  r : ℝ
  f₁ : ℝ
  fL : ℝ
  fH : ℝ
  mL : ℝ
  mH : ℝ

def Model.Valid (p : Model) : Prop :=
  0 < p.ε ∧ 0 ≤ p.b ∧ 0 ≤ p.q ∧ p.q < 1 ∧ 0 < p.r ∧
  0 < p.f₁ ∧ 0 < p.fL ∧ p.fL ≤ p.fH ∧ p.mL ≤ p.mH ∧ p.mH ≤ 0

open MeasureTheory Set

noncomputable section

/-- The stipulated posterior of the common real fundamental at signal x. -/
def posterior (p : Model) (x : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * p.ε))⁻¹ • volume.restrict (Icc (x - p.ε) (x + p.ε))

/-- The conditional signal law has the same uniform kernel, centered at θ. -/
def signalLaw (p : Model) (θ : ℝ) : Measure ℝ := posterior p θ

/-- Independent noises for any finite selection of firms, including the leader. -/
def finiteSignalLaw (p : Model) (θ : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => signalLaw p θ)

def expectation (p : Model) (x : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ θ, h θ ∂posterior p x

/-- Followers occupy [0,1); real-index profiles are only evaluated there. -/
abbrev Profile := ℝ → ℝ → Bool

def Profile.Measurable (σ : Profile) : Prop :=
  _root_.Measurable (fun z : ℝ × ℝ => σ z.1 z.2)

/-- Integrating conditional adoption probabilities, not random sample-path mass. -/
def adoptionMass (p : Model) (σ : Profile) (θ : ℝ) : ℝ :=
  ∫ i in Ico (0 : ℝ) 1, ∫ x, (if σ i x then (1 : ℝ) else 0) ∂signalLaw p θ

def regulation (p : Model) (α : ℝ) : ℝ := p.q + (1 - p.q) * α ^ p.r

/-- Periods 2 and 3 combined, conditional on development in period 1. -/
def followerPayoff (p : Model) (R : ℝ → ℝ) (a : Bool) (θ α : ℝ) : ℝ :=
  if a then -p.fL + θ - p.b * α + R α * p.mH + (1 - R α) * p.mL
  else R α * (p.mH - p.fH)

/-- No development ends the game with zero payoff. -/
def leaderPayoff (p : Model) (R : ℝ → ℝ) (lam : ℝ) (a : Bool) (θ α : ℝ) : ℝ :=
  if a then lam - p.f₁ + θ - p.b * α + R α * p.mH + (1 - R α) * p.mL
  else 0

/-- Equation (1). -/
def followerGain (p : Model) (θ α : ℝ) : ℝ :=
  θ - p.b * α + (1 - p.q) * (p.fH - p.mL) * α ^ p.r -
    (1 - p.q) * (p.fH - p.mL) + p.fH - p.fL

/-- Equation (2). -/
def leaderGain (p : Model) (lam θ α : ℝ) : ℝ :=
  lam - p.f₁ + p.mL + θ - p.b * α + regulation p α * (p.mH - p.mL)

def fixedFollowerGain (p : Model) (qhat θ α : ℝ) : ℝ :=
  θ - p.b * α - p.fL + (1 - qhat) * p.mL + qhat * p.fH

def followerInterim (p : Model) (R : ℝ → ℝ) (σ : Profile) (x : ℝ) (a : Bool) : ℝ :=
  expectation p x (fun θ => followerPayoff p R a θ (adoptionMass p σ θ))

/-- Atomless best response: a unilateral action leaves the aggregate unchanged.
Both actions are compared; indifference is resolved toward adoption. -/
def AdoptionEquilibrium (p : Model) (R : ℝ → ℝ) (σ : Profile) : Prop :=
  σ.Measurable ∧
  (∀ x a, Integrable (fun θ => followerPayoff p R a θ (adoptionMass p σ θ))
    (posterior p x)) ∧
  ∀ i ∈ Ico (0 : ℝ) 1, ∀ x,
    (∀ a : Bool, followerInterim p R σ x a ≤ followerInterim p R σ x (σ i x)) ∧
    (followerInterim p R σ x false = followerInterim p R σ x true → σ i x = true)

def thresholdProfile (t : ℝ) : Profile := fun _ x => decide (t ≤ x)

/-- Appendix A, equation (4). -/
def thresholdMass (p : Model) (t θ : ℝ) : ℝ :=
  min 1 (max 0 ((θ + p.ε - t) / (2 * p.ε)))

def adoptionCutoff (p : Model) : ℝ :=
  p.b / 2 + p.fL - p.fH + p.r / (p.r + 1) * (1 - p.q) * (p.fH - p.mL)

def fixedAdoptionCutoff (p : Model) (qhat : ℝ) : ℝ :=
  p.b / 2 + p.fL - (1 - qhat) * p.mL - qhat * p.fH

end
end WangGreenTech.Regulation


