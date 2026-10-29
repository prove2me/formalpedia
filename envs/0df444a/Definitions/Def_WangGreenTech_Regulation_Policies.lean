-- Prove2me | Definitions.Def_WangGreenTech_Regulation_Policies
-- name    : WangGreenTech_Regulation_Policies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:57.588738+00:00
-- url     : https://prove2.me/theorems/b8c1e1cb-c2c7-4e64-9a4a-7acde58f669f
-- title:
--   Leader interim utilities, development sets, and specified-belief equilibrium
-- statement:
--   Let $p=(\epsilon,b,q,r,f_1,f_L,f_H,m_L,m_H)$ satisfy $\epsilon>0$, $b\ge0$, $0\le q<1$, $r>0$, $f_1,f_L>0$, $f_H\ge f_L$, and $m_L\le m_H\le0$. Signals and the common fundamental are real. Conditional on signal $x$, the specified posterior is uniform on $[x-\epsilon,x+\epsilon]$. Followers form a unit-mass population on $[0,1)$; the leader has zero population mass. Both choose action 1 at indifference.
--
--   The prescribed endogenous adoption threshold is $t=b/2+f_L-f_H+\frac r{r+1}(1-q)(f_H-m_L)$, with aggregate $A_t(\theta)=\min\{1,\max\{0,(\theta+\epsilon-t)/(2\epsilon)\}\}$. Define
--   $$U_D(\lambda,x)=\frac1{2\epsilon}\int_{x-\epsilon}^{x+\epsilon}\left[\lambda-f_1+m_L+\theta-bA_t(\theta)+(q+(1-q)A_t(\theta)^r)(m_H-m_L)\right]d\theta.$$
--   The development set is $D_\lambda=\{x:U_D(\lambda,x)\ge0\}$ and $x_{\rm aggr}^{(1)}(\lambda)=\inf D_\lambda$.
--
--   For a fixed regulation probability $0<\widehat q<1$, put $\widehat t=b/2+f_L-(1-\widehat q)m_L-\widehat q f_H$ and
--   $$U_F(\lambda,x)=\lambda-f_1+m_L+\widehat q(m_H-m_L)+x-\frac b{2\epsilon}\int_{x-\epsilon}^{x+\epsilon}A_{\widehat t}(\theta)\,d\theta.$$
--   Set $\widehat D_\lambda=\{x:U_F(\lambda,x)\ge0\}$ and $\widehat x^{(1)}(\lambda)=\inf\widehat D_\lambda$.
--
--   A leader strategy is a measurable binary function of its real signal. It is a best response if both action payoffs are integrable, its chosen action maximizes posterior expected payoff at every signal, and it develops at a zero gain. A specified-belief equilibrium combines this condition with adoption equilibrium for the follower profile. The endogenous and fixed decision functions develop precisely on $D_\lambda$ and $\widehat D_\lambda$, respectively.
--
--   These definitions tie the comparison to the actual payoff functions and their development regions.
--
--   **Formalization Note** Utilities are defined by integrals of the original action gains/payoffs against the normalized posterior; the displayed $U_F$ is the corresponding expanded expression. All infima are real. Nonempty, lower-bounded development sets and the switching characterization are requested in Proposition 3(a) and Lemma 2; they are not assumed in this bundle. This equilibrium uses the stipulated posterior, not a sequential Bayesian consistency assertion.
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, body pp. 12, 19, 21–25 (PDF same); Appendix A pp. 9–14 (PDF 42–47), equations (14), (19)

import Definitions.Def_WangGreenTech_Regulation_Thresholds

set_option autoImplicit false

namespace WangGreenTech.Regulation

open MeasureTheory Set
noncomputable section

def endogenousUtility (p : Model) (lam x : ℝ) : ℝ :=
  expectation p x (fun θ => leaderGain p lam θ (thresholdMass p (adoptionCutoff p) θ))

/-- The fixed-regulation model is defined with its own action payoffs and adoption cutoff. -/
def fixedUtility (p : Model) (qhat lam x : ℝ) : ℝ :=
  expectation p x (fun θ => leaderPayoff p (fun _ => qhat) lam true θ
    (thresholdMass p (fixedAdoptionCutoff p qhat) θ))

def developmentSet (p : Model) (lam : ℝ) : Set ℝ := {x | 0 ≤ endogenousUtility p lam x}

def fixedDevelopmentSet (p : Model) (qhat lam : ℝ) : Set ℝ := {x | 0 ≤ fixedUtility p qhat lam x}

/-- Lower endpoints; nonemptiness and lower boundedness are conclusions, not assumptions. -/
def developmentCutoff (p : Model) (lam : ℝ) : ℝ := sInf (developmentSet p lam)

def fixedDevelopmentCutoff (p : Model) (qhat lam : ℝ) : ℝ := sInf (fixedDevelopmentSet p qhat lam)

/-- Both leader actions are checked, with development at a tie. -/
def DevelopmentBestResponse (p : Model) (R : ℝ → ℝ) (σ : Profile)
    (lam : ℝ) (d : ℝ → Bool) : Prop :=
  Measurable d ∧
  (∀ x a, Integrable (fun θ => leaderPayoff p R lam a θ (adoptionMass p σ θ))
    (posterior p x)) ∧
  ∀ x, (∀ a : Bool,
    expectation p x (fun θ => leaderPayoff p R lam a θ (adoptionMass p σ θ)) ≤
    expectation p x (fun θ => leaderPayoff p R lam (d x) θ (adoptionMass p σ θ))) ∧
    (expectation p x (fun θ => leaderPayoff p R lam true θ (adoptionMass p σ θ)) = 0 →
      d x = true)

/-- Optimal actions under the stipulated posterior at each period, not a claim of
Bayesian consistency after observing the public development action. -/
def SpecifiedBeliefEquilibrium (p : Model) (R : ℝ → ℝ) (lam : ℝ)
    (σ : Profile) (d : ℝ → Bool) : Prop :=
  AdoptionEquilibrium p R σ ∧ DevelopmentBestResponse p R σ lam d

def endogenousDecision (p : Model) (lam : ℝ) : ℝ → Bool :=
  fun x => decide (0 ≤ endogenousUtility p lam x)

def fixedDecision (p : Model) (qhat lam : ℝ) : ℝ → Bool :=
  fun x => decide (0 ≤ fixedUtility p qhat lam x)

end
end WangGreenTech.Regulation


