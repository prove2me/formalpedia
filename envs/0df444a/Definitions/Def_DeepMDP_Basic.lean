-- Prove2me | Definitions.Def_DeepMDP_Basic
-- name    : DeepMDP_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T18:26:10.949504+00:00
-- url     : https://prove2.me/theorems/f58895b4-80ba-4e09-b895-99db96e114fc
-- title:
--   DeepMDP: MDPs, value functions, latent space models, DeepMDP losses, Wasserstein and bisimulation metrics
-- statement:
--   Objects of Sections 2-6 and Appendix A of Gelada, Kumar, Buckman, Nachum and Bellemare (2019).
--
--   1. **Wasserstein metric (Definition 1).** For measures $P,Q$ on a space $X$ and a cost $d:X\times X\to[0,\infty]$, $W_d(P,Q)=\inf_{\lambda\in\Gamma(P,Q)}\int d(x,y)\,d\lambda(x,y)$, where $\Gamma(P,Q)$ is the set of couplings (measures on $X\times X$ with marginals $P$ and $Q$). On a metric space, $W=W_d$ with $d$ the metric. Values lie in $[0,\infty]$.
--   2. **MDP and value functions (Section 2.1).** An MDP $\langle X,A,r,P,\gamma\rangle$ has a finite action set $A$, Markov transition kernels $P(\cdot\mid x,a)$, bounded measurable rewards $r(x,a)$ and a discount $0\le\gamma<1$. A stationary policy is a Markov kernel $\pi(a\mid x)$. With $Q_0=0$ and $Q_{n+1}(x,a)=r(x,a)+\gamma\,\mathbb E_{y\sim P(\cdot|x,a)}\sum_{a'}\pi(a'|y)Q_n(y,a')$ (the expected discounted reward of the first $n+1$ steps), $Q^\pi=\lim_n Q_n$ and $V^\pi(x)=\sum_a\pi(a|x)Q^\pi(x,a)$. A policy is optimal if $V^{\pi'}\le V^{\pi}$ pointwise for every policy $\pi'$, and $V^*(x)=\sup_\pi V^\pi(x)$. The policy's reward and transition functions are $r_\pi(x)=\sum_a\pi(a|x)r(x,a)$ and $P_\pi(\cdot|x)=\sum_a\pi(a|x)P(\cdot|x,a)$.
--   3. **Lipschitz notions (Definitions 2-3).** On a metric state space, $\pi$ is $K$-Lipschitz-valued if $V^\pi$ and every $Q^\pi(\cdot,a)$ are $K$-Lipschitz. The MDP is $(K_R,K_P)$-Lipschitz if every $r(\cdot,a)$ is $K_R$-Lipschitz and $W(P(\cdot|x_1,a),P(\cdot|x_2,a))\le K_P\,d(x_1,x_2)$.
--   4. **Latent space model (Section 2.2).** $M=\langle S,A,R,P,\gamma\rangle$ has a countable discrete state space $S$; the DeepMDP $\bar M=\langle\bar S,A,\bar R,\bar P,\gamma\rangle$ has a metric state space $\bar S$ with its Borel $\sigma$-algebra; $\phi:S\to\bar S$ is the embedding. A latent policy $\bar\pi$ acts on $M$ by $\bar\pi(\cdot|s)=\bar\pi(\cdot|\phi(s))$, and $\phi P(\cdot|s,a)$ is the law of $\phi(s')$, $s'\sim P(\cdot|s,a)$.
--   5. **DeepMDP losses (eqs. (4)-(7)).** Global: $L^\infty_{\bar R}=\sup_{s,a}|R(s,a)-\bar R(\phi(s),a)|$ and $L^\infty_{\bar P}=\sup_{s,a}W(\phi P(\cdot|s,a),\bar P(\cdot|\phi(s),a))$. Local to a state-action distribution $\xi$: $L^\xi_{\bar R}=\mathbb E_{(s,a)\sim\xi}|R(s,a)-\bar R(\phi(s),a)|$ and $L^\xi_{\bar P}=\mathbb E_{(s,a)\sim\xi}W(\phi P(\cdot|s,a),\bar P(\cdot|\phi(s),a))$. All take values in $[0,\infty]$.
--   6. **Stationary distributions (Section 2.1).** $\xi$ is a stationary distribution of $\pi$ in $M$ if it is a probability on $S$ with $\xi(s)=\sum_{\dot s,\dot a}P(s|\dot s,\dot a)\pi(\dot a|\dot s)\xi(\dot s)$; the state-action distribution is $\xi_\pi(s,a)=\xi(s)\pi(a|s)$.
--   7. **Bisimulation metric (Definition 5).** For rewards $r$ and transitions $T$, $d_0=0$ and $d_{n+1}(x,y)=\max_a\big[(1-\gamma)|r(x,a)-r(y,a)|+\gamma W_{d_n}(T(\cdot|x,a),T(\cdot|y,a))\big]$; the bisimulation metric is $\tilde d=\sup_n d_n=\lim_n d_n$. The joined MDP of $M$ and $\bar M$ (Lemma 5) has state space $S\sqcup\bar S$, each state moving and being rewarded according to its own MDP.
--   8. **Norm-MMD (Definitions 6-7).** A function seminorm $\|\cdot\|_D$ on real functions may take the value $+\infty$. The MMD of a class $F$ is $D(P,Q)=\sup_{f\in F}|\mathbb E_Pf-\mathbb E_Qf|$ over the $f\in F$ integrable under $P$ and $Q$; the Norm-MMD uses $F=\{f:\|f\|_D\le1\}$. A policy is $K$-smooth-valued if $\|\bar V^{\bar\pi}\|_D\le K$ and $\|\bar Q^{\bar\pi}(\cdot,a)\|_D\le K$ for all $a$. The global Norm-MMD transition loss is $\sup_{s,a}D(\phi P(\cdot|s,a),\bar P(\cdot|\phi(s),a))$.
--
--   **Formalization Note** The value functions are the limits of the finite-horizon expected discounted rewards, which is the paper's infinite sum of expected rewards. The bisimulation metric is the limit of the iterates of $F$ from $0$, which the proof of Lemma 4 uses; under the paper's assumptions this is the unique fixed point of Definition 5. Losses, Wasserstein distances and bisimulation distances are $[0,\infty]$-valued, so an infinite loss is represented as such.
-- source:
--   Gelada, Kumar, Buckman, Nachum and Bellemare, DeepMDP: Learning Continuous Latent Space Models for Representation Learning, arXiv:1906.02736v1 (ICML 2019), Sections 2.1-2.4 (Definitions 1-3), Sections 3-4 (eqs. (4)-(7)), Section 5.2 (Definition 5), Section 6 (Definitions 6-7), Appendix A.4 (Lemma 5)

import Mathlib

/-!
Gelada, Kumar, Buckman, Nachum and Bellemare, *DeepMDP: Learning Continuous Latent Space Models
for Representation Learning*, arXiv:1906.02736v1 (ICML 2019): Markov decision processes and their
value functions (Section 2.1), latent space models and the DeepMDP losses (Section 2.2, eqs. (1)-(2);
Section 3, eqs. (4)-(5); Section 4, eqs. (6)-(7)), the Wasserstein metric (Section 2.3,
Definition 1), Lipschitz-valued policies and Lipschitz DeepMDPs (Section 2.4, Definitions 2-3),
bisimulation metrics (Section 5.2, Definition 5, and the joined MDP of Lemma 5 in Appendix A.4) and
Norm-MMD metrics with smooth-valued policies (Section 6, Definitions 6-7).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace DeepMDP

section General

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Fintype A]

/-- Definition 1 (Section 2.3, p. 3): `c` is a coupling of `P` and `Q`, i.e. a measure on `X × X`
whose marginals are `P` and `Q`; the set of these is `Γ(P,Q)`. -/
def IsCoupling (P Q : Measure X) (c : Measure (X × X)) : Prop :=
  c.map Prod.fst = P ∧ c.map Prod.snd = Q

/-- Definition 1 (Section 2.3, p. 3) for an arbitrary cost `d`:
`W_d(P,Q) = inf_{λ ∈ Γ(P,Q)} ∫ d(x,y) dλ(x,y)`. Section 5.2 (p. 6) uses it for pseudometrics `d`. -/
def transportCost (d : X → X → ℝ≥0∞) (P Q : Measure X) : ℝ≥0∞ :=
  ⨅ (c : Measure (X × X)) (_ : IsCoupling P Q c), ∫⁻ z, d z.1 z.2 ∂c

/-- Definition 1 (Section 2.3, p. 3): the Wasserstein-1 metric `W(P,Q)` on a metric space, whose
cost is the metric itself. -/
def wasserstein [PseudoEMetricSpace X] (P Q : Measure X) : ℝ≥0∞ :=
  transportCost (fun x y => edist x y) P Q

/-- Section 2.1 (p. 2): the standing conventions of an MDP `⟨X, A, r, P, γ⟩` with a finite action
set: a discount `0 ≤ γ < 1`, Markov transition kernels `P(·|x,a)`, and bounded measurable
rewards `r(x,a)`. -/
def IsMDP (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ) : Prop :=
  (0 ≤ γ ∧ γ < 1) ∧ (∀ a, IsMarkovKernel (P a)) ∧ (∀ a, Measurable fun x => r x a) ∧
    ∃ C : ℝ, ∀ x a, |r x a| ≤ C

/-- Section 2.1 (p. 2): the expected discounted reward of the first `n` steps of a stationary
policy `π(a|x)`, started in state `x` with first action `a`:
`Q_0 = 0`, `Q_{n+1}(x,a) = r(x,a) + γ E_{y ∼ P(·|x,a)} ∑_{a'} π(a'|y) Q_n(y,a')`. -/
def evalIter (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ) (π : Kernel X A) :
    ℕ → X → A → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun x a =>
      r x a + γ * ∫ y, ∑ a', (π y {a'}).toReal * evalIter r P γ π n y a' ∂(P a x)

/-- Section 2.1 (p. 2): the action value function
`Q^π(x,a) = E[∑_{t≥0} γ^t r(x_t,a_t) | x_0 = x, a_0 = a]`, the limit of the expected discounted
rewards of the first `n` steps. -/
def qValue (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ) (π : Kernel X A) (x : X) (a : A) : ℝ :=
  limUnder atTop fun n => evalIter r P γ π n x a

/-- Section 2.1 (p. 2): the value function `V^π(x) = E[∑_{t≥0} γ^t r(x_t,a_t) | x_0 = x]`,
`a_t ∼ π(·|x_t)`, i.e. `V^π(x) = ∑_a π(a|x) Q^π(x,a)`. -/
def vValue (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ) (π : Kernel X A) (x : X) : ℝ :=
  ∑ a, (π x {a}).toReal * qValue r P γ π x a

/-- Section 2.1 (p. 2): `π` is an optimal policy, a stationary policy which maximizes the expected
future reward from every state. -/
def IsOptimalPolicy (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ) (π : Kernel X A) : Prop :=
  IsMarkovKernel π ∧
    ∀ π' : Kernel X A, IsMarkovKernel π' → ∀ x, vValue r P γ π' x ≤ vValue r P γ π x

/-- Section 2.1 (p. 2): the optimal value function `V^*(x)`, the largest value `V^π(x)` over all
stationary policies `π ∈ Π`. -/
def optValue (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ) (x : X) : ℝ :=
  ⨆ π : {π : Kernel X A // IsMarkovKernel π}, vValue r P γ π.1 x

/-- Section 2.1 (p. 2) and Section 2.4 (p. 4): the reward function of a policy,
`r_π(x) = ∑_a r(x,a) π(a|x)`. -/
def policyReward (r : X → A → ℝ) (π : Kernel X A) (x : X) : ℝ :=
  ∑ a, (π x {a}).toReal * r x a

/-- Section 2.1 (p. 2) and Section 2.4 (p. 4): the transition function of a policy,
`P_π(·|x) = ∑_a P(·|x,a) π(a|x)`. -/
def policyTrans (P : A → Kernel X X) (π : Kernel X A) (x : X) : Measure X :=
  ∑ a, π x {a} • P a x

/-- Definition 2 (Section 2.4, p. 3): the policy `π` is `K`-Lipschitz-valued:
`|V^π(x₁) - V^π(x₂)| ≤ K d(x₁,x₂)` and `|Q^π(x₁,a) - Q^π(x₂,a)| ≤ K d(x₁,x₂)` for every action `a`. -/
def IsLipschitzValued [PseudoEMetricSpace X] (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ)
    (π : Kernel X A) (K : ℝ≥0) : Prop :=
  LipschitzWith K (vValue r P γ π) ∧ ∀ a, LipschitzWith K fun x => qValue r P γ π x a

/-- Definition 3 (Section 2.4, p. 3): the MDP is `(K_R, K_P)`-Lipschitz:
`|r(x₁,a) - r(x₂,a)| ≤ K_R d(x₁,x₂)` and `W(P(·|x₁,a), P(·|x₂,a)) ≤ K_P d(x₁,x₂)`. -/
def IsLipschitzMDP [PseudoEMetricSpace X] (r : X → A → ℝ) (P : A → Kernel X X) (KR KP : ℝ≥0) :
    Prop :=
  ∀ a, LipschitzWith KR (fun x => r x a) ∧
    ∀ x y, wasserstein (P a x) (P a y) ≤ (KP : ℝ≥0∞) * edist x y

/-- Definition 5 (Section 5.2, p. 6): the iterates `d_0 = 0`, `d_{n+1} = F(d_n)` of the operator
`F_d(x,y) = max_a (1-γ)|r(x,a) - r(y,a)| + γ W_d(T(·|x,a), T(·|y,a))`. -/
def bisimIter (r : X → A → ℝ) (T : X → A → Measure X) (γ : ℝ) : ℕ → X → X → ℝ≥0∞
  | 0 => fun _ _ => 0
  | n + 1 => fun x y => ⨆ a, (ENNReal.ofReal ((1 - γ) * |r x a - r y a|) +
      ENNReal.ofReal γ * transportCost (bisimIter r T γ n) (T x a) (T y a))

/-- Definition 5 (Section 5.2, p. 6): the bisimulation metric `d̃`, the fixed point of `F`, obtained
as the limit of the nondecreasing iterates `d_n` started from `d_0 = 0` (as in the proof of Lemma 4,
Appendix A.4). -/
def bisimMetric (r : X → A → ℝ) (T : X → A → Measure X) (γ : ℝ) (x y : X) : ℝ≥0∞ :=
  ⨆ n, bisimIter r T γ n x y

/-- Section 6.1 (p. 7): a function seminorm `‖·‖_D` on real functions on `X`, allowed to take the
value `+∞` (as the Lipschitz seminorm does on non-Lipschitz functions). -/
structure FunSeminorm (X : Type*) where
  /-- The value `‖f‖_D`. -/
  toFun : (X → ℝ) → ℝ≥0∞
  /-- Absolute homogeneity `‖c f‖_D = |c| ‖f‖_D`. -/
  map_smul' : ∀ (c : ℝ) (f : X → ℝ), toFun (c • f) = ENNReal.ofReal |c| * toFun f
  /-- Triangle inequality `‖f + g‖_D ≤ ‖f‖_D + ‖g‖_D`. -/
  add_le' : ∀ f g : X → ℝ, toFun (f + g) ≤ toFun f + toFun g

/-- Definition 6 (Section 6.1, p. 7): the Maximum Mean Discrepancy generated by a class `F`,
`D(P,Q) = sup_{f ∈ F} |E_{x∼P} f(x) - E_{y∼Q} f(y)|`, over the members of `F` for which both
expectations exist. -/
def mmd (F : Set (X → ℝ)) (P Q : Measure X) : ℝ≥0∞ :=
  ⨆ (f : X → ℝ) (_ : f ∈ F ∧ Integrable f P ∧ Integrable f Q),
    ENNReal.ofReal |∫ x, f x ∂P - ∫ x, f x ∂Q|

/-- Section 6.1 (p. 7): the Norm-MMD metric of a function seminorm, generated by the class
`F_D = {f : ‖f‖_D ≤ 1}`. -/
def normMMD (sn : FunSeminorm X) (P Q : Measure X) : ℝ≥0∞ :=
  mmd {f | sn.toFun f ≤ 1} P Q

/-- Definition 7 (Section 6.2, p. 8): the policy `π` is `K`-smooth-valued for the Norm-MMD with
seminorm `‖·‖_D`: `‖V^π‖_D ≤ K` and `‖Q^π(·,a)‖_D ≤ K` for every action `a`. -/
def IsSmoothValued (sn : FunSeminorm X) (r : X → A → ℝ) (P : A → Kernel X X) (γ : ℝ)
    (π : Kernel X A) (K : ℝ≥0) : Prop :=
  sn.toFun (vValue r P γ π) ≤ K ∧ ∀ a, sn.toFun (fun x => qValue r P γ π x a) ≤ K

end General

section Latent

variable {S Sb A : Type*} [MeasurableSpace S] [MeasurableSpace Sb] [MeasurableSpace A] [Fintype A]

/-- Section 2.2 (p. 2): a policy `π̄` on the latent space, run on `M` through the embedding:
`π̄(·|s) := π̄(·|φ(s))`. -/
def liftPolicy [DiscreteMeasurableSpace S] (πb : Kernel Sb A) (φ : S → Sb) : Kernel S A :=
  πb.comap φ Measurable.of_discrete

/-- Section 2.2 (p. 2): `φP(·|s,a)`, the law of `φ(s')` for `s' ∼ P(·|s,a)`. -/
def embedTrans (P : A → Kernel S S) (φ : S → Sb) (s : S) (a : A) : Measure Sb :=
  (P a s).map φ

/-- Section 3, eq. (4) (p. 4): the global reward loss
`L^∞_R̄ = sup_{s,a} |R(s,a) - R̄(φ(s),a)|`. -/
def rewardLossGlobal (R : S → A → ℝ) (Rb : Sb → A → ℝ) (φ : S → Sb) : ℝ≥0∞ :=
  ⨆ s, ⨆ a, ENNReal.ofReal |R s a - Rb (φ s) a|

/-- Section 3, eq. (5) (p. 4): the global transition loss
`L^∞_P̄ = sup_{s,a} W(φP(·|s,a), P̄(·|φ(s),a))`. -/
def transLossGlobal [PseudoEMetricSpace Sb] (P : A → Kernel S S) (Pb : A → Kernel Sb Sb)
    (φ : S → Sb) : ℝ≥0∞ :=
  ⨆ s, ⨆ a, wasserstein (embedTrans P φ s a) (Pb a (φ s))

/-- Section 6.3 (p. 8) and Lemma 7 (Appendix A.6): the global transition loss with a Norm-MMD `D`,
`L^∞_P̄ = sup_{s,a} D(φP(·|s,a), P̄(·|φ(s),a))`. -/
def transLossGlobalMMD (sn : FunSeminorm Sb) (P : A → Kernel S S) (Pb : A → Kernel Sb Sb)
    (φ : S → Sb) : ℝ≥0∞ :=
  ⨆ s, ⨆ a, normMMD sn (embedTrans P φ s a) (Pb a (φ s))

/-- Section 4, eq. (6) (p. 5): the reward loss local to a state-action distribution `ξ`,
`L^ξ_R̄ = E_{(s,a)∼ξ} |R(s,a) - R̄(φ(s),a)|`. -/
def rewardLossLocal (ξ : Measure (S × A)) (R : S → A → ℝ) (Rb : Sb → A → ℝ) (φ : S → Sb) :
    ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal |R z.1 z.2 - Rb (φ z.1) z.2| ∂ξ

/-- Section 4, eq. (7) (p. 5): the transition loss local to a state-action distribution `ξ`,
`L^ξ_P̄ = E_{(s,a)∼ξ} W(φP(·|s,a), P̄(·|φ(s),a))`. -/
def transLossLocal [PseudoEMetricSpace Sb] (ξ : Measure (S × A)) (P : A → Kernel S S)
    (Pb : A → Kernel Sb Sb) (φ : S → Sb) : ℝ≥0∞ :=
  ∫⁻ z, wasserstein (embedTrans P φ z.1 z.2) (Pb z.2 (φ z.1)) ∂ξ

/-- Section 2.1 (p. 2): `ξ` is a stationary distribution of the policy `π` in `M`:
`ξ(s) = ∑_{ṡ,ȧ} P(s|ṡ,ȧ) π(ȧ|ṡ) ξ(ṡ)`. -/
def IsStationary (P : A → Kernel S S) (π : Kernel S A) (ξ : Measure S) : Prop :=
  IsProbabilityMeasure ξ ∧ ∀ s, ξ {s} = ∫⁻ s', ∑ a', π s' {a'} * P a' s' {s} ∂ξ

/-- Section 2.1 (p. 2): the state-action distribution `ξ_π(s,a) = ξ(s) π(a|s)`. -/
def stateActionDist (ξ : Measure S) (π : Kernel S A) : Measure (S × A) :=
  ξ.compProd π

/-- Lemma 5 (Appendix A.4, p. 19): reward of the MDP joining `M` and `M̄` on `S ⊕ S̄`. -/
def joinReward (R : S → A → ℝ) (Rb : Sb → A → ℝ) : S ⊕ Sb → A → ℝ
  | .inl s, a => R s a
  | .inr x, a => Rb x a

/-- Lemma 5 (Appendix A.4, p. 19): transition of the MDP joining `M` and `M̄` on `S ⊕ S̄`; each
state transitions according to the transition function of its own MDP. -/
def joinTrans (P : A → Kernel S S) (Pb : A → Kernel Sb Sb) : S ⊕ Sb → A → Measure (S ⊕ Sb)
  | .inl s, a => (P a s).map Sum.inl
  | .inr x, a => (Pb a x).map Sum.inr

end Latent

end DeepMDP


