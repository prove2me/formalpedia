-- Prove2me | Definitions.Def_MBRLGuarantees_Basic
-- name    : MBRLGuarantees_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T11:25:03.009319+00:00
-- url     : https://prove2.me/theorems/8160179d-dd75-4a96-a463-c6f0ae8a034e
-- title:
--   Model-based RL: values, discounted state distributions, model discrepancy and policy distances
-- statement:
--   Objects of Sections 2-4 and Appendices A, D.1 and E of Luo, Xu, Li, Tian, Darrell and Ma (arXiv:1807.03858v5).
--
--   1. **Markov decision process.** States lie in a measurable space $\mathcal S$ and actions in a measurable space $\mathcal A$. A policy $\pi(\cdot\mid s)$ is a Markov kernel from $\mathcal S$ to $\mathcal A$, and a dynamical model $M(\cdot\mid s,a)$ is a Markov kernel from $\mathcal S\times\mathcal A$ to $\mathcal S$; a deterministic model $M(s,a)$ is the kernel $\delta_{M(s,a)}$. The reward $R(s,a)$ is known, $\gamma$ is the discount factor, $S_0\sim\mu_0$, and $\kappa=\gamma(1-\gamma)^{-1}$.
--   2. **Transition kernels.** $P_{\pi,M}(\cdot\mid s)=\int M(\cdot\mid s,a)\,\pi(da\mid s)$ is the state-to-state kernel of $\pi$ on $M$, and $P^t$ is its $t$-step kernel ($P^0=\mathrm{Id}$).
--   3. **Values (eq. 2.1).** $V^{\pi,M}(s)=\sum_{t\ge0}\gamma^t\,\mathbb E[R(S_t,A_t)\mid S_0=s]$ with $A_t\sim\pi(\cdot\mid S_t)$, $S_{t+1}\sim M(\cdot\mid S_t,A_t)$, and $V^{\pi,M}=\mathbb E_{S_0\sim\mu_0}V^{\pi,M}(S_0)$.
--   4. **Discounted state distributions.** For a kernel $P$ and a distribution $\mu$, $\bar G\mu=(1-\gamma)\sum_{t\ge0}\gamma^tP^t\mu$. $\rho^{\pi,M}=\bar G\mu_0$ for $P=P_{\pi,M}$ (Definition 2.1), and $\beta^{\pi}=(1-\gamma)^2\sum_{t\ge1}t\gamma^{t-1}P^t\mu_0$ (Definition A.1); the paper writes $\rho^\pi,\beta^\pi$ for the true model $M^\star$.
--   5. **Model discrepancy (eq. 4.5).** $G^{\pi,\widehat M}(s,a)=\mathbb E_{\hat s'\sim\widehat M(\cdot\mid s,a)}V^{\pi,\widehat M}(\hat s')-\mathbb E_{s'\sim M(\cdot\mid s,a)}V^{\pi,\widehat M}(s')$ against a reference model $M$ ($M=M^\star$ in Section 4.2), and $G^{\pi,\widehat M}(s)=\mathbb E_{A\sim\pi(\cdot\mid s)}G^{\pi,\widehat M}(s,A)$.
--   6. **Discrepancy bounds.** $\varepsilon_1=\mathbb E_{S\sim\rho^{\pi_{\mathrm{ref}}}}|G^{\pi,\widehat M}(S)|$, $\varepsilon_{\max}=\sup_S|G^{\pi,\widehat M}(S)|$, $\varepsilon_2=\mathbb E_{S\sim\beta^{\pi_{\mathrm{ref}}}}G^{\pi,\widehat M}(S)^2$, and $D^G_{\pi_{\mathrm{ref}},\delta}(\widehat M,\pi)=\kappa\varepsilon_1+\kappa^2\delta\varepsilon_{\max}$ (eq. 4.7).
--   7. **Divergences.** $\mathrm{KL}$ is the Kullback-Leibler divergence. $\chi^2(p,q)=\int(p-q)^2/q$ is the Neyman $\chi^2$ distance (Definition E.1), equal to $+\infty$ unless $p\ll q$, and $\chi^2_\mu(P',P)=\int\chi^2(P'(\cdot\mid x),P(\cdot\mid x))\,\mu(dx)$ (Definition E.3). $|\rho-\rho'|_1=\sup\{\int f\,d\rho-\int f\,d\rho' : f \text{ measurable}, |f|\le1\}$.
--   8. **Policy distances.** $d^{\mathrm{KL}}(\pi,\pi_{\mathrm{ref}})=\mathbb E_{S\sim\rho^\pi}\big[\mathrm{KL}(\pi(\cdot\mid S),\pi_{\mathrm{ref}}(\cdot\mid S))^{1/2}\big]$ (eq. 4.3) and $d^{\chi^2}(\pi,\pi_{\mathrm{ref}})=\max\{\mathbb E_{S\sim\rho^{\pi_{\mathrm{ref}}}}\chi^2(\pi(\cdot\mid S),\pi_{\mathrm{ref}}(\cdot\mid S)),\ \mathbb E_{S\sim\beta^{\pi_{\mathrm{ref}}}}\chi^2(\pi(\cdot\mid S),\pi_{\mathrm{ref}}(\cdot\mid S))\}$ (eq. A.1).
--
--   **Formalization Note** The value function is written as the discounted sum of the expected rewards at each step, computed from the $t$-step kernels; for a bounded measurable reward this equals the paper's expectation of the discounted sum over trajectories. Divergences, $|\cdot|_1$ and the policy distances take values in $[0,\infty]$. $\varepsilon_1$ and $\varepsilon_2$ use $G^{\pi,\widehat M}(S)$, as in the proofs of Propositions 4.4 and A.2.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Section 2 (eq. (2.1), Definition 2.1), Section 4 (eqs. (4.3), (4.5), (4.7)), Appendix A (Definition A.1, eqs. (A.1)-(A.2)), Appendix D.1, Appendix E (Definitions E.1, E.3)

import Mathlib

/-!
Luo, Xu, Li, Tian, Darrell and Ma, *Algorithmic Framework for Model-based Deep Reinforcement
Learning with Theoretical Guarantees*, arXiv:1807.03858v5 (ICLR 2019): the value functions,
discounted state distributions, model discrepancy `G`, discrepancy bounds and policy distances of
Sections 2-4, Appendix A, Appendix D.1 and Appendix E.

States and actions live in arbitrary measurable spaces `S`, `A`. A policy `π(· | s)` is a kernel
`Kernel S A` and a dynamical model `M(· | s, a)` is a kernel `Kernel (S × A) S`; statements assume
them to be Markov kernels. The reward `R : S × A → ℝ` is known.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

namespace MBRLGuarantees

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- Section 2: `κ = γ (1 - γ)⁻¹`, the constant the paper fixes "throughout the paper". -/
def kappa (γ : ℝ) : ℝ := γ / (1 - γ)

/-- Section 2: the state-to-state transition kernel of a policy `π` on a model `M`,
`s ↦ ∫ M(· | s, a) π(da | s)`, the law of `S_{t+1}` given `S_t = s`
(Appendix D.1 calls it "the transition kernel induced by some policy `π`"). -/
def stateKernel (pi : Kernel S A) (M : Kernel (S × A) S) : Kernel S S :=
  Kernel.snd (pi ⊗ₖ M)

/-- The `t`-step kernel `P^t` of a transition kernel `P` on the state space (`P^0 = Id`);
`P^t(· | s)` is the law of `S_t` given `S_0 = s` (Section 2, Appendix D.1). -/
def iterKernel (P : Kernel S S) : ℕ → Kernel S S
  | 0 => Kernel.id
  | n + 1 => P ∘ₖ iterKernel P n

/-- Appendix D.1: `Ḡμ = (1 - γ) ∑_{t ≥ 0} γ^t P^t μ`, the discounted distribution of the states
visited by the Markov chain with transition kernel `P` started from the distribution `μ`. -/
def discOcc (γ : ℝ) (P : Kernel S S) (μ : Measure S) : Measure S :=
  ENNReal.ofReal (1 - γ) • Measure.sum fun t : ℕ => ENNReal.ofReal (γ ^ t) • μ.bind (iterKernel P t)

/-- Definition A.1 (written for a general chain): `(1 - γ)² ∑_{t ≥ 1} t γ^{t-1} P^t μ`. -/
def reweightedOcc (γ : ℝ) (P : Kernel S S) (μ : Measure S) : Measure S :=
  ENNReal.ofReal ((1 - γ) ^ 2) • Measure.sum fun t : ℕ =>
    ENNReal.ofReal (((t : ℝ) + 1) * γ ^ t) • μ.bind (iterKernel P (t + 1))

/-- Section 2: the expected one-step reward `E_{a ∼ π(·|s)} R(s, a)` of policy `π` at state `s`. -/
def expReward (R : S × A → ℝ) (pi : Kernel S A) (s : S) : ℝ :=
  ∫ a, R (s, a) ∂(pi s)

/-- Section 2, eq. (2.1): the value function
`V^{π,M}(s) = E[∑_{t ≥ 0} γ^t R(S_t, A_t) | S_0 = s]` with `A_t ∼ π(· | S_t)` and
`S_{t+1} ∼ M(· | S_t, A_t)`, written as `∑_t γ^t E[R(S_t, A_t) | S_0 = s]`. -/
def stateValue (γ : ℝ) (R : S × A → ℝ) (pi : Kernel S A) (M : Kernel (S × A) S) (s : S) : ℝ :=
  ∑' t : ℕ, γ ^ t * ∫ s', expReward R pi s' ∂(iterKernel (stateKernel pi M) t s)

/-- Section 2: `V^{π,M} = E[V^{π,M}(S_0)]`, the expected reward-to-go averaged over the initial
state `S_0 ∼ μ₀`. -/
def value (γ : ℝ) (R : S × A → ℝ) (μ₀ : Measure S) (pi : Kernel S A) (M : Kernel (S × A) S) : ℝ :=
  ∫ s, stateValue γ R pi M s ∂μ₀

/-- Definition 2.1: `ρ^{π,M} = (1 - γ) ∑_{t ≥ 0} γ^t p_{S_t^{π,M}}`, the discounted distribution
of the states visited by `π` on `M` from `S_0 ∼ μ₀`; `ρ^π` is `ρ^{π,M⋆}`. -/
def occ (γ : ℝ) (μ₀ : Measure S) (pi : Kernel S A) (M : Kernel (S × A) S) : Measure S :=
  discOcc γ (stateKernel pi M) μ₀

/-- Definition A.1: `β^{π} = (1 - γ)² ∑_{t ≥ 1} t γ^{t-1} p_{S_t^π}`, the re-weighted discounted
state distribution of `π` on the model `M` (the paper takes `M = M⋆`). -/
def beta (γ : ℝ) (μ₀ : Measure S) (pi : Kernel S A) (M : Kernel (S × A) S) : Measure S :=
  reweightedOcc γ (stateKernel pi M) μ₀

/-- Section 4.1, eq. (4.5): `G^{π,M̂}(s, a) = E_{ŝ' ∼ M̂(·|s,a)} V^{π,M̂}(ŝ') - E_{s' ∼ M(·|s,a)} V^{π,M̂}(s')`,
the one-step discrepancy of the model `M̂` against the reference model `M` (the paper's `M = M⋆`;
Lemma 4.3 uses a general `M`). -/
def gapFn (γ : ℝ) (R : S × A → ℝ) (pi : Kernel S A) (Mhat M : Kernel (S × A) S) (s : S) (a : A) :
    ℝ :=
  (∫ s', stateValue γ R pi Mhat s' ∂(Mhat (s, a))) - ∫ s', stateValue γ R pi Mhat s' ∂(M (s, a))

/-- Section 4.2: `G^{π,M̂}(s) = E_{A ∼ π(·|s)} G^{π,M̂}(s, A)`. -/
def gapState (γ : ℝ) (R : S × A → ℝ) (pi : Kernel S A) (Mhat M : Kernel (S × A) S) (s : S) : ℝ :=
  ∫ a, gapFn γ R pi Mhat M s a ∂(pi s)

/-- Section 4.2, display before eq. (4.7): `ε₁ = E_{S ∼ ρ^{π_ref}} |G^{π,M̂}(S)|` (the form used in the proof of
Proposition 4.4, Appendix C.1). -/
def epsOne (γ : ℝ) (R : S × A → ℝ) (μ₀ : Measure S) (Mstar : Kernel (S × A) S)
    (piref pi : Kernel S A) (Mhat : Kernel (S × A) S) : ℝ :=
  ∫ s, |gapState γ R pi Mhat Mstar s| ∂(occ γ μ₀ piref Mstar)

/-- Section 4.2, display before eq. (4.7): `ε_max = max_S |G^{π,M̂}(S)|`. -/
def epsMax (γ : ℝ) (R : S × A → ℝ) (Mstar : Kernel (S × A) S) (pi : Kernel S A)
    (Mhat : Kernel (S × A) S) : ℝ :=
  ⨆ s, |gapState γ R pi Mhat Mstar s|

/-- Appendix A, after eq. (A.2): `ε₂ = E_{S ∼ β^{π_ref}} [G^{π,M̂}(S)²]` (the form used in the
proof of Proposition A.2, Appendix C.2). -/
def epsTwo (γ : ℝ) (R : S × A → ℝ) (μ₀ : Measure S) (Mstar : Kernel (S × A) S)
    (piref pi : Kernel S A) (Mhat : Kernel (S × A) S) : ℝ :=
  ∫ s, gapState γ R pi Mhat Mstar s ^ 2 ∂(beta γ μ₀ piref Mstar)

/-- Section 4.2, eq. (4.7): `D^G_{π_ref,δ}(M̂, π) = κ ε₁ + κ² δ ε_max`. -/
def discG (γ : ℝ) (R : S × A → ℝ) (μ₀ : Measure S) (Mstar : Kernel (S × A) S) (δ : ℝ)
    (piref : Kernel S A) (Mhat : Kernel (S × A) S) (pi : Kernel S A) : ℝ :=
  kappa γ * epsOne γ R μ₀ Mstar piref pi Mhat + kappa γ ^ 2 * δ * epsMax γ R Mstar pi Mhat

/-- Section 4.1, eq. (4.3): `d^{KL}(π, π_ref) = E_{S ∼ ρ^π} [KL(π(·|S), π_ref(·|S))^{1/2}]`,
with `ρ^π` the discounted state distribution of `π` on the true model `M⋆`. -/
def dKL (γ : ℝ) (μ₀ : Measure S) (Mstar : Kernel (S × A) S) (pi piref : Kernel S A) : ℝ≥0∞ :=
  ∫⁻ s, klDiv (pi s) (piref s) ^ (1 / 2 : ℝ) ∂(occ γ μ₀ pi Mstar)

open Classical in
/-- Definition E.1: the Neyman `χ²` distance `χ²(p, q) = ∫ (p(x) - q(x))² / q(x) dx`, equal to
`∫ (dp/dq - 1)² dq` when `p ≪ q` and to `+∞` otherwise. -/
def chiSq {X : Type*} [MeasurableSpace X] (p q : Measure X) : ℝ≥0∞ :=
  if p ≪ q then ∫⁻ x, ENNReal.ofReal (((p.rnDeriv q x).toReal - 1) ^ 2) ∂q else ∞

/-- Definition E.3: `χ²_μ(P', P) = ∫ μ(x) χ²(P'(·|x), P(·|x)) dx`, the `χ²` distance between two
transition kernels measured with respect to the distribution `μ`. -/
def chiSqTrans {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (P' P : Kernel X Y) : ℝ≥0∞ :=
  ∫⁻ x, chiSq (P' x) (P x) ∂μ

/-- Appendix A, eq. (A.1): `d^{χ²}(π, π_ref) = max { E_{S ∼ ρ^{π_ref}} χ²(π(·|S), π_ref(·|S)),
E_{S ∼ β^{π_ref}} χ²(π(·|S), π_ref(·|S)) }`, with `ρ^{π_ref}`, `β^{π_ref}` taken on `M⋆`. -/
def dChi (γ : ℝ) (μ₀ : Measure S) (Mstar : Kernel (S × A) S) (pi piref : Kernel S A) : ℝ≥0∞ :=
  max (chiSqTrans (occ γ μ₀ piref Mstar) pi piref) (chiSqTrans (beta γ μ₀ piref Mstar) pi piref)

/-- The `ℓ₁` distance `|ρ - ρ'|₁` between two finite measures (Appendix C.3, Claim E.6,
Corollary E.7), in its dual form `sup { ∫ f dρ - ∫ f dρ' : f measurable, |f| ≤ 1 }`. -/
def lOneDist {X : Type*} [MeasurableSpace X] (ρ ρ' : Measure X) : ℝ≥0∞ :=
  ⨆ (f : X → ℝ) (_ : Measurable f) (_ : ∀ x, |f x| ≤ 1),
    ENNReal.ofReal ((∫ x, f x ∂ρ) - ∫ x, f x ∂ρ')

end MBRLGuarantees


