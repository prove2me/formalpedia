-- Prove2me | Definitions.Def_ManyServerFluid_Equilibrium_Renewal
-- name    : ManyServerFluid_Equilibrium_Renewal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:59.882818+00:00
-- url     : https://prove2.me/theorems/4a8a18fb-8f03-43af-b7db-6a25cfbf2e06
-- title:
--   Section 6 objects: the renewal measure U = Σ_{n≥0} G^{*n}, τ_1 of (6.1), Z of (6.5), the relation (6.6), monotone weak convergence
-- statement:
--   These are the objects of Section 6 of Kaspi and Ramanan, built on the fluid model (service law $G$ with density $g$, $M$, $\bar\nu_*$).
--
--   1. **Renewal measure.** With $G^{*0}=\delta_0$ and $G^{*(n+1)}=G^{*n}*G$, the renewal measure associated with $G$ is
--   $$U=\sum_{n=0}^{\infty}G^{*n},$$
--   and $U(t)=U([0,t])$ is the renewal function. The term $n=0$ is the unit mass at $0$, so $U(t)\ge1$ for $t\ge0$.
--   2. **First hitting time of full occupancy (6.1).** For a locally integrable arrival rate $\bar\lambda$,
--   $$\tau_1=\inf\Big\{t>0:\int_0^t(1-G(t-s))\,\bar\lambda(s)\,ds=1\Big\}\in[0,\infty],$$
--   with the usual convention $\inf\emptyset=\infty$.
--   3. **The function $Z$ (6.5).** For $\pi_0\in\mathcal M_{\le1}[0,M)$ and $t\ge0$,
--   $$Z(t)=\int_{[0,t]}\Big(\int_{[0,M)}\frac{G(x+t-s)-G(x)}{1-G(x)}\,\pi_0(dx)\Big)dU(s).$$
--   4. **The relation (6.6).** A family $\{\pi_t\}$ of finite measures satisfies (6.6) if for every bounded continuous $f$ and every $t\ge0$,
--   $$\langle f,\pi_t\rangle=\int_{[0,M)}f(x+t)\frac{1-G(x+t)}{1-G(x)}\,\pi_0(dx)+\int_{[0,t]}f(t-s)\big(1-G(t-s)\big)\,dZ(s).$$
--   5. **Monotone weak convergence (p. 47).** A family $\{\mu_t\}_{t\ge0}$ of finite nonnegative measures converges weakly, as $t\to\infty$, monotonically up to a finite nonnegative measure $\mu$ if for every nonnegative bounded continuous $f$, $t\mapsto\langle f,\mu_t\rangle$ is nondecreasing and tends to $\langle f,\mu\rangle$.
--
--   $U$ enters the representation (4.6) of the entry process $\bar K$ and the estimate of Lemma 6.3; $Z$ and $\{\pi_t\}$ are the reference system of Lemma 6.2 with which the proof of Theorem 3.9(2) compares the fluid solution.
--
--   **Formalization Note** The service distribution is the measure $g(x)\,dx$; the convolution powers are the published `QueueingFundamentals.MG1.convPow` (Mathlib's additive convolution, with $G^{*0}=\delta_0$). $\tau_1$ is an extended real, the infimum of the image of the set in $\overline{\mathbb R}$, so $\inf\emptyset=+\infty$ as on p. 106. $Z$ is a Bochner integral against $U$ restricted to $[0,t]$ (the integrand is bounded by $\langle\mathbf 1,\pi_0\rangle$ and $U$ is finite on bounded sets). $dZ$ is the Lebesgue–Stieltjes measure of the model file. "Increases" in the definition of monotone weak convergence is read as nondecreasing on $[0,\infty)$. Test functions are bounded continuous functions on $\mathbb R$; since all measures involved are carried by $[0,M)$, this gives the same notion as test functions in $\mathcal C_b[0,M)$ or $\mathcal C_b(\mathbb R_+)$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 47 (monotone weak convergence), p. 52 (renewal measure dU in Corollary 4.4), p. 105 (6.1), pp. 107–108 (6.5), (6.6)

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_ManyServerFluid_Equilibrium_Model

namespace ManyServerFluid.Equilibrium

open MeasureTheory Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

namespace ServiceLaw
variable (S : ServiceLaw)

/-- The service distribution as a measure on ℝ: dG = g(x) dx. -/
noncomputable def serviceMeasure : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (S.g x)

/-- The renewal measure U = Σ_{n ≥ 0} G^{*n} associated with the distribution G (p. 52, p. 107;
Asmussen [1], Chapter V), **δ_0 included**: the n = 0 term is the unit mass at 0, so
U([0, t]) ≥ 1. The convolution powers are the published `QueueingFundamentals.MG1.convPow`
(G^{*0} = δ_0, G^{*(n+1)} = G^{*n} ∗ G). -/
noncomputable def renewalMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ => QueueingFundamentals.MG1.convPow S.serviceMeasure n

/-- (6.1) τ_1 = inf{t > 0 : ∫_0^t (1 − G(t − s)) λ̄(s) ds = 1} in [0, ∞], with inf ∅ = ∞
(p. 106: "the usual convention that inf ∅ = ∞"). -/
noncomputable def tau1 (lam : ℝ → ℝ) : EReal :=
  sInf (((↑) : ℝ → EReal) '' {t : ℝ | 0 < t ∧ ∫ s in Icc 0 t, (1 - S.G (t - s)) * lam s = 1})

/-- (6.5) Z(t) = ∫_[0,t] (∫_[0,M) (G(x + t − s) − G(x))/(1 − G(x)) π_0(dx)) dU(s). -/
noncomputable def Zfun (pi0 : FiniteMeasure ℝ) (t : ℝ) : ℝ :=
  ∫ s in Icc 0 t,
    (∫ x, (S.G (x + t - s) - S.G x) / (1 - S.G x) ∂(pi0 : Measure ℝ)) ∂S.renewalMeasure

/-- (6.6): the family {π_t} satisfies, for every bounded continuous f and t ≥ 0,
⟨f, π_t⟩ = ∫_[0,M) f(x + t) (1 − G(x + t))/(1 − G(x)) π_0(dx) + ∫_[0,t] f(t − s)(1 − G(t − s)) dZ(s),
with Z = `Zfun pi0` of (6.5) and dZ its Lebesgue–Stieltjes measure. -/
def SatisfiesEq66 (pi0 : FiniteMeasure ℝ) (piMeas : ℝ → FiniteMeasure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, ∀ t, 0 ≤ t →
    ∫ x, f x ∂(piMeas t : Measure ℝ) =
      ∫ x, f (x + t) * ((1 - S.G (x + t)) / (1 - S.G x)) ∂(pi0 : Measure ℝ)
      + ∫ s in Icc 0 t, f (t - s) * (1 - S.G (t - s)) ∂(ManyServerFluid.Uniqueness.stieltjes (S.Zfun pi0))

end ServiceLaw

/-- Monotone weak convergence (p. 47): the family {μ_t} converges weakly, as t → ∞,
monotonically up to μ iff for every nonnegative bounded continuous f, t ↦ ⟨f, μ_t⟩ is
nondecreasing on [0, ∞) ("increases") and tends to ⟨f, μ⟩. -/
def MonoWeakUpTo (μt : ℝ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, 0 ≤ f →
    MonotoneOn (fun t => ∫ x, f x ∂(μt t)) (Ici 0) ∧
    Tendsto (fun t => ∫ x, f x ∂(μt t)) atTop (𝓝 (∫ x, f x ∂μ))

end ManyServerFluid.Equilibrium


