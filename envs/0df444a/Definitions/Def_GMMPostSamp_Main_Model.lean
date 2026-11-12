-- Prove2me | Definitions.Def_GMMPostSamp_Main_Model
-- name    : GMMPostSamp_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:22:24.615045+00:00
-- url     : https://prove2.me/theorems/8b5ab89a-8ac5-44ec-a0a9-bbc605f01738
-- title:
--   Model 1 (Dirichlet–Gaussian mixture), the label and parameter posteriors, relabellings, the lifted posterior, Algorithm 1 and conditional sampling oracles
-- statement:
--   Fix $k,d,n\ge1$, $\sigma>0$ and $\alpha\in(0,\infty)^k$. A **parameter** is $\theta=(w,\mu_{[k]})$ with $w\in\mathbb R^k$ and $\mu_i\in\mathbb R^d$; $\Theta=\Delta_k\times(\mathbb R^d)^k$ with $\Delta_k=\{w\ge0,\sum_iw_i=1\}$, and $\|\theta-\theta'\|_2$ is the Euclidean norm of all $k+kd$ coordinates. Let $\varphi_\sigma(x)=(2\pi\sigma^2)^{-d/2}e^{-\|x\|_2^2/(2\sigma^2)}$, $p_\theta(x)=\sum_iw_i\varphi_\sigma(x-\mu_i)$ and $L_\theta(x_{[n]})=\prod_jp_\theta(x_j)$ (25).
--
--   **Model 1.** $w^\star\sim\mathrm{Dir}(\alpha)$ and $\mu^\star_1,\dots,\mu^\star_k$ i.i.d. $\mathcal N(0_d,\tfrac1dI_d)$, independently; given $\theta^\star=(w^\star,\mu^\star)$, the pairs $(\iota^\star_j,x_j)$ are independent with $\iota^\star_j\sim\mathrm{Cat}(w^\star)$ and $x_j\mid\iota^\star_j\sim\mathcal N(\mu^\star_{\iota^\star_j},\sigma^2I_d)$. The joint law of $(\theta^\star,\iota^\star_{[n]},x_{[n]})$ has density
--   $$\prod_{j\in[n]}w_{\iota_j}\,\varphi_\sigma(x_j-\mu_{\iota_j})$$
--   with respect to prior $\otimes$ counting $\otimes$ Lebesgue measure; its $x$-marginal is the law of the observations.
--
--   The **label posterior** (24) is defined for every $x_{[n]}$ by Bayes' rule,
--   $$\pi_x(\iota)=\frac{\int\prod_jw_{\iota_j}\varphi_\sigma(x_j-\mu_{\iota_j})\,\mathrm{prior}(d\theta)}{\sum_{\iota'}\int\prod_jw_{\iota'_j}\varphi_\sigma(x_j-\mu_{\iota'_j})\,\mathrm{prior}(d\theta)},\qquad\iota\in[k]^n,$$
--   and the **parameter posterior** (26) is $\Pi(d\theta)\propto L_\theta(x_{[n]})\,\mathrm{prior}(d\theta)$, i.e. density $\propto L_\theta(x)e^{-\frac d2\sum\|\mu_i\|^2}\prod w_i^{\alpha_i-1}$.
--
--   For $c\in S_k$, $\Phi_c(\theta)=(\{w_{c^{-1}(i)}\}_i,\{\mu_{c^{-1}(i)}\}_i)$; $\mathrm{Orb}(\theta)=\{\Phi_c(\theta)\}_c$; $B=\{\theta\in\Theta:\|\theta-\bar\theta\|_2\le3r\}$ (28). $R(\tau)$ (52) is the set of $\theta\in\Theta$ with $\min_iw_i\ge\tau$ and $\frac34I_k\preceq A^\top A\preceq\frac54I_k$, $A=[\mu_1|\cdots|\mu_k]$. The **lifted posterior** (29) on $B\times S_k$ is
--   $$\tilde\Pi_B(\theta,c)\propto L_\theta(x_{[n]})\,e^{-\frac d2\sum_i\|\mu_i\|_2^2}\prod_iw_i^{\alpha_{c(i)}-1}\,\mathbb 1_{\theta\in B},$$
--   with conditionals $\tilde\Pi_B(\theta\mid c)$ (31) and $\tilde\Pi_B(c\mid\theta)=\prod_iw_i^{\alpha_{c(i)}-1}/Z_\alpha(w)$, $Z_\alpha(w)=\sum_{c'}\prod_iw_i^{\alpha_{c'(i)}-1}$ (32). The potentials are $V(\theta)=-\log L_\theta(x)+\frac d2\sum\|\mu_i\|^2-\log Z_\alpha(w)$ (33) and $V_c(\theta)=-\log L_\theta(x)+\frac d2\sum\|\mu_i\|^2-\sum_i(\alpha_{c(i)}-1)\log w_i$ (34); their Hessians are taken along the tangent space $\mathcal T=\{(\dot w,h):\mathbf 1^\top\dot w=0\}$ (51) with its Euclidean norm.
--
--   **Algorithm 1** (LiftedGMMSampler) draws $c_0\sim\mathrm{Unif}(S_k)$ and, for $t<T$, $\theta_{t+1}\sim\tilde\Pi_B(\cdot\mid c_t)$ and $c_{t+1}\sim\tilde\Pi_B(\cdot\mid\theta_{t+1})$, returning $(\theta_T,c_T)$. **Definition 1:** kernels $(O_\theta,O_c)$ are $\xi$-conditional sampling oracles for $\tilde\Pi_B$ if $\mathrm{TV}(O_\theta,\tilde\Pi_B(\cdot\mid\theta))\le\xi$ for all $\theta\in B$ and $\mathrm{TV}(O_c,\tilde\Pi_B(\cdot\mid c))\le\xi$ for all $c$.
--
--   **Formalization Note.** Indices are `Fin k`, `Fin n` (0-based); $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`; $S_k$ is `Equiv.Perm (Fin k)` with the discrete σ-algebra. $\mathrm{Dir}(\alpha)$ is the published `PolyVoting.dirichletMeasure`. Model 1's printed "$\iota^\star_j\sim\mathrm{Cat}(w)$, $x_j\mid\iota^\star_j\sim\mathcal N(\mu_{\iota^\star_j},\sigma^2I_d)$" is read with $w^\star,\mu^\star$. Since $\mathrm{Dir}(\alpha)$ has density $\propto\prod w_i^{\alpha_i-1}$, the $c$-slice of (29) is written as $L_\theta(x)\prod_iw_i^{\alpha_{c(i)}-\alpha_i}\mathbb 1_B(\theta)\,\mathrm{prior}(d\theta)$. Normalization is $\mu\mapsto\mu(\text{univ})^{-1}\mu$. In Definition 1 the condition on $O_\theta$ is required for $\theta\in B$ with all $w_i>0$, where (32) is defined (the boundary of the simplex is $\tilde\Pi_B$-null). Algorithm 1 never sets $\theta_0$; it is taken to be $\bar\theta$, which only affects $T=0$. The Hessian quadratic form at $\theta$ in direction $v$ is $\frac{d^2}{dt^2}F(\theta+tv)|_{t=0}$.
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 9 §2.1 (Dir); p. 16 Model 1, (24); p. 17 (25)–(27); p. 18 Φ_c, Orb, (28); pp. 19–21 (29)–(34), Algorithm 1, Definition 1; p. 42 (51), (52)

import Mathlib
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-!
# Model 1, the label and parameter posteriors, the lifted posterior and Algorithm 1

Kumar, Sarkar, Tian, Zhu, *Posterior Sampling in Gaussian Mixture Models Beyond the
Clusterability Threshold*, STOC 2027 submission (manuscript sha256 ba5079cd…): §2.1 (pp. 8–9),
Model 1 and (24) (p. 16), (25)–(27) (p. 17), Φ_c, Orb, (28) (p. 18), (29)–(34), Algorithm 1 and
Definition 1 (pp. 19–21), (51)–(52) (p. 42).

* Points of `ℝ^d` are `E d = EuclideanSpace ℝ (Fin d)` (Euclidean norm). Indices `[k]`, `[n]`
  are `Fin k`, `Fin n` (0-based). A parameter is `θ = (w, µ) : Param k d =
  (Fin k → ℝ) × (Fin k → E d)`; `Θ = Δ_k × (ℝ^d)^k` is `Theta k d`.
* `‖θ − θ'‖₂` is `paramDist`: the Euclidean norm of all `k + kd` coordinates.
* The prior is `Dir(α) ⊗ N(0_d, (1/d) I_d)^{⊗k}` (`prior`), with the published
  `PolyVoting.dirichletMeasure`. Model 1 is the probability measure `joint` on
  `Θ × [k]^n × (ℝ^d)^n`: density `∏_j w_{ι_j} φ_σ(x_j − µ_{ι_j})` with respect to
  `prior ⊗ counting ⊗ Lebesgue`, i.e. `ι⋆_j ∼ Cat(w⋆)` and `x_j | ι⋆_j ∼ N(µ⋆_{ι⋆_j}, σ² I_d)`
  independently given `θ⋆ = (w⋆, µ⋆)`. `xLaw` is the law of the observed `x_[n]`.
* The label posterior `π_x = Law(ι⋆ | x)` (24) is `labelPost`, defined for **every** `x` by
  Bayes' rule: `π_x(ι) ∝ ∫ ∏_j w_{ι_j} φ_σ(x_j − µ_{ι_j}) prior(dθ)`. The parameter posterior
  `Π = Law(θ⋆ | x)` (26) is `paramPost`, `∝ L_θ(x) prior(dθ)`.
* The lifted posterior `Π̃_B` (29) is `lifted`, a probability measure on `Θ × S_k`, with
  `S_k = Equiv.Perm (Fin k)` carrying the discrete σ-algebra. Since `Dir(α)` has density
  `∝ ∏ w_i^{α_i − 1}`, the density `∝ L_θ(x) e^{−(d/2)Σ‖µ_i‖²} ∏ w_i^{α_{c(i)} − 1} 1_B(θ)` of (29)
  is written as `L_θ(x) ∏ w_i^{α_{c(i)} − α_i} 1_B(θ)` with respect to `prior`.
* `normalize μ = μ(univ)⁻¹ • μ`.
-/

/-- Points of `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A parameter `θ = (w, µ_[k])`. -/
abbrev Param (k d : ℕ) := (Fin k → ℝ) × (Fin k → E d)

/-- The probability simplex `Δ_k`. -/
def simplex (k : ℕ) : Set (Fin k → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- `Θ = Δ_k × (ℝ^d)^k`. -/
def Theta (k d : ℕ) : Set (Param k d) := {θ | θ.1 ∈ simplex k}

/-- `‖θ − θ'‖₂`, the Euclidean norm of the difference of all `k + kd` coordinates. -/
noncomputable def paramDist {k d : ℕ} (θ θ' : Param k d) : ℝ :=
  Real.sqrt (∑ i, (θ.1 i - θ'.1 i) ^ 2 + ∑ i, ‖θ.2 i - θ'.2 i‖ ^ 2)

/-- The density `φ_σ` of `N(0_d, σ² I_d)`. -/
noncomputable def phi {d : ℕ} (σ : ℝ) (x : E d) : ℝ :=
  (2 * Real.pi * σ ^ 2) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2))

/-- The mixture density `p_θ(x) = ∑_i w_i φ_σ(x − µ_i)` (25). -/
noncomputable def mixDensity {k d : ℕ} (σ : ℝ) (θ : Param k d) (x : E d) : ℝ :=
  ∑ i, θ.1 i * phi σ (x - θ.2 i)

/-- The likelihood `L_θ(x_[n]) = ∏_j p_θ(x_j)` (25). -/
noncomputable def lik {k d n : ℕ} (σ : ℝ) (θ : Param k d) (x : Fin n → E d) : ℝ :=
  ∏ j, mixDensity σ θ (x j)

/-- The prior of the means: `µ_i` i.i.d. `N(0_d, (1/d) I_d)`. -/
noncomputable def meanPrior (k d : ℕ) : Measure (Fin k → E d) :=
  Measure.pi fun _ : Fin k =>
    multivariateGaussian (0 : E d) ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ))

/-- The prior `Dir(α) ⊗ N(0_d, (1/d) I_d)^{⊗k}` of `θ⋆ = (w⋆, µ⋆)`. -/
noncomputable def prior {k : ℕ} (d : ℕ) (α : Fin k → ℝ) : Measure (Param k d) :=
  (PolyVoting.dirichletMeasure α).prod (meanPrior k d)

/-- The density of the pairs `(ι⋆_j, x_j)` given `θ`: `∏_j w_{ι_j} φ_σ(x_j − µ_{ι_j})`. -/
noncomputable def pairDensity {k d n : ℕ} (σ : ℝ) (θ : Param k d) (ι : Fin n → Fin k)
    (x : Fin n → E d) : ℝ :=
  ∏ j, θ.1 (ι j) * phi σ (x j - θ.2 (ι j))

/-- **Model 1**: the joint law of `(θ⋆, ι⋆_[n], x_[n])` on `Θ × [k]^n × (ℝ^d)^n`. -/
noncomputable def joint (k d n : ℕ) (σ : ℝ) (α : Fin k → ℝ) :
    Measure (Param k d × (Fin n → Fin k) × (Fin n → E d)) :=
  ((prior d α).prod ((Measure.count : Measure (Fin n → Fin k)).prod
      (volume : Measure (Fin n → E d)))).withDensity
    fun p => ENNReal.ofReal (pairDensity σ p.1 p.2.1 p.2.2)

/-- The law of the observations `x_[n]` under Model 1. -/
noncomputable def xLaw (k d n : ℕ) (σ : ℝ) (α : Fin k → ℝ) : Measure (Fin n → E d) :=
  (joint k d n σ α).map fun p => p.2.2

/-- The unnormalized posterior weight of a labelling `ι`:
`∫ ∏_j w_{ι_j} φ_σ(x_j − µ_{ι_j}) prior(dθ)`. -/
noncomputable def labelWeight {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (ι : Fin n → Fin k) : ENNReal :=
  ∫⁻ θ, ENNReal.ofReal (pairDensity σ θ ι x) ∂(prior d α)

/-- The label posterior `π_x(ι) = Law(ι⋆_[n] | x_[n])(ι)` (24), by Bayes' rule, for every `x`. -/
noncomputable def labelPost {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (ι : Fin n → Fin k) : ℝ :=
  (labelWeight σ α x ι / ∑ ι', labelWeight σ α x ι').toReal

/-- `μ(univ)⁻¹ • μ`. -/
noncomputable def normalize {X : Type*} [MeasurableSpace X] (μ : Measure X) : Measure X :=
  (μ Set.univ)⁻¹ • μ

/-- The parameter posterior `Π = Law(θ⋆ | x_[n])` (26): `∝ L_θ(x_[n]) prior(dθ)`. -/
noncomputable def paramPost {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d) :
    Measure (Param k d) :=
  normalize ((prior d α).withDensity fun θ => ENNReal.ofReal (lik σ θ x))

/-- Relabelling `Φ_c(θ) = ({w_{c⁻¹(i)}}_i, {µ_{c⁻¹(i)}}_i)`. -/
def relabel {k d : ℕ} (c : Equiv.Perm (Fin k)) (θ : Param k d) : Param k d :=
  (fun i => θ.1 (c.symm i), fun i => θ.2 (c.symm i))

/-- The ball `{θ ∈ Θ : ‖θ − θ̄‖₂ ≤ ρ}` (`B` of (28) is `ballB θ̄ (3 r)`). -/
def ballB {k d : ℕ} (θbar : Param k d) (ρ : ℝ) : Set (Param k d) :=
  {θ | θ ∈ Theta k d ∧ paramDist θ θbar ≤ ρ}

/-- `min_{θ' ∈ Orb(θ̄)} ‖θ' − θ⋆‖₂ ≤ r` (the minimum over the finite orbit). -/
def OrbitClose {k d : ℕ} (θbar θstar : Param k d) (r : ℝ) : Prop :=
  ∃ c : Equiv.Perm (Fin k), paramDist (relabel c θbar) θstar ≤ r

/-- `Φ_c(B) ∩ Φ_{c'}(B) = ∅` for all distinct `c, c'`, `B = ballB θ̄ ρ`. -/
def OrbitDisjoint {k d : ℕ} (θbar : Param k d) (ρ : ℝ) : Prop :=
  ∀ c c' : Equiv.Perm (Fin k), c ≠ c' →
    Disjoint (relabel c '' ballB θbar ρ) (relabel c' '' ballB θbar ρ)

/-- The regularity set `R(τ)` (52): `min_i w_i ≥ τ` and `(3/4) I_k ⪯ AᵀA ⪯ (5/4) I_k` for
`A = [µ_1 | ⋯ | µ_k]`, i.e. `(3/4)‖u‖² ≤ ‖∑ u_i µ_i‖² ≤ (5/4)‖u‖²` for all `u ∈ ℝ^k`. -/
def Regular {k d : ℕ} (τ : ℝ) : Set (Param k d) :=
  {θ | θ ∈ Theta k d ∧ (∀ i, τ ≤ θ.1 i) ∧
    ∀ u : Fin k → ℝ, 3 / 4 * ∑ i, u i ^ 2 ≤ ‖∑ i, u i • θ.2 i‖ ^ 2 ∧
      ‖∑ i, u i • θ.2 i‖ ^ 2 ≤ 5 / 4 * ∑ i, u i ^ 2}

instance (k : ℕ) : MeasurableSpace (Equiv.Perm (Fin k)) := ⊤

instance (k : ℕ) : DiscreteMeasurableSpace (Equiv.Perm (Fin k)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- `∏_i w_i^{α_{c(i)} − 1}`, the weight of `c` in (32). -/
noncomputable def permWeight {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ)
    (c : Equiv.Perm (Fin k)) : ℝ :=
  ∏ i, w i ^ (α (c i) - 1)

/-- `Z_α(w) = ∑_{c'} ∏_i w_i^{α_{c'(i)} − 1}` (32). -/
noncomputable def Zalpha {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  ∑ c, permWeight α w c

/-- The conditional law `Π̃_B(c | θ) = ∏_i w_i^{α_{c(i)} − 1} / Z_α(w)` (32), a mass function on
`S_k`. -/
noncomputable def condPermMass {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ)
    (c : Equiv.Perm (Fin k)) : ℝ :=
  permWeight α w c / Zalpha α w

/-- The same conditional law as a measure on `S_k`. -/
noncomputable def condPerm {k : ℕ} (α : Fin k → ℝ) (w : Fin k → ℝ) :
    Measure (Equiv.Perm (Fin k)) :=
  ∑ c, ENNReal.ofReal (condPermMass α w c) • Measure.dirac c

/-- `∏_i w_i^{α_{c(i)} − α_i}`: the density of `∏ w_i^{α_{c(i)} − 1}` relative to `Dir(α)`. -/
noncomputable def dirTilt {k : ℕ} (α : Fin k → ℝ) (c : Equiv.Perm (Fin k))
    (w : Fin k → ℝ) : ℝ :=
  ∏ i, w i ^ (α (c i) - α i)

/-- The unnormalized `c`-slice of (29): `L_θ(x) ∏ w_i^{α_{c(i)} − α_i} 1_B(θ) prior(dθ)`,
`B = ballB θ̄ ρ`. -/
noncomputable def liftedSlice {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (θbar : Param k d) (ρ : ℝ) (c : Equiv.Perm (Fin k)) : Measure (Param k d) :=
  (prior d α).withDensity fun θ =>
    (ballB θbar ρ).indicator (fun θ => ENNReal.ofReal (lik σ θ x * dirTilt α c θ.1)) θ

/-- The conditional law `Π̃_B(θ | c)` (31), a probability measure on `Θ` supported on `B`. -/
noncomputable def condParam {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (θbar : Param k d) (ρ : ℝ) (c : Equiv.Perm (Fin k)) : Measure (Param k d) :=
  normalize (liftedSlice σ α x θbar ρ c)

/-- The lifted posterior `Π̃_B` (29) on `Θ × S_k`, `B = ballB θ̄ ρ`. -/
noncomputable def lifted {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (θbar : Param k d) (ρ : ℝ) : Measure (Param k d × Equiv.Perm (Fin k)) :=
  normalize (∑ c, (liftedSlice σ α x θbar ρ c).map fun θ => (θ, c))

/-- The exact `θ`-update of Algorithm 1 (line 4) as a kernel `S_k → Θ`. -/
noncomputable def exactParamKernel {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (θbar : Param k d) (ρ : ℝ) : Kernel (Equiv.Perm (Fin k)) (Param k d) :=
  ⟨condParam σ α x θbar ρ, Measurable.of_discrete⟩

/-- `Unif(S_k)`. -/
noncomputable def unifPerm (k : ℕ) : Measure (Equiv.Perm (Fin k)) :=
  normalize Measure.count

/-- One iteration of Algorithm 1 (lines 4–5): from `(θ_t, c_t)` draw `θ_{t+1} ∼ K_c(c_t)` and
then `c_{t+1} ∼ K_θ(θ_{t+1})`. -/
noncomputable def alg1Step {k d : ℕ} (Kc : Kernel (Equiv.Perm (Fin k)) (Param k d))
    (Kθ : Kernel (Param k d) (Equiv.Perm (Fin k))) :
    Kernel (Param k d × Equiv.Perm (Fin k)) (Param k d × Equiv.Perm (Fin k)) :=
  (Kc.comap Prod.snd measurable_snd) ⊗ₖ (Kθ.comap Prod.snd measurable_snd)

/-- The law of the output `(θ_T, c_T)` of Algorithm 1 run for `T` iterations from
`c_0 ∼ Unif(S_k)`, with the updates of lines 4 and 5 drawn from `Kc` and `Kθ`. (The algorithm
never sets `θ_0`; it is taken to be `θ̄`, which only matters for `T = 0`.) -/
noncomputable def alg1Law {k d : ℕ} (Kc : Kernel (Equiv.Perm (Fin k)) (Param k d))
    (Kθ : Kernel (Param k d) (Equiv.Perm (Fin k))) (θbar : Param k d) (T : ℕ) :
    Measure (Param k d × Equiv.Perm (Fin k)) :=
  (fun μ => μ.bind (alg1Step Kc Kθ)) ^[T] ((Measure.dirac θbar).prod (unifPerm k))

/-- Definition 1: `(Kθ, Kc)` are `ξ`-conditional sampling oracles for `Π̃_B`
(`B = ballB θ̄ ρ`): `TV(Kθ θ, Π̃_B(· | θ)) ≤ ξ` for all `θ ∈ B` (with all `w_i > 0`, where (32)
is defined; the boundary of the simplex is `Π̃_B`-null) and `TV(Kc c, Π̃_B(· | c)) ≤ ξ` for all
`c ∈ S_k`. -/
def IsCondOracles {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d) (θbar : Param k d)
    (ρ ξ : ℝ) (Kθ : Kernel (Param k d) (Equiv.Perm (Fin k)))
    (Kc : Kernel (Equiv.Perm (Fin k)) (Param k d)) : Prop :=
  (∀ θ ∈ ballB θbar ρ, (∀ i, 0 < θ.1 i) → tv (Kθ θ) (condPerm α θ.1) ≤ ξ) ∧
    ∀ c, tv (Kc c) (condParam σ α x θbar ρ c) ≤ ξ

/-- The potential `V(θ) = −log L_θ(x) + (d/2) ∑ ‖µ_i‖² − log Z_α(w)` (33). -/
noncomputable def potV {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (θ : Param k d) : ℝ :=
  -Real.log (lik σ θ x) + (d : ℝ) / 2 * ∑ i, ‖θ.2 i‖ ^ 2 - Real.log (Zalpha α θ.1)

/-- The conditional potential `V_c(θ) = −log L_θ(x) + (d/2) ∑ ‖µ_i‖² − ∑ (α_{c(i)} − 1) log w_i`
(34). -/
noncomputable def potVc {k d n : ℕ} (σ : ℝ) (α : Fin k → ℝ) (x : Fin n → E d)
    (c : Equiv.Perm (Fin k)) (θ : Param k d) : ℝ :=
  -Real.log (lik σ θ x) + (d : ℝ) / 2 * ∑ i, ‖θ.2 i‖ ^ 2 -
    ∑ i, (α (c i) - 1) * Real.log (θ.1 i)

/-- The tangent space `T = {(ẇ, h) : 1ᵀẇ = 0}` of `Θ` (51). -/
def tangent (k d : ℕ) : Set (Param k d) := {v | ∑ i, v.1 i = 0}

/-- The squared Euclidean norm `‖v‖₂²` of a tangent vector. -/
noncomputable def normSq {k d : ℕ} (v : Param k d) : ℝ :=
  ∑ i, v.1 i ^ 2 + ∑ i, ‖v.2 i‖ ^ 2

/-- The second derivative of `F` at `θ` in direction `v`, `d²/dt² F(θ + t v)|_{t=0}`: the
Hessian quadratic form `vᵀ ∇²F(θ) v` in orthonormal affine coordinates. -/
noncomputable def d2 {k d : ℕ} (F : Param k d → ℝ) (θ v : Param k d) : ℝ :=
  deriv (fun s : ℝ => deriv (fun t : ℝ => F (θ + t • v)) s) 0

/-- `λ I ⪯ ∇²F(θ) ⪯ L I` on the tangent space (orthonormal affine coordinates on `Θ`). -/
def HessBetween {k d : ℕ} (F : Param k d → ℝ) (θ : Param k d) (lo hi : ℝ) : Prop :=
  ∀ v ∈ tangent k d, lo * normSq v ≤ d2 F θ v ∧ d2 F θ v ≤ hi * normSq v

/-- `λ I ⪯ ∇²F(θ)` on the tangent space. -/
def HessGe {k d : ℕ} (F : Param k d → ℝ) (θ : Param k d) (lo : ℝ) : Prop :=
  ∀ v ∈ tangent k d, lo * normSq v ≤ d2 F θ v

end GMMPostSamp.Main


