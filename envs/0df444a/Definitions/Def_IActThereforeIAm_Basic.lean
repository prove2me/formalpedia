-- Prove2me | Definitions.Def_IActThereforeIAm_Basic
-- name    : IActThereforeIAm_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T19:02:52.330577+00:00
-- url     : https://prove2.me/theorems/a461254f-79d4-49df-b981-7b0a98d226ca
-- title:
--   Latent causal model, information-theoretic JEPA objective and action-variability assumption
-- statement:
--   Objects of Sections 2-3 and Appendices C-E of Liu, Huang and Shi (2026).
--
--   1. **Latent causal model (Eqs. 1-3).** The latent state is $\mathbf s_t\in\mathbb R^d$ and actions lie in a measurable space $A$. The pair $(\mathbf s_{t-1},\mathbf a_{t-1})$ has a probability law $\nu$. Each coordinate evolves as $s_{t,i}=f_i(\mathbf s_{t-1,\mathrm{pa}_i},\mathbf a_{t-1},\epsilon_{t,i})$ with jointly measurable mechanisms $f_i$, parent sets $\mathrm{pa}_i\subseteq\{1,\dots,d\}$, and disturbances $\epsilon_{t,1},\dots,\epsilon_{t,d}$ that are independent of each other and of $(\mathbf s_{t-1},\mathbf a_{t-1})$, with laws $\eta_i$. All statements use the resulting joint law $P$ of $((\mathbf s_{t-1},\mathbf a_{t-1}),\mathbf s_t)$. Observations are $\mathbf x_t=\mathbf g(\mathbf s_t)$.
--   2. **Information quantities.** $I(X;Y)=D_{\mathrm{KL}}(P_{(X,Y)}\,\|\,P_X\otimes P_Y)\in[0,\infty]$, in nats. For a law $\mu$ on $\mathbb R^d$ with Lebesgue density $f$, the differential entropy is $H(\mu)=-\int f\log f$. It is set to $-\infty$ when $\mu$ has no density or $f\log f$ is not integrable. The open unit cube is $(0,1)^d$.
--   3. **Objective (Eq. 4).** For an encoder $\mathbf h:\mathcal X\to(0,1)^d$, write $\mathbf z_t=\mathbf h(\mathbf g(\mathbf s_t))$ and $\mathbf c_t=(\mathbf z_{t-1},\mathbf a_{t-1})$. A transition model $p(\mathbf z\mid\mathbf c)$ is jointly measurable and, for each $\mathbf c$, a probability density on $\mathbb R^d$. The objective is
--   $$\mathcal L_\lambda(\mathbf h,p)=-\mathbb E[\log p(\mathbf z_t\mid\mathbf c_t)]-\lambda H(\mathbf z_t).$$
--   A pair is *admissible* if $\mathbf h$ is measurable with values in $(0,1)^d$, $p(\mathbf z_t\mid\mathbf c_t)>0$ a.s., the log-likelihood is integrable, and $H(\mathbf z_t)>-\infty$; on admissible pairs $\mathcal L_\lambda$ is a real number. A *global minimizer* over a parameterized model $\{p_\phi\}_{\phi\in\Theta}$ is an admissible pair $(\mathbf h,\phi)$ whose objective is at most that of every admissible pair $(\mathbf h',\phi')$.
--   4. **Induced transition density (Eq. 6).** $p$ is a version of $Q_{\mathbf h}(\mathbf z_t\mid\mathbf c_t)$ when the joint law of $(\mathbf c_t,\mathbf z_t)$ equals the law of $\mathbf c_t$ times $p(\mathbf z\mid\mathbf c)\,d\mathbf z$.
--   5. **Assumption 3.1.** $\mathbf g$ is smooth ($C^\infty$) and injective.
--   6. **Assumption 3.2 (Eqs. 7-8).** The functions $p_i(u\mid\mathbf s_{t-1},\mathbf a_{t-1})$ are densities of the conditional laws of $s_{t,i}$. They are positive, $C^2$ in $u$ and jointly continuous. With $q_i=\log p_i$,
--   $$\mathbf w(\mathbf s_t,\mathbf s_{t-1},\mathbf a)=\Big(\tfrac{\partial q_1}{\partial s_{t,1}},\dots,\tfrac{\partial q_d}{\partial s_{t,d}},\tfrac{\partial^2 q_1}{\partial s_{t,1}^2},\dots,\tfrac{\partial^2 q_d}{\partial s_{t,d}^2}\Big)^\top.$$
--   Action variability means that for all $\mathbf s_t,\mathbf s_{t-1}$ there are actions $\mathbf a^{(0)},\dots,\mathbf a^{(2d)}$ for which the $2d$ vectors $\mathbf w(\mathbf a^{(\ell)})-\mathbf w(\mathbf a^{(0)})$ are linearly independent, i.e. the matrix $\mathbf L$ is invertible.
--   7. **Factorized model (Eq. 47).** $p_\phi(\mathbf z\mid\mathbf c)=\prod_j p_{\phi,j}(z_j\mid\mathbf c)$. On the encoder range, i.e. for $\mathbf c=(\mathbf z_{t-1},\mathbf a)$ with $\mathbf z_{t-1}\in(0,1)^d$ and $z_j\in(0,1)$, the factors are positive, $C^2$ in $z_j$ and jointly continuous. Outside this range they are unrestricted.
--   8. **Contrastive term (Eqs. 56-59).** $\|v\|^2=\sum_i v_i^2$. The Gaussian negative log-likelihood is $\ell(\mathbf z)=\|\mathbf z-\mathbf m\|^2/(2\sigma^2)+\tfrac d2\log(2\pi\sigma^2)$. The Gaussian kernel is $\varphi_b(x)=(2\pi b^2)^{-d/2}e^{-\|x\|^2/(2b^2)}$. The contrastive term is $U_K=\log\big[\tfrac1K\sum_{k=1}^K e^{-\ell(\mathbf z^{(k)})/\tau}\big]$, and $(p_{\mathbf z}*\varphi_b)(\mathbf z_t)=\int\varphi_b(\mathbf z-\mathbf z_t)\,dp_{\mathbf z}(\mathbf z)$.
--
--   **Formalization Note** The SCM is encoded by its mechanisms, noise laws and the law of $(\mathbf s_{t-1},\mathbf a_{t-1})$; the joint law is the push-forward of $\nu\otimes\bigotimes_i\eta_i$. The DAG requirement holds for every choice of parent sets, because all edges go from time $t-1$ to time $t$. Mutual information uses Mathlib's `InformationTheory.klDiv`. The objective is real-valued and is only used on admissible pairs, where it equals the paper's value. Encoders and observation spaces are general: $\mathcal X$ is a measurable space, and a real normed space in Theorem 3.3.
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Section 2.1 (Eqs. 1-3, p. 2-3), Section 2.2 (Eq. 4, Theorem 2.1, p. 3), Section 3 (Assumptions 3.1-3.2, Eqs. 7-8, p. 4), Appendix D (Eq. 47, p. 21), Appendix E (Eqs. 56-59, p. 22)

import Mathlib

/-!
Liu, Huang and Shi, *I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn
Causal Mechanisms?*, arXiv:2609.31161v1 (2026): the latent causal generative model of Section 2.1
(Eqs. (1)-(3)), the information-theoretic JEPA objective of Section 2.2 (Eq. (4)), the induced
transition density of Theorem 2.1 (Eq. (6)), Assumptions 3.1 and 3.2 of Section 3 (Eqs. (7)-(8)),
the factorized transition model of Appendix D (Eq. (47)), and the Gaussian contrastive term of
Appendix E (Eqs. (56)-(58)).
-/

open MeasureTheory
open scoped ENNReal ContDiff

noncomputable section

namespace IActThereforeIAm

/-- Section 2.1, Eqs. (1)-(2): a latent causal generative model. The latent state is
`s_t ∈ ℝ^d`, actions lie in `A`, and `s_{t,i} := f_i(s_{t-1,pa_i}, a_{t-1}, ε_{t,i})`, where the
disturbances `ε_{t,1}, …, ε_{t,d}` are mutually independent and independent of `(s_{t-1}, a_{t-1})`.
The observation `x_t = g(s_t)` is attached separately, as a map `g`. -/
structure LatentSCM (d : ℕ) (A : Type*) [MeasurableSpace A] where
  /-- The parent set `pa_i ⊆ {1, …, d}` of `s_{t,i}` in `s_{t-1}`. -/
  pa : Fin d → Finset (Fin d)
  /-- The mechanism `f_i(s_{t-1}, a_{t-1}, ε_{t,i})`. -/
  mech : Fin d → (Fin d → ℝ) → A → ℝ → ℝ
  /-- The law of the disturbance `ε_{t,i}`. -/
  noise : Fin d → Measure ℝ
  /-- The joint law of `(s_{t-1}, a_{t-1})`. -/
  prev : Measure ((Fin d → ℝ) × A)

/-- Section 2.1: the standing conditions on a latent causal model. The laws of `(s_{t-1}, a_{t-1})`
and of each disturbance are probability measures, each mechanism is jointly measurable, and
`f_i` depends on `s_{t-1}` only through its parents `s_{t-1,pa_i}`. -/
def LatentSCM.IsValid {d : ℕ} {A : Type*} [MeasurableSpace A] (M : LatentSCM d A) : Prop :=
  IsProbabilityMeasure M.prev ∧ (∀ i, IsProbabilityMeasure (M.noise i)) ∧
  (∀ i, Measurable (fun x : ((Fin d → ℝ) × A) × ℝ => M.mech i x.1.1 x.1.2 x.2)) ∧
  (∀ i (s s' : Fin d → ℝ) (a : A) (e : ℝ), (∀ j ∈ M.pa i, s j = s' j) →
    M.mech i s a e = M.mech i s' a e)

/-- Section 2.1, Eqs. (1) and (3): the joint law of `((s_{t-1}, a_{t-1}), s_t)`, obtained by drawing
`(s_{t-1}, a_{t-1})` and independent disturbances `ε_{t,i}` and applying the mechanisms. -/
def LatentSCM.jointLaw {d : ℕ} {A : Type*} [MeasurableSpace A] (M : LatentSCM d A) :
    Measure (((Fin d → ℝ) × A) × (Fin d → ℝ)) :=
  (M.prev.prod (Measure.pi M.noise)).map
    (fun x => (x.1, fun i => M.mech i x.1.1 x.1.2 (x.2 i)))

/-- Section 2.2: the mutual information `I(X; Y)` of random variables `X`, `Y` on `(Ω, P)`, the
Kullback-Leibler divergence of their joint law from the product of their laws (in nats, valued
in `[0, ∞]`). -/
def mutualInfo {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (X : Ω → α) (Y : Ω → β) : ℝ≥0∞ :=
  InformationTheory.klDiv (P.map fun w => (X w, Y w)) ((P.map X).prod (P.map Y))

/-- Theorem 2.1, Eq. (5): `I(s_t; s_{t-1}, a_{t-1})` under the latent model. -/
def latentInfo {d : ℕ} {A : Type*} [MeasurableSpace A] (M : LatentSCM d A) : ℝ≥0∞ :=
  mutualInfo M.jointLaw (fun w => w.2) (fun w => w.1)

/-- Theorem 2.1, Eq. (5): `I(z_t; z_{t-1}, a_{t-1})` for the representation `z = h(g(s))`. -/
def reprInfo {d : ℕ} {A X : Type*} [MeasurableSpace A] [MeasurableSpace X] (M : LatentSCM d A)
    (g : (Fin d → ℝ) → X) (h : X → Fin d → ℝ) : ℝ≥0∞ :=
  mutualInfo M.jointLaw (fun w => h (g w.2)) (fun w => (h (g w.1.1), w.1.2))

/-- Section 2.2: the law of the representation `z_t = h(x_t) = h(g(s_t))`. -/
def reprLaw {d : ℕ} {A X : Type*} [MeasurableSpace A] [MeasurableSpace X] (M : LatentSCM d A)
    (g : (Fin d → ℝ) → X) (h : X → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  M.jointLaw.map fun w => h (g w.2)

/-- Theorem 2.1: the open unit cube `(0, 1)^d`, the range of the encoder. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1

open Classical in
/-- Section 2.2, Eq. (4): the differential entropy `H(μ) = -∫ f log f` of a law `μ` on `ℝ^d` with
Lebesgue density `f`. It is `-∞` (`⊥`) when `μ` has no density or `f log f` is not integrable;
for laws carried by a bounded set, such as `(0,1)^d`, this is the standard value. -/
def diffEntropy {d : ℕ} (μ : Measure (Fin d → ℝ)) : EReal :=
  if μ ≪ volume ∧ Integrable (fun z => Real.negMulLog (μ.rnDeriv volume z).toReal) volume then
    ((∫ z, Real.negMulLog (μ.rnDeriv volume z).toReal : ℝ) : EReal)
  else ⊥

/-- Section 2.2: `p(z_t | z_{t-1}, a_{t-1})` is an action-conditioned transition model on `ℝ^d`:
jointly measurable and, for each context `c = (z_{t-1}, a_{t-1})`, a probability density. -/
def IsTransitionModel {d : ℕ} {A : Type*} [MeasurableSpace A]
    (p : (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ) : Prop :=
  Measurable (fun x : ((Fin d → ℝ) × A) × (Fin d → ℝ) => p x.1 x.2) ∧ (∀ c z, 0 ≤ p c z) ∧
    ∀ c, ∫ z, p c z = 1

/-- Section 2.2, Eq. (4): the objective
`L_λ(h, φ) = -E[log p_φ(z_t | z_{t-1}, a_{t-1})] - λ H(z_t)` with `z = h(g(s))`. It is the
paper's (finite) value on admissible pairs (`IsAdmissible`). -/
def objective {d : ℕ} {A X : Type*} [MeasurableSpace A] [MeasurableSpace X] (M : LatentSCM d A)
    (g : (Fin d → ℝ) → X) (lam : ℝ) (h : X → Fin d → ℝ)
    (p : (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ) : ℝ :=
  -(∫ w, Real.log (p (h (g w.1.1), w.1.2) (h (g w.2))) ∂M.jointLaw) -
    lam * (diffEntropy (reprLaw M g h)).toReal

/-- Theorem 2.1: an admissible pair `(h, p_φ)`. The encoder `h : X → (0,1)^d` is measurable, `p_φ`
is a transition model, and both terms of Eq. (4) are finite: the log-likelihood is a.s. defined
(`p_φ > 0`) and integrable, and `z_t` has finite differential entropy. -/
def IsAdmissible {d : ℕ} {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (M : LatentSCM d A) (g : (Fin d → ℝ) → X) (h : X → Fin d → ℝ)
    (p : (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ) : Prop :=
  Measurable h ∧ (∀ x i, h x i ∈ Set.Ioo (0 : ℝ) 1) ∧ IsTransitionModel p ∧
    (∀ᵐ w ∂M.jointLaw, 0 < p (h (g w.1.1), w.1.2) (h (g w.2))) ∧
    Integrable (fun w => Real.log (p (h (g w.1.1), w.1.2) (h (g w.2)))) M.jointLaw ∧
    diffEntropy (reprLaw M g h) ≠ ⊥

/-- Theorems 2.1 and 3.3: `(h, φ)` is a global minimizer of Eq. (4) over all admissible pairs of an
encoder and a parameter `φ` of the transition model `model φ`. -/
def IsGlobalMin {d : ℕ} {A X Θ : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (M : LatentSCM d A) (g : (Fin d → ℝ) → X) (lam : ℝ)
    (model : Θ → (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ) (h : X → Fin d → ℝ) (φ : Θ) : Prop :=
  IsAdmissible M g h (model φ) ∧
    ∀ (h' : X → Fin d → ℝ) (φ' : Θ), IsAdmissible M g h' (model φ') →
      objective M g lam h (model φ) ≤ objective M g lam h' (model φ')

/-- Theorem 2.1, Eq. (6): `p(z_t | z_{t-1}, a_{t-1}) = Q_h(z_t | z_{t-1}, a_{t-1})` a.e., i.e. `p` is a
version of the transition density induced by `h`: the joint law of `(c_t, z_t)`, with
`c_t = (z_{t-1}, a_{t-1})`, is the law of `c_t` times `p(z | c) dz`. -/
def IsReprTransitionDensity {d : ℕ} {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (M : LatentSCM d A) (g : (Fin d → ℝ) → X) (h : X → Fin d → ℝ)
    (p : (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ) : Prop :=
  M.jointLaw.map (fun w => ((h (g w.1.1), w.1.2), h (g w.2))) =
    ((M.jointLaw.map fun w => (h (g w.1.1), w.1.2)).prod volume).withDensity
      (fun x => ENNReal.ofReal (p x.1 x.2))

/-- Assumption 3.1: the observation mapping `g` is smooth and invertible (injective). -/
def ObsRegular {d : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (g : (Fin d → ℝ) → X) : Prop :=
  ContDiff ℝ ∞ g ∧ Function.Injective g

/-- Section 2.1, Eq. (3): `dens i s' a` is a density of `p(s_{t,i} | s_{t-1,pa_i} = s'_{pa_i},
a_{t-1} = a)`, the law of `f_i(s', a, ε_{t,i})`. -/
def HasTransitionDensities {d : ℕ} {A : Type*} [MeasurableSpace A] (M : LatentSCM d A)
    (dens : Fin d → (Fin d → ℝ) → A → ℝ → ℝ) : Prop :=
  ∀ i (s' : Fin d → ℝ) (a : A), (M.noise i).map (fun e => M.mech i s' a e) =
    volume.withDensity (fun u => ENNReal.ofReal (dens i s' a u))

/-- Assumption 3.2 (regularity it presupposes): every conditional density is positive, twice
continuously differentiable in `s_{t,i}`, and jointly continuous in `(s_{t-1}, a_{t-1}, s_{t,i})`. -/
def IsRegularDensity {d : ℕ} {A : Type*} [TopologicalSpace A]
    (dens : Fin d → (Fin d → ℝ) → A → ℝ → ℝ) : Prop :=
  ∀ i, (∀ s' a u, 0 < dens i s' a u) ∧ (∀ s' a, ContDiff ℝ 2 (dens i s' a)) ∧
    Continuous (fun x : ((Fin d → ℝ) × A) × ℝ => dens i x.1.1 x.1.2 x.2)

/-- Assumption 3.2, Eq. (8): `w(s_t, s_{t-1}, a_{t-1}) = (∂q_1/∂s_{t,1}, …, ∂q_d/∂s_{t,d},
∂²q_1/∂s_{t,1}², …, ∂²q_d/∂s_{t,d}²)` with `q_i = log p(s_{t,i} | s_{t-1,pa_i}, a_{t-1})`; the first
block is indexed by `Sum.inl i`, the second by `Sum.inr i`. -/
def scoreVec {d : ℕ} {A : Type*} (dens : Fin d → (Fin d → ℝ) → A → ℝ → ℝ)
    (s s' : Fin d → ℝ) (a : A) : Fin d ⊕ Fin d → ℝ :=
  Sum.elim (fun i => deriv (fun u => Real.log (dens i s' a u)) (s i))
    (fun i => deriv (deriv fun u => Real.log (dens i s' a u)) (s i))

/-- Assumption 3.2, Eq. (7): for all `s_t, s_{t-1}` there are `2d + 1` actions `a^{(0)}, …, a^{(2d)}`
such that the `2d × 2d` matrix `L` with columns `w(a^{(ℓ)}) - w(a^{(0)})`, `ℓ = 1, …, 2d`, is
invertible (its columns are linearly independent). -/
def ActionVariability {d : ℕ} {A : Type*} (dens : Fin d → (Fin d → ℝ) → A → ℝ → ℝ) : Prop :=
  ∀ s s' : Fin d → ℝ, ∃ acts : Fin (2 * d + 1) → A,
    LinearIndependent ℝ (fun l : Fin (2 * d) =>
      scoreVec dens s s' (acts l.succ) - scoreVec dens s s' (acts 0))

/-- Appendix D, Eq. (47): the transition model factorizes across representation components,
`p_φ(z_t | z_{t-1}, a_{t-1}) = ∏_j p_{φ,j}(z_{t,j} | z_{t-1}, a_{t-1})`. On the encoder range
(`z_{t-1} ∈ (0,1)^d`, `z_{t,j} ∈ (0,1)`), where the proof evaluates it, each factor is positive, twice
continuously differentiable in `z_{t,j}`, and jointly continuous. Outside the range the factors are
unrestricted (an optimal model equals `Q_h` a.e. and so vanishes a.e. off `(0,1)^d`). -/
def IsRegularFactorizedModel {d : ℕ} {A : Type*} [TopologicalSpace A]
    (p : (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ) : Prop :=
  ∃ pj : Fin d → (Fin d → ℝ) × A → ℝ → ℝ, (∀ c z, p c z = ∏ j, pj j c (z j)) ∧
    (∀ j c v, c.1 ∈ unitCube d → v ∈ Set.Ioo (0 : ℝ) 1 → 0 < pj j c v) ∧
    (∀ j c, c.1 ∈ unitCube d → ContDiffOn ℝ 2 (pj j c) (Set.Ioo 0 1)) ∧
    ∀ j, ContinuousOn (fun x : ((Fin d → ℝ) × A) × ℝ => pj j x.1 x.2)
      {x | x.1.1 ∈ unitCube d ∧ x.2 ∈ Set.Ioo (0 : ℝ) 1}

/-- Appendix E: the squared Euclidean norm `‖v‖₂² = ∑_i v_i²` on `ℝ^d`. -/
def sqNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Appendix E, Eq. (57): the negative log-likelihood of `z` under `N(m, σ² I)`,
`ℓ_φ(z) = ‖z - m‖² / (2σ²) + (d/2) log(2πσ²)`. -/
def gaussNLL {d : ℕ} (σ : ℝ) (m z : Fin d → ℝ) : ℝ :=
  sqNorm (z - m) / (2 * σ ^ 2) + (d : ℝ) / 2 * Real.log (2 * Real.pi * σ ^ 2)

/-- Appendix E: the Gaussian kernel with bandwidth `b`,
`φ_b(x) = (2π b²)^{-d/2} exp(-‖x‖² / (2b²))`. -/
def gaussKernel {d : ℕ} (b : ℝ) (x : Fin d → ℝ) : ℝ :=
  (2 * Real.pi * b ^ 2) ^ (-(d : ℝ) / 2) * Real.exp (-sqNorm x / (2 * b ^ 2))

/-- Appendix E, Eq. (58): `U_K = log[(1/K) ∑_{k=1}^K exp(-ℓ_φ(z^{(k)}) / τ)]` for the predicted mean
`m = μ_φ(z_{t-1}, a_{t-1})` and the first `K` samples of the sequence `zs`. -/
def contrastiveU {d : ℕ} (σ τ : ℝ) (m : Fin d → ℝ) (zs : ℕ → Fin d → ℝ) (K : ℕ) : ℝ :=
  Real.log ((1 / (K : ℝ)) * ∑ k ∈ Finset.range K, Real.exp (-gaussNLL σ m (zs k) / τ))

/-- Appendix E, Eq. (59): `(p_z * φ_b)(z_t) = ∫ φ_b(z - z_t) dp_z(z)`. -/
def kernelSmoothed {d : ℕ} (μ : Measure (Fin d → ℝ)) (b : ℝ) (zt : Fin d → ℝ) : ℝ :=
  ∫ z, gaussKernel b (z - zt) ∂μ

end IActThereforeIAm


