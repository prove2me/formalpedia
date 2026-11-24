-- Prove2me | Definitions.Def_ContrastiveUnsupervised_Basic
-- name    : ContrastiveUnsupervised_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T23:04:37.28008+00:00
-- url     : https://prove2.me/theorems/1a437c63-cb3b-4cd9-8eab-31922d74fcdc
-- title:
--   Latent classes, contrastive and supervised losses, and collision quantities
-- statement:
--   Objects of Section 2, Sections 4-6 and Appendices A-B of Arora, Khandeparkar, Khodak, Plevrakis and Saunshi (2019).
--
--   1. **Latent classes.** A countable set $\mathcal C$ of latent classes carries a probability distribution $\rho$, and each class $c$ carries a probability distribution $\mathcal D_c$ on the data space $\mathcal X$. A representation is a measurable $f:\mathcal X\to\mathbb R^d$ with $\|f(\cdot)\|\le R$.
--   2. **Losses.** For a vector $(v_i)_{i\in s}$: the hinge loss $\ell(v)=\max\{0,1+\max_i(-v_i)\}$, the logistic loss $\ell(v)=\log_2(1+\sum_ie^{-v_i})$, and the hinge loss with margin $\gamma$, $\ell_\gamma(v)=\max\{0,1+\max_i(-v_i)/\gamma\}$. Both losses (hinge, including with margin, and logistic) of the empty vector are $0$.
--   3. **Supervised tasks (eqs. 3-4, Definitions 2.1-2.2).** A task $\mathcal T$ is a finite set of distinct classes with a label distribution $\mathcal D_{\mathcal T}$; $L_{sup}(\mathcal T,g)=\sum_{c\in\mathcal T}\mathcal D_{\mathcal T}(c)\,\mathbb E_{x\sim\mathcal D_c}\,\ell(\{g(x)_c-g(x)_{c'}\}_{c'\ne c})$. $L_{sup}(\mathcal T,f)=\inf_WL_{sup}(\mathcal T,Wf)$. The mean classifier has rows $\mu_c=\mathbb E_{x\sim\mathcal D_c}f(x)$, giving $L^\mu_{sup}(\mathcal T,f)$. The averages $L_{sup}(f)$ and $L^\mu_{sup}(f)$ over $(k+1)$-way tasks draw $c_1,\dots,c_{k+1}\sim\rho^{k+1}$ conditioned on being distinct, with uniform $\mathcal D_{\mathcal T}$.
--   4. **Unsupervised loss (eqs. 1, 2, 5, 6).** $\mathcal D_{sim}(x,x^+)=\mathbb E_{c\sim\rho}\mathcal D_c(x)\mathcal D_c(x^+)$ and $\mathcal D_{neg}=\mathbb E_{c\sim\rho}\mathcal D_c$. $L_{un}(f)=\mathbb E\,\ell(\{f(x)^\top(f(x^+)-f(x_i^-))\}_{i=1}^k)$ with $(x,x^+)\sim\mathcal D_{sim}$ and $x_i^-\sim\mathcal D_{neg}$ i.i.d. $\widehat L_{un}$ is the average of the same loss over $M$ training tuples, and the training set is drawn from $(\mathcal D_{sim}\times\mathcal D_{neg}^k)^M$.
--   5. **Complexity.** $\mathcal R_{\mathcal S}(\mathcal F)=\mathbb E_{\sigma\sim\{\pm1\}^{(k+2)dM}}\sup_{f\in\mathcal F}\langle\sigma,f_{|\mathcal S}\rangle$, where $f_{|\mathcal S}$ lists all coordinates of $f$ at all points of the training set. $Gen_M=K\big(R\sqrt k\,\mathcal R_{\mathcal S}(\mathcal F)/M+(R^2+\log k)\sqrt{\log(1/\delta)/M}\big)$, which for $k=1$ is $K\big(R\,\mathcal R_{\mathcal S}(\mathcal F)/M+R^2\sqrt{\log(1/\delta)/M}\big)$. $\mathcal F$ is pointwise separable: it has a countable subset $\mathcal F_0$ such that every $f\in\mathcal F$ is a pointwise limit of a sequence in $\mathcal F_0$.
--   6. **Class collision (Section 4.2).** $\tau=\sum_c\rho(c)^2$ and $\nu(c)=\rho(c)^2/\tau$. $L^=_{un}(f)$ is the one-negative loss with $x,x^+,x^-\sim\mathcal D_c^3$, $c\sim\nu$. $\Sigma(f,c)$ is the covariance of $f(x)$, $x\sim\mathcal D_c$, and $s(f)=\mathbb E_{c\sim\nu}\big[\sqrt{\|\Sigma(f,c)\|_2}\,\mathbb E_{x\sim\mathcal D_c}\|f(x)\|\big]$.
--   7. **$k$ negatives (Appendix B.1).** For $(c^+,c_1^-,\dots,c_k^-)\sim\rho^{k+1}$: $I^+=\{i:c_i^-=c^+\}$ and $Q$ is the set of distinct classes. $\tau_k=P[I^+\ne\emptyset]$ and $\tau'=P[c_i^-=c^+\ \forall i]$. $L^{\ne}_{un}(f)=\mathbb E[\ell(\{f(x)^\top(f(x^+)-f(x_i^-))\}_{i\notin I^+})\mid|I^+|<k]$; for $k=1$ this is the loss conditioned on $c^+\ne c^-$. A task $\mathcal T\sim\mathcal D$ is $Q$ conditioned on $I^+=\emptyset$. $\rho^+_{min}(\mathcal T)=\min_{c\in\mathcal T}P(c^+=c\mid Q=\mathcal T,I^+=\emptyset)$ and $p_{max}(\mathcal T)=\max_c\mathcal D_{\mathcal T}(c)$.
--   8. **Sub-Gaussian margin (Section 5.2).** $f$ is $\sigma^2$-sub-Gaussian in every direction if, for every class $c$ and unit $u$, $\mathbb E_{x\sim\mathcal D_c}e^{\lambda u^\top(f(x)-\mu_c)}\le e^{\lambda^2\sigma^2/2}$ for all $\lambda\in\mathbb R$. The margin from the proof of Lemma 5.1 is $\gamma=1+2R\sigma\sqrt{2\log R+\log(3/\varepsilon)}$ for $R\ge1$ and $\gamma=1+2R\sigma\sqrt{\log(3/\varepsilon)}$ for $R<1$.
--   9. **Blocks (eq. 12).** $L^{block}_{un}(f)=\mathbb E\,\ell\big(f(x)^\top(\frac1b\sum_if(x_i^+)-\frac1b\sum_if(x_i^-))\big)$, where $x,x_1^+,\dots,x_b^+\sim\mathcal D_{c^+}$, $x_1^-,\dots,x_b^-\sim\mathcal D_{c^-}$ and $c^+,c^-\sim\rho^2$.
--
--   **Formalization Note** The paper's formulas $\tau=\sum_c\rho(c)^2$ and $\nu(c)\propto\rho(c)^2$ presuppose a discrete $\rho$, so the class set is a countable type and expectations over classes are sums. Conditional expectations are written as ratios of sums. The spectral norm is the operator norm on Euclidean space. Sub-Gaussianity uses Mathlib's `HasSubgaussianMGF` with parameter $\sigma^2$. Pointwise separability of $\mathcal F$ is the standard measurability convention for suprema over a function class. The paper does not state it.
-- source:
--   Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, A Theoretical Analysis of Contrastive Unsupervised Representation Learning, arXiv:1902.09229v1 (2019), Section 2 (eqs. (1)-(6), Definitions 2.1-2.3), Sections 4.1-4.2 (eqs. (8)-(9)), Section 5.2, Section 6.3 (eq. (12)), Appendices A.1-A.3 and B.1

import Mathlib

/-!
Arora, Khandeparkar, Khodak, Plevrakis and Saunshi, *A Theoretical Analysis of Contrastive
Unsupervised Representation Learning*, arXiv:1902.09229v1 (2019): latent classes, similar pairs
and negative samples (Section 2, eqs. (1)-(3)), supervised and unsupervised losses
(Definitions 2.1-2.3, eqs. (4)-(6)), the Rademacher average, collision probability, class
collision losses and intraclass deviation of Section 4 (eqs. (8)-(9)), the sub-Gaussian margin quantities of
Section 5.2, the block loss of Section 6.3 (eq. (12)) and the k-negative-sample quantities of
Appendix B.1.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace ContrastiveUnsupervised

/-- Section 2: representations take values in `ℝ^d` with the Euclidean norm and inner product. -/
abbrev Rep (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Section 2 ("Evaluation Metric for Representations"): the hinge loss
`ℓ(v) = max{0, 1 + max_i (-v_i)}` of the vector `(v_i)_{i ∈ s}`; it is `0` for an empty index set
(the convention used in the proof of Theorem B.1). -/
def hingeLoss {ι : Type*} (s : Finset ι) (v : ι → ℝ) : ℝ :=
  if h : s.Nonempty then max 0 (1 + s.sup' h (fun i => -v i)) else 0

/-- Section 2 ("Evaluation Metric for Representations"): the logistic loss
`ℓ(v) = log₂(1 + ∑_i exp(-v_i))` of the vector `(v_i)_{i ∈ s}`. -/
def logisticLoss {ι : Type*} (s : Finset ι) (v : ι → ℝ) : ℝ :=
  Real.logb 2 (1 + ∑ i ∈ s, Real.exp (-v i))

/-- Section 2: the two losses considered by the paper; `hinge = true` selects the hinge loss and
`hinge = false` the logistic loss. -/
def stdLoss (hinge : Bool) {ι : Type*} (s : Finset ι) (v : ι → ℝ) : ℝ :=
  if hinge then hingeLoss s v else logisticLoss s v

/-- Section 5.2 and Appendix B.2: the hinge loss with margin `γ`,
`ℓ_γ(v) = max{0, 1 + max_i (-v_i) / γ}` (for one coordinate, `ℓ_γ(x) = (1 - x/γ)_+`). -/
def marginHingeLoss (γ : ℝ) {ι : Type*} (s : Finset ι) (v : ι → ℝ) : ℝ :=
  if h : s.Nonempty then max 0 (1 + s.sup' h (fun i => -v i) / γ) else 0

variable {X : Type*} [MeasurableSpace X] {C : Type*} {d : ℕ}

/-- Section 2 ("Latent Classes"): every latent class `c` carries a probability distribution
`D_c` on the data space `X`, and `ρ` is a probability distribution on the classes. -/
def IsLatentClassModel (D : C → Measure X) (ρ : C → ℝ) : Prop :=
  (∀ c, IsProbabilityMeasure (D c)) ∧ (∀ c, 0 ≤ ρ c) ∧ HasSum ρ 1

/-- Section 2: a representation function `f : X → ℝ^d` with `‖f(·)‖ ≤ R` (measurable, the
standing convention for taking expectations). -/
def IsBoundedRep (f : X → Rep d) (R : ℝ) : Prop :=
  Measurable f ∧ ∀ x, ‖f x‖ ≤ R

/-- Definition 2.1: the mean `μ_c = E_{x ∼ D_c}[f(x)]` of the representations of class `c`. -/
def classMean (D : C → Measure X) (f : X → Rep d) (c : C) : Rep d :=
  ∫ x, f x ∂(D c)

open Classical in
/-- Eq. (3) and Section 2: the supervised loss `L_sup(T, g) = E_{(x,c) ∼ D_T} ℓ({g(x)_c - g(x)_{c'}}_{c' ≠ c})`
of a classifier `g` (coordinates indexed by classes) on the task `T`, where
`D_T(x, c) = D_c(x) p(c)` and `p` is the label distribution of the task. -/
def supLoss (ℓ : Finset C → (C → ℝ) → ℝ) (D : C → Measure X) (T : Finset C) (p : C → ℝ)
    (g : X → C → ℝ) : ℝ :=
  ∑ c ∈ T, p c * ∫ x, ℓ (T.erase c) (fun c' => g x c - g x c') ∂(D c)

/-- Eq. (4): the supervised loss of a representation `f` on the task `T`, with the best linear
classifier `g(x) = W f(x)` (row `W c` for class `c`): `L_sup(T, f) = inf_W L_sup(T, W f)`. -/
def repSupLoss (ℓ : Finset C → (C → ℝ) → ℝ) (D : C → Measure X) (T : Finset C) (p : C → ℝ)
    (f : X → Rep d) : ℝ :=
  ⨅ W : C → Rep d, supLoss ℓ D T p (fun x c => inner ℝ (W c) (f x))

/-- Definition 2.1: the loss `L^μ_sup(T, f)` of the mean classifier `W^μ`, whose row for class `c`
is the class mean `μ_c`. -/
def meanSupLoss (ℓ : Finset C → (C → ℝ) → ℝ) (D : C → Measure X) (T : Finset C) (p : C → ℝ)
    (f : X → Rep d) : ℝ :=
  supLoss ℓ D T p (fun x c => inner ℝ (classMean D f c) (f x))

/-- Section 2: the uniform label distribution `D_T(c) = 1/|T|` on a task `T`. -/
def uniformOn (T : Finset C) : C → ℝ := fun _ => 1 / (T.card : ℝ)

/-- The probability `∏_i ρ(c_i)` of a tuple of classes drawn i.i.d. from `ρ`. -/
def tupleWeight (ρ : C → ℝ) {n : ℕ} (c : Fin n → C) : ℝ := ∏ i, ρ (c i)

open Classical in
/-- Definition 2.2: the average supervised loss on `(k+1)`-way tasks,
`L_sup(f) = E_{(c_i) ∼ ρ^{k+1}}[L_sup({c_i}, f) | c_i ≠ c_j]`, with uniform label distributions. -/
def avgSupLoss (ℓ : Finset C → (C → ℝ) → ℝ) (D : C → Measure X) (ρ : C → ℝ) (k : ℕ)
    (f : X → Rep d) : ℝ :=
  (∑' c : Fin (k + 1) → C, if Function.Injective c then
      tupleWeight ρ c * repSupLoss ℓ D (Finset.univ.image c) (uniformOn (Finset.univ.image c)) f
    else 0) /
  (∑' c : Fin (k + 1) → C, if Function.Injective c then tupleWeight ρ c else 0)

open Classical in
/-- Definition 2.2: the average supervised loss of the mean classifier on `(k+1)`-way tasks,
`L^μ_sup(f) = E_{(c_i) ∼ ρ^{k+1}}[L^μ_sup({c_i}, f) | c_i ≠ c_j]`, with uniform label
distributions. -/
def avgMeanSupLoss (ℓ : Finset C → (C → ℝ) → ℝ) (D : C → Measure X) (ρ : C → ℝ) (k : ℕ)
    (f : X → Rep d) : ℝ :=
  (∑' c : Fin (k + 1) → C, if Function.Injective c then
      tupleWeight ρ c * meanSupLoss ℓ D (Finset.univ.image c) (uniformOn (Finset.univ.image c)) f
    else 0) /
  (∑' c : Fin (k + 1) → C, if Function.Injective c then tupleWeight ρ c else 0)

/-- Eq. (1): the distribution of similar pairs, `D_sim(x, x⁺) = E_{c ∼ ρ} D_c(x) D_c(x⁺)`. -/
def simMeasure (D : C → Measure X) (ρ : C → ℝ) : Measure (X × X) :=
  Measure.sum (fun c => ENNReal.ofReal (ρ c) • (D c).prod (D c))

/-- Eq. (2): the distribution of negative samples, `D_neg(x⁻) = E_{c ∼ ρ} D_c(x⁻)`. -/
def negMeasure (D : C → Measure X) (ρ : C → ℝ) : Measure X :=
  Measure.sum (fun c => ENNReal.ofReal (ρ c) • D c)

/-- Definition 2.3: the law `D_sim × D_neg^k` of one training tuple `(x, x⁺, x⁻_1, …, x⁻_k)`
(regrouped from `((x, x⁺), x⁻)` to `(x, (x⁺, x⁻))`). -/
def tupleMeasure (D : C → Measure X) (ρ : C → ℝ) (k : ℕ) : Measure (X × X × (Fin k → X)) :=
  ((simMeasure D ρ).prod (Measure.pi fun _ : Fin k => negMeasure D ρ)).map
    MeasurableEquiv.prodAssoc

/-- Definition 2.3: the contrast scores `f(x)ᵀ(f(x⁺) - f(x⁻_i))`, `i = 1, …, k`, of a tuple. -/
def contrastScores (f : X → Rep d) {k : ℕ} (z : X × X × (Fin k → X)) : Fin k → ℝ :=
  fun i => inner ℝ (f z.1) (f z.2.1 - f (z.2.2 i))

/-- Definition 2.3, eq. (5): the unsupervised (contrastive) loss with `k` negative samples,
`L_un(f) = E[ℓ({f(x)ᵀ(f(x⁺) - f(x⁻_i))}_{i=1}^k)]`, `(x, x⁺) ∼ D_sim`, `x⁻_i ∼ D_neg` i.i.d. -/
def unsupLoss (hinge : Bool) (D : C → Measure X) (ρ : C → ℝ) (k : ℕ) (f : X → Rep d) : ℝ :=
  ∫ z, stdLoss hinge Finset.univ (contrastScores f z) ∂(tupleMeasure D ρ k)

/-- Definition 2.3, eq. (6): the empirical unsupervised loss on `M` training tuples,
`L̂_un(f) = (1/M) ∑_j ℓ({f(x_j)ᵀ(f(x⁺_j) - f(x⁻_{ji}))}_{i=1}^k)`. -/
def empUnsupLoss (hinge : Bool) (k : ℕ) (f : X → Rep d) {M : ℕ}
    (S : Fin M → X × X × (Fin k → X)) : ℝ :=
  (1 / (M : ℝ)) * ∑ j, stdLoss hinge Finset.univ (contrastScores f (S j))

/-- Section 4 and Appendix A.3: the law `(D_sim × D_neg^k)^M` of the training set
`S = {(x_j, x⁺_j, x⁻_{j1}, …, x⁻_{jk})}_{j=1}^M`. -/
def sampleMeasure (D : C → Measure X) (ρ : C → ℝ) (k M : ℕ) :
    Measure (Fin M → X × X × (Fin k → X)) :=
  Measure.pi fun _ : Fin M => tupleMeasure D ρ k

/-- The points `(x, x⁺, x⁻_1, …, x⁻_k)` of a training tuple, listed as positions `0, …, k+1`. -/
def tuplePoints {k : ℕ} (z : X × X × (Fin k → X)) : Fin (k + 2) → X :=
  Fin.cons (α := fun _ => X) z.1 (Fin.cons (α := fun _ => X) z.2.1 z.2.2)

/-- Section 4.1 and Appendix A.3: the Rademacher average
`R_S(F) = E_{σ ∼ {±1}^{(k+2)dM}}[sup_{f ∈ F} ⟨σ, f_{|S}⟩]`, where `f_{|S}` lists the coordinates
`f_t` of `f` at every point of every training tuple (`σ = true` stands for `+1`). -/
def rademacherAvg (F : Set (X → Rep d)) {k M : ℕ} (S : Fin M → X × X × (Fin k → X)) : ℝ :=
  (1 / (2 : ℝ) ^ (M * (k + 2) * d)) *
    ∑ σ : Fin M → Fin (k + 2) → Fin d → Bool,
      ⨆ f : F, ∑ j, ∑ p, ∑ t, (if σ j p t then (1 : ℝ) else -1) * (f.1 (tuplePoints (S j) p)) t

/-- Section 4.1 and Appendix A.3: the generalization error term
`Gen_M = K (R √k R_S(F)/M + (R² + log k) √(log(1/δ)/M))`, with the constant `K` of the `O(·)`
made explicit; for `k = 1` this is `K (R R_S(F)/M + R² √(log(1/δ)/M))`. -/
def genError (K R : ℝ) (k M : ℕ) (rad δ : ℝ) : ℝ :=
  K * (R * Real.sqrt k * rad / M + (R ^ 2 + Real.log k) * Real.sqrt (Real.log (1 / δ) / M))

/-- Standing measurability convention for the function class (pointwise separability, the usual
condition making suprema over `F` countable suprema): a countable `F₀ ⊆ F` such that every
`f ∈ F` is a pointwise limit of a sequence in `F₀`. -/
def IsPointwiseSeparable (F : Set (X → Rep d)) : Prop :=
  ∃ F₀ ⊆ F, F₀.Countable ∧ ∀ f ∈ F, ∃ u : ℕ → X → Rep d, (∀ n, u n ∈ F₀) ∧
    ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))

/-- Section 4.1: `τ = P_{c, c' ∼ ρ²}(c = c') = ∑_c ρ(c)²`, the probability that two independent
classes coincide. -/
def collisionProb (ρ : C → ℝ) : ℝ := ∑' c, ρ c ^ 2

/-- The law of `(x, x⁺, x⁻_1, …, x⁻_k)` given the classes: `x, x⁺ ∼ D_{c⁺}`, `x⁻_i ∼ D_{c⁻_i}`,
all independent. -/
def classTupleMeasure (D : C → Measure X) (k : ℕ) (cp : C) (cn : Fin k → C) :
    Measure (X × X × (Fin k → X)) :=
  (D cp).prod ((D cp).prod (Measure.pi fun i => D (cn i)))

/-- Section 4.2 and Appendix A.1: the unsupervised loss given the classes `c⁺, c⁻_1, …, c⁻_k`,
keeping only the negative samples with index in `I`:
`E[ℓ({f(x)ᵀ(f(x⁺) - f(x⁻_i))}_{i ∈ I})]`. -/
def condUnsupLoss (hinge : Bool) (D : C → Measure X) (k : ℕ) (f : X → Rep d) (cp : C)
    (cn : Fin k → C) (I : Finset (Fin k)) : ℝ :=
  ∫ z, stdLoss hinge I (contrastScores f z) ∂(classTupleMeasure D k cp cn)

/-- Section 4.2: `L^=_un(f) = E_{c ∼ ν, x, x⁺, x⁻ ∼ D_c³}[ℓ(f(x)ᵀ(f(x⁺) - f(x⁻)))]` with
`ν(c) ∝ ρ(c)²` (one negative sample). -/
def unsupLossEq (hinge : Bool) (D : C → Measure X) (ρ : C → ℝ) (f : X → Rep d) : ℝ :=
  (∑' c, ρ c ^ 2 * condUnsupLoss hinge D 1 f c (fun _ => c) Finset.univ) / collisionProb ρ

/-- Section 4.2: `Σ(f, c)`, the covariance matrix of `f(x)` for `x ∼ D_c`. -/
def classCov (D : C → Measure X) (f : X → Rep d) (c : C) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∫ x, (f x i - classMean D f c i) * (f x j - classMean D f c j) ∂(D c)

/-- Section 4.2: the spectral norm `‖A‖₂` (operator norm on Euclidean space). -/
def specNorm (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- Section 4.2, eq. (9): the intraclass deviation
`s(f) = E_{c ∼ ν}[√‖Σ(f, c)‖₂ E_{x ∼ D_c}‖f(x)‖]` with `ν(c) ∝ ρ(c)²`. -/
def intraclassDeviation (D : C → Measure X) (ρ : C → ℝ) (f : X → Rep d) : ℝ :=
  (∑' c, ρ c ^ 2 * (Real.sqrt (specNorm (classCov D f c)) * ∫ x, ‖f x‖ ∂(D c))) /
    collisionProb ρ

/-- Section 5.2 (footnote 6, Appendix A.2): `f(X)`, `X ∼ D_c`, is `σ²`-sub-Gaussian in every
direction for every class `c`: for every unit `u`, `E[exp(λ uᵀ(f(X) - μ_c))] ≤ exp(λ²σ²/2)` for
all real `λ`. -/
def IsSubGaussianRep (D : C → Measure X) (f : X → Rep d) (σ : ℝ) : Prop :=
  ∀ c, ∀ u : Rep d, ‖u‖ = 1 →
    ProbabilityTheory.HasSubgaussianMGF (fun x => inner ℝ u (f x - classMean D f c))
      (Real.toNNReal (σ ^ 2)) (D c)

/-- Appendix A.2 (proof of Lemma 5.1): the margin
`γ = 1 + 2Rσ √(2 log R + log(3/ε))` for `R ≥ 1`, and `γ = 1 + 2Rσ √(log(3/ε))` for `R < 1`
(footnote 7). -/
def subGaussianMargin (R σ ε : ℝ) : ℝ :=
  if 1 ≤ R then 1 + 2 * R * σ * Real.sqrt (2 * Real.log R + Real.log (3 / ε))
  else 1 + 2 * R * σ * Real.sqrt (Real.log (3 / ε))

/-- Section 6.3: the law of a positive block `x, x⁺_1, …, x⁺_b ∼ D_{c⁺}` and a negative block
`x⁻_1, …, x⁻_b ∼ D_{c⁻}`, all independent. -/
def blockMeasure (D : C → Measure X) (b : ℕ) (cp cn : C) :
    Measure (X × (Fin b → X) × (Fin b → X)) :=
  (D cp).prod ((Measure.pi fun _ : Fin b => D cp).prod (Measure.pi fun _ : Fin b => D cn))

/-- Section 6.3, eq. (12): the block loss
`L^block_un(f) = E[ℓ(f(x)ᵀ((1/b)∑_i f(x⁺_i) - (1/b)∑_i f(x⁻_i)))]`, `c⁺, c⁻ ∼ ρ²`. -/
def blockUnsupLoss (hinge : Bool) (D : C → Measure X) (ρ : C → ℝ) (b : ℕ) (f : X → Rep d) : ℝ :=
  ∑' cp, ∑' cn, ρ cp * ρ cn *
    ∫ z, stdLoss hinge (Finset.univ : Finset (Fin 1)) (fun _ => inner ℝ (f z.1)
        ((1 / (b : ℝ)) • ∑ i, f (z.2.1 i) - (1 / (b : ℝ)) • ∑ i, f (z.2.2 i)))
      ∂(blockMeasure D b cp cn)

open Classical in
/-- Appendix B.1: `I⁺(c⁻_1, …, c⁻_k) = {i ∈ [k] : c⁻_i = c⁺}`. -/
def collisionIdx {k : ℕ} (cp : C) (cn : Fin k → C) : Finset (Fin k) :=
  Finset.univ.filter (fun i => cn i = cp)

open Classical in
/-- Appendix B.1: `Q(c⁺, c⁻_1, …, c⁻_k)`, the set of distinct classes of the tuple. -/
def tupleClasses {k : ℕ} (cp : C) (cn : Fin k → C) : Finset C :=
  insert cp (Finset.univ.image cn)

open Classical in
/-- The probability of an event about `(c⁺, c⁻_1, …, c⁻_k) ∼ ρ^{k+1}`. -/
def tupleProb (ρ : C → ℝ) (k : ℕ) (E : C → (Fin k → C) → Prop) : ℝ :=
  ∑' cp, ∑' cn : Fin k → C, if E cp cn then ρ cp * tupleWeight ρ cn else 0

/-- Appendix B.1: `τ_k = P[I⁺ ≠ ∅]` for `(c⁺, c⁻_1, …, c⁻_k) ∼ ρ^{k+1}`. -/
def tauK (ρ : C → ℝ) (k : ℕ) : ℝ :=
  tupleProb ρ k (fun cp cn => (collisionIdx cp cn).Nonempty)

/-- Appendix B.1: `τ' = P[c⁺ = c⁻_i for all i]`. -/
def tauAll (ρ : C → ℝ) (k : ℕ) : ℝ :=
  tupleProb ρ k (fun cp cn => ∀ i, cn i = cp)

open Classical in
/-- Section 4.2 (`k = 1`) and Appendix B.1: `L^≠_un(f)`, the unsupervised loss conditioned on
`|I⁺| < k` with the negative samples of index in `I⁺` removed,
`E[ℓ({f(x)ᵀ(f(x⁺) - f(x⁻_i))}_{i ∉ I⁺}) | |I⁺| < k]`. -/
def unsupLossNeq (hinge : Bool) (D : C → Measure X) (ρ : C → ℝ) (k : ℕ) (f : X → Rep d) : ℝ :=
  (∑' cp, ∑' cn : Fin k → C, if (collisionIdx cp cn).card < k then
      ρ cp * tupleWeight ρ cn *
        condUnsupLoss hinge D k f cp cn (Finset.univ.filter (fun i => cn i ≠ cp))
    else 0) /
  tupleProb ρ k (fun cp cn => (collisionIdx cp cn).card < k)

open Classical in
/-- Appendix B.1: `ρ⁺_min(T) = min_{c ∈ T} P(c⁺ = c | Q = T, I⁺ = ∅)`. -/
def rhoPlusMin (ρ : C → ℝ) (k : ℕ) (T : Finset C) : ℝ :=
  if h : T.Nonempty then
    T.inf' h (fun c =>
      tupleProb ρ k (fun cp cn => cp = c ∧ tupleClasses cp cn = T ∧ collisionIdx cp cn = ∅) /
        tupleProb ρ k (fun cp cn => tupleClasses cp cn = T ∧ collisionIdx cp cn = ∅))
  else 0

/-- Appendix B.1: `p_max(T) = max_{c ∈ T} D_T(c)`. -/
def pMax (T : Finset C) (p : C → ℝ) : ℝ :=
  if h : T.Nonempty then T.sup' h p else 0

/-- Appendix B.1: a label distribution `D_T` on every nonempty task `T`. -/
def IsTaskDistFamily (pT : Finset C → C → ℝ) : Prop :=
  ∀ T : Finset C, T.Nonempty → (∀ c, 0 ≤ pT T c) ∧ ∑ c ∈ T, pT T c = 1

open Classical in
/-- Appendix B.1: `E_{T ∼ 𝒟}[ρ⁺_min(T)/p_max(T) · L^μ_sup(T, f)]`, where `T ∼ 𝒟` is the set of
distinct classes of `(c⁺, c⁻_1, …, c⁻_k) ∼ ρ^{k+1}` conditioned on `I⁺ = ∅` (Section 6.1), and
the task `T` has label distribution `D_T = pT T`. -/
def weightedTaskMeanSupLoss (ℓ : Finset C → (C → ℝ) → ℝ) (D : C → Measure X) (ρ : C → ℝ)
    (k : ℕ) (pT : Finset C → C → ℝ) (f : X → Rep d) : ℝ :=
  (∑' cp, ∑' cn : Fin k → C, if collisionIdx cp cn = ∅ then
      ρ cp * tupleWeight ρ cn *
        (rhoPlusMin ρ k (tupleClasses cp cn) /
            pMax (tupleClasses cp cn) (pT (tupleClasses cp cn)) *
          meanSupLoss ℓ D (tupleClasses cp cn) (pT (tupleClasses cp cn)) f)
    else 0) /
  tupleProb ρ k (fun cp cn => collisionIdx cp cn = ∅)

end ContrastiveUnsupervised


