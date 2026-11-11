-- Prove2me | Definitions.Def_GMMIsoSample_Main_Model
-- name    : GMMIsoSample_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:31:16.644964+00:00
-- url     : https://prove2.me/theorems/556eb967-e1a9-4496-9f19-c6ac53a32d78
-- title:
--   Spherical Gaussian mixtures, normalized separation, d_iso and ε-density estimation up to isometry (§1.2, Definition 1, §3)
-- statement:
--   Work in $\mathbb R^d$ (`E d`). For $m\in\mathbb R^d$ and $\sigma\in\mathbb R$, `gauss m σ` is the spherical Gaussian $N(m,\sigma^2 I_d)$. A $k$-component **parameter tuple** $p$ assigns to each component $i\in\{0,\dots,k-1\}$ a weight $w_i$, a radius $\sigma_i$ and a mean $\mu_i$; the **mixture** is
--   $$\mathrm{Mix}(\bar\mu,\bar\sigma,\bar w)=\sum_{i}w_iN(\mu_i,\sigma_i^2I_d),$$
--   and `labeledMix p` is the joint law of (component label, point). For a set $I$ of components, $D_I$ (`condMix`) is the mixture conditioned on the label lying in $I$, with weights $w_i/\sum_{j\in I}w_j$.
--
--   The **normalized separation** of components $i\ne j$ is $\|\mu_i-\mu_j\|/\sqrt{\sigma_i^2+\sigma_j^2}$, and $\Gamma(D)\ge\Gamma$ means every pair of distinct components has normalized separation at least $\Gamma$ (vacuous for $k=1$). The **target class** $\mathcal D(d,k_{\max},w_{\min},\Gamma_{\min})$ consists of tuples with $1\le k\le k_{\max}$, weights $\ge w_{\min}$ summing to $1$, positive radii and $\Gamma(D)\ge\Gamma_{\min}$.
--
--   With $d_{TV}$ the total variation distance, $d_{iso}(P,Q)=\inf_{\tau}d_{TV}(P,\tau(Q))$ over all Euclidean isometries $\tau$ of $\mathbb R^d$ (pushforward), and $d_{iso}(F_0,F_1)=\inf_{P\in F_0,Q\in F_1}d_{iso}(P,Q)\in[0,\infty]$. $D^{\otimes T}$ (`iidLaw`) is the law of $T$ i.i.d. draws.
--
--   A hypothesis $h$ is **$\varepsilon$-good** for $D$ if it is a valid mixture (nonnegative weights summing to 1, positive radii; at most $k_{\max}$ components) and some isometry $\tau$ has $d_{TV}(D,\mathrm{Mix}(\tau(\hat\mu),\hat\sigma,\hat w))\le\varepsilon$. A randomized **estimator** using $T$ samples is a Markov kernel $K$ from $(\mathbb R^d)^T$ to hypotheses; it **succeeds** on $D$ if, over $T$ i.i.d. draws from $D$ and its randomness, the output fails to be $\varepsilon$-good with probability at most $1/10$; `IsEstimator` asks this for every target in the class (Definition 1), and `IsEstimatorEqualUnit` only for the equal-weight, unit-radius targets. `rateTwo` and `rateMany` are the rates $\min\{d,1+d/\Gamma^4+\sqrt d/\Gamma\}$ and $\min\{d,d/\Gamma^4+\sqrt d\}$ of Theorem 2, and `avgPerm` averages over a uniformly random permutation.
--
--   **Formalization Note.** Components are 0-based (`Fin k`). Hypotheses with $\hat k\le k_{\max}$ components are $k_{\max}$-slot tuples whose unused slots have weight 0. Failure probabilities are written as measures of failure sets (outer measure for a non-measurable set). `iidLaw` is the zero measure on non-probability measures, which never occur as arguments.
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 2, §1.2 and Definition 1; p. 3 (N_kmax, Theorem 2); p. 13, (11)–(12); p. 35 (D_I)

import Mathlib
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-!
# Spherical Gaussian mixtures, normalized separation, d_iso, randomized estimators

Chen, De, Lee, Servedio, *Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to
Isometry*, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 2 (§1.2,
Definition 1), p. 3 (N_kmax), p. 13 ((11)–(12)), p. 63 ((104)).

* `E d` is `ℝ^d` (`EuclideanSpace ℝ (Fin d)`); `gauss m σ` is `N(m, σ² I_d)` (Mathlib's
  `multivariateGaussian` with covariance `σ² • 1`, which is positive semidefinite).
* A `k`-component parameter tuple `p : Params d k` lists, for each component `i : Fin k`
  (0-based), its mixing weight `wt p i`, radius `rad p i` and mean `ctr p i`; `mix p` is
  `Mix(μ̄, σ̄, w̄) = Σ_i w_i N(μ_i, σ_i² I_d)`. `labeledMix p` is the joint law of the latent
  component label and the sample point (label `i` with probability `w_i`, then `N(μ_i, σ_i² I_d)`).
* A hypothesis with `1 ≤ k̂ ≤ kmax` components is encoded as a `kmax`-slot tuple whose unused slots
  carry weight `0` (`IsValidParams`: nonnegative weights summing to `1`, positive radii).
* `iidLaw D T` is `D^{⊗T}`, the law of `T` i.i.d. draws, for a probability measure `D`.
* A randomized estimator using `T` samples is a Markov kernel from `(ℝ^d)^T` to hypothesis
  tuples (its internal randomness is the kernel). Failure probabilities are written as "the
  measure of the failure set is at most p"; for a set that is not measurable this is its outer
  measure, the strongest reading.
-/

/-- `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The spherical Gaussian `N(m, σ² I_d)`. -/
noncomputable def gauss {d : ℕ} (m : E d) (σ : ℝ) : Measure (E d) :=
  multivariateGaussian m (σ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ))

/-- A `k`-component parameter tuple: component `i` has weight `(p i).1`, radius `(p i).2.1` and
mean `(p i).2.2`. -/
abbrev Params (d k : ℕ) := Fin k → ℝ × ℝ × E d

/-- Mixing weight `w_i`. -/
def wt {d k : ℕ} (p : Params d k) (i : Fin k) : ℝ := (p i).1

/-- Radius `σ_i`. -/
def rad {d k : ℕ} (p : Params d k) (i : Fin k) : ℝ := (p i).2.1

/-- Mean vector `μ_i`. -/
def ctr {d k : ℕ} (p : Params d k) (i : Fin k) : E d := (p i).2.2

/-- The mixture `Mix(μ̄, σ̄, w̄) = Σ_i w_i N(μ_i, σ_i² I_d)`. -/
noncomputable def mix {d k : ℕ} (p : Params d k) : Measure (E d) :=
  ∑ i, ENNReal.ofReal (wt p i) • gauss (ctr p i) (rad p i)

/-- The joint law of (latent component label, sample point) under the mixture `p`. -/
noncomputable def labeledMix {d k : ℕ} (p : Params d k) : Measure (Fin k × E d) :=
  ∑ i, ENNReal.ofReal (wt p i) • (Measure.dirac i).prod (gauss (ctr p i) (rad p i))

/-- Total mixing weight `Σ_{i ∈ I} w_i` of a set `I` of components. -/
def weightOf {d k : ℕ} (p : Params d k) (I : Finset (Fin k)) : ℝ := ∑ i ∈ I, wt p i

/-- `D_I`: the mixture conditioned on the component lying in `I` (§5.1, p. 35),
`Σ_{i ∈ I} (w_i / Σ_{j ∈ I} w_j) N(μ_i, σ_i² I_d)`. -/
noncomputable def condMix {d k : ℕ} (p : Params d k) (I : Finset (Fin k)) : Measure (E d) :=
  ∑ i ∈ I, ENNReal.ofReal (wt p i / weightOf p I) • gauss (ctr p i) (rad p i)

/-- Joint law of (label, point) under `D_I`. -/
noncomputable def condLabeledMix {d k : ℕ} (p : Params d k) (I : Finset (Fin k)) :
    Measure (Fin k × E d) :=
  ∑ i ∈ I, ENNReal.ofReal (wt p i / weightOf p I) •
    (Measure.dirac i).prod (gauss (ctr p i) (rad p i))

/-- Normalized separation of components `i, j`: `‖μ_i − μ_j‖ / √(σ_i² + σ_j²)`. -/
noncomputable def normSep {d k : ℕ} (p : Params d k) (i j : Fin k) : ℝ :=
  ‖ctr p i - ctr p j‖ / Real.sqrt (rad p i ^ 2 + rad p j ^ 2)

/-- `Γ(D) ≥ Γ`: every pair of distinct components has normalized separation at least `Γ`
(`Γ(D) = min_{i<j} Δ_{ij}/√(σ_i²+σ_j²)`; vacuous when `k = 1`). -/
def SepAtLeast {d k : ℕ} (p : Params d k) (Γ : ℝ) : Prop :=
  ∀ i j : Fin k, i ≠ j → Γ ≤ normSep p i j

/-- The target class `𝒟(d, kmax, wmin, Γmin)` (§1.2): `1 ≤ k ≤ kmax` components, weights
`≥ wmin` summing to `1`, positive radii, `Γ(D) ≥ Γmin`. -/
def IsTarget {d k : ℕ} (kmax : ℕ) (wmin Γmin : ℝ) (p : Params d k) : Prop :=
  1 ≤ k ∧ k ≤ kmax ∧ (∀ i, wmin ≤ wt p i) ∧ ∑ i, wt p i = 1 ∧ (∀ i, 0 < rad p i) ∧
    SepAtLeast p Γmin

/-- A valid mixture parameter tuple: nonnegative weights summing to `1`, positive radii. As a
hypothesis in `Params d kmax`, it is a mixture of between `1` and `kmax` spherical Gaussians
(slots of weight `0` are absent components). -/
def IsValidParams {d k : ℕ} (p : Params d k) : Prop :=
  (∀ i, 0 ≤ wt p i) ∧ ∑ i, wt p i = 1 ∧ ∀ i, 0 < rad p i

/-- `τ(μ̂)`: apply a map to every mean, keeping weights and radii. -/
def mapCtr {d k : ℕ} (τ : E d → E d) (p : Params d k) : Params d k :=
  fun i => ((p i).1, (p i).2.1, τ (p i).2.2)

/-- `d_iso(P, Q) = inf_{τ ∈ Iso(ℝ^d)} d_TV(P, τ(Q))` (p. 13), `τ(Q)` the pushforward. -/
noncomputable def diso {d : ℕ} (P Q : Measure (E d)) : ℝ :=
  ⨅ τ : E d ≃ᵢ E d, PolySampIso.tvDist P (Q.map τ)

/-- `d_iso(F₀, F₁) = inf_{P ∈ F₀, Q ∈ F₁} d_iso(P, Q)` (12), valued in `[0, ∞]` so that the
infimum over an empty family is `∞`. -/
noncomputable def disoFam {d : ℕ} (F₀ F₁ : Set (Measure (E d))) : ℝ≥0∞ :=
  ⨅ P ∈ F₀, ⨅ Q ∈ F₁, ENNReal.ofReal (diso P Q)

/-- `D^{⊗T}`: the law of `T` i.i.d. draws from a probability measure `D` (the zero measure if `D`
is not a probability measure; never used in that case). -/
noncomputable def iidLaw {α : Type*} [MeasurableSpace α] (D : Measure α) (T : ℕ) :
    Measure (Fin T → α) :=
  open Classical in
  if h : IsProbabilityMeasure D then
    haveI := h
    Measure.pi (fun _ : Fin T => D)
  else 0

/-- A hypothesis `h` is `ε`-good for `D` (Definition 1): it is a valid mixture of at most `kmax`
spherical Gaussians and some Euclidean isometry `τ` has `d_TV(D, Mix(τ(μ̂), σ̂, ŵ)) ≤ ε`. -/
def GoodHyp {d kmax : ℕ} (ε : ℝ) (D : Measure (E d)) (h : Params d kmax) : Prop :=
  IsValidParams h ∧ ∃ τ : E d ≃ᵢ E d, PolySampIso.tvDist D (mix (mapCtr τ h)) ≤ ε

/-- The randomized estimator `K` (a kernel from `T` sample points to hypotheses) succeeds on `D`:
the probability, over `T` i.i.d. draws from `D` and the estimator's randomness, that its output is
not `ε`-good is at most `1/10`. -/
def Succeeds {d kmax : ℕ} (ε : ℝ) (T : ℕ) (K : Kernel (Fin T → E d) (Params d kmax))
    (D : Measure (E d)) : Prop :=
  (iidLaw D T).bind K {h | ¬ GoodHyp ε D h} ≤ 1 / 10

/-- `K` is an `ε`-density estimator up to isometry for `𝒟(d, kmax, wmin, Γmin)` using `T` sample
points (Definition 1): a Markov kernel that succeeds on every target in the class. -/
def IsEstimator (d kmax : ℕ) (wmin Γmin ε : ℝ) (T : ℕ)
    (K : Kernel (Fin T → E d) (Params d kmax)) : Prop :=
  IsMarkovKernel K ∧
    ∀ (k : ℕ) (p : Params d k), IsTarget kmax wmin Γmin p → Succeeds ε T K (mix p)

/-- Equal weights `1/k` and unit radii. -/
def IsEqualWeightUnit {d k : ℕ} (p : Params d k) : Prop :=
  ∀ i, wt p i = 1 / (k : ℝ) ∧ rad p i = 1

/-- `K` succeeds on every equal-weight, unit-radius target of `𝒟(d, kmax, wmin, Γmin)` (the
restricted class of the lower bounds, Propositions 53, 54, 57). Every `IsEstimator` satisfies it. -/
def IsEstimatorEqualUnit (d kmax : ℕ) (wmin Γmin ε : ℝ) (T : ℕ)
    (K : Kernel (Fin T → E d) (Params d kmax)) : Prop :=
  IsMarkovKernel K ∧
    ∀ (k : ℕ) (p : Params d k), IsTarget kmax wmin Γmin p → IsEqualWeightUnit p →
      Succeeds ε T K (mix p)

/-- `f(d, Γ) = min{d, 1 + d/Γ⁴ + √d/Γ}` of (1). -/
noncomputable def rateTwo (d : ℕ) (Γ : ℝ) : ℝ :=
  min (d : ℝ) (1 + d / Γ ^ 4 + Real.sqrt d / Γ)

/-- `f(d, Γ) = min{d, d/Γ⁴ + √d}` of (2). -/
noncomputable def rateMany (d : ℕ) (Γ : ℝ) : ℝ :=
  min (d : ℝ) (d / Γ ^ 4 + Real.sqrt d)

/-- Average of `f` over a uniformly random permutation of `Fin n` (the algorithms' internal
randomness: uniformly random subsets, pairings and partitions are read off a uniform
permutation). -/
noncomputable def avgPerm (n : ℕ) (f : Equiv.Perm (Fin n) → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ π, f π) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)

end GMMIsoSample.Main


