-- Prove2me | Definitions.Def_InhomMJPStrong_J1_Model
-- name    : InhomMJPStrong_J1_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:08.656493+00:00
-- url     : https://prove2.me/theorems/8fddfc31-4856-44ee-8ffe-ad948ffd3180
-- title:
--   Intensity matrices, coupled Poisson grids, jump paths, the J1 metric, and the time change
-- statement:
--   Let $\mathcal E$ be a nonempty finite state space, and let $\Lambda(t)$ be an intensity matrix function: its entries are measurable and locally integrable, off-diagonal entries are nonnegative, diagonal entries are nonpositive, and every row sum is nonpositive. Under Condition 1, its diagonal rates are uniformly bounded. Set
--
--   $$
--   \lambda_0=\left\lceil\sup_{i\in\mathcal E,\,t\ge0}|\Lambda_{ii}(t)|\right\rceil.
--   $$
--
--   Step (1) supplies independent rate-$\lambda_0$ Poisson clocks $\mathcal N,\mathcal M$, independent unit-rate clocks indexed by $k>\lambda_0$, and independent uniforms $U_\ell$. Their superpositions provide inspection times $\chi^{(n)}_\ell$ and observation times $\theta^{(n)}_\ell$. An inverse-CDF draw from the initial distribution $\alpha$ starts $\mathcal J$; at inspection time $\chi_\ell$, its transition weights are $\delta_{ij}+\lambda_0^{-1}\Lambda_{ij}(\chi_\ell)$. The remaining probability terminates the path at an absorbing cemetery state. The approximation $J^{(n)}$ reads $\mathcal J(\chi^{(n)}_\ell)$ and places this value on $[\theta^{(n)}_\ell,\theta^{(n)}_{\ell+1})$.
--
--   The file also defines the paper's $J_1$ distance: the infimum over homeomorphic time changes of the maximum of a weighted sum of state mismatches on $[0,c_k]$ and the largest time displacement. Finally it defines the piecewise-linear time change $\Delta_n$ of (12), the cutoff $\lfloor n^{1+\varepsilon}\rfloor$, and $\kappa(q,\varepsilon)=4e^{1/2+\varepsilon/2+2q}$. These definitions support the rate theorem and its grid lemmas.
--
--   **Formalization Note** The cemetery state is `none` in `Option (Fin p)`; paths are functions on nonnegative reals. The inverse-CDF intervals correct the one-state index shift printed in (4) and in the initial draw. Superposition counts use `Set.ncard`, which returns zero on an infinite set; this value occurs only on null sample paths under the stated Poisson laws. The metric takes values in extended nonnegative reals, preserving unbounded suprema. At $n<\lambda_0$ the superposition is a placeholder; every finite-$n$ theorem assumes $n\ge\lambda_0$, and the asymptotic theorems are unaffected.
-- source:
--   Bladt & Peralta, Strongly convergent homogeneous approximations to inhomogeneous Markov jump processes and applications, arXiv:2204.02954v3, pp. 3, 5–6, 8–9, Condition 1, (3)–(5), (12)

import Mathlib

namespace InhomMJPStrong.J1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- An intensity matrix function as defined on p. 3. -/
structure IsIntensityFn {p : ℕ} (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ) : Prop where
  measurable : ∀ i j, Measurable (fun t : Set.Ici (0 : ℝ) => Lam (t : ℝ) i j)
  locInt : ∀ i j (T : ℝ), IntegrableOn (fun t => Lam t i j) (Set.Icc 0 T)
  diag_nonpos : ∀ t, 0 ≤ t → ∀ i, Lam t i i ≤ 0
  offdiag_nonneg : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Lam t i j
  rowSum_nonpos : ∀ t, 0 ≤ t → ∀ i, ∑ j, Lam t i j ≤ 0

/-- Condition 1 on p. 5: the diagonal rates are uniformly bounded. -/
def Condition1 {p : ℕ} (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ) : Prop :=
  BddAbove {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|}

/-- The ceiling of the diagonal-rate supremum, exactly as on p. 5. -/
noncomputable def lam0 {p : ℕ} (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ) : ℕ :=
  ⌈sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|}⌉₊

/-- Independent source coordinates: the base clocks, unit-rate extra clocks, and uniforms. -/
inductive Src
  | gapN (i : ℕ) | gapM (i : ℕ) | gapNh (k i : ℕ) | gapMh (k i : ℕ) | unif (l : ℕ)
  deriving DecidableEq

/-- Exactly the source coordinates used when the base rate is `rate`. -/
def Relevant (rate : ℕ) : Src → Prop
  | .gapN _ | .gapM _ | .unif _ => True
  | .gapNh k _ | .gapMh k _ => rate < k

/-- The joint law of the ingredients in Step (1), pp. 5–6. -/
structure IsUnifSetup {Ω : Type*} [MeasurableSpace Ω] (rate : ℕ) (X : Src → Ω → ℝ)
    (P : Measure Ω) : Prop where
  indep : iIndepFun (fun s : {s : Src // Relevant rate s} => X s.1) P
  gapN : ∀ i, HasLaw (X (.gapN i)) (expMeasure rate) P
  gapM : ∀ i, HasLaw (X (.gapM i)) (expMeasure rate) P
  gapNh : ∀ k, rate < k → ∀ i, HasLaw (X (.gapNh k i)) (expMeasure 1) P
  gapMh : ∀ k, rate < k → ∀ i, HasLaw (X (.gapMh k i)) (expMeasure 1) P
  unif : ∀ l, HasLaw (X (.unif l)) (volume.restrict (Set.Icc (0 : ℝ) 1)) P

/-- Arrival time zero is zero; subsequent times are partial sums of gaps. -/
def arrival (g : ℕ → ℝ) (l : ℕ) : ℝ := ∑ i ∈ Finset.range l, g i

/-- Number of positive-index arrivals by time `t`. Infinite sets receive Lean's junk value zero. -/
noncomputable def count (T : ℕ → ℝ) (t : ℝ) : ℕ :=
  {l : ℕ | 1 ≤ l ∧ T l ≤ t}.ncard

/-- Base count plus counts of all clocks indexed between `rate + 1` and `n`. -/
noncomputable def supCount (rate n : ℕ) (base : ℕ → ℝ) (extra : ℕ → ℕ → ℝ)
    (t : ℝ) : ℕ :=
  count (arrival base) t + ∑ k ∈ Finset.Ioc rate n, count (arrival (extra k)) t

/-- The `l`-th arrival of a counting process, with the zeroth arrival fixed at zero. -/
noncomputable def arrivalOf (N : ℝ → ℕ) (l : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ l ≤ N t}

/-- Inspection-grid arrivals `χ⁽ⁿ⁾`. -/
noncomputable def chi {Ω : Type*} (rate n : ℕ) (X : Src → Ω → ℝ) (ω : Ω) : ℕ → ℝ :=
  arrivalOf (supCount rate n (fun i => X (.gapN i) ω)
    (fun k i => X (.gapNh k i) ω))

/-- Observation-grid arrivals `θ⁽ⁿ⁾`. -/
noncomputable def theta {Ω : Type*} (rate n : ℕ) (X : Src → Ω → ℝ) (ω : Ω) : ℕ → ℝ :=
  arrivalOf (supCount rate n (fun i => X (.gapM i) ω)
    (fun k i => X (.gapMh k i) ω))

/-- The inverse-CDF sampler: the first state whose cumulative weight exceeds `u`, or termination. -/
noncomputable def pick {p : ℕ} (w : Fin p → ℝ) (u : ℝ) : Option (Fin p) :=
  let S := Finset.univ.filter (fun k : Fin p => u < ∑ j ∈ Finset.Iic k, w j)
  if h : S.Nonempty then some (S.min' h) else none

/-- Uniformized embedded chain of `𝒥`, with termination absorbing, equation (4). -/
noncomputable def chain {p : ℕ} (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (rate : ℕ) (alpha : Fin p → ℝ) (T U : ℕ → ℝ) : ℕ → Option (Fin p)
  | 0 => pick alpha (U 0)
  | l + 1 => (chain Lam rate alpha T U l).bind fun i =>
      pick (fun j => (if i = j then 1 else 0) + Lam (T (l + 1)) i j / (rate : ℝ))
        (U (l + 1))

/-- The uniformized inhomogeneous process `𝒥` of Step (1). -/
noncomputable def procJ {p : ℕ} {Ω : Type*}
    (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ) (alpha : Fin p → ℝ)
    (X : Src → Ω → ℝ) (ω : Ω) : ℝ≥0 → Option (Fin p) := fun t =>
  chain Lam (lam0 Lam) alpha (arrival (fun i => X (.gapN i) ω))
    (fun l => X (.unif l) ω)
    (count (arrival (fun i => X (.gapN i) ω)) (t : ℝ))

/-- The approximation `J⁽ⁿ⁾`: observe `𝒥` on the `χ⁽ⁿ⁾` grid and place those values on `θ⁽ⁿ⁾`, equation (5). -/
noncomputable def procJn {p : ℕ} {Ω : Type*}
    (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ) (alpha : Fin p → ℝ)
    (X : Src → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0 → Option (Fin p) := fun t =>
  procJ Lam alpha X ω (Real.toNNReal
    (chi (lam0 Lam) n X ω
      (supCount (lam0 Lam) n (fun i => X (.gapM i) ω)
        (fun k i => X (.gapMh k i) ω) (t : ℝ))))

/-- Metric (3), in extended nonnegative reals so every supremum has its actual value. -/
noncomputable def dJ1 {p : ℕ} (c : ℕ → ℝ)
    (y z : ℝ≥0 → Option (Fin p)) : ℝ≥0∞ :=
  ⨅ D : ℝ≥0 ≃ₜ ℝ≥0,
    max (∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) *
      ⨆ (s : ℝ≥0) (_ : (s : ℝ) ≤ c (k + 1)),
        (if y (D s) = z s then (0 : ℝ≥0∞) else 1))
      (⨆ s : ℝ≥0, edist (D s) s)

/-- The explicit constant fixed in the proof of Lemma 1 on p. 9. -/
noncomputable def kappa (q eps : ℝ) : ℝ :=
  4 * Real.exp (1 / 2 + eps / 2 + 2 * q)

/-- The integer cutoff `⌊n^(1+ε)⌋` used in Lemma 1 and Theorem 3. -/
noncomputable def gridSize (n : ℕ) (eps : ℝ) : ℕ :=
  ⌊(n : ℝ) ^ (1 + eps)⌋₊

/-- Largest absolute difference at indices `1, …, m`; zero for the empty exceptional range. -/
noncomputable def maxGap (T U : ℕ → ℝ) (m : ℕ) : ℝ :=
  if h : (Finset.Icc 1 m).Nonempty then
    (Finset.Icc 1 m).sup' h (fun l => |T l - U l|)
  else 0

/-- Piecewise linear time change (12); the final branch has slope one. -/
noncomputable def timeChange (χ θ : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  if χ m ≤ t then θ m + (t - χ m)
  else
    let l := count χ t
    θ l + (t - χ l) * (θ (l + 1) - θ l) / (χ (l + 1) - χ l)

end InhomMJPStrong.J1


