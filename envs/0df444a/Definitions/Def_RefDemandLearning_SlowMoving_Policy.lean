-- Prove2me | Definitions.Def_RefDemandLearning_SlowMoving_Policy
-- name    : RefDemandLearning_SlowMoving_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:23:37.102986+00:00
-- url     : https://prove2.me/theorems/4664b47f-358e-4ca4-86b4-be0fbbafe470
-- title:
--   The clipped two-block slow-moving policy and its causal run
-- statement:
--   For the known parameter bounds, choose $0<c_0<2^{-3/4}(u-\ell)$ and initial estimates $(a_0,b_0)$ in the respective intercept and slope intervals. Episode $i\ge1$ starts after $2^{i+1}-4$ observations and has two blocks of $n_i=2^i$ periods. Its perturbation is $\delta_i=c_0 2^{-i/4}$. Given the preceding projected estimates, let $z=a_{i-1}/(2b_{i-1})$. Charge $\mu_i=\max(z-\delta_i,\ell)$ in the first block and $\lambda_i=\min(z+\delta_i,u)$ in the second.
--
--   If $D_i^-,D_i^+$ are the two observed demand means in completed episode $i$, compute
--   $$\widehat\beta_i=\frac{D_i^- -D_i^+}{\lambda_i-\mu_i},\qquad \widehat\alpha_i=\frac{\lambda_i D_i^- -\mu_i D_i^+}{\lambda_i-\mu_i}.$$
--   Project each coordinate onto its known interval to obtain $(a_i,b_i)$. Equal positive block sizes and distinct prices make these the unique unconstrained least-squares estimates on exactly that episode. There is no projection onto the full four-dimensional $\Theta$.
--
--   The seller's price rule takes only known bounds, tuning, initial estimates and past price-demand pairs. Given a full shock path, the environment recursively appends the selected price and $d(p_t,r_t,\theta)+\varepsilon_t$. The environment evaluates the latent reference from past prices; the seller does not receive that reference or the true parameters. The recursion defines compatible finite prefixes of an infinite run. Incomplete episodes use only prefix observations, without an early update.
--
--   **Formalization Note.** Finite histories are functions on `Fin n`. At zero-based time $n$, the active episode is $\lfloor\log_2(n+4)\rfloor-1$. The first episode is source periods 1–4. The accessor's out-of-range zero default is never read in a required completed data window. Real powers use a real exponent. The rule extends to real observations, agreeing with the printed nonnegative-history domain wherever the latter applies. The finite-time rule is Borel measurable (finite arithmetic, total real division and fixed-index branches); composing continuous reference maps with interval clipping yields a measurable causal run. The clamp of past reference inputs changes no generated feasible price. No estimator accuracy is assumed.
--
--   The policy and price path return interval elements. The implementation clips each perturbed center to the full interval; because every allowed projected center is interior, this equals precisely the printed lower-only first-block and upper-only second-block rule. This total extension changes no allowed source run.
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, policy box printed/PDF p. 13; schedules printed/PDF pp. 14 and 17

import Definitions.Def_RefDemandLearning_SlowMoving_Model

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace RefDemandLearning.SlowMoving

/-- Source episode i starts after this many observations. -/
def episodeStart (i : ℕ) : ℕ := 2 ^ (i + 1) - 4

def blockLength (i : ℕ) : ℕ := 2 ^ i

/-- At zero-based time n, source episode floor(log2(n+4))-1 is active. -/
def episodeAt (n : ℕ) : ℕ := Nat.log2 (n + 4) - 1

def perturbation (c₀ : ℝ) (i : ℕ) : ℝ := c₀ * (2 : ℝ) ^ (-(i : ℝ) / 4)

def TuningOK (B : Bounds) (c₀ a₀ b₀ : ℝ) : Prop :=
  0 < c₀ ∧ c₀ < (2 : ℝ) ^ (-(3 : ℝ) / 4) * (B.prices.hi - B.prices.lo) ∧
  a₀ ∈ Set.Icc B.alphaMin B.alphaMax ∧ b₀ ∈ Set.Icc B.betaMin B.betaMax

/-- Total accessor; its default is never used by an active episode's completed data window. -/
def datum {n : ℕ} (h : Fin n → ℝ × ℝ) (j : ℕ) : ℝ × ℝ :=
  if hj : j < n then h ⟨j, hj⟩ else (0, 0)

/-- Block demand mean, using only data in the indicated completed window. -/
def blockMean {n : ℕ} (h : Fin n → ℝ × ℝ) (start len : ℕ) : ℝ :=
  (∑ j ∈ Finset.range len, (datum h (start + j)).2) / (len : ℝ)

/-- Unique unconstrained two-block least-squares estimator (intercept, positive slope). -/
def twoBlockEstimate {n : ℕ} (h : Fin n → ℝ × ℝ) (i : ℕ) : ℝ × ℝ :=
  let start := episodeStart i
  let len := blockLength i
  let μ := (datum h start).1
  let lam := (datum h (start + len)).1
  let dm := blockMean h start len
  let dp := blockMean h (start + len) len
  ((lam * dm - μ * dp) / (lam - μ), (dm - dp) / (lam - μ))

def project (lo hi x : ℝ) : ℝ := max lo (min x hi)

/-- The seller's rule depends only on known bounds, tuning and observations.
Under Standing and TuningOK, the center is interior, so full interval clipping equals
the source's lower-only clipping in the first block and upper-only clipping in the second. -/
def policyPrice (B : Bounds) (c₀ a₀ b₀ : ℝ) (n : ℕ) (h : Fin n → ℝ × ℝ) : Price B.prices :=
  let i := episodeAt n
  let ab := if i = 1 then (a₀, b₀) else
    let est := twoBlockEstimate h (i - 1)
    (project B.alphaMin B.alphaMax est.1, project B.betaMin B.betaMax est.2)
  let center := ab.1 / (2 * ab.2)
  clipPrice B.prices (if n < episodeStart i + blockLength i then
    center - perturbation c₀ i else center + perturbation c₀ i)

/-- A single causal infinite run represented by compatible finite prefixes.
The reference mechanism is used by the environment, never by policyPrice. -/
def run (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters)
    (c₀ a₀ b₀ : ℝ) (e : ℕ → ℝ) : (n : ℕ) → Fin n → ℝ × ℝ
  | 0 => Fin.elim0
  | n + 1 =>
    let h := run B ρ θ c₀ a₀ b₀ e n
    let p : ℝ := policyPrice B c₀ a₀ b₀ n h
    let r : ℝ := ρ.ref n (fun j => clipPrice B.prices (h j).1)
    Fin.snoc h (p, demand θ p r + e n)

def pricePath (B : Bounds) (ρ : Mechanism B.prices) (θ : Parameters)
    (c₀ a₀ b₀ : ℝ) (e : ℕ → ℝ) (n : ℕ) : Price B.prices :=
  policyPrice B c₀ a₀ b₀ n (run B ρ θ c₀ a₀ b₀ e n)

end RefDemandLearning.SlowMoving


