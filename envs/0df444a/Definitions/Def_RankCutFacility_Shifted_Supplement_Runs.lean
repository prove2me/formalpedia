-- Prove2me | Definitions.Def_RankCutFacility_Shifted_Supplement_Runs
-- name    : RankCutFacility_Shifted_Supplement_Runs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:20:15.133382+00:00
-- url     : https://prove2.me/theorems/e10ad709-f4cf-4cfd-885a-f7997ab4ce45
-- title:
--   Rank-penalty schedules, the order-statistic clock rule, Algorithm 2 and TimeDist rules
-- statement:
--   Built on the published model of the mission (candidate geometry, `select`, `opens`, `nextOpen`, service-time `connection`, labeled arrival orders and the offline optimum), this file defines the algorithms of Section 5 and Appendices A and B.
--
--   1. **Deterministic runs.** A round update maps (rank, open set, current location) to the new open set; folding it over the revealed locations gives the open sets $O_t$, and the cost is $\sum_{y\in O_n} f_y+\sum_t d(v_t,O_t)$ with full opening fees and service-time connection distances.
--   2. **Rank-penalty schedules (Section 5).** For a schedule $\lambda_{t,n}$, positive at every rank $1\le t\le n$, the run uses the same candidate choice $\arg\min_y\{d(x,y)+\lambda_{t,n}f_y\}$ and the same opening test as Algorithm 1. With $\lambda_{t,n}=\min\{1,(t-1+\delta)/(\mu n)\}$ it is literally the published Algorithm 1 (a definitional lemma). `FullSpaceCompetitive lam C` says that $\mathbb E[\mathrm{ALG}]\le C\,\mathrm{OPT}$ on every finite metric in which every point is a candidate, for arbitrary positive costs, horizons and demand copies, under some tie order of the candidates.
--   3. **OSRC$_\mu$ (Appendix A.1).** $n$ independent Uniform$(0,1)$ clocks are sorted, $Z_{(1)}\le\dots\le Z_{(n)}$, and the request at rank $t$ gets penalty $\min\{1,Z_{(t)}/\mu\}$. Its expected cost averages over the labeled arrival orders and integrates over the clocks. The constants $\mu_R$ (root of $e^{-(1+\mu)}=\mu(2+3\mu)$ in $(0,1]$) and $\rho^*_R=A(\mu_R)$ are defined canonically.
--   4. **Algorithm 2 (Appendix B.1).** With $\theta_\mu(z)=\min\{1,z/\mu\}$, $a_x=d(x,F)$ and $\Delta=(d(x,O_{t-1})-a_x)^+$ (infinite when $O_{t-1}=\emptyset$), the request at rank $t$ opens its nearest candidate iff $\Delta\ge\theta_\mu((t-1)/n)$. Per-copy opening cost $L_p$, post-service distance $D_p$ and total charge are defined.
--   5. **Candidate Marginal TimeDist rules (Definition B.4).** A rule is a family $g_n(t,\Delta)\in[0,1]$ for $2\le t\le n$, $\Delta\ge0$. Rank 1 opens a nearest candidate; at rank $t\ge2$ the rule opens the nearest candidate with probability exactly $g_n(t,\Delta_t)$. Its expected cost on a fixed arrival sequence is computed by the recursion this conditional law determines. The DistCut rule $g_n(t,\Delta)=\mathbf 1\{\Delta\ge\theta_\mu((t-1)/n)\}$, the root $\mu^*$ of $\Phi(\mu)=3+2\mu$ in $(0,1]$ and $C^*=\Phi(\mu^*)$ are defined.
--
--   **Formalization Note** Roots are canonical infima of their solution sets; their existence and uniqueness are theorem conclusions. The clock law is the product of Lebesgue measure on $[0,1]$; ties among clocks are a null set.
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Section 5 (printed p. 16, PDF p. 18), Appendix A.1 eqs. (39)–(40) (printed p. 27, PDF p. 29), Appendix B.1 Algorithm 2 (printed pp. 30–31, PDF pp. 32–33), Definition B.4 and µ*, C* (printed p. 33, PDF p. 35)

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace RankCutFacility.Shifted.Supplement
open RankCutFacility.Shifted

variable {M : Type*} [MetricSpace M]

/-! ### Generic deterministic runs on a revealed location list -/

/-- One deterministic round: (rank, open set before the round, current location) ↦ open set
after the round's openings. Facilities never close in the runs built from it below. -/
abbrev Step (G : Geometry M) := ℕ → Finset (Fin G.m) → M → Finset (Fin G.m)

/-- Open set after folding a step over the revealed locations; ranks start at 1. -/
def runOpen (G : Geometry M) (step : Step G) (xs : List M) : Finset (Fin G.m) :=
  xs.zipIdx.foldl (fun O z => step (z.2 + 1) O z.1) ∅

/-- Full fees of every facility open at the end plus every service-time connection distance. -/
def runCost (G : Geometry M) (step : Step G) (xs : List M) : ℝ :=
  (∑ y ∈ runOpen G step xs, G.fee y) +
  ((xs.zipIdx.map fun z => connection G (runOpen G step (xs.take (z.2 + 1))) z.1).sum)

/-! ### Rank-penalty schedules (Section 5) and the shifted schedule -/

/-- Same candidate choice (`select`) and opening test (`opens`) as Algorithm 1, with the
penalty at rank `t` read from an arbitrary real schedule `β`. -/
def scheduleStep (G : Geometry M) (β : ℕ → ℝ) : Step G :=
  fun t O x => nextOpen G O (β t) x

def scheduleAlg {n : ℕ} (G : Geometry M) (u : Fin n → M) (β : ℕ → ℝ) (π : Arrival n) : ℝ :=
  runCost G (scheduleStep G β) (stream u π)

/-- With the shifted penalty the schedule run is literally the published Algorithm 1. -/
theorem scheduleAlg_penalty {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ)
    (π : Arrival n) : scheduleAlg G u (fun t => penalty n t μ δ) π = alg G u μ δ π := rfl

/-- A deterministic rank-penalty algorithm: `lam n t` is the penalty at rank `t` for horizon
`n`; it is fixed in advance and must be positive at every rank `1 ≤ t ≤ n`. -/
def IsRankSchedule (lam : ℕ → ℕ → ℝ) : Prop :=
  ∀ n t : ℕ, 1 ≤ t → t ≤ n → 0 < lam n t

def rankPenaltyAlg {n : ℕ} (G : Geometry M) (u : Fin n → M) (lam : ℕ → ℕ → ℝ)
    (π : Arrival n) : ℝ :=
  scheduleAlg G u (lam n) π

/-- `E[ALG] ≤ C · OPT` on every finite full-space instance (every point a candidate, arbitrary
positive costs, every horizon `n ≥ 1` and demand map), for some candidate enumeration (tie order)
of that instance. -/
def FullSpaceCompetitive (lam : ℕ → ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ (X : Type) [MetricSpace X] [Fintype X] (f : X → ℝ), (∀ x, 0 < f x) →
    ∀ n : ℕ, 0 < n → ∀ u : Fin n → X,
      ∃ G : Geometry X, Function.Surjective G.site ∧ (∀ y, G.fee y = f (G.site y)) ∧
        uniformAvg (rankPenaltyAlg G u lam) ≤ C * optimum G u

/-! ### The order-statistic-clock rule OSRC_μ (Appendix A.1) -/

/-- The `t`-th smallest clock value (`t` is 1-based); `0` outside `1 ≤ t ≤ n`. -/
def orderStat {n : ℕ} (z : Fin n → ℝ) (t : ℕ) : ℝ :=
  ((List.ofFn z).mergeSort (fun a b => decide (a ≤ b))).getD (t - 1) 0

/-- Law of `n` independent Uniform(0,1) clocks. -/
def clockLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1))

/-- Penalty `λ(q_t) = min{1, q_t/μ}` at rank `t`, with clock `q_t = Z_(t)`. -/
def osrcPenalty (μ : ℝ) {n : ℕ} (z : Fin n → ℝ) (t : ℕ) : ℝ := min 1 (orderStat z t / μ)

def osrcRun {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) (z : Fin n → ℝ)
    (π : Arrival n) : ℝ :=
  scheduleAlg G u (osrcPenalty μ z) π

/-- `E[ALG]` of OSRC_μ: uniform labeled permutation, independent uniform clocks. -/
def osrcExpected {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) : ℝ :=
  uniformAvg (fun π => ∫ z, osrcRun G u μ z π ∂(clockLaw n))

/-- Canonical root of `e^{-(1+μ)} = μ(2+3μ)` in `(0,1]`; well-posedness is a theorem conclusion. -/
def muR : ℝ := sInf {μ : ℝ | 0 < μ ∧ μ ≤ 1 ∧ Real.exp (-(1 + μ)) = μ * (2 + 3 * μ)}

def rhoR : ℝ := limitingA muR

/-! ### Zero-start Candidate Marginal DistCut, Algorithm 2 (Appendix B.1) -/

/-- `θ_μ(z) = min{1, z/μ}`. -/
def theta (μ z : ℝ) : ℝ := min 1 (z / μ)

/-- First nearest candidate in the enumeration order (a zero penalty in `select`). -/
def nearest (G : Geometry M) (x : M) : Fin G.m := select G 0 x

/-- `a_x = d(x, F)`. -/
def candDist (G : Geometry M) (x : M) : ℝ := dist x (G.site (nearest G x))

/-- Algorithm 2: open the nearest candidate iff `O = ∅` (then `Δ = +∞`) or
`Δ = (D - a)^+ ≥ θ_μ((t-1)/n)`. -/
def zeroStartStep (G : Geometry M) (n : ℕ) (μ : ℝ) : Step G := fun t O x => by
  classical
  exact if O = ∅ ∨ theta μ (((t : ℝ) - 1) / n) ≤ positivePart (connection G O x - candDist G x)
    then insert (nearest G x) O else O

def zeroStartAlg {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) (π : Arrival n) : ℝ :=
  runCost G (zeroStartStep G n μ) (stream u π)

/-- Open set just before copy `p` is served. -/
def zsBefore {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) (π : Arrival n) (p : Fin n) :
    Finset (Fin G.m) :=
  runOpen G (zeroStartStep G n μ) ((stream u π).take ((π.symm p).val))

/-- Open set just after the round of copy `p`. -/
def zsAfter {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) (π : Arrival n) (p : Fin n) :
    Finset (Fin G.m) :=
  zeroStartStep G n μ (rank π p) (zsBefore G u μ π p) (u p)

/-- `D_p`: the connection distance paid by copy `p` at its service time. -/
def zsDistance {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) (π : Arrival n) (p : Fin n) : ℝ :=
  connection G (zsAfter G u μ π p) (u p)

/-- `L_p`: opening cost paid in the round of copy `p`. -/
def zsOpening {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) (π : Arrival n) (p : Fin n) : ℝ := by
  classical
  exact ∑ y ∈ zsAfter G u μ π p \ zsBefore G u μ π p, G.fee y

/-- `ALG(p)`: opening plus connection cost charged to the round of copy `p`. -/
def zsCopyCost {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ : ℝ) (π : Arrival n) (p : Fin n) : ℝ :=
  zsOpening G u μ π p + zsDistance G u μ π p

/-! ### Candidate Marginal TimeDist rules (Definition B.4) -/

/-- `g n t Δ` is the opening probability at rank `2 ≤ t ≤ n` with marginal saving `Δ ≥ 0`. -/
def IsTimeDistRule (g : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∀ n t : ℕ, ∀ Δ : ℝ, 2 ≤ t → t ≤ n → 0 ≤ Δ → 0 ≤ g n t Δ ∧ g n t Δ ≤ 1

/-- Opening probability of the current round: one at rank 1, else `g n t Δ_t`. -/
def tdOpenProb (G : Geometry M) (g : ℕ → ℕ → ℝ → ℝ) (n t : ℕ) (O : Finset (Fin G.m))
    (x : M) : ℝ :=
  if t = 1 then 1 else g n t (positivePart (connection G O x - candDist G x))

/-- Expected remaining cost from rank `t` with open set `O` on the remaining locations; the
conditional law of every round is the one prescribed by Definition B.4. -/
def tdValue (G : Geometry M) (g : ℕ → ℕ → ℝ → ℝ) (n : ℕ) :
    ℕ → Finset (Fin G.m) → List M → ℝ
  | _, _, [] => 0
  | t, O, x :: rest => by
    classical
    exact tdOpenProb G g n t O x *
        ((if nearest G x ∈ O then 0 else G.fee (nearest G x)) +
          connection G (insert (nearest G x) O) x +
          tdValue G g n (t + 1) (insert (nearest G x) O) rest) +
      (1 - tdOpenProb G g n t O x) * (connection G O x + tdValue G g n (t + 1) O rest)

/-- `E[ALG_G(I)]`: uniform labeled arrival order and the rule's internal randomness. -/
def tdExpected {n : ℕ} (G : Geometry M) (g : ℕ → ℕ → ℝ → ℝ) (u : Fin n → M) : ℝ :=
  uniformAvg (fun π => tdValue G g n 1 ∅ (stream u π))

/-- Candidate Marginal DistCut with zero-start clock: open iff `Δ ≥ θ_μ((t-1)/n)`. -/
def distCutRule (μ : ℝ) : ℕ → ℕ → ℝ → ℝ := fun n t Δ => by
  classical
  exact if theta μ (((t : ℝ) - 1) / n) ≤ Δ then 1 else 0

/-- Canonical root of `Φ(μ) = 3 + 2μ` in `(0,1]`; well-posedness is a theorem conclusion. -/
def muStar : ℝ := sInf {μ : ℝ | 0 < μ ∧ μ ≤ 1 ∧ limitingA μ = 3 + 2 * μ}

def CStar : ℝ := limitingA muStar

end RankCutFacility.Shifted.Supplement


