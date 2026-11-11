-- Prove2me | Definitions.Def_SampQueryLB_WarmSLC_Model
-- name    : SampQueryLB_WarmSLC_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:14:26.377572+00:00
-- url     : https://prove2.me/theorems/0646c839-cc09-4292-8188-3d0035bd3076
-- title:
--   §2.2 — warm-start randomized adaptive first-order sampling algorithms, their output law and expected query count
-- statement:
--   Points of $\mathbb R^d$ are vectors of `Point d` $=\mathbb R^d$ with the Euclidean norm. A potential $V:\mathbb R^d\to\mathbb R$ is accessed through the **exact first-order oracle**, which on a query $y$ returns $(V(y),\nabla V(y))$; its target is the Gibbs law $\pi_V(dx)\propto e^{-V(x)}\,dx$ (`gibbs V`).
--
--   A **history** of $t$ rounds is $h_t=((y_1,r_1),\dots,(y_t,r_t))$, queries with their replies. A **warm-start sampling algorithm** is given by Borel query maps $A_{t+1}$, Borel stopping sets $S_t$ and Borel output maps $A^{(t)}_{\mathrm{out}}$, all functions of the pair $(x_{\mathrm{init}},\omega)$ and of the history, fixed independently of $V$. Given an initial sample $x_{\mathrm{init}}$ and a seed $\omega$, after $t$ rounds the algorithm stops and outputs $X=A^{(t)}_{\mathrm{out}}((x_{\mathrm{init}},\omega),h_t)$ if $((x_{\mathrm{init}},\omega),h_t)\in S_t$, and otherwise queries $y_{t+1}=A_{t+1}((x_{\mathrm{init}},\omega),h_t)$ and receives $r_{t+1}=(V(y_{t+1}),\nabla V(y_{t+1}))$. The number of queries $N\in\{0,1,\dots\}\cup\{\infty\}$ is the number of rounds before stopping.
--
--   With $x_{\mathrm{init}}\sim\nu$ and $\omega\sim\mathrm{Unif}[0,1]$ independent, $\rho^{\mathrm{Alg}}_{V,\nu}$ is the law of $X$ and
--   $$\mathbb E_{V,\nu}[N]=\int N\,d(\nu\otimes\mathrm{Unif}[0,1])\in[0,\infty].$$
--   The file also fixes the vocabulary of the goal: Hessian bounds $\alpha I\preceq\nabla^2V\preceq LI$ as $\alpha\|v\|^2\le\langle v,D(\nabla V)(x)v\rangle\le L\|v\|^2$ for all $x,v$; a law with mean zero (Bochner-integrable identity with integral $0$); a law with a $C^\infty$, everywhere positive, even Lebesgue density; and the two density-ratio bounds $d\nu/d\pi\le a$, $d\pi/d\nu\le b$ (absolute continuity both ways and Radon–Nikodym derivatives bounded almost everywhere).
--
--   **Formalization Note.** The seed is a real number with law $\mathrm{Unif}[0,1]$ (`seedLaw`), as in §2.2; maps take $((x,\omega),h_t)$. `numQueries` is $\top$ when the run never stops and `output` is then $0$ (a null event for the algorithms considered, which have $N<\infty$ a.s., `FiniteQueriesAS`). A cold-start algorithm is one whose maps ignore $x$. `transcript q` records $N$ and the history $h_q$ with every round at or after $N$ set to $0$.
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 13, §2.1; p. 14, §2.2; p. 55, §7

import Mathlib
import Definitions.Def_LogConcaveQuery

/-!
# Warm-start first-order sampling algorithms (§2.2, §7)

Zhou, Suzuki, *Towards the Query Complexity of Sampling under Strong Log-Concavity and
Log-Sobolev Inequalities*, arXiv:2611.05813 (held version dated November 3, 2026),
p. 13–14 (§2.1–§2.2) and p. 55 (§7 preamble).

Conventions.
* Points of `ℝ^d` are `OAI.LogConcaveSampling.Point d = EuclideanSpace ℝ (Fin d)`; the oracle
  reply at `y` is `firstOrderReply V y = (V y, ∇V y)`; the target of a potential is
  `gibbs V`, the law with density proportional to `exp (-V)` (all from `LogConcaveQuery`).
* A history of `t` rounds is `Fin t → Point d × (ℝ × Point d)`: the `k`-th query and its reply.
* The algorithm is given by Borel query maps, Borel stopping sets and Borel output maps of the
  pair (initial sample, seed) and the history. The seed `w` is real with law `Unif[0,1]`
  (`seedLaw`); the initial sample `x` has law `ν` and is independent of the seed. A cold-start
  algorithm is one whose maps ignore `x`.
* `numQueries` is the number of rounds before the first stop (`⊤` if the run never stops);
  `output` is the output at that round (the origin if the run never stops, an event of
  probability zero for the algorithms considered).
* `outputLaw` is the law of the output under `ν ⊗ Unif[0,1]`, `expectedQueries` the expected
  number of queries in `ℝ≥0∞`.
-/

namespace SampQueryLB.WarmSLC

open MeasureTheory OAI.LogConcaveSampling
open scoped ENNReal ContDiff RealInnerProductSpace

noncomputable section

/-- Histories of `t` rounds: the queries `y_1, …, y_t` with their replies `(V y_k, ∇V y_k)`. -/
abbrev Hist (d t : ℕ) := Fin t → Point d × Reply d

/-- A randomized adaptive first-order sampling algorithm in the warm-start model of §2.2:
Borel query maps, stopping sets and output maps of `((x_init, ω), h_t)`. -/
structure WarmAlgorithm (d : ℕ) where
  /-- `query t ((x, w), h_t)` is the query `y_{t+1}` made after the history `h_t`. -/
  query : (t : ℕ) → (Point d × ℝ) × Hist d t → Point d
  /-- The algorithm stops after `t` rounds when `((x, w), h_t) ∈ stop t`. -/
  stop : (t : ℕ) → Set ((Point d × ℝ) × Hist d t)
  /-- `out t ((x, w), h_t)` is the output when the algorithm stops after `t` rounds. -/
  out : (t : ℕ) → (Point d × ℝ) × Hist d t → Point d
  query_measurable : ∀ t, Measurable (query t)
  stop_measurable : ∀ t, MeasurableSet (stop t)
  out_measurable : ∀ t, Measurable (out t)

namespace WarmAlgorithm

variable {d : ℕ}

/-- The history after `t` rounds on the potential `V`, initial sample `x` and seed `w`
(rounds after stopping are computed but never used). -/
def history (A : WarmAlgorithm d) (V : Point d → ℝ) (x : Point d) (w : ℝ) :
    (t : ℕ) → Hist d t
  | 0 => fun i => i.elim0
  | t + 1 => fun i =>
      if h : (i : ℕ) < t then history A V x w t ⟨i, h⟩
      else (A.query t ((x, w), history A V x w t),
        firstOrderReply V (A.query t ((x, w), history A V x w t)))

/-- The run stops after `t` rounds. -/
def Stops (A : WarmAlgorithm d) (V : Point d → ℝ) (x : Point d) (w : ℝ) (t : ℕ) : Prop :=
  ((x, w), A.history V x w t) ∈ A.stop t

open Classical in
/-- The number of queries `N`: the first `t` at which the run stops, `⊤` if it never stops. -/
def numQueries (A : WarmAlgorithm d) (V : Point d → ℝ) (x : Point d) (w : ℝ) : ℕ∞ :=
  if h : ∃ t, A.Stops V x w t then (Nat.find h : ℕ∞) else ⊤

open Classical in
/-- The output `X = A_out^{(N)}((x, w), h_N)`; the origin on the (null) event `N = ∞`. -/
def output (A : WarmAlgorithm d) (V : Point d → ℝ) (x : Point d) (w : ℝ) : Point d :=
  if h : ∃ t, A.Stops V x w t then
    A.out (Nat.find h) ((x, w), A.history V x w (Nat.find h))
  else 0

open Classical in
/-- The algorithm's transcript, padded to length `q`: the number of queries `N` and the history
`h_q` with every round at or after `N` replaced by `0`. When `N ≤ q` it determines
`(N, (y_k, r_k)_{k ≤ N})` and conversely. -/
def transcript (A : WarmAlgorithm d) (V : Point d → ℝ) (x : Point d) (w : ℝ) (q : ℕ) :
    ℕ∞ × Hist d q :=
  (A.numQueries V x w, fun k =>
    if ((k : ℕ) : ℕ∞) < A.numQueries V x w then A.history V x w q k else 0)

end WarmAlgorithm

/-- The seed law `Unif[0,1]`. -/
def seedLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The law of the output `ρ^Alg_{V,ν}` when `x_init ∼ ν` and `ω ∼ Unif[0,1]` independently. -/
def outputLaw {d : ℕ} (A : WarmAlgorithm d) (V : Point d → ℝ) (ν : Measure (Point d)) :
    Measure (Point d) :=
  (ν.prod seedLaw).map (fun p => A.output V p.1 p.2)

/-- The expected number of queries `E_{V,ν}[N] ∈ [0, ∞]`. -/
def expectedQueries {d : ℕ} (A : WarmAlgorithm d) (V : Point d → ℝ) (ν : Measure (Point d)) :
    ℝ≥0∞ :=
  ∫⁻ p, ENat.toENNReal (A.numQueries V p.1 p.2) ∂(ν.prod seedLaw)

/-- `N < ∞` almost surely. -/
def FiniteQueriesAS {d : ℕ} (A : WarmAlgorithm d) (V : Point d → ℝ) (ν : Measure (Point d)) :
    Prop :=
  (ν.prod seedLaw) {p | A.numQueries V p.1 p.2 = ⊤} = 0

/-- Hessian bounds `α I ⪯ ∇²V(x) ⪯ L I` at every `x`, as quadratic-form bounds on the derivative
of the gradient. -/
def HessianBetween {d : ℕ} (V : Point d → ℝ) (α L : ℝ) : Prop :=
  ∀ x v : Point d,
    α * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient V) x v⟫ ∧ ⟪v, fderiv ℝ (gradient V) x v⟫ ≤ L * ‖v‖ ^ 2

/-- `μ` has mean zero: the identity is Bochner integrable and integrates to `0`. -/
def MeanZero {d : ℕ} (μ : Measure (Point d)) : Prop :=
  Integrable (fun x : Point d => x) μ ∧ ∫ x, x ∂μ = 0

/-- `ν` has a smooth (`C^∞`), everywhere positive, even density with respect to Lebesgue measure. -/
def HasSmoothPosEvenDensity {d : ℕ} (ν : Measure (Point d)) : Prop :=
  ∃ ρ : Point d → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ x, 0 < ρ x) ∧ (∀ x, ρ (-x) = ρ x) ∧
    ν = volume.withDensity (fun x => ENNReal.ofReal (ρ x))

/-- The two density-ratio bounds `dν/dπ ≤ a` and `dπ/dν ≤ b` (each with absolute continuity). -/
def RatioBounds {d : ℕ} (ν π : Measure (Point d)) (a b : ℝ) : Prop :=
  ν ≪ π ∧ (∀ᵐ x ∂π, ν.rnDeriv π x ≤ ENNReal.ofReal a) ∧
    π ≪ ν ∧ (∀ᵐ x ∂ν, π.rnDeriv ν x ≤ ENNReal.ofReal b)

end

end SampQueryLB.WarmSLC


