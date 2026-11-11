-- Prove2me | Definitions.Def_MixedORAM_PublicRead_Workload
-- name    : MixedORAM_PublicRead_Workload
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:46:57.713837+00:00
-- url     : https://prove2.me/theorems/bd79e8db-0a87-45b3-9e09-bf00ef309a11
-- title:
--   The workloads W_{R,W}, W_{R,R}, the average costs Π_N, R_N, T_N and the worst-case-input budget
-- statement:
--   For private probability $p$, a request of the workload $\mathcal W_{R,W}$ is, independently of everything else, with probability $p$ a private write of a fresh uniform $w$-bit word to a uniform address, and otherwise (probability $r=1-p$) a public read of a uniform address. In $\mathcal W_{R,R}$ the private request is a read of a uniform address. The workload of horizon $N$ is a list of $N$ independent such requests, independent of the implementation's randomness. Theorem 3.1 pairs $\mathcal W_{R,W}$ with the disclosed-kind leakage and $\mathcal W_{R,R}$ with the hidden-kind leakage.
--
--   For an implementation $I$ and initial array $A_0$, with expectations over the workload and the implementation,
--   $$\Pi_N=\frac{\mathbb E[\text{probes of private requests among the first }N]}{pN},\qquad R_N=\frac{\mathbb E[\text{probes of public reads among the first }N]}{(1-p)N},$$
--   and, for a general IID request law, $T_N$ is the expected number of probes per request among the first $N$. Every probe is charged to the request performing it; preprocessing probes are charged separately and are not counted.
--
--   $I$ has a **worst-case-input private budget** $P$ if for every initial array and every finite request list $u$ the expected number of probes of the private requests of $u$ is at most $P$ times their number. The expected total probe count of the workload execution, preprocessing included, is recorded for the computational qualification.
--
--   **Formalization Note** Costs take values in $[0,\infty]$. The coin of probability $p$ is clamped to $[0,1]$, which changes nothing for $0<p\le 1/2$.
-- source:
--   Ciszewski, Ragnoli, Access Cost Tradeoffs in Mixed-Mode Oblivious RAM, STOC 2027 submission (manuscript sha256 a4f849fd…), p. 5, §2.3, Eq. (3)

import Mathlib
import Definitions.Def_MixedORAM_PublicRead_Privacy

set_option autoImplicit false

namespace MixedORAM.PublicRead

/-- The two two-class workloads of the read frontier (§2.3, p. 5): `RW` = `W_{R,W}` (public reads
and private writes), `RR` = `W_{R,R}` (public and private reads). -/
inductive Workload where
  | RW
  | RR
  deriving DecidableEq

/-- The leakage under which the public-read lower bound is stated for each workload (Theorem 3.1,
p. 6: "W_{R,W} with disclosed or hidden private kinds, or W_{R,R} with hidden private kinds"):
disclosed kinds on `W_{R,W}`, hidden kinds on `W_{R,R}`. -/
def Workload.leak : Workload → LeakKind
  | .RW => .dis
  | .RR => .hid

/-- A biased coin: `true` with probability `p` (clamped to `[0, 1]`; for `0 < p ≤ 1/2` it is
exactly `p`). -/
noncomputable def coin (p : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => cond b (ENNReal.ofReal (max 0 (min p 1)))
      (ENNReal.ofReal (1 - max 0 (min p 1)))) (by
    have h0 : (0:ℝ) ≤ max 0 (min p 1) := le_max_left _ _
    have h1 : max 0 (min p 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
    simp only [Fintype.sum_bool, cond_true, cond_false]
    rw [← ENNReal.ofReal_add h0 (by linarith)]
    simp)

/-- The law of one request of the workload `wl` with private probability `p` (§2.3, p. 5): with
probability `p` a private request, otherwise (probability `r = 1 − p`) a public read; the address is
uniform on `Fin n`; on `W_{R,W}` the private request is a write of a fresh uniform `w`-bit word, on
`W_{R,R}` a read ("Lower-bound workloads have independent uniform addresses and fresh uniform write
values"). -/
noncomputable def reqDist (wl : Workload) (n w : ℕ) [NeZero n] (p : ℝ) : PMF (Request n w) :=
  (coin p).bind fun isPriv =>
    (PMF.uniformOfFintype (Fin n)).bind fun x =>
      (PMF.uniformOfFintype (BitVec w)).map fun v =>
        if isPriv then
          (match wl with
            | .RW => ⟨.priv, .write x v⟩
            | .RR => ⟨.priv, .read x⟩)
        else ⟨.pub, .read x⟩

/-- `k` independent draws from `d`, as a list (request classes are IID, §2.3, p. 5). -/
noncomputable def iidList {α : Type} (d : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | k + 1 => d.bind fun x => (iidList d k).map (x :: ·)

/-- Expectation of a `[0, ∞]`-valued function under a law. -/
noncomputable def pexp {α : Type} (P : PMF α) (f : α → ENNReal) : ENNReal := ∑' x, P x * f x

/-- The joint law of the first `N` requests of the IID workload with request law `δ` and the
execution of `I` on them from the initial array `A₀`; the workload randomness is independent of the
implementation's (§2.3, p. 5). -/
noncomputable def workExec {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (δ : PMF (Request n w)) (N : ℕ) : PMF (List (Request n w) × List (StepRecord a w)) :=
  (iidList δ N).bind fun u => (I.exec A₀ u).map fun res => (u, res)

/-- The number of probes made by the requests of `u` satisfying `cls` ("Every probe is charged to the
request performing it", §2.3, p. 5). -/
def classProbes {n w a : ℕ} (cls : Request n w → Bool) (u : List (Request n w))
    (res : List (StepRecord a w)) : ℕ :=
  (((u.zip res).filter (fun q => cls q.1)).map (fun q => q.2.probes.length)).sum

/-- A private request. -/
def isPriv {n w : ℕ} (r : Request n w) : Bool := decide (r.mode = .priv)

/-- A public read. -/
def isPubRead {n w : ℕ} (r : Request n w) : Bool :=
  decide (r.mode = .pub) && decide (r.op.kind = .read)

/-- The total number of probes of the requests of an execution (preprocessing not included). -/
def totalProbes {a w : ℕ} (res : List (StepRecord a w)) : ℕ := (res.map (·.probes.length)).sum

/-- **Average private cost** `Π_N = E[private probes]/(pN)` over the first `N` requests of the
workload `wl` (Eq. (3), p. 5), with expectation over the workload and the implementation's
randomness; preprocessing is charged separately and not counted. Values in `[0, ∞]`. -/
noncomputable def PiN {n w m a : ℕ} [NeZero n] (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (wl : Workload) (p : ℝ) (N : ℕ) : ENNReal :=
  pexp (workExec I A₀ (reqDist wl n w p) N) (fun q => (classProbes isPriv q.1 q.2 : ENNReal)) /
    (ENNReal.ofReal p * N)

/-- **Average public-read cost** `R_N = E[public-read probes]/(rN)` with `r = 1 − p` (Eq. (3),
p. 5). Values in `[0, ∞]`. -/
noncomputable def RN {n w m a : ℕ} [NeZero n] (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (wl : Workload) (p : ℝ) (N : ℕ) : ENNReal :=
  pexp (workExec I A₀ (reqDist wl n w p) N) (fun q => (classProbes isPubRead q.1 q.2 : ENNReal)) /
    (ENNReal.ofReal (1 - p) * N)

/-- **Average total cost** `T_N`: the expected number of probes per request among the first `N`
requests of the IID workload with request law `δ` (§2.3, p. 5: "the expected probes per request in
the first N of them"). On the two-class workloads `T_N = pΠ_N + (1 − p)R_N`. -/
noncomputable def TN {n w m a : ℕ} (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (δ : PMF (Request n w)) (N : ℕ) : ENNReal :=
  pexp (workExec I A₀ δ N) (fun q => (totalProbes q.2 : ENNReal)) / N

/-- The expected total number of probes, preprocessing included, of the exact workload execution of
horizon `N` (the expected-probe qualification of the computational lower bounds, §2.2, p. 5:
"polynomial expected probes, including preprocessing, on the exact reference workload"). -/
noncomputable def expProbes {n w m a : ℕ} [NeZero n] (I : Impl n w m a) (A₀ : Fin n → BitVec w)
    (wl : Workload) (p : ℝ) (N : ℕ) : ENNReal :=
  pexp (iidList (reqDist wl n w p) N)
    (fun u => pexp (I.run A₀ u) (fun x => ((x.1.length + totalProbes x.2 : ℕ) : ENNReal)))

/-- A **worst-case-input private budget** `P` (§2.3, p. 5: it "bounds the expected average number of
probes per private request on every fixed input prefix by P, with expectation over the algorithm's
randomness"): for every initial array and every finite request list `u` (each prefix of an input is
itself an input, and execution is online), the expected number of probes of the private requests of
`u` is at most `P` times their number. -/
def WorstCaseBudget {n w m a : ℕ} (I : Impl n w m a) (P : ℝ) : Prop :=
  ∀ (A₀ : Fin n → BitVec w) (u : List (Request n w)),
    pexp (I.exec A₀ u) (fun res => (classProbes isPriv u res : ENNReal)) ≤
      ENNReal.ofReal P * ((u.filter isPriv).length : ENNReal)

end MixedORAM.PublicRead


