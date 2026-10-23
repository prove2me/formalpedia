-- Prove2me | Definitions.Def_AssemblyCoord_Feedback_Model
-- name    : AssemblyCoord_Feedback_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:58.495518+00:00
-- url     : https://prove2.me/theorems/cf8049a5-37b4-4d13-a41c-9375d0922d42
-- title:
--   §3, §3.1 and Definition 2, pp. 6–10, oa4–oa5 — M-contractor N-period minimum-effort game with feedback: histories, strategies, profit (2), SPE, SPSE (24)
-- statement:
--   This file sets up the $M$-contractor, $N$-period assembly coordination game with periodic information feedback of Zhang, Shokoohyar, Qi and Katok.
--
--   **Parameters.** There are $M$ contractors, indexed $i = 1,\dots,M$, and $N$ periods. Each contractor's total effort over the $N$ periods lies in $[\underline q, \bar q]$ and the effort in each period lies in $[\underline q/N, \bar q/N]$. The OEM's payoff-dominant target is $q^*$, $p$ is its marginal benefit of project effort, $\gamma$ is the proportion of the OEM payoff each contractor receives, and $c$ is the marginal cost of effort. The standing assumptions are
--   $$1 \le M,\quad 1 \le N,\quad 0 \le \underline q < q^* < \bar q,\quad p > 0,\quad \gamma > 0,\quad c > 0.$$
--
--   **Play.** All contractors start with effort level $\hat q_{i,0}$ (zero in the main model). In period $n$ each contractor first observes every contractor's effort so far (the feedback) and then all simultaneously choose $q_{i,n} \in [\underline q/N, \bar q/N]$. The cumulative level is $\hat q_{i,n} = \hat q_{i,0} + \sum_{t \le n} q_{i,t}$. A *history* is the list of effort profiles played so far, and a pure strategy of contractor $i$ maps each history to the current period's effort.
--
--   **Payoffs.** The project level is $q_{\min}(\hat{\mathbf q}_N) = \min_i \hat q_{i,N}$, the OEM payoff is $S = p\min\{q_{\min}(\hat{\mathbf q}_N), q^*\}$ (equation (1)), and contractor $i$'s profit is (equation (2))
--   $$\pi_i(\hat{\mathbf q}_N) = \gamma\, p \min\{q_{\min}(\hat{\mathbf q}_N), q^*\} - c\,\hat q_{i,N}.$$
--
--   **SPE.** A strategy profile is a subgame-perfect equilibrium if all its strategies are feasible and at every history with feasible past efforts and fewer than $N$ periods played, no contractor can raise its final profit by switching to another feasible strategy.
--
--   **SPSE (Definition 2).** For a history $h$, let $\hat E(h)$ be the set of final level vectors produced by continuing some SPE from $h$. The secure value of contractor $i$ choosing final level $y$ at $h$ is
--   $$V_i(h, y) = \inf_{x \in \hat E(h)} \pi_i(y;\, x_{-i}),$$
--   the worst profit against the other contractors' components of the SPE outcomes. A profile $\sigma^\dagger$ is a subgame-perfect secure equilibrium if it is an SPE and, at the start of every period $n = 1,\dots,N$ along its own path, every contractor's own final level maximizes $V_i(h, \cdot)$ over the $i$-th components of $\hat E(h)$; this is condition (24).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Contractors are `Fin M` and periods are 0-based: `pathHist σ n` is the history before the paper's period $n+1$. Strategies are history-dependent, since under feedback every past effort is observed; restricting to state-dependent strategies would shrink the set of SPEs that Definition 2 compares against. Condition (24) is stated with final level vectors instead of the period-$n$-to-$N$ totals; with the history fixed the two are in bijection and the profit depends only on the final levels. The "$=$ arg max" of (24) is read as membership in the argmax, the inner "min" as an infimum (`sInf`), and (24) is imposed only at the SPSE's own on-path histories, as the definition's "with the state of period $n$, $\hat{\mathbf q}^\dagger_{n-1}$" says. The positivity of $p$, $\gamma$, $c$ and $1 \le M$, $1 \le N$ are implicit in the meaning of the parameters and are stated explicitly.
-- source:
--   Zhang, Shokoohyar, Qi & Katok, Coordination for assembly, author manuscript (10 July 2025) of MSOM doi:10.1287/msom.2023.0342, pp. 6–7 (PDF 6–7), §3, eqs. (1)–(2); p. 10 (PDF 10), §3.1; oa4–oa5 (PDF 36–37), Online Appendix OA.2, Definition 2, (24)

import Mathlib

namespace AssemblyCoord.Feedback

/-- Parameters, §3 (p. 7): `M` contractors, `N` periods (= feedback periods, §3.1), total effort
bounds `qlo` (q̲, the minimum) and `qhi` (q̄, the maximum), the OEM's effort target `qstar` (q*),
marginal benefit `p`, contractor share `γ`, marginal effort cost `c`. -/
structure Params where
  M : ℕ
  N : ℕ
  qlo : ℝ
  qhi : ℝ
  qstar : ℝ
  p : ℝ
  γ : ℝ
  c : ℝ

/-- The standing assumptions of §3 (pp. 6–7): at least one contractor and one period,
`q̄ > q* > q̲ ≥ 0`, and positive `p`, `γ`, `c`. -/
def Params.Standing (P : Params) : Prop :=
  1 ≤ P.M ∧ 1 ≤ P.N ∧ 0 ≤ P.qlo ∧ P.qlo < P.qstar ∧ P.qstar < P.qhi ∧
  0 < P.p ∧ 0 < P.γ ∧ 0 < P.c

/-- A history: the effort profiles of the periods played so far, oldest first. Under the
information-feedback mechanism every contractor observes it before choosing the current
period's effort. -/
abbrev History (M : ℕ) := List (Fin M → ℝ)

/-- A pure history-dependent strategy profile: `σ i h` is contractor `i`'s effort in the current
period after history `h`. -/
abbrev Profile (M : ℕ) := Fin M → History M → ℝ

/-- Per-period effort range `[q̲/N, q̄/N]` (p. 7). -/
def Params.FeasibleEffort (P : Params) (e : ℝ) : Prop :=
  P.qlo / P.N ≤ e ∧ e ≤ P.qhi / P.N

/-- A strategy is feasible when it prescribes a feasible effort after every history. -/
def Params.FeasibleStrategy (P : Params) (s : History P.M → ℝ) : Prop :=
  ∀ h, P.FeasibleEffort (s h)

/-- A history at which the contractors still move (fewer than `N` periods played) and whose past
efforts are all feasible. -/
def Params.FeasibleHistory (P : Params) (h : History P.M) : Prop :=
  h.length < P.N ∧ ∀ a ∈ h, ∀ i, P.FeasibleEffort (a i)

/-- `k` further periods of play of `σ` after history `h`. -/
def play {M : ℕ} (σ : Profile M) : History M → ℕ → History M
  | h, 0 => h
  | h, k + 1 => play σ (h ++ [fun i => σ i h]) k

/-- Cumulative effort level `q̂_i` after history `h`, from initial levels `q0`
(`q0 = 0` in the main model). -/
def level {M : ℕ} (q0 : Fin M → ℝ) (h : History M) (i : Fin M) : ℝ :=
  q0 i + (h.map (fun a => a i)).sum

/-- Final levels `q̂_N` when `σ` is played from history `h` to the end of period `N`. -/
def Params.final (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) (h : History P.M) :
    Fin P.M → ℝ :=
  level q0 (play σ h (P.N - h.length))

/-- Project effort level `q_min = min_i q̂_{i,N}`. -/
noncomputable def projectLevel {M : ℕ} (x : Fin M → ℝ) : ℝ := ⨅ j, x j

/-- Contractor `i`'s profit (2), `γ S(q_min) − c q̂_{i,N}`, with the OEM payoff (1)
`S(q_min) = p min{q_min, q*}`, as a function of the final level vector `x`. -/
noncomputable def Params.profit (P : Params) (x : Fin P.M → ℝ) (i : Fin P.M) : ℝ :=
  P.γ * (P.p * min (projectLevel x) P.qstar) - P.c * x i

/-- Subgame-perfect equilibrium: every strategy is feasible, and at every feasible history no
contractor gains by switching to any feasible strategy. -/
def Params.IsSPE (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) : Prop :=
  (∀ i, P.FeasibleStrategy (σ i)) ∧
  ∀ h, P.FeasibleHistory h → ∀ (i : Fin P.M) (τ : History P.M → ℝ), P.FeasibleStrategy τ →
    P.profit (P.final q0 (Function.update σ i τ) h) i ≤ P.profit (P.final q0 σ h) i

/-- The history after the first `n` periods of `σ`'s own path. -/
def pathHist {M : ℕ} (σ : Profile M) (n : ℕ) : History M := play σ [] n

/-- `Ê_{n:N}` at history `h`: the final level vectors of all SPEs continued from `h`. -/
def Params.SPEOutcomes (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) :
    Set (Fin P.M → ℝ) :=
  {x | ∃ σ', P.IsSPE q0 σ' ∧ P.final q0 σ' h = x}

/-- The inner "min" of (24): contractor `i`'s worst profit when its own final level is `y` and
the other contractors' final levels range over their components of the SPE outcomes at `h`. -/
noncomputable def Params.secureValue (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M)
    (i : Fin P.M) (y : ℝ) : ℝ :=
  sInf ((fun x => P.profit (Function.update x i y) i) '' P.SPEOutcomes q0 h)

/-- Definition 2 (SPSE): an SPE such that, at the start of every period along its own path,
each contractor's own final level maximizes the secure value (24) over its components of the
SPE outcomes of that subgame. -/
def Params.IsSPSE (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) : Prop :=
  P.IsSPE q0 σ ∧ ∀ n, n < P.N → ∀ i : Fin P.M,
    ∀ y ∈ (fun x => x i) '' P.SPEOutcomes q0 (pathHist σ n),
      P.secureValue q0 (pathHist σ n) i y ≤
        P.secureValue q0 (pathHist σ n) i (P.final q0 σ (pathHist σ n) i)

end AssemblyCoord.Feedback


