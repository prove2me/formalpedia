-- Prove2me | Definitions.Def_ReentrantScheduling_LBFS_Model
-- name    : ReentrantScheduling_LBFS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:59.658763+00:00
-- url     : https://prove2.me/theorems/437111b4-8364-4a47-a0ac-d061cf3e6468
-- title:
--   §II, pp. 1408–1409 — nonacyclic flow line, admissible nonidling nonpreemptive buffer-priority runs, arrivals (1), load (3), x(t), stability (4)
-- statement:
--   This file sets up the manufacturing model of Lu and Kumar (1991), §II.
--
--   **The line.** There are $S$ service centers; center $\sigma$ has $m_\sigma \ge 1$ identical machines in parallel, each working on one part at a time. Every part follows the same route: it visits buffers $b_1, b_2, \dots, b_l$ ($l \ge 1$) in order, buffer $b_i$ sits at center $\sigma_i$, and a part in $b_i$ needs $\tau_i > 0$ time units of uninterrupted processing on one of the $m_{\sigma_i}$ machines. A center may be visited several times (the line is *nonacyclic*, i.e. reentrant). Derived quantities:
--
--   $$
--   w_\sigma = \sum_{i:\ \sigma_i = \sigma} \frac{\tau_i}{m_\sigma}, \qquad \overline w = \max_\sigma w_\sigma, \qquad \rho = \lambda \overline w, \qquad \overline\tau = \max_j \tau_j,
--   $$
--
--   $$
--   w^{(k)} = \max_{k \le j \le l} \ \sum_{i:\ \sigma_i = \sigma_j,\ i \ge k} \frac{\tau_i}{m_{\sigma_j}} \quad (6).
--   $$
--
--   Here $w_\sigma$ is the work per machine that one part brings to center $\sigma$ (2), $\rho$ is the load (3), and $w^{(k)}$ is the same maximum computed for the truncated line $b_k, \dots, b_l$.
--
--   **Runs.** A run consists of a set of parts, each with a release time $\alpha(\pi)$ and, for each buffer, the instant its service there begins (possibly never). Finitely many parts are present at time $0$ (they may sit in any buffer, and may already be in service); all other parts are released into $b_1$ at times $\alpha(\pi) \ge 0$, finitely many by any time. A part arrives at $b_{i+1}$ when its service at $b_i$ ends, and exits at $e(\pi)$, the end of its service at $b_l$. The parts are listed in *line order*: parts present at time $0$ first (deeper buffer first, then earlier service start), then released parts by release time. A run is **admissible** for a buffer priority rule when
--
--   1. service at a buffer begins only after the part has arrived there;
--   2. at most $m_\sigma$ parts are in service at center $\sigma$ at any time;
--   3. it is *nonidling*: if a part is waiting at center $\sigma$, all $m_\sigma$ machines are busy;
--   4. a machine takes the part at the head of a buffer (the first waiting part in line order);
--   5. a machine takes a part from buffer $b_i$ only if no part waits in a buffer of the same center with higher priority.
--
--   Under **FBFS** buffer $b_j$ has priority over $b_i$ when $j < i$; under **LBFS** when $j > i$. Service is nonpreemptive: once begun it lasts exactly $\tau_i$.
--
--   **Arrivals, number in system, stability.** The arrivals satisfy (1) with constants $\lambda, \gamma \ge 0$ if, writing $u(t)$ for the number of parts released in $[0,t]$,
--
--   $$
--   u(t) - u(s) \le \lambda (t-s) + \gamma \qquad \text{for all } 0 \le s \le t. \quad (1)
--   $$
--
--   $x(t)$ is the number of parts in the system at time $t$ (released by $t$ and not yet exited; parts in service count). A run is **stable** (4) if some $\Gamma \ge 0$ bounds every delay: $e(\pi) - \alpha(\pi) \le \Gamma$ for all parts $\pi$.
--
--   This is the common setting of every theorem of the paper's §§III–V.
--
--   **Formalization Note.** Buffers are 0-based: the paper's $b_i$ is Lean index $i-1$, so `wk k` is the paper's $w^{(k+1)}$. Service start and exit times live in `WithTop ℝ`, with `⊤` meaning "never", so a run need not serve every part; stability and the delay bounds therefore assert that parts are served. The counts in the capacity and nonidling rules, in (1) and in $x(t)$ use `Set.encard`, so infinite sets are not counted as $0$. The line order `ord` is injective and breaks ties between simultaneous arrivals; with the head-of-buffer rule it makes every buffer first-in-first-out. Rules 2–5 are imposed for $t \ge 0$. $\tau_i > 0$ is pinned: §II leaves it implicit, the paper's proofs divide by $\tau_i$, and its only zero processing times (Example 1) are ones the authors wish to remove. The fourth line-order clause (initial parts in one buffer ordered by service start) is needed for "parts exit in the order they enter" when several initial parts are already in service at time $0$.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, pp. 1408–1409, §II, (1)–(4); p. 1410, (6)–(7) and Theorem 2's w̄

import Mathlib

namespace ReentrantScheduling.LBFS

/-- A nonacyclic flow line (Lu–Kumar 1991, §II, p. 1408). There are `S` service centers;
center `σ` has `m σ > 0` identical machines in parallel. Every part visits the `l > 0` buffers
`b_1, …, b_l` in order; buffer `b_i` sits at center `center i` (the paper's `σ_i`) and a part
there needs `τ i > 0` time units of uninterrupted processing on one machine.
Buffers are 0-based: the paper's `b_i` is the Lean index `i - 1`. -/
structure Line where
  /-- number of service centers -/
  S : ℕ
  /-- number of identical machines at each center -/
  m : Fin S → ℕ
  m_pos : ∀ σ, 0 < m σ
  /-- number of buffers on the route -/
  l : ℕ
  l_pos : 0 < l
  /-- the center `σ_i` of buffer `b_i` -/
  center : Fin l → Fin S
  /-- processing time `τ_i` at buffer `b_i` -/
  τ : Fin l → ℝ
  τ_pos : ∀ i, 0 < τ i

namespace Line

variable (L : Line)

/-- The first buffer `b_1` (Lean index `0`). -/
def first : Fin L.l := ⟨0, L.l_pos⟩

/-- The last buffer `b_l` (Lean index `l - 1`). -/
def last : Fin L.l := ⟨L.l - 1, by have := L.l_pos; omega⟩

/-- `w_σ := Σ_{i | σ_i = σ} τ_i / m_σ`, the work brought per machine at center `σ` by one
incoming part, (2). -/
noncomputable def w (σ : Fin L.S) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => L.center i = σ), L.τ i / (L.m σ : ℝ)

/-- `w̄ := max_σ w_σ` (Theorem 2, p. 1410). -/
noncomputable def wbar : ℝ :=
  Finset.univ.sup' ⟨L.center L.first, Finset.mem_univ _⟩ L.w

/-- The load `ρ := max_σ λ w_σ` of (3); for `λ ≥ 0` this is `λ w̄`. -/
noncomputable def load (lam : ℝ) : ℝ := lam * L.wbar

/-- `τ̄ := max_j τ_j`, (7). -/
noncomputable def τbar : ℝ :=
  Finset.univ.sup' ⟨L.first, Finset.mem_univ _⟩ L.τ

/-- `w^(k) := max_{k ≤ j ≤ l} Σ_{i | σ_i = σ_j, i ≥ k} τ_i / m_{σ_j}`, (6), with a 0-based
buffer index `k` (the paper's `w^(k+1)`). -/
noncomputable def wk (k : Fin L.l) : ℝ :=
  (Finset.univ.filter (fun j : Fin L.l => k ≤ j)).sup' ⟨k, by simp⟩
    (fun j => ∑ i ∈ Finset.univ.filter (fun i => k ≤ i ∧ L.center i = L.center j),
      L.τ i / (L.m (L.center j) : ℝ))

/-- First Buffer First Serve: at a common center, buffer `j` has priority over buffer `i`
iff `j < i` (p. 1408). -/
def fbfsPrio : Fin L.l → Fin L.l → Prop := fun j i => j < i

/-- Last Buffer First Serve: at a common center, buffer `j` has priority over buffer `i`
iff `i < j` (p. 1408). -/
def lbfsPrio : Fin L.l → Fin L.l → Prop := fun j i => i < j

end Line

/-- A sample path (run) of the line `L` (§II, pp. 1408–1409).

* `Part` is the set of parts; `ord` lists them injectively in line order (used to break ties).
* `initial p`: part `p` is in the system at time `0`; there are finitely many such parts.
* `entry p` is the buffer `p` first occupies: released parts enter at `b_1`, an initial part
  may sit in any buffer.
* `α p` is the release time `α(π)`; released parts have `α p ≥ 0`, initial parts `α p = 0`,
  and only finitely many parts are released by any time `t`.
* `start p i` is the instant service of `p` at buffer `i` begins, `⊤` if never; only
  `entry p ≤ i` is meaningful. -/
structure Run (L : Line) where
  Part : Type
  ord : Part → ℕ
  ord_inj : Function.Injective ord
  initial : Part → Prop
  initial_finite : {p | initial p}.Finite
  entry : Part → Fin L.l
  released_entry : ∀ p, ¬ initial p → entry p = L.first
  α : Part → ℝ
  released_nonneg : ∀ p, ¬ initial p → 0 ≤ α p
  initial_zero : ∀ p, initial p → α p = 0
  released_finite : ∀ t : ℝ, {p | α p ≤ t}.Finite
  start : Part → Fin L.l → WithTop ℝ

namespace Run

variable {L : Line} (R : Run L)

/-- The time part `p` arrives at buffer `i`: its release time at `entry p`, and the end of its
service at the previous buffer otherwise (`⊤` if that never happens). Meaningless (`⊤`) for
`i < entry p`. -/
noncomputable def arrive (p : R.Part) (i : Fin L.l) : WithTop ℝ :=
  if i = R.entry p then ((R.α p : ℝ) : WithTop ℝ)
  else if h : R.entry p < i then
    R.start p ⟨i.val - 1, by omega⟩ + ((L.τ ⟨i.val - 1, by omega⟩ : ℝ) : WithTop ℝ)
  else ⊤

/-- The exit time `e(π)`: the end of service at the last buffer (`⊤` if never). -/
noncomputable def exit (p : R.Part) : WithTop ℝ :=
  R.start p L.last + ((L.τ L.last : ℝ) : WithTop ℝ)

/-- Part `p` is in service at buffer `i` at time `t`. -/
def inService (p : R.Part) (i : Fin L.l) (t : ℝ) : Prop :=
  R.entry p ≤ i ∧ R.start p i ≤ (t : WithTop ℝ) ∧
    (t : WithTop ℝ) < R.start p i + ((L.τ i : ℝ) : WithTop ℝ)

/-- Part `p` is waiting (not in service) in buffer `i` at time `t`; this includes waiting
forever (`start p i = ⊤`). -/
def waiting (p : R.Part) (i : Fin L.l) (t : ℝ) : Prop :=
  R.entry p ≤ i ∧ R.arrive p i ≤ (t : WithTop ℝ) ∧ (t : WithTop ℝ) < R.start p i

/-- The number of (part, buffer) pairs in service at center `σ` at time `t`, as an `encard`. -/
noncomputable def busyCount (σ : Fin L.S) (t : ℝ) : ℕ∞ :=
  {pi : R.Part × Fin L.l | L.center pi.2 = σ ∧ R.inService pi.1 pi.2 t}.encard

/-- The run is admissible for the priority relation `prio` (`prio j i`: at a common center,
buffer `j` is served before buffer `i`): a nonidling, nonpreemptive, head-of-buffer,
buffer-priority schedule (p. 1408). -/
structure Admissible (prio : Fin L.l → Fin L.l → Prop) : Prop where
  /-- 1. service at a buffer starts after arrival there; an initial part may already be in
  service at time `0`. -/
  precedence : ∀ p i, R.entry p ≤ i →
    R.arrive p i ≤ R.start p i ∨
      (i = R.entry p ∧ R.initial p ∧ (((-(L.τ i)) : ℝ) : WithTop ℝ) < R.start p i ∧
        R.start p i ≤ ((0 : ℝ) : WithTop ℝ))
  /-- 2. at most `m σ` parts in service at center `σ`. -/
  capacity : ∀ σ (t : ℝ), 0 ≤ t → R.busyCount σ t ≤ (L.m σ : ℕ∞)
  /-- 3. nonidling: if some part waits at center `σ`, all `m σ` machines are busy. -/
  nonidling : ∀ σ (t : ℝ), 0 ≤ t → (∃ p i, L.center i = σ ∧ R.waiting p i t) →
    R.busyCount σ t = (L.m σ : ℕ∞)
  /-- 4. a machine takes up the part at the head of the buffer. -/
  head : ∀ p i (t : ℝ), 0 ≤ t → R.entry p ≤ i → R.start p i = (t : WithTop ℝ) →
    ∀ q, R.ord q < R.ord p → ¬ R.waiting q i t
  /-- 5a. line order: initial parts before released ones. -/
  ord_initial : ∀ p q, R.initial p → ¬ R.initial q → R.ord p < R.ord q
  /-- 5b. line order: among initial parts, deeper buffer first. -/
  ord_deeper : ∀ p q, R.initial p → R.initial q → R.entry q < R.entry p → R.ord p < R.ord q
  /-- 5c. line order: among released parts, earlier release first. -/
  ord_release : ∀ p q, ¬ R.initial p → ¬ R.initial q → R.α p < R.α q → R.ord p < R.ord q
  /-- 5d. line order: among initial parts in the same buffer, earlier service start first. -/
  ord_start : ∀ p q, R.initial p → R.initial q → R.entry p = R.entry q →
    R.start p (R.entry p) < R.start q (R.entry q) → R.ord p < R.ord q
  /-- 6. buffer priority: no part waits in a higher-priority buffer of the same center when
  service starts. -/
  priority : ∀ p i (t : ℝ), 0 ≤ t → R.entry p ≤ i → R.start p i = (t : WithTop ℝ) →
    ∀ q j, L.center j = L.center i → prio j i → ¬ R.waiting q j t

/-- The arrival constraint (1): for all `0 ≤ s ≤ t`, the number `u(t) − u(s)` of parts released
in `(s, t]` is at most `λ(t − s) + γ`. -/
def Arrivals (lam γ : ℝ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    (({p | ¬ R.initial p ∧ s < R.α p ∧ R.α p ≤ t}.encard : ℕ∞) : ENNReal) ≤
      ENNReal.ofReal (lam * (t - s) + γ)

/-- `x(t)`: the number of parts in the system at time `t` (initial parts and parts in service
included; a part leaves at `e(π)`). -/
noncomputable def x (t : ℝ) : ℕ∞ :=
  {p | R.α p ≤ t ∧ (t : WithTop ℝ) < R.exit p}.encard

/-- Stability (4), p. 1409: some `Γ ≥ 0` bounds the delay `e(π) − α(π)` of every part. -/
def Stable : Prop :=
  ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ p, R.exit p ≤ ((R.α p + Γ : ℝ) : WithTop ℝ)

end Run

end ReentrantScheduling.LBFS


