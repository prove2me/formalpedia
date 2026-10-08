-- Prove2me | Definitions.Def_ReentrantScheduling_FBFS_Model
-- name    : ReentrantScheduling_FBFS_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:09.735309+00:00
-- url     : https://prove2.me/theorems/06b39668-96d9-4b07-873f-d35cf0a3375f
-- title:
--   §II, pp. 1408–1409 — nonacyclic flow line, admissible nonidling nonpreemptive buffer-priority runs, arrivals (1), load (3), x(t), stability (4)
-- statement:
--   This file sets up the manufacturing model of §II of Lu and Kumar (1991): a **nonacyclic flow line**, today usually called a reentrant line, together with its sample paths under a nonidling, nonpreemptive buffer priority policy.
--
--   **The line.** There are $S$ service centers; center $\sigma$ has $m_\sigma\ge 1$ identical machines in parallel, each working on one part at a time. Every part visits $l\ge 1$ buffers $b_1,\dots,b_l$ in this order. Buffer $b_i$ sits at center $\sigma_i$, and a part in $b_i$ needs $\tau_i>0$ time units of uninterrupted processing on one machine of $\sigma_i$. The work per machine that one part brings to center $\sigma$, the load and the largest processing time are
--   $$w_\sigma=\sum_{i:\,\sigma_i=\sigma}\frac{\tau_i}{m_\sigma},\qquad \rho=\max_\sigma \lambda w_\sigma=\lambda\bar w,\qquad \bar\tau=\max_j\tau_j ,$$
--   displays (2), (3) and (7). The file also defines $w^{(k)}=\max_{k\le j\le l}\sum_{i\ge k,\ \sigma_i=\sigma_j}\tau_i/m_{\sigma_j}$ of (6).
--
--   **Runs.** A run consists of a set of parts with an injective line order, a finite set of *initial* parts present at time $0$ (in any buffer, possibly already in service), and the *released* parts, which enter $b_1$ at their release times $\alpha(\pi)\ge 0$; only finitely many parts are released by any time $t$. For each part and each buffer from its entry buffer on, the run records the instant its service there begins, possibly $+\infty$ (never). A part arrives at its entry buffer at its release time and at $b_{i+1}$ when its service at $b_i$ ends; its exit time $e(\pi)$ is the end of its service at $b_l$. At time $t$ a part is *in service* at $b_i$ if its service there began at or before $t$ and has not ended, and *waiting* in $b_i$ if it has arrived there and its service has not begun.
--
--   **Admissibility.** A run is admissible for a priority relation "$b_j$ is served before $b_i$" if, at every time $t\ge0$:
--   1. service at a buffer begins no earlier than arrival there (an initial part may already be in service at time $0$);
--   2. at most $m_\sigma$ parts are in service at center $\sigma$;
--   3. (nonidling) if some part waits at center $\sigma$, all $m_\sigma$ machines are busy;
--   4. a machine takes up the part at the head of a buffer: no part ahead of it in the line order is waiting in the same buffer;
--   5. the line order puts initial parts before released ones, deeper buffers first among initial parts, and earlier releases first among released parts;
--   6. when service of a part begins at $b_i$, no part is waiting in a buffer $b_j$ of the same center that has priority over $b_i$.
--
--   **First buffer first serve** (FBFS) gives $b_j$ priority over $b_i$ when $j<i$; **last buffer first serve** (LBFS) when $j>i$.
--
--   **Arrivals and stability.** The releases satisfy the burstiness constraint (1) with constants $\lambda,\gamma\ge0$ if, writing $u(t)$ for the number of parts released in $[0,t]$,
--   $$u(t)-u(s)\le\lambda(t-s)+\gamma\qquad\text{for all }0\le s\le t .$$
--   The number in the system $x(t)$ counts the parts released by time $t$ that have not exited. A run is **stable** in the sense of (4) if there is $\Gamma\ge0$ with
--   $$e(\pi)-\alpha(\pi)\le\Gamma\qquad\text{for all parts }\pi .$$
--
--   These objects are the language of Theorem 1 (FBFS is stable) and of its proof.
--
--   **Formalization Note** Buffers are 0-based: the paper's $b_i,\sigma_i,\tau_i$ are Lean index $i-1$. Start and exit times live in `WithTop ℝ`, so a part that is never served has exit time $\top$ and stability rules this out. All counts (capacity, nonidling, arrivals, $x(t)$) use `Set.encard`, which is $\top$ on infinite sets, never `Set.ncard`. The positivity $\tau_i>0$ is pinned: §II does not state it, and the proof of Theorem 1 divides by $\tau_1$. The load is written $\lambda\bar w$, equal to $\max_\sigma\lambda w_\sigma$ for $\lambda\ge0$. The dispatch constraints are imposed at times $t\ge 0$ only. The line order breaks ties between simultaneous arrivals so that every buffer is FIFO.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, pp. 1408–1409, §II, (1)–(4); p. 1410, (6), (7), w̄

import Mathlib

namespace ReentrantScheduling.FBFS

open Finset

/-- A nonacyclic flow line (Lu–Kumar 1991, §II, p. 1408).

* `S` service centers; center `σ` has `m σ > 0` identical machines in parallel.
* Every part visits `l > 0` buffers in sequence. At its `i`-th visit it waits in buffer `b_i`
  at center `center i` (the paper's `σ_i`) and needs `τ i` time units of uninterrupted
  processing on one machine of that center.
* `τ i > 0` is a pinned hypothesis: §II never states it, the proof of Theorem 1 divides by `τ_1`.

Buffers are 0-based: the paper's `b_i`, `σ_i`, `τ_i` are the Lean index `i - 1`. -/
structure Line where
  S : ℕ
  m : Fin S → ℕ
  m_pos : ∀ σ, 0 < m σ
  l : ℕ
  l_pos : 0 < l
  center : Fin l → Fin S
  τ : Fin l → ℝ
  τ_pos : ∀ i, 0 < τ i

namespace Line

variable (L : Line)

/-- `w σ = ∑_{i : σ_i = σ} τ_i / m_σ`, the work per machine that one part brings to center `σ`
(display (2), p. 1408). -/
noncomputable def w (σ : Fin L.S) : ℝ :=
  ∑ i ∈ univ.filter (fun i => L.center i = σ), L.τ i / (L.m σ : ℝ)

/-- `w̄ = max_σ w_σ` (p. 1410). The line has at least one center, namely `σ_1`. -/
noncomputable def wbar : ℝ :=
  univ.sup' ⟨L.center ⟨0, L.l_pos⟩, mem_univ _⟩ L.w

/-- The load `ρ = max_σ λ w_σ` of display (3), p. 1408, written `λ w̄` (equal for `λ ≥ 0`). -/
noncomputable def load (lam : ℝ) : ℝ := lam * L.wbar

/-- `τ̄ = max_j τ_j` (display (7), p. 1410; also p. 1409). -/
noncomputable def τbar : ℝ :=
  univ.sup' ⟨⟨0, L.l_pos⟩, mem_univ _⟩ L.τ

/-- `w^(k) = max_{k ≤ j ≤ l} ∑_{i ≥ k, σ_i = σ_j} τ_i / m_{σ_j}` (display (6), p. 1410), 0-based. -/
noncomputable def wk (k : Fin L.l) : ℝ :=
  (univ.filter (fun j => k ≤ j)).sup' ⟨k, by simp⟩
    (fun j => ∑ i ∈ univ.filter (fun i => k ≤ i ∧ L.center i = L.center j),
      L.τ i / (L.m (L.center j) : ℝ))

/-- First buffer first serve (p. 1408): `b_j` has priority over `b_i` iff `j < i`. -/
abbrev fbfs : Fin L.l → Fin L.l → Prop := fun j i => j < i

/-- Last buffer first serve (p. 1408): `b_j` has priority over `b_i` iff `i < j`. -/
abbrev lbfs : Fin L.l → Fin L.l → Prop := fun j i => i < j

end Line

/-- A sample path (run) of the line `L`.

* `Part` is the set of parts; `ord` is an injective line order, used to break ties.
* `initial p`: part `p` is in the system at time `0`; there are finitely many such parts.
* `entry p` is the buffer `p` first occupies: buffer `b_1` (index `0`) for released parts,
  any buffer for initial parts.
* `α p` is the release time `α(π)`: `α p ≥ 0` for released parts, `α p = 0` for initial ones,
  and only finitely many parts are released by any time `t`.
* `start p i` is the instant service of `p` at buffer `i` begins; `⊤` means never. Only
  `entry p ≤ i` is meaningful. -/
structure Run (L : Line) where
  Part : Type
  ord : Part → ℕ
  ord_inj : Function.Injective ord
  initial : Part → Prop
  initial_finite : {p | initial p}.Finite
  entry : Part → Fin L.l
  α : Part → ℝ
  entry_released : ∀ p, ¬ initial p → entry p = ⟨0, L.l_pos⟩
  α_released : ∀ p, ¬ initial p → 0 ≤ α p
  α_initial : ∀ p, initial p → α p = 0
  α_finite : ∀ t : ℝ, {p | α p ≤ t}.Finite
  start : Part → Fin L.l → WithTop ℝ

namespace Run

variable {L : Line} (R : Run L)

/-- The instant part `p` arrives at buffer `i`: its release time at `entry p`, and the end of
its service at buffer `i - 1` for later buffers; `⊤` (never) for buffers before `entry p`. -/
noncomputable def arrive (p : R.Part) (i : Fin L.l) : WithTop ℝ :=
  if i = R.entry p then ((R.α p : ℝ) : WithTop ℝ)
  else if R.entry p < i then
    R.start p ⟨i.val - 1, by omega⟩ + ((L.τ ⟨i.val - 1, by omega⟩ : ℝ) : WithTop ℝ)
  else ⊤

/-- The exit time `e(π)`: the end of service at the last buffer `b_l`; `⊤` if never served. -/
noncomputable def exit (p : R.Part) : WithTop ℝ :=
  R.start p ⟨L.l - 1, by have := L.l_pos; omega⟩ +
    ((L.τ ⟨L.l - 1, by have := L.l_pos; omega⟩ : ℝ) : WithTop ℝ)

/-- Part `p` is in service at buffer `i` at time `t`. -/
def InService (p : R.Part) (i : Fin L.l) (t : ℝ) : Prop :=
  R.entry p ≤ i ∧ R.start p i ≤ (t : WithTop ℝ) ∧
    (t : WithTop ℝ) < R.start p i + ((L.τ i : ℝ) : WithTop ℝ)

/-- Part `p` is waiting (not in service) in buffer `i` at time `t`; includes `start p i = ⊤`. -/
def Waiting (p : R.Part) (i : Fin L.l) (t : ℝ) : Prop :=
  R.entry p ≤ i ∧ R.arrive p i ≤ (t : WithTop ℝ) ∧ (t : WithTop ℝ) < R.start p i

/-- The set of (part, buffer) pairs in service at center `σ` at time `t`. -/
def busySlots (σ : Fin L.S) (t : ℝ) : Set (R.Part × Fin L.l) :=
  {x | L.center x.2 = σ ∧ R.InService x.1 x.2 t}

/-- Admissibility of a run for the priority relation `prio j i` ("buffer `j` is served before
buffer `i` at a common center"): a nonidling, nonpreemptive, head-of-buffer dispatch (§II,
p. 1408). -/
structure Admissible (prio : Fin L.l → Fin L.l → Prop) : Prop where
  /-- Service at a buffer begins no earlier than arrival there, except that an initial part
  may already be in service at time `0`. -/
  precedence : ∀ p i, R.entry p ≤ i →
    (R.arrive p i ≤ R.start p i ∨
      (R.initial p ∧ i = R.entry p ∧ ((-(L.τ i) : ℝ) : WithTop ℝ) < R.start p i ∧
        R.start p i ≤ ((0 : ℝ) : WithTop ℝ)))
  /-- At most `m σ` parts are in service at center `σ`. -/
  capacity : ∀ σ (t : ℝ), 0 ≤ t → (R.busySlots σ t).encard ≤ L.m σ
  /-- Nonidling: if a part waits at center `σ`, all `m σ` machines are busy. -/
  nonidling : ∀ σ (t : ℝ), 0 ≤ t → (∃ p i, L.center i = σ ∧ R.Waiting p i t) →
    (R.busySlots σ t).encard = L.m σ
  /-- A machine takes up the part at the head of the buffer. -/
  head : ∀ p i (t : ℝ), 0 ≤ t → R.entry p ≤ i → R.start p i = (t : WithTop ℝ) →
    ∀ q, R.ord q < R.ord p → ¬ R.Waiting q i t
  /-- The line order: initial parts first, deeper buffer first among them, earlier release
  first among released parts. -/
  ord_initial : ∀ p q, R.initial p → ¬ R.initial q → R.ord p < R.ord q
  ord_deeper : ∀ p q, R.initial p → R.initial q → R.entry q < R.entry p → R.ord p < R.ord q
  ord_release : ∀ p q, ¬ R.initial p → ¬ R.initial q → R.α p < R.α q → R.ord p < R.ord q
  /-- The buffer priority rule: no part waits in a higher-priority buffer at the same center
  when service begins. -/
  priority : ∀ p i (t : ℝ), 0 ≤ t → R.entry p ≤ i → R.start p i = (t : WithTop ℝ) →
    ∀ q j, L.center j = L.center i → prio j i → ¬ R.Waiting q j t

/-- The arrival constraint (1), p. 1408: `u(t) - u(s) ≤ λ (t - s) + γ` for all `0 ≤ s ≤ t`,
where `u(t)` counts the parts released in `[0, t]`. -/
def Arrivals (lam γ : ℝ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s ≤ t →
    (({p | ¬ R.initial p ∧ s < R.α p ∧ R.α p ≤ t}.encard : ℕ∞) : ENNReal) ≤
      ENNReal.ofReal (lam * (t - s) + γ)

/-- `x(t)`: the number of parts in the system at time `t` (waiting or in service). -/
noncomputable def x (t : ℝ) : ℕ∞ :=
  {p | R.α p ≤ t ∧ (t : WithTop ℝ) < R.exit p}.encard

/-- Stability (4), p. 1409: `e(π) - α(π) ≤ Γ` for all parts, for some `Γ ≥ 0`. -/
def Stable : Prop :=
  ∃ Γ : ℝ, 0 ≤ Γ ∧ ∀ p, R.exit p ≤ ((R.α p + Γ : ℝ) : WithTop ℝ)

end Run

end ReentrantScheduling.FBFS


