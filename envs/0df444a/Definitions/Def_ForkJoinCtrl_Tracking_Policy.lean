-- Prove2me | Definitions.Def_ForkJoinCtrl_Tracking_Policy
-- name    : ForkJoinCtrl_Tracking_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:41.730026+00:00
-- url     : https://prove2.me/theorems/b904c6af-4232-4963-b3c7-d52bcff0bf4a
-- title:
--   Definition 2, p. 15 — the LP/QP-tracking policy with review epochs τ^r_in and the sets J^>, J^≤, J^< of p. 14
-- statement:
--   Let $(y^{*,r}(t),q^{*,r}(t))$ be the optimal solution of the LP (18) at the unscaled parameter $(Q^r_k(t),W^r_i(t))$ selected by the QP (19). For a shared server $i$ (p. 14)
--
--   $$\mathcal J^{>,r}_i(t)=\{j\in\mathcal J_i: Q^r_{ij}(t)>\lceil q^{*,r}_{ij}(t)\rceil\},\qquad \mathcal J^{\le,r}_i(t)=\{j\in\mathcal J_i: Q^r_{ij}(t)\le\lceil q^{*,r}_{ij}(t)\rceil\},$$
--
--   and $\mathcal J^{<,r}_i(t)=\arg\max_{j\in\mathcal J^{\le,r}_i(t)}(q^{*,r}_{ij}(t)-Q^r_{ij}(t))/\lambda_j$ with the limiting rates $\lambda_j$.
--
--   A **run under the proposed policy** (Definition 2, applied simultaneously at all shared servers) is an admissible run started empty, together with the process $(y^*,q^*)$, optimal for the QP at every $t\ge 0$, and review epochs $\tau^r_{in}\in\mathbb R_+\cup\{\infty\}$, $n\ge1$, with $\tau^r_{i1}=0$ and $\tau^r_{im}=\infty$ for $m>n$ once $\tau^r_{in}=\infty$. At each finite review epoch $t=\tau^r_{in}$:
--
--   1. **Step 2** (if $\mathcal J^{>,r}_i(t)=\emptyset$): the server serves one job of a single buffer $ij$ — a job at the head of a nonempty buffer if one exists, otherwise the first job that arrives externally after $t$ — and $\tau^r_{i(n+1)}$ is the first service completion epoch of server $i$ after $t$.
--   2. **Step 3** (otherwise): for some $m\in\mathcal J^{<,r}_i(t)$ the server does not serve type $m$, serves a buffer $ij$ only while $Q^r_{ij}>\lceil q^{*,r}_{ij}(t)\rceil$ (it processes excess jobs), never has two jobs in partial service (non-preemptive), and the period ends at
--
--   $$\tau^r_{i(n+1)}=\inf\{s\ge t: Q^r_{ij}(s)=\lceil q^{*,r}_{ij}(t)\rceil\ \forall j\in\mathcal J^{>,r}_i(t),\ Q^r_{ij}(s)\le\lceil q^{*,r}_{ij}(t)\rceil\ \forall j\in\mathcal J^{\le,r}_i(t)\setminus\{m\}\},$$
--
--   with $\inf\emptyset=\infty$.
--
--   The policy keeps the buffers in front of each shared server close to the QP-selected LP solution, which is what makes it asymptotically optimal.
--
--   **Formalization Note** The phrase "in an admissible and non-preemptive way" is read as: only buffers in excess of $\lceil q^{*,r}_{ij}(t)\rceil$ are served, type $m$ is not served, and no two buffers are in partial service at the same time, where a buffer is in partial service when $V_{ij}(S_{ij}(T_{ij}(s)))<T_{ij}(s)$. The choices left arbitrary by the paper (which excess job, which $m$, which head-of-line job) are existential. All conditions are required for almost every $\omega$; the review epochs are not required to be stopping times.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 13 (20), p. 14 (𝒥^{>,r}, 𝒥^{≤,r}, 𝒥^{<,r}), p. 15 Definition 2, p. 20 (τ^r_in)

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Model

namespace ForkJoinCtrl.Tracking

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Filter Topology

/-!
Özkan, arXiv:2002.01496v1, §5 (pp. 13–15) and Appendix C (p. 20): the optimal solution process
`(y^{*,r}, q^{*,r})` of the LP (18) selected by the QP (19), the sets `𝒥^{>,r}_i(t)`,
`𝒥^{≤,r}_i(t)`, `𝒥^{<,r}_i(t)`, and the proposed policy (Definition 2) with its review epochs
`τ^r_in ∈ ℝ₊ ∪ {∞}`.
-/

variable {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `⌈x⌉`, the smallest integer `≥ x`, as a real number. -/
noncomputable def ceilR (x : ℝ) : ℝ := ((⌈x⌉ : ℤ) : ℝ)

/-- `𝒥^{>,r}_i(t) := {j ∈ 𝒥_i : Q^r_ij(t) > ⌈q^{*,r}_ij(t)⌉}` (p. 14). -/
noncomputable def Jgt (X : Paths N Ω) (qs : Fin N.I → Fin N.J → Ω → ℝ → ℝ) (i : Fin N.I)
    (ω : Ω) (t : ℝ) : Finset (Fin N.J) :=
  (N.Ji i).filter (fun j => ceilR (qs i j ω t) < X.Qij i j ω t)

/-- `𝒥^{≤,r}_i(t) := {j ∈ 𝒥_i : Q^r_ij(t) ≤ ⌈q^{*,r}_ij(t)⌉}` (p. 14). -/
noncomputable def Jle (X : Paths N Ω) (qs : Fin N.I → Fin N.J → Ω → ℝ → ℝ) (i : Fin N.I)
    (ω : Ω) (t : ℝ) : Finset (Fin N.J) :=
  (N.Ji i).filter (fun j => X.Qij i j ω t ≤ ceilR (qs i j ω t))

/-- `𝒥^{<,r}_i(t) := argmax_{j ∈ 𝒥^{≤,r}_i(t)} (q^{*,r}_ij(t) − Q^r_ij(t)) / λ_j` (p. 14), with the
limiting rates `λ_j`. -/
noncomputable def Jlt (X : Paths N Ω) (qs : Fin N.I → Fin N.J → Ω → ℝ → ℝ) (i : Fin N.I)
    (ω : Ω) (t : ℝ) : Finset (Fin N.J) :=
  (Jle X qs i ω t).filter (fun j => ∀ l ∈ Jle X qs i ω t,
    (qs i l ω t - X.Qij i l ω t) / N.lam l ≤ (qs i j ω t - X.Qij i j ω t) / N.lam j)

/-- `D_i(s) = ∑_{j ∈ 𝒥_i} S_ij(T_ij(s))`, the number of service completions in shared server `i`
by time `s`. -/
noncomputable def completions (M : Model N Ω P) (X : Paths N Ω) (i : Fin N.I) (ω : Ω)
    (s : ℝ) : ℝ :=
  ∑ j ∈ N.Ji i, (M.Ss i j ω (X.Tij i j ω s) : ℝ)

/-- Buffer `ij` has a job in (partial) service at time `s`: `V_ij(S_ij(T_ij(s))) < T_ij(s)`, i.e.
server `i` has started, and not completed, the service of a type `j` job. -/
def InService (M : Model N Ω P) (X : Paths N Ω) (i : Fin N.I) (j : Fin N.J) (ω : Ω)
    (s : ℝ) : Prop :=
  M.Vs i j ω (M.Ss i j ω (X.Tij i j ω s)) < X.Tij i j ω s

/-- Step 2 of Definition 2 (p. 15) for a review period of shared server `i` that starts at the
current time `t` and ends at `t'` (`t' = ∞` allowed):
* `t'` is the first service completion epoch in server `i` after `t`: the completion count is
  constant on `[t, t')`, and, if `t'` is finite, `t < t'` and a completion occurs at `t'`;
* during `[t, t']` server `i` works on a single buffer `ij` only (one job);
* if some buffer `il`, `l ∈ 𝒥_i`, is nonempty at `t`, then `Q_ij(t) > 0` (an arbitrary job among
  those waiting at the head of the nonempty buffers);
* if all buffers of server `i` are empty at `t`, then `j` is the type of the first job that
  externally arrives after `t`: whenever some type `l ∈ 𝒥_i` has had an arrival in `(t, s]`, so has
  type `j`. -/
def Step2Rule (M : Model N Ω P) (r : ℕ) (X : Paths N Ω) (i : Fin N.I) (ω : Ω) (t : ℝ)
    (t' : ℝ≥0∞) : Prop :=
  (∀ s : ℝ, t ≤ s → ENNReal.ofReal s < t' →
    completions M X i ω s = completions M X i ω t) ∧
  (∀ e : ℝ, 0 ≤ e → t' = ENNReal.ofReal e →
    t < e ∧ completions M X i ω t < completions M X i ω e) ∧
  ∃ j ∈ N.Ji i,
    (∀ l ∈ N.Ji i, l ≠ j → ∀ s : ℝ, t ≤ s → ENNReal.ofReal s ≤ t' →
      X.Tij i l ω s = X.Tij i l ω t) ∧
    ((∃ l ∈ N.Ji i, 0 < X.Qij i l ω t) → 0 < X.Qij i j ω t) ∧
    ((∀ l ∈ N.Ji i, X.Qij i l ω t = 0) → ∀ s : ℝ, t ≤ s →
      (∃ l ∈ N.Ji i, M.A r l ω t < M.A r l ω s) → M.A r j ω t < M.A r j ω s)

/-- Step 3 of Definition 2 (p. 15) for a review period of shared server `i` that starts at the
current time `t` and ends at `t'`, given the QP-selected solution `qs`: there is an idled type
`m ∈ 𝒥^{<,r}_i(t)` such that, during `[t, t']`,
* server `i` does not process type `m` (`T_im` is constant);
* server `i` processes only excess jobs: `T_ij` is constant on every interval throughout which
  `Q_ij ≤ ⌈q^{*,r}_ij(t)⌉`;
* service is non-preemptive: at no time are two buffers of server `i` in partial service;
and the period ends at
`t' = inf{s ≥ t : Q_ij(s) = ⌈q^{*,r}_ij(t)⌉ ∀ j ∈ 𝒥^{>,r}_i(t), Q_ij(s) ≤ ⌈q^{*,r}_ij(t)⌉ ∀ j ∈ 𝒥^{≤,r}_i(t) \ {m}}`
(the infimum is taken in `ℝ₊ ∪ {∞}`, so it is `∞` when no such `s` exists). -/
def Step3Rule (M : Model N Ω P) (X : Paths N Ω) (qs : Fin N.I → Fin N.J → Ω → ℝ → ℝ)
    (i : Fin N.I) (ω : Ω) (t : ℝ) (t' : ℝ≥0∞) : Prop :=
  ∃ m ∈ Jlt X qs i ω t,
    (∀ s : ℝ, t ≤ s → ENNReal.ofReal s ≤ t' → X.Tij i m ω s = X.Tij i m ω t) ∧
    (∀ j ∈ N.Ji i, ∀ s₁ s₂ : ℝ, t ≤ s₁ → s₁ ≤ s₂ → ENNReal.ofReal s₂ ≤ t' →
      (∀ u ∈ Set.Icc s₁ s₂, X.Qij i j ω u ≤ ceilR (qs i j ω t)) →
      X.Tij i j ω s₂ = X.Tij i j ω s₁) ∧
    (∀ s : ℝ, t ≤ s → ENNReal.ofReal s ≤ t' → ∀ j ∈ N.Ji i, ∀ l ∈ N.Ji i, j ≠ l →
      ¬ (InService M X i j ω s ∧ InService M X i l ω s)) ∧
    t' = ⨅ (s : ℝ) (_ : t ≤ s ∧
        (∀ j ∈ Jgt X qs i ω t, X.Qij i j ω s = ceilR (qs i j ω t)) ∧
        (∀ j ∈ (Jle X qs i ω t).erase m, X.Qij i j ω s ≤ ceilR (qs i j ω t))),
      ENNReal.ofReal s

/-- A run of system `r` under the proposed policy (Definition 2, p. 15, implemented
simultaneously in all shared servers): an admissible run started empty, together with
* `ystar`, `qstar`: the optimal solution process `(y^{*,r}_j(t), q^{*,r}_ij(t))` of the LP (18)
  under the (unscaled) parameters `(Q^r_k(t), W^r_i(t))` selected by the QP (19) (p. 13), i.e. an
  optimal solution of the QP (19) at every `t ≥ 0`;
* `tau i n = τ^r_in ∈ ℝ₊ ∪ {∞}`, the start of the `n`th review period of shared server `i`
  (`n ≥ 1`; p. 20): `τ^r_i1 = 0`, and `τ^r_im = ∞` for `m > n` once `τ^r_in = ∞`;
* for every review period `n ≥ 1` starting at a finite `t = τ^r_in` (Step 1 solves the LP and
  the QP at `t`): if `𝒥^{>,r}_i(t) = ∅` the period is Step 2, otherwise Step 3, and it ends at
  `τ^r_{i(n+1)}`.
All conditions hold for `P`-almost every `ω`. -/
structure PolicyRun (M : Model N Ω P) (r : ℕ) extends Run M r where
  ystar : Fin N.J → Ω → ℝ → ℝ
  qstar : Fin N.I → Fin N.J → Ω → ℝ → ℝ
  tau : Fin N.I → ℕ → Ω → ℝ≥0∞
  policy : ∀ᵐ ω ∂P,
    (∀ t : ℝ, 0 ≤ t →
      QPOpt N (toPaths.b ω t) ⟨fun j => ystar j ω t, fun i j => qstar i j ω t⟩) ∧
    (∀ i, tau i 1 ω = 0) ∧
    (∀ i n, 1 ≤ n → tau i n ω = ⊤ → tau i (n + 1) ω = ⊤) ∧
    (∀ i n, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → tau i n ω = ENNReal.ofReal t →
      (Jgt toPaths qstar i ω t = ∅ → Step2Rule M r toPaths i ω t (tau i (n + 1) ω)) ∧
      (Jgt toPaths qstar i ω t ≠ ∅ → Step3Rule M toPaths qstar i ω t (tau i (n + 1) ω)))

end ForkJoinCtrl.Tracking


