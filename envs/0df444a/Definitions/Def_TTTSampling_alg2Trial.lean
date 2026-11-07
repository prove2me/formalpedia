-- Prove2me | Definitions.Def_TTTSampling_alg2Trial
-- name    : TTTSampling_alg2Trial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:06.486476+00:00
-- url     : https://prove2.me/theorems/a9e3a4fa-083d-4b7c-aa53-250ad86d53e9
-- title:
--   One trial (outer iteration $i$) of Algorithm 2, with its record
-- statement:
--   One **trial** of Algorithm 2 (Tree-structured Rejection Sampling) at node $w$ with class $\mathcal G$, density-ratio parameter $M\ge1$ and oracle parameter $R$, as on p.11:
--
--   1. Line 3: $w_{i,0}=w$, $\mathcal G_{i,0}=\{\eta\in\mathcal G \mid \frac1R\le\frac{\hat\mu(w)}{\eta(w)}\le R\}$, $\bar\eta_{i,0}$ its mean.
--   2. Stage $t\ge1$ starts at $w_{i,t}=w_{i,t-1}$. While $|w_{i,t}|<n$, every child passes the upper test $\frac{\hat\mu(w_{i,t}\circ y)}{\hat\mu(w_{i,t-1})\bar\eta_{i,t-1}(w_{i,t}\circ y\mid w_{i,t-1})}\le M$ and the lower test $\frac1M\le\frac{\hat\mu(w_{i,t})}{\hat\mu(w_{i,t-1})\bar\eta_{i,t-1}(w_{i,t}\mid w_{i,t-1})}$ holds, draw $y\sim\bar\eta_{i,t-1}(\cdot\mid w_{i,t})$ and extend.
--   3. Line 9 (if some child fails the upper test): flip a coin with parameter (ratio)$/M$; on success add $w_{i,t}$ to $\mathcal T$ and intersect $\mathcal G^{\mathrm{ret}}$ with $\{\eta\in\mathcal G_{i,t-1}\mid \hat\mu(w_{i,t}\circ y)/\eta(w_{i,t}\circ y)\le R\}$; stop.
--   4. Line 13 (if the lower test fails): flip a coin with parameter (ratio); on failure stop; on success set $\mathcal G_{i,t}=\{\eta\in\mathcal G_{i,t-1}\mid \frac1R\le\frac{\hat\mu(w_{i,t})}{\eta(w_{i,t})}\le R\}$ and start stage $t+1$.
--   5. Line 17 ($|w_{i,t}|=n$): flip a coin with parameter (ratio)$/M$; on success add $w_{i,t}$ to $\mathcal T$; stop.
--
--   The trial's **record** lists every assignment $w_{i,t}=v$ (with its stage), the final node of each stage, each class $\mathcal G_{i,t}$ set on Line 16, the node added to $\mathcal T$ and the restriction of $\mathcal G^{\mathrm{ret}}$ (if any), and the nodes at which $\hat\mu$ is read. The module also defines the list of $M$ independent trials.
--
--   **Formalization Note**
--   1. All ratio tests are multiplicative ($0/0=1$, $a/0=\infty$).
--   2. Line 11's $y$, left unspecified by "for some $y$", is the least violating symbol in a fixed linear order on $\Sigma$; both actions of Line 11 happen only when $\xi=1$.
--   3. Coin parameters are clamped to $[0,1]$, a no-op on reachable states (proof of (15), p.23).
--   4. Reads follow the caching paragraph of p.18: a test at $v$ with $|v|<n$ reads $\hat\mu(v)$ and every $\hat\mu(v\circ y)$; the start node is read on Line 3.
--   5. The recursion carries a fuel of $2(n+1)$ steps, which is never exhausted; if $\bar\eta(\cdot\mid v)$ is undefined (unreachable when $\mu^\star$ is in the class and $\hat\mu(w)>0$) the trial ends with nothing added.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Algorithm 2, Lines 2–19, p.11 (PDF p.13); caching, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_TTTSampling_mixPrefix

open Classical

namespace TTTSampling

/-- The **record of one outer iteration `i`** (one trial) of Algorithm 2.
* `visits` — every pair `(t, v)` such that the trial sets `w_{i,t} = v` (Lines 5 and 8), in order;
* `finals` — `finals[t−1]` is the final value of `w_{i,t}` at stage `t`, for each stage reached;
* `classes` — `classes[t−1]` is the class `𝒢_{i,t}` set on Line 16 at stage `t` (only for the
  stages at which Line 16 is executed with `ξ = 1`);
* `added` — the node the trial adds to `𝒯` (Line 11 or Line 19), if any;
* `restr` — the set `{η ∈ 𝒢_{i,t−1} | µ̂(w_{i,t}∘y)/η(w_{i,t}∘y) ≤ R}` intersected into `𝒢^ret` on
  Line 11, if that line is executed with `ξ = 1`;
* `reads` — the nodes at which the trial evaluates `µ̂` (see `trialGo`). -/
structure TrialOut (α : Type) (n : ℕ) where
  visits : List (ℕ × List α)
  finals : List (List α)
  classes : List (Finset (PMF (Fin n → α)))
  added : Option (List α)
  restr : Option (Finset (PMF (Fin n → α)))
  reads : Finset (List α)

/-- **One step of a trial of Algorithm 2** (Golowich, Moitra, Rohatgi, arXiv:2606.11437, version
of November 3, 2026, Algorithm 2, Lines 4–19, printed p.11, PDF p.13).

The arguments after the fuel are: the stage `t`, the stage start `u = w_{i,t−1}`, its class
`Gc = 𝒢_{i,t−1}`, the current node `v = w_{i,t}`, and the record so far. At `v` (after recording the
visit `(t, v)` and the reads at `v`):
* **Line 9** (tested first): if `|v| < n` and some child violates the upper threshold,
  `M·µ̂(u)·η̄(v∘y | u) < µ̂(v∘y)`, flip `ξ ∼ Ber(µ̂(v)/(µ̂(u)η̄(v | u)) · 1/M)` (Line 10); if `ξ = 1`
  add `v` to `𝒯` and restrict `𝒢^ret` by `{η ∈ Gc | µ̂(v∘y)/η(v∘y) ≤ R}` with `y` the **least**
  violating symbol (Line 11); the trial ends (Line 12).
* **Line 13**: else, if `|v| < n` and `M·µ̂(v) < µ̂(u)·η̄(v | u)`, flip
  `ξ ∼ Ber(µ̂(v)/(µ̂(u)η̄(v | u)))` (Line 14); if `ξ = 0` the trial ends (Line 15); if `ξ = 1` set
  `𝒢_{i,t} = {η ∈ Gc | 1/R ≤ µ̂(v)/η(v) ≤ R}` (Line 16) and start stage `t + 1` at `v`
  (Lines 4–5).
* **Line 6–8**: else, if `|v| < n` (the while condition holds), draw `y ∼ η̄(· | v)` and move to
  `v∘y`.
* **Line 17–19**: else (`|v| = n`) flip `ξ ∼ Ber(µ̂(v)/(µ̂(u)η̄(v | u)) · 1/M)`; if `ξ = 1` add `v`
  to `𝒯`; the trial ends.

**Formalization Note**
* All ratio tests are multiplicative (`den`), so `a/0 = ∞` and `0/0 = 1` as in footnote 12.
* "for some y" on Line 9 leaves the `y` of Line 11 unspecified when several children violate;
  the **least** violating `y` in the order of `Σ` is used. "If ξ = 1, add w_{i,t} to 𝒯; set
  𝒢^ret ← …" is read with both actions under `ξ = 1`.
* Bernoulli parameters are clamped to `[0,1]` (`bern`), a no-op on reachable states.
* **Reads (caching, p.18).** At each visited `v` with `|v| < n` the tests of Lines 6/9 read `µ̂(v)`
  and `µ̂(v∘y)` for every `y ∈ Σ`; at `|v| = n` they read `µ̂(v)`. The start node `w` is read on
  Line 3. All other values used (`µ̂(u)`) were read earlier.
* **Fuel.** Every recursive call either moves to a child (the length grows by one, and never
  beyond `n`) or starts a new stage at the same node, and a new stage never starts twice in a row
  at the same node (the ratio at `u` itself is `1 ≥ 1/M`). So `2(n+1)` calls always suffice for a
  start node of length `≤ n`; the branch for exhausted fuel is never reached.
* If `η̄(· | v)` is undefined (every child of `v` has mean mass `0`), the trial ends with nothing
  added; this is unreachable when the target `µ⋆` lies in the class and `µ̂(w) > 0`. -/
noncomputable def trialGo {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) :
    ℕ → ℕ → List α → Finset (PMF (Fin n → α)) → List α → TrialOut α n → PMF (TrialOut α n)
  | 0, _, _, _, _, acc => PMF.pure acc
  | fuel + 1, t, u, Gc, v, acc0 =>
    let acc : TrialOut α n :=
      { acc0 with
        visits := acc0.visits ++ [(t, v)],
        reads := acc0.reads ∪
          (if v.length < n then insert v (Finset.univ.image (fun y : α => v ++ [y])) else {v}) }
    if h9 : v.length < n ∧ ∃ y : α, (M : ℝ) * den μh Gc u (v ++ [y]) < (μh (v ++ [y]) : ℝ) then
      let ystar : α :=
        (Finset.univ.filter (fun y : α => (M : ℝ) * den μh Gc u (v ++ [y]) < (μh (v ++ [y]) : ℝ))).min'
          (by obtain ⟨y, hy⟩ := h9.2; exact ⟨y, by simp [hy]⟩)
      (bern ((μh v : ℝ) / ((M : ℝ) * den μh Gc u v))).bind fun ξ =>
        PMF.pure { acc with
          finals := acc.finals ++ [v],
          added := if ξ then some v else none,
          restr := if ξ then
              some (Gc.filter (fun η => (μh (v ++ [ystar]) : ℝ) ≤ R * prefixMass η (v ++ [ystar])))
            else none }
    else if v.length < n ∧ (M : ℝ) * (μh v : ℝ) < den μh Gc u v then
      (bern ((μh v : ℝ) / den μh Gc u v)).bind fun ξ =>
        if ξ then
          trialGo R M μh fuel (t + 1) v (Gc.filter (fun η => Consistent R μh η v)) v
            { acc with
              finals := acc.finals ++ [v],
              classes := acc.classes ++ [Gc.filter (fun η => Consistent R μh η v)] }
        else PMF.pure { acc with finals := acc.finals ++ [v] }
    else if v.length < n then
      (nextSym Gc v).bind fun
        | none => PMF.pure { acc with finals := acc.finals ++ [v] }
        | some y => trialGo R M μh fuel t u Gc (v ++ [y]) acc
    else
      (bern ((μh v : ℝ) / ((M : ℝ) * den μh Gc u v))).bind fun ξ =>
        PMF.pure { acc with finals := acc.finals ++ [v], added := if ξ then some v else none }

/-- **One trial (outer iteration `i`) of Algorithm 2** started at the node `w` with class `𝒢`:
Line 3 sets `w_{i,0} = w`, `𝒢_{i,0} = {η ∈ 𝒢 | 1/R ≤ µ̂(w)/η(w) ≤ R}`, and stage `t = 1` starts at
`w` (Lines 4–5). The record starts with `reads = {w}` (Line 3 reads `µ̂(w)`). -/
noncomputable def alg2Trial {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (w : List α) (G : Finset (PMF (Fin n → α))) : PMF (TrialOut α n) :=
  trialGo R M μh (2 * (n + 1)) 1 w (G.filter (fun η => Consistent R μh η w)) w
    ⟨[], [], [], none, none, {w}⟩

/-- `k` independent draws from `p`, as a list. -/
noncomputable def iidList {β : Type} (p : PMF β) : ℕ → PMF (List β)
  | 0 => PMF.pure []
  | k + 1 => p.bind fun a => (iidList p k).bind fun l => PMF.pure (a :: l)

/-- The **`M` independent trials** `i = 1, …, M` of Algorithm 2 (Line 2), as the list of their
records (the `i`-th entry is outer iteration `i`). The trials are independent and identically
distributed: each depends only on `(w, 𝒢)`, not on `𝒢^ret` or `𝒯`. -/
noncomputable def alg2Trials {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (R : ℝ) (M : ℕ)
    (μh : List α → NNReal) (w : List α) (G : Finset (PMF (Fin n → α))) :
    PMF (List (TrialOut α n)) :=
  iidList (alg2Trial R M μh w G) M

end TTTSampling


