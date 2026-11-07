-- Prove2me | Definitions.Def_TTTSampling_cutHist
-- name    : TTTSampling_cutHist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:05.145645+00:00
-- url     : https://prove2.me/theorems/b25e0be3-9c11-405b-9e36-30ee715d34c4
-- title:
--   Cut sets $\mathcal N^{\mathrm{int}}_t(w)$, $\mathcal N^{\mathrm{fin}}_t(w)$, classes $\mathcal G_t(w')$ of (10), $\mathcal S_t(w)$, simple $w$-cuts
-- statement:
--   Fix $R>0$, an oracle $\hat\mu$, a finite class $\mathcal G$, a node $w\in\Sigma^{\le n}$ and $M\ge1$. Nodes are strings of length at most $n$, ordered by the prefix relation $\preceq$ ($\prec$ strict).
--
--   1. $\mathcal N^{\mathrm{int}}_0(w)=\{w\}$ and $\mathcal N^{\mathrm{fin}}_0(w)=\emptyset$.
--   2. For $t\ge1$ and $w'\succeq w$, the class (10) is
--   $$
--   \mathcal G_{t-1}(w')=\bigcap_{0\le s\le t-1}\Bigl\{\eta\in\mathcal G \;\Big|\; \tfrac1R\le\tfrac{\hat\mu(w'')}{\eta(w'')}\le R\ \ \forall w''\preceq w',\ w''\in\mathcal N^{\mathrm{int}}_s(w)\Bigr\},
--   $$
--   and $\bar\eta_{t-1,w'}$ is its mean density. For $w''\in\mathcal N^{\mathrm{int}}_{t-1}(w)$ and $w'\succeq w''$:
--    - (P1) $\dfrac{\hat\mu(w')}{\hat\mu(w'')\,\bar\eta_{t-1,w''}(w'\mid w'')}<\dfrac1M$;
--    - (P2) $|w'|=n$, or $\dfrac{\hat\mu(w'\circ y)}{\hat\mu(w'')\,\bar\eta_{t-1,w''}(w'\circ y\mid w'')}>M$ for some $y\in\Sigma$.
--   3. Along each descending path from each $w''\in\mathcal N^{\mathrm{int}}_{t-1}(w)$, stop at the first node $w'\succeq w''$ satisfying (P1) or (P2). It goes to $\mathcal N^{\mathrm{fin}}_t(w)$ if it satisfies (P2) and to $\mathcal N^{\mathrm{int}}_t(w)$ otherwise; also $\mathcal N^{\mathrm{fin}}_{t-1}(w)\subseteq\mathcal N^{\mathrm{fin}}_t(w)$.
--   4. $\mathcal N^{\mathrm{fin}}(w)=\mathcal N^{\mathrm{fin}}_{n-|w|}(w)$ (the stable value, Lemma 3.4); $\mathcal N^{\mathrm{append}}_t(w)=\mathcal N^{\mathrm{int}}_t(w)\cup(\mathcal N^{\mathrm{fin}}_t(w)\setminus\mathcal N^{\mathrm{fin}}_{t-1}(w))$; and
--   $$
--   \mathcal S_t(w)=\{w'\succeq w \mid \exists\, w_{t-1}\in\mathcal N^{\mathrm{int}}_{t-1}(w),\ w_t\in\mathcal N^{\mathrm{append}}_t(w):\ w_{t-1}\prec w'\prec w_t\}.
--   $$
--   5. A set $\mathcal N$ of nodes is a **simple $w$-cut** if every leaf $v\in\Sigma^n$ with $v\succ w$ has exactly one node $w'\in\mathcal N$ with $w\preceq w'\preceq v$.
--
--   These sets describe, deterministically, where the trials of Algorithm 2 stop at each stage; they carry the analysis of Algorithm 2 (Lemmas 3.3–3.8).
--
--   **Formalization Note** (P1), (P2) and the filter of (10) are multiplicative, as in footnote 12. The construction is computed with its history $[\mathcal N^{\mathrm{int}}_0,\dots,\mathcal N^{\mathrm{int}}_t]$, because (10) depends on all earlier intermediate sets.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), §3.1, pp.18–19 (PDF pp.20–21), (10), (P1), (P2); p.22 (PDF p.24)

import Mathlib
import Definitions.Def_TTTSampling_mixPrefix

open Classical

namespace TTTSampling

variable {α : Type} [Fintype α] [DecidableEq α] {n : ℕ}

/-- The **nodes** `Σ^{≤n}` of the complete `Σ`-ary tree: all lists of length at most `n`. -/
noncomputable def nodes (α : Type) [Fintype α] [DecidableEq α] (n : ℕ) : Finset (List α) :=
  (Finset.range (n + 1)).biUnion (fun k => Finset.univ.image (fun v : Fin k → α => List.ofFn v))

/-- The class `𝒢_{t−1}(w′)` of (10), given the list `hist = [𝒩^int_0, …, 𝒩^int_{t−1}]`: the
densities of `𝒢` consistent with `µ̂` (`1/R ≤ µ̂(w″)/η(w″) ≤ R`) at every ancestor-or-self `w″ ⪯ w′`
lying in one of the listed intermediate sets. -/
noncomputable def classAt (R : ℝ) (μh : List α → NNReal) (G : Finset (PMF (Fin n → α)))
    (hist : List (Finset (List α))) (w' : List α) : Finset (PMF (Fin n → α)) :=
  G.filter (fun η => ∀ S ∈ hist, ∀ w'' ∈ S, w'' <+: w' → Consistent R μh η w'')

/-- **(P1) Lower-threshold condition** of `w′` relative to `w″` (p.19), for the class `Gc` used at
`w″`: `µ̂(w′)/(µ̂(w″)·η̄(w′ | w″)) < 1/M`, i.e. `M·µ̂(w′) < µ̂(w″)·η̄(w′ | w″)`. -/
def P1 (M : ℕ) (μh : List α → NNReal) (Gc : Finset (PMF (Fin n → α))) (w'' w' : List α) : Prop :=
  (M : ℝ) * (μh w' : ℝ) < den μh Gc w'' w'

/-- **(P2) Upper-threshold condition** of `w′` relative to `w″` (p.19): `|w′| = n`, or for some
`y ∈ Σ`, `µ̂(w′∘y)/(µ̂(w″)·η̄(w′∘y | w″)) > M`, i.e. `M·µ̂(w″)·η̄(w′∘y | w″) < µ̂(w′∘y)`. -/
def P2 (M : ℕ) (μh : List α → NNReal) (Gc : Finset (PMF (Fin n → α))) (w'' w' : List α) : Prop :=
  w'.length = n ∨ ∃ y : α, (M : ℝ) * den μh Gc w'' (w' ++ [y]) < (μh (w' ++ [y]) : ℝ)

/-- The **stopping nodes** relative to `w″` (p.19): the nodes `w′ ⪰ w″` of the tree satisfying
(P1) or (P2) relative to `w″` such that no `w̃` with `w″ ⪯ w̃ ≺ w′` does, where (P1)/(P2) use
`η̄_{t−1,w″}`, the mean of `𝒢_{t−1}(w″)` computed from `hist`. -/
noncomputable def stopNodes (R : ℝ) (M : ℕ) (μh : List α → NNReal)
    (G : Finset (PMF (Fin n → α))) (hist : List (Finset (List α))) (w'' : List α) :
    Finset (List α) :=
  (nodes α n).filter (fun w' => w'' <+: w' ∧
    (P1 M μh (classAt R μh G hist w'') w'' w' ∨ P2 M μh (classAt R μh G hist w'') w'' w') ∧
    ∀ z : List α, w'' <+: z → z <+: w' → z ≠ w' →
      ¬ (P1 M μh (classAt R μh G hist w'') w'' z ∨ P2 M μh (classAt R μh G hist w'') w'' z))

/-- The **intermediate and final node sets** `𝒩^int_{𝒢,M,t}(w)`, `𝒩^fin_{𝒢,M,t}(w)`.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), §3.1, printed
pp.18–19 (PDF pp.20–21), with (10), (P1), (P2):
* `𝒩^int_0(w) := {w}` and `𝒩^fin_0(w) = ∅`;
* for `t ≥ 1`, along each descending path from each `w″ ∈ 𝒩^int_{t−1}(w)` stop at the first node
  `w′ ⪰ w″` satisfying (P1) or (P2) relative to `w″`; place it in `𝒩^fin_t(w)` if it satisfies
  (P2) and in `𝒩^int_t(w)` otherwise; also place all of `𝒩^fin_{t−1}(w)` in `𝒩^fin_t(w)`.

`cutHist R M µ̂ 𝒢 w t = ([𝒩^int_0, …, 𝒩^int_t], 𝒩^fin_t)`. The history is carried because the
class `𝒢_{t−1}(w″)` of (10) used in (P1)/(P2) depends on all of `𝒩^int_0, …, 𝒩^int_{t−1}`.

**Formalization Note**
* (P1), (P2) and the class filter of (10) are multiplicative (`P1`, `P2`, `Consistent`), as in
  footnote 12, p.18.
* Nodes are lists of length `≤ n`; "w′ ⪰ w″" is `w″ <+: w′` (`List.IsPrefix`) and "≺" is the
  proper prefix relation.
* The paper fixes `M ≥ 1` (Algorithm 2, "Require"); the theorems that use these sets assume it. -/
noncomputable def cutHist (R : ℝ) (M : ℕ) (μh : List α → NNReal)
    (G : Finset (PMF (Fin n → α))) (w : List α) : ℕ → List (Finset (List α)) × Finset (List α)
  | 0 => ([{w}], ∅)
  | t + 1 =>
    let hist := (cutHist R M μh G w t).1
    let fin := (cutHist R M μh G w t).2
    let last := hist.getLastD ∅
    (hist ++ [last.biUnion (fun u => (stopNodes R M μh G hist u).filter
        (fun w' => ¬ P2 M μh (classAt R μh G hist u) u w'))],
     fin ∪ last.biUnion (fun u => (stopNodes R M μh G hist u).filter
        (fun w' => P2 M μh (classAt R μh G hist u) u w')))

/-- `𝒩^int_{𝒢,M,t}(w)`, the `(𝒢, M, t)`-intermediate nodes (p.18–19). -/
noncomputable def Nint (R : ℝ) (M : ℕ) (μh : List α → NNReal) (G : Finset (PMF (Fin n → α)))
    (w : List α) (t : ℕ) : Finset (List α) :=
  (cutHist R M μh G w t).1.getLastD ∅

/-- `𝒩^fin_{𝒢,M,t}(w)`, the `(𝒢, M, t)`-final nodes (p.18–19). -/
noncomputable def Nfin (R : ℝ) (M : ℕ) (μh : List α → NNReal) (G : Finset (PMF (Fin n → α)))
    (w : List α) (t : ℕ) : Finset (List α) :=
  (cutHist R M μh G w t).2

/-- The class `𝒢_t(w′)` of (10) (p.19): the densities of `𝒢` consistent with `µ̂` at every
`w″ ⪯ w′` with `w″ ∈ 𝒩^int_s(w)` for some `s ≤ t`. -/
noncomputable def Gt (R : ℝ) (M : ℕ) (μh : List α → NNReal) (G : Finset (PMF (Fin n → α)))
    (w : List α) (t : ℕ) (w' : List α) : Finset (PMF (Fin n → α)) :=
  classAt R μh G (cutHist R M μh G w t).1 w'

/-- `𝒩^fin_{𝒢,M}(w)`, the limit `𝒩^fin_{t₀}(w) = 𝒩^fin_{t₀+1}(w) = ⋯` (p.22), taken at
`t = n − |w| + 1`.

**Formalization Note** The final sets are constant from the first `t₀` with `𝒩^int_{t₀}(w) = ∅`
on. For `|w| < n` that `t₀` is at most `n − |w|` (Lemma 3.4), so `t = n − |w| + 1` gives the same
set as `t = n − |w|`. For `|w| = n` the printed bound `t₀ ≤ n − |w| = 0` fails
(`𝒩^int_0(w) = {w}`), the sets stabilize at `t₀ = 1`, and the limit is `𝒩^fin_1(w) = {w}`, not
`𝒩^fin_0(w) = ∅`. The index `n − |w| + 1` is past stabilization in every case. -/
noncomputable def NfinLim (R : ℝ) (M : ℕ) (μh : List α → NNReal) (G : Finset (PMF (Fin n → α)))
    (w : List α) : Finset (List α) :=
  Nfin R M μh G w (n - w.length + 1)

/-- `𝒩^append_{𝒢,M,t}(w) := 𝒩^int_t(w) ∪ (𝒩^fin_t(w) \ 𝒩^fin_{t−1}(w))` (p.22), for `t ≥ 1`. -/
noncomputable def Nappend (R : ℝ) (M : ℕ) (μh : List α → NNReal) (G : Finset (PMF (Fin n → α)))
    (w : List α) (t : ℕ) : Finset (List α) :=
  Nint R M μh G w t ∪ (Nfin R M μh G w t \ Nfin R M μh G w (t - 1))

/-- `𝒮_{𝒢,M,t}(w)` (p.22): the nodes `w′ ⪰ w` strictly between some `w_{t−1} ∈ 𝒩^int_{t−1}(w)`
and some `w_t ∈ 𝒩^append_t(w)`, i.e. `w_{t−1} ≺ w′ ≺ w_t`. -/
noncomputable def Ssand (R : ℝ) (M : ℕ) (μh : List α → NNReal) (G : Finset (PMF (Fin n → α)))
    (w : List α) (t : ℕ) : Finset (List α) :=
  (nodes α n).filter (fun w' => w <+: w' ∧
    ∃ a ∈ Nint R M μh G w (t - 1), ∃ b ∈ Nappend R M μh G w t,
      a <+: w' ∧ a ≠ w' ∧ w' <+: b ∧ w' ≠ b)

/-- A **simple `w`-cut** (p.19): `𝒩 ⊆ Σ^{≤n}` such that for each leaf `v ∈ Σⁿ` with `v ≻ w` there
is a single node `w′ ∈ 𝒩` with `w ⪯ w′ ⪯ v`. -/
def IsSimpleCut (n : ℕ) (w : List α) (N : Finset (List α)) : Prop :=
  ∀ v : List α, v.length = n → w <+: v → w ≠ v → ∃! w' : List α, w' ∈ N ∧ w <+: w' ∧ w' <+: v

end TTTSampling


