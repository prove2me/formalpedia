-- Prove2me | Definitions.Def_LPAllocRM_IsArrivalPath
-- name    : LPAllocRM_IsArrivalPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:04.91805+00:00
-- url     : https://prove2.me/theorems/393026a1-de86-42d6-9f41-8bba559d0e68
-- title:
--   Sample path of a simple arrival process on $(0,\tau]$
-- statement:
--   A function $d:\mathbb R\to\mathbb N^n$, where $d_j(t)$ is the number of class-$j$ requests in $(0,t]$, is an **arrival path** on the horizon $(0,\tau]$ if
--
--   1. $d(t)=0$ for $t\le 0$;
--   2. $d$ is nondecreasing;
--   3. $d$ is right-continuous (for every $t$ there is $\varepsilon>0$ with $d(s)=d(t)$ for $s\in[t,t+\varepsilon)$);
--   4. $d(t)=d(\tau)$ for $t\ge\tau$ (no arrivals after $\tau$);
--   5. the process is simple: for every $t$ there is $\varepsilon>0$ with $\sum_j d_j(t)\le\sum_j d_j(s)+1$ for $s\in(t-\varepsilon,t)$, i.e. at most one request (of any class) arrives at any time.
--
--   This is the paper's standing assumption on the demand: "requests arrive one at a time to the system over $(0,\tau]$ according to a random point process that has a finite number of points (almost surely); i.e., the overall arrival process is a simple point process", restated for each scaled problem as (a) and (b) in §4.
--
--   **Formalization Note** A finite number of arrivals is automatic: the counts are natural numbers, nondecreasing and constant after $\tau$.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, §2, p.722 and §4 (a)–(b), p.723

import Mathlib

namespace LPAllocRM

/-- A sample path of the vector arrival process over the horizon `(0, τ]`: `d t j` is the number
of class-`j` requests in `(0, t]` ("let D_j(t) be the number of class j requests in (0, t]").
The clauses: no arrivals at or before time 0; `d` is nondecreasing; `d` is right-continuous
(counts over `(0, t]`); no arrivals after `τ`; and the process is **simple**: at any time the total
count over all classes jumps by at most one ("requests arrive one at a time", "(b) at most one
arrival at any point in time").
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
§2, p.722 (PDF p.3), and §4 (a)–(b), p.723 (PDF p.4).

**Formalization Note** The arrival process is encoded by its counting paths `ℝ → Fin n → ℕ`. A
finite number of arrivals (§4 (a)) is automatic: the counts are natural numbers, nondecreasing and
constant after `τ`, so each path has at most `∑ j, d τ j` jumps. Simplicity is stated as: for every
`t` there is `ε > 0` with `∑ j, d t j ≤ ∑ j, d s j + 1` for all `s ∈ (t − ε, t)`. -/
def IsArrivalPath {n : ℕ} (τ : ℝ) (d : ℝ → Fin n → ℕ) : Prop :=
  (∀ t : ℝ, t ≤ 0 → d t = 0) ∧
  Monotone d ∧
  (∀ t : ℝ, ∃ ε > 0, ∀ s ∈ Set.Ico t (t + ε), d s = d t) ∧
  (∀ t : ℝ, τ ≤ t → d t = d τ) ∧
  (∀ t : ℝ, ∃ ε > 0, ∀ s ∈ Set.Ioo (t - ε) t, ∑ j, d t j ≤ ∑ j, d s j + 1)

end LPAllocRM


