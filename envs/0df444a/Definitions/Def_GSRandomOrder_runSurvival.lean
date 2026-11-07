-- Prove2me | Definitions.Def_GSRandomOrder_runSurvival
-- name    : GSRandomOrder_runSurvival
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:52.723445+00:00
-- url     : https://prove2.me/theorems/162f307b-f21b-449c-963c-a9a09f0d5005
-- title:
--   The survival algorithm in continuous time
-- statement:
--   **Arrival times.** Each item $g$ has an arrival time $t_g$, uniform on $[0,1]$ and independent of the others, and items arrive in increasing order of these times.
--
--   **The survival algorithm.** Maintain the set $S$ of items that have arrived and the accepted set $A$, both initially empty. When item $x$ arrives at time $t$:
--
--   1. if $t\le 1/e$, reject $x$;
--   2. if $x\notin D_v(S+x)$, reject $x$;
--   3. otherwise accept $x$ with probability $\alpha_x(A,S,t)$;
--
--   then replace $S$ by $S+x$, and $A$ by $A+x$ if $x$ was accepted.
--
--   The module also defines the run restricted to a set $Q$ of items with arrival times uniform on $[0,t]$ (used in the proof of distribution matching), the set of items arrived by real time $s$, the accepted set at real time $s$, and the final accepted set.
--
--   **Formalization Note** The sample space is $\Omega_n=[0,1]^n\times[0,1]^n$ with the product of uniform laws: arrival variables $r_g$ (arrival time $t\,r_g$) and one acceptance coin $c_g$ per item. Step 3 accepts $x$ iff $c_x<\alpha_x(A,S,t)$, which has probability $\alpha_x$ whenever $\alpha_x\in[0,1]$; no clamping is applied. Items are processed in increasing order of $(t\,r_g,g)$: ties have probability zero and are broken by label. The run is online: it queries $v$ only on subsets of arrived items. The random-order model with known $n$ reduces to this model (p.9).
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §3.1, pp.9–10 (arrival times and the survival algorithm); §B.2, p.25 (the run on Q alone with horizon t)

import Mathlib
import Definitions.Def_GSRandomOrder_acceptProb

set_option autoImplicit false

namespace GSRandomOrder

/-- The sample space of the survival algorithm: one uniform arrival variable `r_g ∈ [0, 1]` and
one uniform acceptance coin `c_g ∈ [0, 1]` per item, all independent (`volume` is the product of
the uniform laws). -/
abbrev Ω (n : ℕ) := (Fin n → unitInterval) × (Fin n → unitInterval)

/-- The arrival time `t · r_g` of item `g`: with `t = 1` this is `t_g`, uniform on `[0, 1]`
(§3.1, p.9); with a horizon `t` it is uniform on `[0, t]` (§B.2, p.25). -/
noncomputable def arrivalTime {n : ℕ} (t : ℝ) (ω : Ω n) (g : Fin n) : ℝ :=
  t * (ω.1 g : ℝ)

/-- The items of `Q` in increasing order of arrival time, ties (a null event) broken by label. -/
noncomputable def arrivalOrder {n : ℕ} (a : Fin n → ℝ) (Q : Finset (Fin n)) : List (Fin n) :=
  Q.toList.insertionSort fun g h => a g < a h ∨ (a g = a h ∧ g ≤ h)

/-- One step of the survival algorithm (§3.1, pp.9–10). The state is `(S, A)`, the arrived set and
the accepted set. When `x` arrives at time `a x`:
1. if `a x ≤ 1/e`, reject `x`;
2. if `x ∉ D_v(S + x)`, reject `x`;
3. otherwise accept `x` with probability `α_x(A, S, a x)`, realized as `c x < α_x(A, S, a x)` for
   the coin `c x` uniform on `[0, 1]`;
then `S` becomes `S + x`, and `A` becomes `A + x` if `x` was accepted. -/
noncomputable def survivalStep {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (a c : Fin n → ℝ)
    (st : Finset (Fin n) × Finset (Fin n)) (x : Fin n) : Finset (Fin n) × Finset (Fin n) :=
  if a x ≤ Real.exp (-1) then (insert x st.1, st.2)
  else if x ∉ canonicalDemand v (insert x st.1) then (insert x st.1, st.2)
  else if c x < acceptProb v x st.2 st.1 (a x) then (insert x st.1, insert x st.2)
  else (insert x st.1, st.2)

/-- **The survival algorithm** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §3.1, pp.9–10), run on the items of
`Q` with arrival times `t · r_g` (uniform on `[0, t]`), starting from `S = A = ∅`:
`runSurvival v Q t ω s` is the state `(S, A)` after the items of `Q` that arrive by real time `s`
have been processed, in increasing order of arrival.

**Formalization Note.** The randomness is `ω = (r, c)` of `Ω n` (arrival variables and coins).
Items are processed in increasing `(t · r_g, g)` order; ties among arrival times have probability
zero and are broken by label. Item `x` is accepted in step 3 iff `c_x < α_x`, which has
probability `α_x` given the past whenever `α_x ∈ [0, 1]`; the coin is never clamped. The run is
online: step 3 queries `v` only through `D_v(S + x)` and the survival laws of `v` and `v/x` on
`S`, i.e. only sets of arrived items. With `Q = univ` and `t = 1` this is the algorithm of
Theorem 3.1; with general `Q`, `t` it is "the algorithm run on the items of `Q` alone, with
independent arrival times uniform on `[0, t]`" of §B.2, p.25. -/
noncomputable def runSurvival {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (Q : Finset (Fin n))
    (t : ℝ) (ω : Ω n) (s : ℝ) : Finset (Fin n) × Finset (Fin n) :=
  ((arrivalOrder (arrivalTime t ω) Q).filter fun g => decide (arrivalTime t ω g ≤ s)).foldl
    (survivalStep v (arrivalTime t ω) fun g => (ω.2 g : ℝ)) (∅, ∅)

/-- The set of items that have arrived by real time `s` (Theorem 3.1's setting: `Q = N`,
`t = 1`). -/
noncomputable def arrivedBy {n : ℕ} (ω : Ω n) (s : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun g => arrivalTime 1 ω g ≤ s

/-- The accepted set `A` at real time `s` in the survival algorithm of Theorem 3.1. -/
noncomputable def acceptedBy {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (ω : Ω n) (s : ℝ) :
    Finset (Fin n) :=
  (runSurvival v Finset.univ 1 ω s).2

/-- The final accepted set of the survival algorithm of Theorem 3.1 (every arrival time is at most
`1`). -/
noncomputable def finalAccepted {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (ω : Ω n) :
    Finset (Fin n) :=
  acceptedBy v ω 1

end GSRandomOrder


