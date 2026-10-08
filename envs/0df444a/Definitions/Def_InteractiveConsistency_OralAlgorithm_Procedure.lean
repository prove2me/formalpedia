-- Prove2me | Definitions.Def_InteractiveConsistency_OralAlgorithm_Procedure
-- name    : InteractiveConsistency_OralAlgorithm_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:28.624556+00:00
-- url     : https://prove2.me/theorems/a0ea3f1f-bf28-4555-ae22-ad1e1c14a23e
-- title:
--   Section 3 (p. 230) — the recursive procedure (1)–(2) for m faults
-- statement:
--   This is the procedure of Section 3 by which processor $p$ computes, from its view $\sigma_p$ alone, the entry of its interactive-consistency vector for a processor $q$. In the paper's words (p. 230):
--
--   > (1) If for some subset $Q$ of $P$ of size $>(n + m)/2$ and some value $v$, $\sigma_p(pwq) = v$ for each string $w$ over $Q$ of length $\le m$, $p$ records $v$.
--   > (2) Otherwise, the algorithm for $m - 1$, $n - 1$ is recursively applied with $P$ replaced by $P - \{q\}$, and $\sigma_p$ by the mapping $\hat\sigma_p$ defined by $\hat\sigma_p(pw) = \sigma_p(pwq)$ for each string $w$ of length $\le m$ over $P - \{q\}$. If at least $\lfloor (n + m)/2\rfloor$ of the $n - 1$ elements in the vector obtained in the recursive call agree, $p$ records the common value, otherwise $p$ records NIL.
--
--   Here $n = |P|$ and $m$ are the **current** processor count and fault bound; both decrease by one in the recursive call. Formally, $\mathrm{record}(m, P, \tau, q)$ is defined by recursion on $m$, where $\tau(w) = \sigma_p(pw)$:
--
--   1. **Step (1).** If there are $Q\subseteq P$ with $n + m < 2|Q|$ and $v\in V$ such that $\tau(wq) = v$ for every string $w$ over $Q$ with $|w|\le m$, record $v$. Taking $w$ empty shows $v = \tau(q) = \sigma(pq)$, so the recorded value is $\sigma_p(pq)$.
--   2. **Step (2), $m \ge 1$.** Otherwise form the vector
--   $$x_{q'} = \mathrm{record}\bigl(m-1,\ P\setminus\{q\},\ w\mapsto \tau(wq),\ q'\bigr),\qquad q'\in P\setminus\{q\},$$
--   with entries in $V\cup\{\mathrm{NIL}\}$. If some value is taken by at least $\lfloor (n+m)/2\rfloor$ of these $n-1$ entries, record it; otherwise record NIL.
--   3. **$m = 0$ and step (1) fails:** record NIL. (The paper's basis case shows step (1) always succeeds when $m = 0$; this branch is never reached under its hypotheses.)
--
--   The procedure is the paper's algorithm for $n \ge 3m+1$; the goal theorem of this mission states that it assures interactive consistency for $m$ faults.
--
--   **Formalization Note.** The view $\tau$ is `fun w => σ (p :: w)`, so $\tau(w ++ [q]) = \sigma_p(pwq)$, and the recursive view $\hat\sigma_p$ is `fun w => τ (w ++ [q])`. "Size $>(n+m)/2$" is written without division as `P.card + m < 2 * Q.card`; $\lfloor (n+m)/2\rfloor$ is natural-number division `(P.card + m) / 2`; the agreement count runs over `P.erase q` and includes $p$'s own entry. Step (1)'s condition is the page's condition, and the recorded value is written `some (τ [q])`, which equals the witnessing $v$. When several values reach the step-(2) threshold, one is chosen by `Classical.choose` (a deterministic function of the vector); under $n \ge 3m+1$ and $m \ge 1$ at most one value can reach it. The definition is noncomputable because step (1) quantifies over subsets and strings.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 230, Section 3, steps (1)–(2)

import Mathlib
import Definitions.Def_InteractiveConsistency_OralAlgorithm_Scenario

namespace InteractiveConsistency.OralAlgorithm

/-- The condition of step (1) of the procedure (p. 230), for processor `p` with view
`τ = fun w => σ (p :: w)`, `m` faults, processor set `P` and target processor `q`: there are a
subset `Q ⊆ P` of size `> (|P| + m)/2` and a value `v` with `σ_p(p w q) = τ (w ++ [q]) = v` for
every string `w` over `Q` of length `≤ m` (including the empty string). -/
def StepOne {α V : Type*} (m : ℕ) (P : Finset α) (τ : List α → V) (q : α) : Prop :=
  ∃ Q ⊆ P, P.card + m < 2 * Q.card ∧
    ∃ v : V, ∀ w : List α, IsStringOver Q w → w.length ≤ m → τ (w ++ [q]) = v

open Classical in
/-- The recursive procedure of Section 3 (p. 230): `record m P τ q` is the value (`none` = NIL)
that a processor with view `τ` (`τ w = σ (p :: w)`) records for processor `q`, with `m` faults
and processor set `P`.
* Step (1): if `StepOne m P τ q` holds, record the common value; it equals `τ [q]` (take `w = []`).
* Step (2), `m = m' + 1`: apply the procedure for `m'` to `P.erase q` and the view
  `fun w => τ (w ++ [q])` (that is, `σ̂_p(p w) = σ_p(p w q)`), obtaining a vector indexed by
  `P.erase q`; if some value `x` is taken by at least `⌊(|P| + m)/2⌋` of its entries, record `x`,
  otherwise record NIL.
* `m = 0` and step (1) fails: record NIL. -/
noncomputable def record {α V : Type*} [DecidableEq α] :
    ℕ → Finset α → (List α → V) → α → Option V
  | 0, P, τ, q => if StepOne 0 P τ q then some (τ [q]) else none
  | m' + 1, P, τ, q =>
    if StepOne (m' + 1) P τ q then some (τ [q]) else
      if h : ∃ x : Option V, (P.card + (m' + 1)) / 2 ≤
          ((P.erase q).filter
            (fun q' => record m' (P.erase q) (fun w => τ (w ++ [q])) q' = x)).card
      then Classical.choose h else none

end InteractiveConsistency.OralAlgorithm


