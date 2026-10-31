-- Prove2me | Definitions.Def_StreamSubmod_Algorithm2
-- name    : StreamSubmod_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:04.547352+00:00
-- url     : https://prove2.me/theorems/c2ec2306-594e-4d49-86b0-8b7c9561497b
-- title:
--   Algorithm 2: StreamProcess $(p,\alpha,\varepsilon^\prime)$
-- statement:
--   Algorithm 2 receives an integer $p\ge1$, $\alpha$ and $\varepsilon'\in(0,1)$, and needs no estimate of $f(\mathrm{OPT})$. Let $c=\alpha/(1+\alpha)$. It tracks a lower bound $m$, initially $f(\varnothing)$, and the set of guesses
--
--   $$
--   T=\Bigl\{(1+\varepsilon')^h : h\in\mathbb Z,\ \frac{m}{1+\varepsilon'}\le(1+\varepsilon')^h\le\frac{mk}{c}\Bigr\}.
--   $$
--
--   For every $\tau\in T$ it maintains sets $S^\tau_1,\dots,S^\tau_p$. When $e$ arrives:
--
--   1. it computes $m'=\max\{f(\{e\}),\max_{\tau\in T,\,1\le i\le p}f(S^\tau_i)\}$;
--   2. if $m<m'$, it sets $m\leftarrow m'$ and recomputes $T$, deletes the sets of the guesses removed from $T$, and starts the sets of the guesses added to $T$ empty;
--   3. for every $\tau\in T$ it processes $e$ as Algorithm 1 does with the estimate $\tau$.
--
--   After the stream ends it post-processes $S^\tau_1,\dots,S^\tau_p$ for every $\tau\in T$ into a set $\bar S_\tau$, and returns the best of them, or the empty set if $T=\varnothing$.
--
--   The module defines the memory `Alg2State`, the step `alg2Step`, the run `alg2Run` on a list of arrivals, the set of guesses `alg2Guesses`, the output `alg2Out`, the stored elements `alg2Stored` $=\sum_{\tau\in T}\sum_i|S^\tau_i|$, and the count `alg2Queries` made by the step.
--
--   **Formalization Note** A guess is represented by its exponent $h\in\mathbb Z$. The step counts $1+p|T|$ evaluations for the maximum of line 4, with no caching, plus the marginals counted by the threshold step of every guess. The set of exponents is finite for $\varepsilon'>0$ and $m\ge0$, and empty for $m=0$; the sanity file proves this and the membership criterion.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Algorithm 2, p.11, and proof of Lemma 12, p.13

import Mathlib
import Definitions.Def_StreamSubmod_threshStep
import Definitions.Def_StreamSubmod_postProcess

namespace StreamSubmod

/-- The exponents `h ∈ ℤ` of the guesses `(1 + ε')^h` with
`m/(1 + ε') ≤ (1 + ε')^h ≤ mk/c` (Alaluf, Ene, Feldman, Nguyen & Suh, arXiv:1911.12959v3,
Algorithm 2, line 2, p.11). -/
def guessExponents (ε' c : ℝ) (k : ℕ) (m : ℝ) : Set ℤ :=
  {h | m / (1 + ε') ≤ (1 + ε') ^ h ∧ (1 + ε') ^ h ≤ m * (k : ℝ) / c}

open Classical in
/-- The set `T` of Algorithm 2 (lines 2 and 6, p.11), represented by the exponents `h`, so that
`τ = (1 + ε')^h`.

**Formalization Note.** `guessExponents` is a finite set when `ε' > 0` (it is empty when `m = 0`);
the junk value `∅` of the `else` branch never occurs for `ε' ∈ (0, 1)`, `m ≥ 0`. -/
noncomputable def guessSet (ε' c : ℝ) (k : ℕ) (m : ℝ) : Finset ℤ :=
  if hfin : (guessExponents ε' c k m).Finite then hfin.toFinset else ∅

/-- The memory of Algorithm 2: the lower bound `m` on `f(OPT)` and, for every exponent `h`, the sets
`S^τ_1, …, S^τ_p` of the guess `τ = (1 + ε')^h`. The set `T` is determined by `m`. -/
structure Alg2State (E : Type) (p : ℕ) where
  /-- The current lower bound `m`. -/
  m : ℝ
  /-- The sets `S^τ_i` for `τ = (1 + ε')^h`; they are empty for every `h` outside `T`. -/
  sets : ℤ → Fin p → Finset E

variable {E : Type} [DecidableEq E]

/-- Line 2 of Algorithm 2 (p.11): `m = f(∅)`, and all the sets start empty. -/
def alg2Init (p : ℕ) (f : Finset E → ℝ) : Alg2State E p :=
  { m := f ∅, sets := fun _ _ => ∅ }

/-- The current set `T` of a state (Algorithm 2, lines 2 and 6, p.11), for `c = α/(1+α)`. -/
noncomputable def alg2Guesses {p : ℕ} (k : ℕ) (α ε' : ℝ) (st : Alg2State E p) : Finset ℤ :=
  guessSet ε' (α / (1 + α)) k st.m

/-- Lines 4–11 of Algorithm 2 (p.11), the processing of one arriving element `e`. The second
component counts the value computations of this step.

* Line 4: `m' = max {f({e}), max_{τ∈T, 1≤i≤p} f(S^τ_i)}`, from the sets before `e` is inserted
  anywhere; this evaluates `f` at `1 + p|T|` sets.
* Lines 5–6: if `m < m'`, then `m` becomes `m'` and `T` is recomputed from the new `m`; otherwise
  `m` and `T` do not change.
* Lines 7–8: the sets of a guess removed from `T` are deleted, and the sets of a guess added to `T`
  start empty, before lines 9–11, so a new guess already sees `e`.
* Lines 9–11: every `τ` of the new `T` processes `e` by `threshStep` with threshold `cτ/k`.

**Formalization Note.** Every evaluation of line 4 is counted, without the caching available
to an implementation. The count is the number of terms of the maximum of line 4 plus the counts
made by `threshStep`. -/
noncomputable def alg2Step (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (e : E)
    (st : Alg2State E p) : Alg2State E p × ℕ :=
  let T := alg2Guesses k α ε' st
  let terms := T ×ˢ (Finset.univ : Finset (Fin p))
  let m' := terms.fold max (f {e}) (fun x => f (st.sets x.1 x.2))
  let m₁ := if st.m < m' then m' else st.m
  let T₁ := guessSet ε' (α / (1 + α)) k m₁
  let kept : ℤ → Fin p → Finset E := fun h => if h ∈ T then st.sets h else fun _ => ∅
  let r := fun h : ℤ => threshStep f k (threshold α k ((1 + ε') ^ h)) e (kept h)
  ({ m := m₁, sets := fun h => if h ∈ T₁ then (r h).1 else fun _ => ∅ },
    1 + terms.card + ∑ h ∈ T₁, (r h).2)

/-- The memory of Algorithm 2 after the elements of the list `L` have arrived. -/
noncomputable def alg2Run (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (L : List E) :
    Alg2State E p :=
  L.foldl (fun st e => (alg2Step p f k α ε' e st).1) (alg2Init p f)

/-- The number of elements stored in a state, `∑_{τ∈T} ∑ᵢ |S^τ_i|` (proof of Lemma 12, p.13). -/
noncomputable def alg2Stored {p : ℕ} (k : ℕ) (α ε' : ℝ) (st : Alg2State E p) : ℕ :=
  ∑ h ∈ alg2Guesses k α ε' st, ∑ i, (st.sets h i).card

/-- The number of value computations Algorithm 2 makes while processing the arriving element `e`,
when the elements of `L` have already arrived. It is the count made by `alg2Step`. -/
noncomputable def alg2Queries (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ) (L : List E) (e : E) :
    ℕ :=
  (alg2Step p f k α ε' e (alg2Run p f k α ε' L)).2

/-- The output of Algorithm 2 on the stream `σ` when the offline algorithm has seed `ω`
(lines 12–15, p.11): for every `τ ∈ T` the set `S̄_τ` is the post-processing of the final
`S^τ_1, …, S^τ_p`, and the output is the best among the `S̄_τ`, or the empty set if `T = ∅`. -/
noncomputable def alg2Out {Ω : Type} [Fintype E] (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α ε' : ℝ)
    (Off : Ω → Finset E → Finset E) (σ : List E) (ω : Ω) : Finset E :=
  let st := alg2Run p f k α ε' σ
  bestOf f (((alg2Guesses k α ε' st).sort (· ≤ ·)).map fun h => postProcess f Off ω (st.sets h))

end StreamSubmod


