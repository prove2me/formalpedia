-- Prove2me | Definitions.Def_XOSMax_alg4
-- name    : XOSMax_alg4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:30.123147+00:00
-- url     : https://prove2.me/theorems/1ecaafe1-388d-4857-8387-c280c2d8f35e
-- title:
--   Algorithm 4: the $(k-1)$-approximation algorithm
-- statement:
--   Algorithm 4 of the paper, on the ground list $L$:
--
--   - Lines 1–6 compute cliques $V_1,\dots,V_\ell$ (`cliquePhase`);
--   - Line 7: for each $i\in[\ell]$, $Y_i\leftarrow V_i\cup\{v\in V\setminus V_i: f(V_i+v)>f(V_i)\}$;
--   - Line 8: for each unordered pair $\{i,j\}$ of distinct indices and each $v\in V$, $Z^v_{ij}\leftarrow V_i\cup V_j\cup\{v\}$;
--   - Lines 9–10: return $\tilde X\in\arg\max_{X\in\mathcal V\cup\mathcal Y\cup\mathcal Z}f(X)$, where $\mathcal V$, $\mathcal Y$, $\mathcal Z$ are the families of the $V_i$, the $Y_i$ and the $Z^v_{ij}$.
--
--   If $\ell=1$ the family $\mathcal Z$ is empty.
--
--   The algorithm takes neither the width $k$ nor $f$: "the algorithm does not use the information of the width k".
--
--   **Formalization Note** Candidates are evaluated in the order $V_i$, $Y_i$, $Z^v_{ij}$ and the first best one is kept. Following the proof of Lemma 11, each union $V_i\cup V_j$ is built once at a charge of $n$ steps and each $Z^v_{ij}$ is then one insertion. The incumbent is an $O(1)$ descriptor, and the output is materialized at a charge of $n$ steps. On the empty list nothing is charged and the result is $\emptyset$.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Algorithm 4, p.7; Lemma 11, proof, p.7

import Mathlib
import Definitions.Def_XOSMax_OracleProg
import Definitions.Def_XOSMax_cliquePhase
import Definitions.Def_XOSMax_buildY

namespace XOSMax

open OracleProg

variable {E : Type} [DecidableEq E]

/-- Compare the candidate `X` with the incumbent of Line 10, a stored pair (candidate, value). The
first best candidate stays: a later one replaces it only if its value is strictly larger.

**Formalization Note** Charges: one step for the iteration and for the construction of `X` from what
is stored (one insertion, for `Z^v_ij`), one oracle call, one step for the comparison and the store
of the incumbent. The incumbent is an `O(1)` descriptor even though Lean holds it as a `Finset`; the
output is materialized, at a charge of `n`, at the end of `alg4`. -/
noncomputable def consider (inc : Option (Finset E × ℝ)) (X : Finset E) :
    OracleProg E (Option (Finset E × ℝ)) := do
  tick
  let a ← ask X
  tick
  match inc with
  | none => pure (some (X, a))
  | some (B, b) => if b < a then pure (some (X, a)) else pure (some (B, b))

/-- The family `Z` of Lines 8–9, for the pair of `V'` with one `W`: build `U = V' ∪ W` once, at a
charge of `n` steps, and go through `Z^v = U ∪ {v}` for **every** `v ∈ V`, including `v ∈ U`
(proof of Lemma 11, p.7: "we first construct Vi ∪ Vj"). -/
noncomputable def scanPair (L : List E) (V' : Finset E) (inc : Option (Finset E × ℝ))
    (W : Finset E) : OracleProg E (Option (Finset E × ℝ)) := do
  ticks L.length
  let U := V' ∪ W
  L.foldlM (fun inc' v => consider inc' (insert v U)) inc

/-- The family `Z` of Lines 8–9 over all unordered pairs `{i, j}`: each element of the list is paired
with the elements after it. -/
noncomputable def scanPairs (L : List E) :
    List (Finset E) → Option (Finset E × ℝ) → OracleProg E (Option (Finset E × ℝ))
  | [], inc => pure inc
  | V' :: rest, inc => do
    tick
    let inc' ← rest.foldlM (scanPair L V') inc
    scanPairs L rest inc'

/-- **Algorithm 4**, the `(k − 1)`-approximation algorithm for `k`-XOS maximization (Filmus, Kawase,
Kobayashi & Yamaguchi, arXiv:1811.09045v3, §2.4, p.7). The ground set is the list `L`.

Lines 1–6 are `cliquePhase`, Line 7 is `buildY` for each `Vᵢ`, and Lines 8–10 find the first best
candidate over `V₁, …, V_ℓ`, then `Y₁, …, Y_ℓ`, then all `Z^v_ij` (no `Z` at all when `ℓ = 1`).

**Formalization Note** The width `k` is not an argument and `f` is reachable only through queries:
"the algorithm does not use the information of the width k" (p.7). The output is materialized at a
charge of `n` steps. On the empty list, which the paper excludes, nothing is charged and the result
is `∅`. -/
noncomputable def alg4 (L : List E) : OracleProg E (Finset E) := do
  let Vs ← cliquePhase L
  let Ys ← Vs.foldlM (fun acc V' => do
    let Y ← buildY L V'
    pure (acc ++ [Y])) []
  let inc₁ ← Vs.foldlM consider none
  let inc₂ ← Ys.foldlM consider inc₁
  let inc₃ ← scanPairs L Vs inc₂
  ticks L.length
  match inc₃ with
  | none => pure ∅
  | some (B, _) => pure B

end XOSMax


