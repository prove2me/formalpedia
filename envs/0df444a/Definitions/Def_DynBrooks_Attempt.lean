-- Prove2me | Definitions.Def_DynBrooks_Attempt
-- name    : DynBrooks_Attempt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:07.258476+00:00
-- url     : https://prove2.me/theorems/aa43f451-e4be-4782-9640-9a70ac2e2361
-- title:
--   Algorithm 3 — one repair attempt: tests, moves, continuing arrivals, failure probability
-- statement:
--   Fix a graph $G$ on $[n]$, a proper partial coloring $\chi_0$ (colors in $[\Delta]$, value $0$ for an uncolored vertex) with one hole $v_0$, and a **stored neighbor array** (a list of the neighbors of each vertex, each once). An attempt builds a simple path $v_0,v_1,\dots,v_i$; the current coloring gives $v_j$ ($j<i$) the initial color $\chi_0(v_{j+1})$, leaves $v_i$ uncolored, and keeps $\chi_0$ elsewhere. Let $X_i=\{v_0,\dots,v_i\}$ and $G_i=G[X_i]$. At an arrival at $v_i$ the **stopping tests** are:
--
--   1. a color of $[\Delta]$ is available at $v_i$;
--   2. $G_i$ is not a Gallai tree;
--   3. $i\ge2$ and some vertex is adjacent to all of $v_{i-2},v_{i-1},v_i$;
--   4. $i\ge1$, $v_i$ has two neighbors in $X_{i-1}$, and the edge $v_{i-1}v_i$ has a common neighbor.
--
--   If none succeeds and $i<L$, the attempt moves: at $i=0$ to the first neighbor of $v_0$ in the stored array that is not a **true twin** of $v_0$ ($N[u]\ne N[v_0]$); at $i>0$ to a uniformly random vertex of $N(v_i)\setminus(N[v_{i-1}]\cup X_i)$. If none succeeds and $i=L$, the attempt fails.
--
--   The definition provides: the arrivals the attempt can reach, the **continuing arrivals** (reachable, with tests 1–4 failing), the counts $a_i$ (size of the choice set), $s_i=|N[v_i]\setminus N[v_{i-1}]|$ and $b_i=|N(v_i)\cap X_{i-1}|-1$, **collisions** (an arrival $i\ge1$ whose vertex has a second earlier neighbor besides its predecessor), and the exact probability that the attempt with length limit $L$ fails.
--
--   **Formalization Note** A path is stored most-recent-first. The probability is computed by the recursion of the procedure's law. An empty choice set does not occur under the hypotheses of §5 (Lemma 5.2) and would be counted as a failure. Test 4's "two neighbors" is read as "at least two"; with three or more earlier neighbors test 2 already succeeds (p.62).
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Algorithm 3, p.56 (PDF 58); §5.1, pp.55–57 (PDF 57–59)

import Mathlib
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynBrooks_Gallai

namespace DynBrooks

/-! # One repair attempt (Algorithm 3)

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), §5.1,
pp.55–57 (PDF 57–59), Algorithm 3, p.56.

**Formalization Note.** A partial coloring is `χ : Fin n → ℕ`, with value `0` for a hole and values
`1, …, Δ` for colors. A path `v₀, …, v_i` is the list `[v_i, …, v₀]`, most recent vertex first, so a
prefix of the visited path is a suffix of the list. The tests of Algorithm 3 are stated on the current
coloring, in which `v_j` holds the initial color of `v_{j+1}` and `v_i` is the hole. Whether a test
succeeds depends only on the path and `χ₀`; what a success recolors does not enter any statement
of this file, since an attempt that stops at a test does not fail. -/

open Classical

variable {n : ℕ}

/-- A proper partial `Δ`-coloring: colors at most `Δ`, `0` means uncolored, and adjacent colored
vertices differ. -/
def IsPartialColoring (Δ : ℕ) (G : SimpleGraph (Fin n)) (χ : Fin n → ℕ) : Prop :=
  (∀ v, χ v ≤ Δ) ∧ ∀ u v, G.Adj u v → χ u ≠ 0 → χ u ≠ χ v

/-- `χ` has exactly one hole, at `v₀`. -/
def HasOneHole (χ : Fin n → ℕ) (v₀ : Fin n) : Prop :=
  ∀ v, χ v = 0 ↔ v = v₀

/-- The closed neighborhood `N[v]`. -/
noncomputable def closedNbr (G : SimpleGraph (Fin n)) (v : Fin n) : Finset (Fin n) :=
  insert v (G.neighborFinset v)

/-- The current coloring at the arrival with path `p`: colors have shifted backward along the path
and the last vertex of the path is uncolored (`χ_i` of §5.1). -/
def curColoring (χ₀ : Fin n → ℕ) : List (Fin n) → Fin n → ℕ
  | [] => χ₀
  | [_] => χ₀
  | w :: v :: rest =>
      let χ := curColoring χ₀ (v :: rest)
      Function.update (Function.update χ v (χ w)) w 0

/-- The stopping tests 1–4 of Algorithm 3 at an arrival with path `p`:
1. a color is available at `v_i`;
2. `G_i = G[X_i]` is not a Gallai tree;
3. `i ≥ 2` and some vertex is adjacent to all of `v_{i-2}, v_{i-1}, v_i`;
4. `i ≥ 1`, `v_i` has two neighbors in `X_{i-1}`, and the edge `v_{i-1}v_i` has a common neighbor. -/
def Stops (Δ : ℕ) (G : SimpleGraph (Fin n)) (χ₀ : Fin n → ℕ) (p : List (Fin n)) : Prop :=
  (∃ v ∈ p.head?, ∃ c : ℕ, 1 ≤ c ∧ c ≤ Δ ∧ ∀ u, G.Adj v u → curColoring χ₀ p u ≠ c) ∨
  ¬ IsGallaiTree (G.induce {x | x ∈ p}) ∨
  (match p with
    | v :: u :: t :: _ => ∃ x, G.Adj x t ∧ G.Adj x u ∧ G.Adj x v
    | _ => False) ∨
  (match p with
    | v :: u :: rest =>
        2 ≤ ((G.neighborFinset v).filter fun x => x ∈ u :: rest).card ∧
          ∃ x, G.Adj x u ∧ G.Adj x v
    | _ => False)

/-- `u` is a true twin of `v`: `N[u] = N[v]`. -/
def IsTrueTwin (G : SimpleGraph (Fin n)) (u v : Fin n) : Prop :=
  closedNbr G u = closedNbr G v

/-- `nbr v` is a "stored neighbor array" of `v`: it lists the neighbors of `v` once each. -/
def IsNeighborArray (G : SimpleGraph (Fin n)) (nbr : Fin n → List (Fin n)) : Prop :=
  ∀ v, (nbr v).Nodup ∧ ∀ u, u ∈ nbr v ↔ G.Adj v u

/-- The first move: the first neighbor in the stored array of `v₀` that is not a true twin of `v₀`. -/
noncomputable def firstMove (G : SimpleGraph (Fin n)) (nbr : Fin n → List (Fin n)) (v₀ : Fin n) :
    Option (Fin n) :=
  (nbr v₀).find? fun u => decide (¬ IsTrueTwin G u v₀)

/-- The choice set at an arrival `i ≥ 1`, `N(v_i) \ (N[v_{i-1}] ∪ X_i)`; empty for a shorter path. -/
noncomputable def choices (G : SimpleGraph (Fin n)) : List (Fin n) → Finset (Fin n)
  | v :: u :: rest =>
      (G.neighborFinset v).filter fun x => x ∉ closedNbr G u ∧ x ∉ (v :: u :: rest)
  | _ => ∅

/-- `Visited … p`: an attempt from hole `v₀` can arrive with path `p` when no length limit applies. -/
inductive Visited (Δ : ℕ) (G : SimpleGraph (Fin n)) (χ₀ : Fin n → ℕ) (nbr : Fin n → List (Fin n))
    (v₀ : Fin n) : List (Fin n) → Prop
  | root : Visited Δ G χ₀ nbr v₀ [v₀]
  | first {v₁ : Fin n} : ¬ Stops Δ G χ₀ [v₀] → firstMove G nbr v₀ = some v₁ →
      Visited Δ G χ₀ nbr v₀ [v₁, v₀]
  | move {v u : Fin n} {rest : List (Fin n)} {x : Fin n} :
      Visited Δ G χ₀ nbr v₀ (v :: u :: rest) → ¬ Stops Δ G χ₀ (v :: u :: rest) →
      x ∈ choices G (v :: u :: rest) → Visited Δ G χ₀ nbr v₀ (x :: v :: u :: rest)

/-- A **continuing arrival**: the attempt arrives with path `p` and tests 1–4 fail there. (The test
`i = L` only cuts the path off, so an arrival that continues under some limit `L > i` is exactly
this.) -/
def Continuing (Δ : ℕ) (G : SimpleGraph (Fin n)) (χ₀ : Fin n → ℕ) (nbr : Fin n → List (Fin n))
    (v₀ : Fin n) (p : List (Fin n)) : Prop :=
  Visited Δ G χ₀ nbr v₀ p ∧ ¬ Stops Δ G χ₀ p

/-- `a_i`: the number of choices for the next vertex. -/
noncomputable def numChoices (G : SimpleGraph (Fin n)) (p : List (Fin n)) : ℕ :=
  (choices G p).card

/-- `s_i = |N[v_i] \ N[v_{i-1}]|`. -/
noncomputable def sIdx (G : SimpleGraph (Fin n)) : List (Fin n) → ℕ
  | v :: u :: _ => (closedNbr G v \ closedNbr G u).card
  | _ => 0

/-- `|N(v_i) ∩ X_{i-1}|`, the number of earlier neighbors of the arriving vertex. -/
noncomputable def earlierNbrs (G : SimpleGraph (Fin n)) : List (Fin n) → ℕ
  | v :: rest => ((G.neighborFinset v).filter fun x => x ∈ rest).card
  | [] => 0

/-- `b_i = |N(v_i) ∩ X_{i-1}| - 1`, as an integer. -/
noncomputable def bIdx (G : SimpleGraph (Fin n)) (p : List (Fin n)) : ℤ :=
  (earlierNbrs G p : ℤ) - 1

/-- Arrival `i ≥ 1` is a **collision**: the arriving vertex has a second earlier neighbor besides its
predecessor. -/
def IsCollision (G : SimpleGraph (Fin n)) (p : List (Fin n)) : Prop :=
  2 ≤ p.length ∧ 2 ≤ earlierNbrs G p

/-- The probability that one attempt fails, with `r` moves still allowed (`r = L - i`), by the exact
law of Algorithm 3: stopping tests first; at `r = 0` the attempt fails; otherwise the first move is
deterministic and a later move is uniform on `choices`. An empty first or later choice set never
occurs under the hypotheses of §5 (p.55, Lemma 5.2); it is counted as a failure here, which can only
increase the failure probability. -/
noncomputable def failProb (Δ : ℕ) (G : SimpleGraph (Fin n)) (χ₀ : Fin n → ℕ)
    (nbr : Fin n → List (Fin n)) (v₀ : Fin n) : ℕ → List (Fin n) → ℝ
  | 0, p => if Stops Δ G χ₀ p then 0 else 1
  | r + 1, p =>
      if Stops Δ G χ₀ p then 0
      else if p.length = 1 then
        match firstMove G nbr v₀ with
        | some x => failProb Δ G χ₀ nbr v₀ r (x :: p)
        | none => 1
      else if (choices G p).card = 0 then 1
      else
        ((choices G p).card : ℝ)⁻¹ *
          ∑ x ∈ choices G p, failProb Δ G χ₀ nbr v₀ r (x :: p)

end DynBrooks


