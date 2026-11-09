-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_Approximator
-- name    : SpreadMatchCircuit_Matching_Approximator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:20.007659+00:00
-- url     : https://prove2.me/theorems/e34c905f-d244-443e-b73e-baf4095e9196
-- title:
--   The distributions $X_0,X_1$, the error sets, and Algorithm 1 at an AND gate
-- statement:
--   These are the objects of the approximation method (§3 and §3.1). Let $n=2N$.
--
--   **Distributions.** $X_1$ is a uniformly random matching with exactly $k$ edges from $[n/2]$ to $[n]\setminus[n/2]$, with support $\mathcal X_1$. $X_0$ is $G(W_0)$, for $W_0$ a uniformly random subset of $[n]$ of size $b$, with support $\mathcal X_0$. The source writes $q$ for $b$.
--
--   **Approximators and errors.** For a family $M$ of matchings, $f_M(x)=1$ if some $m\in M$ has $m\subseteq x$ and $f_M(x)=0$ otherwise. For a gate function $g$ with family $M_g$,
--   $$E^1_g=\{x\in\mathcal X_1: g(x)=1,\ f_{M_g}(x)=0\},\qquad E^0_g=\{x\in\mathcal X_0: g(x)=0,\ f_{M_g}(x)=1\}.$$
--
--   **The AND gate.** For $g=h_1\wedge h_2$ with families $M_{h_1},M_{h_2}$,
--   $$M'_g=\{m\cup m': m\in M_{h_1},\ m'\in M_{h_2},\ m\cup m'\text{ is a matching}\},$$
--   and the new errors are $N^1_g=E^1_g\setminus(E^1_{h_1}\cup E^1_{h_2})$ and $N^0_g=E^0_g\setminus(E^0_{h_1}\cup E^0_{h_2})$. $Z(x)$ is the first matching of $M'_g$ contained in $x$.
--
--   **Algorithm 1.** Start from $M_g=\emptyset$. While $p(X_1\in N^1_g)>0$, find a largest matching $m$ with
--   $$p(m\subseteq Z(X_1)\mid X_1\in N^1_g)\ge r^{-|m|}.$$
--   If $|m|\le t$ add $m$ to $M_g$ and continue; otherwise halt. Return $M_g$.
--
--   The error sets depend on the current family $M_g$, so they are recomputed at each pass. The output of the algorithm is what Lemmas 11 and 12 are about.
--
--   **Formalization Note** $X_1$ and $X_0$ are given by uniform counting over $\mathcal X_1$ and over size-$b$ vertex sets. The support of $X_0$ is the image of the size-$b$ vertex sets under $W↦G(W)$; probabilities count vertex sets, so repeated images retain their correct probability. These graphs include all incident edges, as on p. 10; they need not be bipartite. Ties for "largest" are broken by a fixed ordering. The while-loop is run with a step allowance $|\text{sets of edges}|+1$. For $r>0$ every pass that does not stop adds a matching not yet in $M_g$, since a matching of $M_g$ contained in $Z(x)\subseteq x$ excludes $x$ from $N^1_g$; so the loop's own exit is always reached first and the allowance only makes the function total. `coreProb` divides by $p(X_1\in N^1_g)$ and is used only when that quantity is positive, as the loop guard ensures. If $M'_g$ has no matching inside $x$, $Z(x)=\emptyset$; this does not occur on $N^1_g$.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 10 (X1, X0), p. 11 (f_M, E), p. 12 (M', N, Algorithm 1)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Encoding

namespace SpreadMatchCircuit.Matching

open Finset

/-- The source's side `[n/2]` of the vertex set `[n]`, for `n = 2N`. -/
def halfSide (N : ℕ) : Finset (Fin (2 * N)) := univ.filter fun v => v.val < N

open scoped Classical in
/-- The support of `X₁`: all matchings with exactly `k` edges from `[n/2]` to `[n] \ [n/2]`.
`X₁` is uniform on this set. -/
noncomputable def crossMatchings (N k : ℕ) : Finset (Finset (Edge (2 * N))) :=
  univ.filter fun x => IsMatching x ∧ x.card = k ∧ IsCrossGraph (halfSide N) x

open scoped Classical in
/-- The support of `X₀ = G(W₀)`, where `W₀` is uniform among vertex sets of size `b`.
The source calls this size `q`; it is independent of the goal's promise threshold. -/
noncomputable def incidentCovers (N b : ℕ) : Finset (Finset (Edge (2 * N))) :=
  (Finset.powersetCard b univ).image incident

/-- `f_M(x) = 1`: some matching of the family `M` is contained in `x`. -/
def Fires {n : ℕ} (M : Finset (Finset (Edge n))) (x : Finset (Edge n)) : Prop :=
  ∃ m ∈ M, m ⊆ x

open scoped Classical in
/-- `E¹_g = {x ∈ 𝒳₁ : g(x) = 1, f_{M}(x) = 0}` for a gate function `g` with family `M`. -/
noncomputable def errorPos (N k : ℕ) (g : Finset (Edge (2 * N)) → Bool)
    (M : Finset (Finset (Edge (2 * N)))) : Finset (Finset (Edge (2 * N))) :=
  (crossMatchings N k).filter fun x => g x = true ∧ ¬ Fires M x

open scoped Classical in
/-- `E⁰_g = {x ∈ 𝒳₀ : g(x) = 0, f_{M}(x) = 1}` for a gate function `g` with family `M`. -/
noncomputable def errorNeg (N b : ℕ) (g : Finset (Edge (2 * N)) → Bool)
    (M : Finset (Finset (Edge (2 * N)))) : Finset (Finset (Edge (2 * N))) :=
  (incidentCovers N b).filter fun x => g x = false ∧ Fires M x

/-- The data of a binary AND gate `g = h₁ ∧ h₂` of the approximation: the functions computed by
the two predecessors and their families `M_{h₁}`, `M_{h₂}`. -/
structure AndGate (N : ℕ) where
  h₁ : Finset (Edge (2 * N)) → Bool
  h₂ : Finset (Edge (2 * N)) → Bool
  M₁ : Finset (Finset (Edge (2 * N)))
  M₂ : Finset (Finset (Edge (2 * N)))

namespace AndGate

variable {N : ℕ}

/-- The function computed at `g = h₁ ∧ h₂`. -/
def g (G : AndGate N) (x : Finset (Edge (2 * N))) : Bool := G.h₁ x && G.h₂ x

/-- `m` has at most `t` edges for every `m` in either predecessor family. -/
def SizeBounded (G : AndGate N) (t : ℝ) : Prop :=
  (∀ m ∈ G.M₁, (m.card : ℝ) ≤ t) ∧ (∀ m ∈ G.M₂, (m.card : ℝ) ≤ t)

open scoped Classical in
/-- `M'_g = {m ∪ m' : m ∈ M_{h₁}, m' ∈ M_{h₂}, m ∪ m' is a matching}`. -/
noncomputable def candidates (G : AndGate N) : Finset (Finset (Edge (2 * N))) :=
  (Finset.image₂ (· ∪ ·) G.M₁ G.M₂).filter IsMatching

open scoped Classical in
/-- `Z(x)`: the first matching of `M'_g` under `ord` contained in `x`, and `∅` if there is none.
On a new positive error `x` such a matching exists. -/
noncomputable def selector (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N))))
    (x : Finset (Edge (2 * N))) : Finset (Edge (2 * N)) :=
  firstOf ord (G.candidates.filter fun m => m ⊆ x) ∅

open scoped Classical in
/-- `N¹_g = E¹_g \ (E¹_{h₁} ∪ E¹_{h₂})` for the current family `M` at `g`. -/
noncomputable def newPos (G : AndGate N) (k : ℕ) (M : Finset (Finset (Edge (2 * N)))) :
    Finset (Finset (Edge (2 * N))) :=
  errorPos N k G.g M \ (errorPos N k G.h₁ G.M₁ ∪ errorPos N k G.h₂ G.M₂)

open scoped Classical in
/-- `N⁰_g = E⁰_g \ (E⁰_{h₁} ∪ E⁰_{h₂})` for the current family `M` at `g`. -/
noncomputable def newNeg (G : AndGate N) (b : ℕ) (M : Finset (Finset (Edge (2 * N)))) :
    Finset (Finset (Edge (2 * N))) :=
  errorNeg N b G.g M \ (errorNeg N b G.h₁ G.M₁ ∪ errorNeg N b G.h₂ G.M₂)

/-- `p(X₁ ∈ N¹_g)` for the current family `M`, with `X₁` uniform on `crossMatchings N k`. -/
noncomputable def newPosProb (G : AndGate N) (k : ℕ) (M : Finset (Finset (Edge (2 * N)))) : ℝ :=
  uniformProb (crossMatchings N k) (fun x => x ∈ G.newPos k M)

/-- `p(m ⊆ Z(X₁) | X₁ ∈ N¹_g)` for the current family `M`; used only when `p(X₁ ∈ N¹_g) > 0`. -/
noncomputable def coreProb (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (M : Finset (Finset (Edge (2 * N)))) (m : Finset (Edge (2 * N))) : ℝ :=
  uniformProb (crossMatchings N k) (fun x => m ⊆ G.selector ord x ∧ x ∈ G.newPos k M) /
    G.newPosProb k M

open scoped Classical in
/-- One matching of largest size among those with `p(m ⊆ Z(X₁) | X₁ ∈ N¹_g) ≥ r^{-|m|}`, ties
broken by `ord`. The empty matching always qualifies when `p(X₁ ∈ N¹_g) > 0`. -/
noncomputable def largestCore (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r : ℝ) (M : Finset (Finset (Edge (2 * N)))) : Finset (Edge (2 * N)) :=
  let F := univ.filter fun m => IsMatching m ∧ (r ^ m.card)⁻¹ ≤ G.coreProb ord k M m
  firstOf ord (F.filter fun m => ∀ m' ∈ F, m'.card ≤ m.card) ∅

open scoped Classical in
/-- The while-loop of Algorithm 1, with a step allowance: while `p(X₁ ∈ N¹_g) > 0`, take a largest
core `m`; if `|m| ≤ t` add it to `M` and repeat, otherwise halt and return `M`. -/
noncomputable def loop (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r t : ℝ) : ℕ → Finset (Finset (Edge (2 * N))) → Finset (Finset (Edge (2 * N)))
  | 0, M => M
  | steps + 1, M =>
      if 0 < G.newPosProb k M then
        if ((G.largestCore ord k r M).card : ℝ) ≤ t then
          loop G ord k r t steps (insert (G.largestCore ord k r M) M)
        else M
      else M

/-- `M_g`, the output of Algorithm 1 started from `M_g = ∅`. For `r > 0`, every pass that does not
stop adds a matching not yet in `M`, so `|Finset (Edge (2N))| + 1` steps always reach the loop's
own exit: the allowance never cuts the loop short. -/
noncomputable def algorithm1 (G : AndGate N) (ord : LinearOrder (Finset (Edge (2 * N)))) (k : ℕ)
    (r t : ℝ) : Finset (Finset (Edge (2 * N))) :=
  G.loop ord k r t (Fintype.card (Finset (Edge (2 * N))) + 1) ∅

end AndGate

end SpreadMatchCircuit.Matching


