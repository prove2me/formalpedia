-- Prove2me | Definitions.Def_TurnstileRank_TightBounds_LinearSketch
-- name    : TurnstileRank_TightBounds_LinearSketch
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:07:34.730199+00:00
-- url     : https://prove2.me/theorems/f7213082-64e1-4a0c-b247-d4b0ff12826f
-- title:
--   Randomized linear sketches (Definition 3.1), their space, stored bits and rank correctness
-- statement:
--   Definition 3.1: a randomized linear sketch on $[U]$ draws a public random seed $\rho$ (here from a discrete law `law` on a type $\mathrm P$), which fixes an item map $A_\rho:[U]\to G$ into an abelian group $G$ and a decoder $g_\rho$ from states and queries (type $Q$) to answers (type $O$). On $f\in\mathbb Z^U$ the state is $A_\rho(f)=\sum_u f_uA_\rho(u)$, and a query $x$ is answered by $g_\rho(A_\rho(f),x)$. One group serves every seed (a family $G_\rho$ embeds in the product).
--
--   * `HasSpace L s` ("$s$ bits suffice"): for every seed in the support of the seed law, the set of states $\{A_\rho(f):f\in\mathbb Z^U\}$ is finite and has at most $2^s$ elements. The paper's space is the least such $s$; "a sketch of $s$ bits" is `HasSpace L s`.
--   * `StoredBits L B` (space "with random seed included"): the seed law has finite support and $\log_2(\#\text{seeds})+s\le B$ for some $s$ with `HasSpace L s`.
--   * `SketchRankCorrect L n ε δ`: for every input $f\in\mathbb N^U$ with $\sum_uf_u\le n$ and every query $x\le U$, the answer is within $\varepsilon\|f\|_1$ of $R_f(x)$ with probability at least $1-\delta$ ("errs by more than $\varepsilon\|f\|_1$ with probability at most $\delta$ on every fixed input of mass at most $n$").
--   * `Query`: a rank query `rank x` or a select query `select r` (§7).
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, Definition 3.1, printed p. 11 (PDF 12), recalled printed p. 30 (PDF 31)

import Mathlib
import Definitions.Def_TurnstileRank_TightBounds_Info
import Definitions.Def_TurnstileRank_TightBounds_Rank

/-!
# Randomized linear sketches (Definition 3.1)

Hu, Jiang, Liu, Yu (2026), held STOC 2027 submission (SHA-256 4be42600…), Definition 3.1, printed
p. 11 (PDF 12), recalled p. 30 (PDF 31): "A randomized linear sketch draws a public random seed `ρ`,
independent of the input and the query, which fixes an abelian group `G_ρ`, an item map
`A_ρ : [U] → G_ρ` and a decoder `g_ρ`. On a frequency vector `f ∈ ℤ^U`, it stores the state
`A_ρ(f) := Σ_{u∈[U]} f_u A_ρ(u) ∈ G_ρ`, and answers a query `x` with `g_ρ(A_ρ(f), x)`. Its space is
the least `s` such that, for every seed `ρ`, the state takes at most `2^s` values. Its seed length is
the number of bits of `ρ`."

**Formalization Note.**
* The seed is drawn from a discrete law `law : PMF Ρ` (a bit string is a discrete random
  variable), and "every seed" means every seed in its support.
* One abelian group `G` serves every seed: a family `G_ρ` embeds in the product `Π_ρ G_ρ`, which
  changes no state count. Queries have a type `Q` and answers a type `O`.
* `HasSpace L s` says that `s` bits suffice: for every seed the set of states `{A_ρ(f) : f ∈ ℤ^U}`
  is finite with at most `2^s` elements; "a sketch of `s` bits" is `HasSpace L s`, and "uses `O(B)`
  bits" is `HasSpace L (C * B)`.
* `StoredBits L B` counts the seed as well ("with random seed included"): the seed takes finitely
  many values, and `log₂ (number of seeds) + s ≤ B` for some `s` with `HasSpace L s`.
* `RankCorrect L n ε δ`: on every fixed input `f ∈ ℤ^U_{≥0}` of mass at most `n` and every fixed
  query `x ∈ {0, …, U}`, the answer errs by more than `ε‖f‖₁` with probability at most `δ`.
* `Query` bundles the two query types of §7: a rank query `x` and a select query with target `r`.
-/

noncomputable section

open scoped BigOperators

namespace TurnstileRank.TightBounds

/-- Definition 3.1: a randomized linear sketch over `[U]` with seeds `Ρ`, state group `G`, queries
`Q` and answers `O`. -/
structure LinearSketch (U : ℕ) (Ρ G Q O : Type) [AddCommGroup G] where
  /-- The law of the public random seed. -/
  law : PMF Ρ
  /-- The item map `A_ρ : [U] → G`. -/
  item : Ρ → Fin U → G
  /-- The decoder `g_ρ`. -/
  dec : Ρ → G → Q → O

namespace LinearSketch

variable {U : ℕ} {Ρ G Q O : Type} [AddCommGroup G]

/-- The state `A_ρ(f) = Σ_u f_u A_ρ(u)`. -/
def state (L : LinearSketch U Ρ G Q O) (ρ : Ρ) (f : Fin U → ℤ) : G := ∑ u, f u • L.item ρ u

/-- `s` bits suffice: for every seed in the support, the state takes finitely many and at most
`2^s` values. -/
def HasSpace (L : LinearSketch U Ρ G Q O) (s : ℝ) : Prop :=
  ∀ ρ ∈ L.law.support, (Set.range (L.state ρ)).Finite ∧
    ((Set.range (L.state ρ)).ncard : ℝ) ≤ (2 : ℝ) ^ s

/-- At most `B` bits with the random seed included. -/
def StoredBits (L : LinearSketch U Ρ G Q O) (B : ℝ) : Prop :=
  L.law.support.Finite ∧ ∃ s : ℝ, L.HasSpace s ∧ Real.logb 2 (L.law.support.ncard : ℝ) + s ≤ B

end LinearSketch

/-- A nonnegative integer input `f ∈ ℕ^U`, as a vector of `ℤ^U`. -/
def toZ {U : ℕ} (f : Fin U → ℕ) : Fin U → ℤ := fun u => (f u : ℤ)

/-- Rank correctness with failure probability at most `δ`: on every fixed input of mass at most
`n` and every fixed query `x ≤ U`, the answer is within `ε‖f‖₁` of `R_f(x)` with probability at
least `1 − δ`. -/
def SketchRankCorrect {U : ℕ} {Ρ G : Type} [AddCommGroup G] (L : LinearSketch U Ρ G ℕ ℝ)
    (n : ℕ) (ε δ : ℝ) : Prop :=
  ∀ f : Fin U → ℕ, (∑ u, f u) ≤ n → ∀ x : ℕ, x ≤ U →
    1 - δ ≤ prob L.law {ρ | RankOK (toZ f) ε x (L.dec ρ (L.state ρ (toZ f)) x)}

/-- The two query types of §7: a rank query at `x ∈ {0, …, U}` and a select query with target
rank `r ∈ [0, ‖f‖₁]`. -/
inductive Query where
  | rank (x : ℕ)
  | select (r : ℝ)

end TurnstileRank.TightBounds


