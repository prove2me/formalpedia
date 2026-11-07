-- Prove2me | Definitions.Def_UncrowdedColoring_SatisfiesP
-- name    : UncrowdedColoring_SatisfiesP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:49.773022+00:00
-- url     : https://prove2.me/theorems/a034980a-cb34-4e2a-8800-9e07bf3ee1d1
-- title:
--   Property $P(i)$, with the integrality correction $|L(v)|=\lceil q_i\rceil$
-- statement:
--   Let $F$ be a family of restriction hypergraphs with respect to $L$ on $U$. $(L,F)$ **satisfies $P(i)$**, for $i\in[s]$, if
--
--   1. (Q1) $\bigcup_{c\in L(U)}F_c$ is rank-$k$ and uncrowded; moreover for every $c\ne c'$ in $L(U)$, $e\in E(F_c)$, $e'\in E(F_{c'})$, either $e=e'$ with $|e|=|e'|=k$, or $|e\cap e'|\le 1$;
--   2. (Q2) $|L(v)|=\lceil q_i\rceil$ for every $v\in U$;
--   3. (Q3) for every $v\in U$, $c\in L(v)$ and $2\le\ell\le k$,
--   $$\deg(F_c,\ell,v)\le\binom{k-1}{\ell-1}\Big(\frac{\alpha\gamma_i}{q_i}\Big)^{k-\ell}\beta_i^{\ell-1}t_i.$$
--
--   $P(i)$ is the invariant of the iterated nibble.
--
--   **Formalization Note** The paper prints (Q2) as $|L(v)|=q_i$ with $q_i$ real and warns on p.14 that ceilings are omitted. Read literally, nothing nonempty satisfies $P(1)$ when $q_1$ is irrational, for instance $k=2$, $\varepsilon=1/2$, integer $d$. The ceiling is the intended condition. (Q3) keeps the real $q_i$.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Definition 4.5, p.18

import Mathlib
import Definitions.Def_UncrowdedColoring_IsUncrowded
import Definitions.Def_UncrowdedColoring_IsUniform
import Definitions.Def_UncrowdedColoring_paramState
import Definitions.Def_UncrowdedColoring_IsRestrictionFamily

open scoped Classical

namespace UncrowdedColoring

/-- The union hypergraph `⋃_{c∈L(U)} F_c` on the vertex set `U` (§3.1, p.13; Definition 4.5, p.18).

**Formalization Note.** The vertex set is `U` together with all vertices of the edges, so that the
Mathlib `Hypergraph` is defined for any data; for a family of restriction hypergraphs, where edges lie
in `U`, it is exactly `U`. -/
noncomputable def unionHypergraph {V : Type*} (U : Finset V) (L : V → Finset ℕ)
    (F : ℕ → Finset (Finset V)) : Hypergraph V where
  vertexSet := (U : Set V) ∪ ⋃₀ {e : Set V | ∃ c ∈ colours U L, ∃ f ∈ F c, e = (f : Set V)}
  edgeSet := {e : Set V | ∃ c ∈ colours U L, ∃ f ∈ F c, e = (f : Set V)}
  subset_vertexSet_of_mem_edgeSet' := fun _ he _ hx => Or.inr ⟨_, he, hx⟩

/-- **Property `P(i)`** (Definition 4.5, p.18). `(L, F)` satisfies `P(i)` for `i ∈ [s]` if

* (Q1) `⋃_{c∈L(U)} F_c` is rank-`k` and uncrowded; moreover, for every `c ≠ c′` in `L(U)`, every
  `e ∈ E(F_c)` and `e′ ∈ E(F_{c′})`, either `e = e′` with `|e| = |e′| = k`, or `|e ∩ e′| ≤ 1`;
* (Q2) for every `v ∈ U`, `|L(v)| = ⌈q_i⌉`;
* (Q3) for every `v ∈ U`, `c ∈ L(v)`, `2 ≤ ℓ ≤ k`:
  `deg(F_c, ℓ, v) ≤ binom(k−1, ℓ−1) (αγ_i/q_i)^{k−ℓ} β_i^{ℓ−1} t_i`.

Dhawan, Methuku, Vo, *List Coloring Uncrowded Hypergraphs at the Shattering Threshold*, STOC 2027
submission (manuscript sha256 2e7243ce…), Definition 4.5, p.18.

**Formalization Note (correction).** The paper prints (Q2) as `|L(v)| = q_i`, with `q_i` real by
(14)–(16), and warns on p.14 that floors and ceilings are omitted. Read literally, no nonempty instance
satisfies `P(1)` when `q_1` is irrational (`k = 2`, `ε = 1/2`, integer `d`: `q_1 = (3/2) d / log d`),
so Lemma 4.7 would be vacuous and Proposition 4.6 false. (Q3) keeps the real `q_i`. In (Q3), `0 ^ 0 = 1`
is what the paper needs: at `i = 1`, `γ_1 = 0` and only `ℓ = k` survives. The clause `1 ≤ i ≤ s`
is "for some `i ∈ [s]`". -/
def SatisfiesP {V : Type*} (k : ℕ) (ε d : ℝ) (i : ℕ) (U : Finset V) (L : V → Finset ℕ)
    (F : ℕ → Finset (Finset V)) : Prop :=
  (1 ≤ i ∧ i ≤ numSteps ε d) ∧
  -- (Q1)
  (IsRank (unionHypergraph U L F) k ∧ IsUncrowded (unionHypergraph U L F) ∧
    ∀ c ∈ colours U L, ∀ c' ∈ colours U L, c ≠ c' → ∀ e ∈ F c, ∀ e' ∈ F c',
      (e = e' ∧ e.card = k) ∨ (e ∩ e').card ≤ 1) ∧
  -- (Q2)
  (∀ v ∈ U, (L v).card = ⌈qSeq k ε d i⌉₊) ∧
  -- (Q3)
  ∀ v ∈ U, ∀ c ∈ L v, ∀ ℓ, 2 ≤ ℓ → ℓ ≤ k →
    (ellDegree (F c) ℓ v : ℝ) ≤
      ((k - 1).choose (ℓ - 1) : ℝ) *
        (alpha ε d * gammaSeq k ε d i / qSeq k ε d i) ^ (k - ℓ) *
        betaSeq k ε d i ^ (ℓ - 1) * tSeq k ε d i

end UncrowdedColoring


