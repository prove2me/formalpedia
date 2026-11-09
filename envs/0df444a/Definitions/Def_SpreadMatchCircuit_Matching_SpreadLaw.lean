-- Prove2me | Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
-- name    : SpreadMatchCircuit_Matching_SpreadLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:34.84311+00:00
-- url     : https://prove2.me/theorems/3ca1a5ce-34dc-4b32-926d-711f0815ec65
-- title:
--   Random matchings, their support, $r$-spreadness and uniform probabilities
-- statement:
--   A **random matching** is given by a probability law $\mu$ on the finite collection of sets of edges of $[n]$, with arbitrary weights. The notation is the following.
--
--   1. For an event $A$, $p_\mu(A)=\sum_{z\in A}\mu(z)$, as a real number.
--   2. $\mathcal Z=\{z:\mu(z)>0\}$ is the support of the random matching $Z\sim\mu$.
--   3. The law is that of a random matching with $|Z|\le t$ if every $z\in\mathcal Z$ is a matching with at most $t$ edges.
--   4. The random matching is **$r$-spread** if for every matching $m$,
--   $$p(m\subseteq Z)\le r^{-|m|}.$$
--   5. For a finite set $F$, the uniform probability of an event $A$ is $|\{x\in F:A(x)\}|/|F|$.
--
--   The law is not assumed uniform, its edges are not assumed independent, and the matchings are not assumed bipartite. Spreadness is the hypothesis of the Spread Matching Lemma.
--
--   **Formalization Note** The law is a Mathlib `PMF`; probabilities are converted to real numbers by summing over a finite type. The empty matching is included in the spread condition, where it reads $1\le 1$. If $F$ is empty the uniform probability is $0/0=0$ in Lean; every use in this mission has $F$ nonempty.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 4 (§1.2: r-spread random matching, support)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs

namespace SpreadMatchCircuit.Matching

open Finset

variable {α : Type} [Fintype α] {n : ℕ}

open scoped Classical in
/-- The probability, as a real number, of the event `A` under the law `μ` on a finite type. -/
noncomputable def lawProb (μ : PMF α) (A : α → Prop) : ℝ :=
  ∑ x ∈ univ.filter A, (μ x).toReal

open scoped Classical in
/-- The support of a law on a finite type, as a finite set. This is the source's `𝒵` when `μ` is
the law of the random matching `Z`. -/
noncomputable def lawSupport (μ : PMF α) : Finset α :=
  univ.filter fun x => x ∈ μ.support

open scoped Classical in
/-- The probability of `A` under the uniform law on the finite set `F`:
`|{x ∈ F : A x}| / |F|`. -/
noncomputable def uniformProb {β : Type} (F : Finset β) (A : β → Prop) : ℝ :=
  ((F.filter A).card : ℝ) / (F.card : ℝ)

/-- The law `μ` is that of a random matching with at most `t` edges: every matching in its
support has at most `t` edges. -/
def IsBoundedMatchingLaw (μ : PMF (Finset (Edge n))) (t : ℝ) : Prop :=
  ∀ z ∈ lawSupport μ, IsMatching z ∧ (z.card : ℝ) ≤ t

/-- The random matching `Z ∼ μ` is `r`-spread: `p(m ⊆ Z) ≤ r^{-|m|}` for every matching `m`
(the empty matching included, where the bound reads `1 ≤ 1`). -/
def IsSpread (μ : PMF (Finset (Edge n))) (r : ℝ) : Prop :=
  ∀ m : Finset (Edge n), IsMatching m → lawProb μ (fun z => m ⊆ z) ≤ (r ^ m.card)⁻¹

end SpreadMatchCircuit.Matching


