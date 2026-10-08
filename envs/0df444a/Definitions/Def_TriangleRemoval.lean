-- Prove2me | Definitions.Def_TriangleRemoval
-- name    : TriangleRemoval
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:20.789871+00:00
-- url     : https://prove2.me/theorems/2e170b47-d49b-4e4f-830c-d20b9118fb87
-- statement:
--   This block works in the namespace SharpTerminalLeave. A Graph on n vertices is a finite set of two-element subsets of Fin n (its edges), and completeGraph(n) is the set of all two-element subsets. triangles(G) is the set of three-element vertex sets all of whose three pairs lie in G. The step map is a probability mass function on graphs: if G has at least one triangle, it picks a triangle t uniformly at random from triangles(G) and returns G with the three edges of t removed; if G has no triangles, it returns G unchanged. evolve(G,k) is the law obtained by applying step k times starting from G, and terminalLaw(n) is evolve of the complete graph for C(n,2) steps, i.e. the random triangle-removal process run for as many steps as there are edges. expectation(n,f) is the sum over graphs G of the terminal law's probability of G times f(G), and probability(n,P) is the expectation of the indicator of a property P. normalization(n) is n^(3/2), normalizedLeave(n,G) is the number of edges of G divided by n^(3/2), and sharpConstant is the real number 1/(2√2). These are only definitions; the block states no theorem or asymptotic claim about them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangleRemoval.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangleRemoval.lean; bytes 16..1423
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

section
section

open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

abbrev Graph (n : ℕ) := Finset (Finset (Fin n))

def completeGraph (n : ℕ) : Graph n := Finset.univ.powersetCard 2

def triangles {n : ℕ} (G : Graph n) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter (fun t => t.powersetCard 2 ⊆ G)

noncomputable def step {n : ℕ} (G : Graph n) : PMF (Graph n) :=
  if h : (triangles G).Nonempty then
    (PMF.uniformOfFinset (triangles G) h).map (fun t => G \ t.powersetCard 2)
  else PMF.pure G

noncomputable def evolve {n : ℕ} (G : Graph n) : ℕ → PMF (Graph n)
  | 0 => PMF.pure G
  | k + 1 => (evolve G k).bind step

noncomputable def terminalLaw (n : ℕ) : PMF (Graph n) :=
  evolve (completeGraph n) (n.choose 2)

noncomputable def expectation (n : ℕ) (f : Graph n → ℝ) : ℝ :=
  ∑ G, (terminalLaw n G).toReal * f G

noncomputable def probability (n : ℕ) (P : Graph n → Prop) : ℝ := by
  classical
  exact expectation n (fun G => if P G then 1 else 0)

noncomputable def normalization (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)

noncomputable def normalizedLeave (n : ℕ) (G : Graph n) : ℝ :=
  (G.card : ℝ) / normalization n

noncomputable def sharpConstant : ℝ := 1 / (2 * Real.sqrt 2)

end SharpTerminalLeave
end
end

open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave



end SharpTerminalLeave
end OAI


