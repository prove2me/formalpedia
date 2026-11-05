-- Prove2me | Definitions.Def_TenChallenges_ErdosHajnal
-- name    : TenChallenges_ErdosHajnal
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:28:51.445497+00:00
-- url     : https://prove2.me/theorems/98b68fdd-9505-4c03-9d39-a0f8d63053b9
-- title:
--   The Erdős–Hajnal property for a fixed forbidden induced subgraph $H$
-- statement:
--   The definition behind Challenge 5 of the Ten Challenges benchmark. For a graph $H$ on a vertex type $W$, the **Erdős–Hajnal property for $H$** says that there is a real constant $c>0$ such that for every finite graph $G$ (on a vertex type in the lowest universe) containing no induced subgraph isomorphic to $H$, there is a finite set $s$ of vertices of $G$ which is a clique of $G$ or a clique of the complement of $G$ (an independent set), with
--
--   $$|s| \ \ge\ |V(G)|^{c}.$$
--
--   The constant $c$ depends only on $H$. The Erdős–Hajnal conjecture asserts this property for every finite graph $H$; the property is the basic object of the theory of induced subgraph density.
--
--   **Formalization Note.** "No induced copy of $H$" is `¬ H ⊴ G` with Mathlib's induced-subgraph relation; the size bound is stated in the reals with real exponentiation, so $|V(G)|=0$ is covered by $s=\emptyset$.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/ErdosHajnal.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/ErdosHajnal.lean; conjecture as in P. Erdős, A. Hajnal, Ramsey-type theorems, Discrete Appl. Math. 25 (1989).

import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-- The Erdős–Hajnal conjecture for a fixed forbidden graph `H`: there is `c_H > 0`
such that every finite `H`-free graph `G` has a clique or an independent set of
size at least `|V(G)|^c_H`. -/
def ErdosHajnalConjectureFor {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V), ¬ H ⊴ G →
      ∃ s : Finset V, (G.IsClique s ∨ Gᶜ.IsClique s) ∧
        (s.card : ℝ) ≥ (Fintype.card V : ℝ) ^ c


