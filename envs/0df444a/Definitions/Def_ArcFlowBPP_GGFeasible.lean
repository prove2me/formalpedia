-- Prove2me | Definitions.Def_ArcFlowBPP_GGFeasible
-- name    : ArcFlowBPP_GGFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:58.979041+00:00
-- url     : https://prove2.me/theorems/20811e8f-474a-4d0a-80f7-8646f2e24eb1
-- title:
--   Feasible solution of the Gilmore–Gomory model (6)–(8) over a pattern set $P$
-- statement:
--   Let $P \subseteq \mathbb N^m$ be a set of patterns and $b \in \mathbb N^m$ the demands. A solution $x$ is **feasible** for the Gilmore–Gomory model over $P$,
--
--   $$
--   \text{minimize } \sum_{p \in P} x_p \quad \text{subject to} \quad \sum_{p\in P} p_i\, x_p \ge b_i \ (i = 1,\dots,m), \qquad x_p \ge 0,
--   $$
--
--   if it uses only patterns of $P$, meets every demand (7), and is nonnegative (8). The ring is $\mathbb N$ for the integer program and $\mathbb R$ for its linear relaxation.
--
--   In the paper the pattern set is the set of valid cutting patterns (9). Property 1 takes instead "the same patterns as the ones obtained from paths in the graph", which is why the pattern set is a parameter here.
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, model (6)–(8), p.4

import Mathlib
import Definitions.Def_ArcFlowBPP_coverage

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, model (6)–(8), p.4, with the set of patterns `P` in place of the patterns (9): `x` is
a feasible solution of the Gilmore–Gomory model over the pattern set `P` with demands `b`:
1. `x` uses only patterns of `P`;
2. (7) `∑_{p} pᵢ x_p ≥ bᵢ` for every item `i`;
3. (8) `x ≥ 0`.
The objective (6) is `ArcFlowBPP.numRolls x`. Property 1 (p.7) takes `P` to be "the same
patterns as the ones obtained from paths in the graph" (`ArcFlowBPP.pathPatterns`).

**Formalization Note.** Over `R = ℕ` this is the integer program ((8) "integer"); over `R = ℝ`
its linear relaxation. -/
def GGFeasible {m : ℕ} (R : Type*) [Semiring R] [PartialOrder R] (P : Set (Fin m → ℕ))
    (b : Fin m → ℕ) (x : (Fin m → ℕ) →₀ R) : Prop :=
  (↑x.support ⊆ P) ∧ (∀ i, (b i : R) ≤ coverage x i) ∧ (∀ p, 0 ≤ x p)

end ArcFlowBPP


