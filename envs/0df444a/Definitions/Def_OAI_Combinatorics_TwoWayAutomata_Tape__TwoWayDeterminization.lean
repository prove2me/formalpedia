-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:49:08.277722+00:00
-- url     : https://prove2.me/theorems/6abfcd75-d2d4-4eba-ba98-ff509bc687e2
-- title:
--   Tape coordinates for chain vertices and the step relation on a bounded tape with a terminal position
-- statement:
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$ be a set of state labels. For $n\in\mathbb N$, the chain vertex set $C_{m,n}$ is defined by $C_{m,0}=[m]$ and $C_{m,n+1}=[m]\sqcup C_{m,n}$; every vertex $c$ has a position $\mathrm{pos}(c)\in\{0,\dots,n\}$ and a label $\mathrm{lab}(c)\in[m]$, and $c\mapsto(\mathrm{lab}(c),\mathrm{pos}(c))$ is a bijection onto $[m]\times\{0,\dots,n\}$. For a word $w=a_0\cdots a_{n-1}$ (indexed from $0$) and an extra symbol $\ell$, the chain symbol at position $p\le n$ is $s_p=a_p$ for $p<n$ and $s_n=\ell$.
--
--   1. **Exit equivalence.** The map
--   $$C_{m,n}\sqcup[m]\ \to\ [m]\times\{0,1,\dots,n+1\},\qquad c\mapsto(\mathrm{lab}(c),\mathrm{pos}(c)),\qquad q\mapsto(q,n+1),$$
--   is a bijection: the additional copy of $[m]$ is a terminal column at position $n+1$, just beyond the last cell.
--   2. **Chain step relation.** Let move relations $M(a,\mu)$ on $[m]$ be given for every symbol $a$ and move code $\mu\in\{0,1,2\}$ (left, stay, right), and let $w$ have length $n$. On $[m]\times\{0,\dots,n+1\}$, a pair $(q,i)\to(r,j)$ is a step iff $i\le n$ and there is a move code $\mu$ with
--   $$(q,r)\in M(s_i,\mu)\qquad\text{and}\qquad j=i+\mu-1 .$$
--   No step leaves the terminal position $n+1$, and since $j$ must lie in $\{0,\dots,n+1\}$, there is no left move from position $0$.
--
--   Under the bijection of item 1, the internal edges of the chain network together with its right exits into the terminal column become exactly these local steps (proved separately). Consequently a run on the bounded tape from position $0$ to the terminal position $n+1$ corresponds to a forward traversal of the chain network, that is, to the forward component of a product of cell diagrams.
--
--   **Formalization Note** `ChainNode.exitEquiv m n : (ChainNode m n ⊕ Fin m) ≃ (Fin m × Fin (n + 2))` is noncomputable, being built from a proof of bijectivity. `chainStep moves w last` is a relation on `Fin m × Fin (w.length + 2)` with `moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)`; the condition $i\le n$ is expressed by the existence of a chain vertex at position $i$, and the displacement condition is stated in `ℤ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Convert the recursively joined cells and one terminal exit into tape coordinates. -/
noncomputable def ChainNode.exitEquiv (m n : ℕ) :
    (ChainNode m n ⊕ Fin m) ≃ (Fin m × Fin (n + 2)) :=
  Equiv.ofBijective (fun c => match c with
    | .inl v => (v.label, ⟨v.position, by have := v.position_le; omega⟩)
    | .inr q => (q, ⟨n + 1, by omega⟩)) (by
      constructor
      · intro c d h
        have hq := congrArg (fun p : Fin m × Fin (n + 2) => p.1) h
        have hp := congrArg (fun p : Fin m × Fin (n + 2) => p.2.val) h
        cases c with
        | inl c =>
          cases d with
          | inl d => exact congrArg Sum.inl (c.coordinates_injective d hp hq)
          | inr q => have := c.position_le; dsimp at hp; omega
        | inr q =>
          cases d with
          | inl d => have := d.position_le; dsimp at hp; omega
          | inr r => exact congrArg Sum.inr hq
      · rintro ⟨q, p⟩
        by_cases hp : p.val ≤ n
        · obtain ⟨c, hq, hc⟩ := ChainNode.coordinates_surjective q p.val hp
          exact ⟨Sum.inl c, Prod.ext hq (Fin.ext hc)⟩
        · exact ⟨Sum.inr q, Prod.ext rfl (Fin.ext (by change n + 1 = p.val; omega))⟩)

/-- Local moves on the bounded tape, with a final terminal position beyond the last cell. -/
def chainStep {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    SetRel (Fin m × Fin (w.length + 2)) (Fin m × Fin (w.length + 2)) :=
  {cd | ∃ c : ChainNode m w.length, cd.1.2.val = c.position ∧ ∃ move : Fin 3,
    (cd.1.1, cd.2.1) ∈ moves (chainSymbol w last c) move ∧
      (cd.2.2.val : ℤ) = (cd.1.2.val : ℤ) + (move.val : ℤ) - 1}

end TwoWayComplementation

end OAI


