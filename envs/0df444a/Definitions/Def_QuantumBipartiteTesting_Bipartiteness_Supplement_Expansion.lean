-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Expansion
-- name    : QuantumBipartiteTesting_Bipartiteness_Supplement_Expansion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:10:59.349415+00:00
-- url     : https://prove2.me/theorems/2bc683cd-e95b-42ce-9237-f69ee27ea928
-- title:
--   Vertex expansion, edit distance, and quantum testers
-- statement:
--   For a simple graph $G$ on $n$ labeled vertices, the external boundary $\partial_G U$ contains vertices outside $U$ adjacent to $U$. Vertex expansion means $|\partial_G U|\ge\alpha|U|$ for every $2|U|\le n$, including the empty set. The all-cuts edge expansion predicate counts crossing edges once.
--
--   Distance to $\alpha$-expansion is the infimum of the numbers of edge additions and deletions over actual simple target graphs on the same vertices. It is an extended nonnegative real number, equal to $+\infty$ if no target exists. Farness compares this distance with $\varepsilon dn$. The two-threshold tester must accept every $\alpha$-expander and reject every graph $\varepsilon$-far from $\alpha'$-expansion with probability at least $2/3$, for every packed neighbor ordering. It uses the published complex quantum circuits and XOR response encodings, rather than a supplied acceptance function.
--
--   The rate is $n^{1/3}/(\ln n)^{4/3}$. This layer gives the expansion-specific interface without changing the published bipartiteness distance.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Definitions 2.2–2.5, printed = PDF p.9; quantum model p.8; Theorem 4.1 pp.21,27

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Query

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Definition 2.5: the external vertex boundary, with no multiplicities. -/
def Boundary {n : ℕ} (G : Finset (Edge n)) (U : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter fun v => v ∉ U ∧ ∃ u ∈ U, v ∈ Neighbors G u

def VertexExpander {n : ℕ} (α : ℝ) (G : Finset (Edge n)) : Prop :=
  ∀ U : Finset (Fin n), 2 * U.card ≤ n → α * U.card ≤ (Boundary G U).card

def Crossing {n : ℕ} (G : Finset (Edge n)) (U : Finset (Fin n)) : Finset (Edge n) :=
  G.filter fun e => (e.1 ∈ U ∧ e.2 ∉ U) ∨ (e.2 ∈ U ∧ e.1 ∉ U)

def EdgeExpander {n : ℕ} (ρ : ℝ) (G : Finset (Edge n)) : Prop :=
  ∀ U : Finset (Fin n), ρ * min (U.card : ℝ) (n - (U.card : ℝ)) ≤ (Crossing G U).card

/-- The infimum is +∞ when there is no same-vertex-set expanding target. -/
def ExpansionDistance {n : ℕ} (α : ℝ) (G : Finset (Edge n)) : ENNReal :=
  sInf {x | ∃ T : Finset (Edge n), IsGraph T ∧ VertexExpander α T ∧
    x = (((G \ T).card + (T \ G).card : ℕ) : ENNReal)}

def ExpansionFar {n : ℕ} (d : ℕ) (ε α : ℝ) (G : Finset (Edge n)) : Prop :=
  ENNReal.ofReal (ε * d * n) ≤ ExpansionDistance α G

/-- Correctness on every promised graph and every packed adjacency representation. -/
def ExpansionTester {n d k w q : ℕ} (ε α α' : ℝ) (E : Encoding (Fin n) k)
    (A : Algorithm (Address n d) k w q)
    (out : (Address n d × Bits k) × Fin w → Bool) : Prop :=
  ∀ G : Finset (Edge n), IsGraph G → DegreeBound d G →
    ∀ O : Fin n × Fin d → Option (Fin n), Represents G O →
      (VertexExpander α G → 2/3 ≤ Accept E A out (LiftOracle O)) ∧
      (ExpansionFar d ε α' G → Accept E A out (LiftOracle O) ≤ 1/3)

def ExpansionScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1/3 : ℝ) / (Real.log n) ^ (4/3 : ℝ)

end
end QuantumBipartiteTesting.Bipartiteness.Supplement


