-- Prove2me | Definitions.Def_AssadiSemiStreaming_Greedy_Blueprint
-- name    : AssadiSemiStreaming_Greedy_Blueprint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:38:34.0604+00:00
-- url     : https://prove2.me/theorems/a64f6b4e-665a-4ed5-a4f4-6b3f5544a725
-- title:
--   Blueprints, global matching and ban constraints, and value
-- statement:
--   For integer parameters P,C, labels are P-tuples of C symbols, with distinct left and right copies. An optional type on each left-right pair defines its presence and, when present, its unique edge type. Properness requires P,C≥1, that all edges together form a matching, and the following global ban condition: a type-p edge (x,y) bans, for every common suffix z, simultaneous incidence of the two vertices obtained from the prefixes x_<p and y_<p followed by z. At least one of these vertices must have no incident edge of any type. The value is the number of edges divided by C^P; the framework factor is (2−2 value)/(2−value). Symbols and types use zero-based finite indices internally; a type index p corresponds to source type p+1. Splicing keeps indices strictly below p. The full label used to supply a suffix has an ignored prefix, hence supplies exactly all source suffixes.
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Definition 3.1, printed p. 4 / PDF 6; Theorem 2, printed p. 6 / PDF 8

import Mathlib

namespace AssadiSemiStreaming.Greedy

abbrev Label (P C : ℕ) := Fin P → Fin C

/-- An optional type assigns each edge exactly one type; absence means no edge. -/
structure Blueprint where
  P : ℕ
  C : ℕ
  edgeType : Label P C → Label P C → Option (Fin P)

noncomputable def Blueprint.edges (G : Blueprint) : Finset (Label G.P G.C × Label G.P G.C) := by
  classical
  exact Finset.univ.filter (fun e => (G.edgeType e.1 e.2).isSome)

def Blueprint.Matching (G : Blueprint) : Prop :=
  ∀ e ∈ G.edges, ∀ f ∈ G.edges, (e.1 = f.1 ∨ e.2 = f.2) → e = f

/-- Replace all coordinates from p onward by a common suffix. The unused
prefix of z is immaterial, so quantifying over full labels is exactly suffix quantification. -/
def splice {P C : ℕ} (p : Fin P) (x z : Label P C) : Label P C :=
  fun i => if i.val < p.val then x i else z i

def Blueprint.Ban (G : Blueprint) : Prop :=
  ∀ x y p, G.edgeType x y = some p → ∀ z : Label G.P G.C,
    (∀ y', G.edgeType (splice p x z) y' = none) ∨
    (∀ x', G.edgeType x' (splice p y z) = none)

def Blueprint.Proper (G : Blueprint) : Prop :=
  1 ≤ G.P ∧ 1 ≤ G.C ∧ G.Matching ∧ G.Ban

noncomputable def Blueprint.value (G : Blueprint) : ℝ :=
  (G.edges.card : ℝ) / (G.C : ℝ) ^ G.P

noncomputable def Blueprint.factor (G : Blueprint) : ℝ :=
  (2 - 2 * G.value) / (2 - G.value)

end AssadiSemiStreaming.Greedy


