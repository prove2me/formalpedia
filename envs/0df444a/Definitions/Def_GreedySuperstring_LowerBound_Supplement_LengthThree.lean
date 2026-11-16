-- Prove2me | Definitions.Def_GreedySuperstring_LowerBound_Supplement_LengthThree
-- name    : GreedySuperstring_LowerBound_Supplement_LengthThree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:36:36.821755+00:00
-- url     : https://prove2.me/theorems/c96b1f61-b696-4f37-bb18-240c18134246
-- title:
--   The graphs $G_2$, $G_1$, the greedy stages, $\nu$ and $\mathrm{contr}$ for strings of length three
-- statement:
--   Let $S$ be a nonempty set of words of length three. The directed multigraph $G_2$ has the length-two prefixes and suffixes of members of $S$ as vertices, and every $abc\in S$ is an edge from $ab$ to $bc$.
--
--   A greedy run on $S$ first merges strings with overlap two. The **overlap-two stage** ends at a set $B_2$ of current blocks reached by greedy steps of overlap two after which no two distinct current words overlap by two; $\kappa_2=|B_2|$. The **overlap-one stage** continues from $B_2$ with greedy steps of overlap one to a set $B_1$ in which no two distinct current words overlap; $\kappa_1=|B_1|$.
--
--   The histories of the blocks of $B_2$ form the trail cover $\mathcal T$ of $G_2$. A trail $P$ with edges $t_1,\dots,t_{m_P}$ starts at the length-two prefix of $t_1$ and ends at the length-two suffix of $t_{m_P}$; it is **closed** if these coincide and **open** otherwise. Define
--
--   $$\mathrm{contr}(P)=\begin{cases}2m_P-4 & P\text{ closed},\\ 2m_P & P\text{ open},\end{cases}$$
--
--   and let $\nu$ be the number of weak components of $G_2$ that contain no open trail of $\mathcal T$. The multigraph $G_1$ has symbols as vertices and one edge $e_P$ for each $P\in\mathcal T$, from the first to the last symbol of the current word of $P$.
--
--   These objects are the vocabulary of Lemmas 5.4–5.7, which together give Theorem 5.1.
--
--   **Formalization Note** Edges of $G_2$ are labelled by the input words and edges of $G_1$ by the blocks of $B_2$, so parallel edges and loops are kept. Vertices of $G_1$ are optional symbols (`head?`/`getLast?`), which are always defined on the nonempty current words. A trail lies in the weak component of its first vertex. The stage predicates assume no invariant of greedy; they record only the run, its overlap lengths and the stopping condition.
-- source:
--   Nikolai Chukhin, Rishikesh Gajjala, Juha Harviainen, Alexander S. Kulikov, Ivan Mihajlin, Hiroki Shibata, Alexander V. Smal, The Greedy Superstring Conjecture Is False, STOC 2027 submission #316 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/316.pdf, SHA-256 84e171350ae4e20ed6899c32b480753dae49f7b418819656dfedbcac0f60e8fa, §5 and §5.1, printed pp.23–27 = PDF pp.23–27

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_GreedyModel
import Definitions.Def_GreedySuperstring_LowerBound_Supplement_TrailCover

universe l3_u

namespace GreedySuperstring.LowerBound.Supplement

open GreedySuperstring.LowerBound

variable {α : Type l3_u} [DecidableEq α]

/-- `G₂` (§5, p.23): vertices are length-two words; every input word `abc` is an edge from
`ab` to `bc`. Edges are labelled by the input words themselves. -/
def G2 (S : Finset (List α)) : Multigraph (List α) (List α) :=
  ⟨S, fun s => s.take 2, fun s => s.drop 1⟩

/-- The overlap-two stage (§5, p.23) ends at `B₂`: a greedy run from the singleton blocks of
`S` all of whose recorded overlaps are `2`, after which no two distinct current words overlap
by two or more symbols. `κ₂ = |B₂|`. -/
def OverlapTwoStage (S : Finset (List α)) (B2 : Finset (Block α)) : Prop :=
  ∃ ls : List ℕ, GreedyRun (initialBlocks S) ls B2 ∧ (∀ l ∈ ls, l = 2) ∧
    ∀ a ∈ B2, ∀ b ∈ B2, a.word ≠ b.word → overlapLength a.word b.word < 2

/-- The overlap-one stage (§5, p.23) continues from `B₂` and ends at `B₁`: a greedy run all of
whose recorded overlaps are `1`, after which no two distinct current words overlap.
`κ₁ = |B₁|`. -/
def OverlapOneStage (B2 B1 : Finset (Block α)) : Prop :=
  ∃ ls : List ℕ, GreedyRun B2 ls B1 ∧ (∀ l ∈ ls, l = 1) ∧
    ∀ a ∈ B1, ∀ b ∈ B1, a.word ≠ b.word → overlapLength a.word b.word = 0

/-- First vertex `P₀` of the trail of `G₂` with edges `t₁, …, t_m` (the history of a block):
the length-two prefix of `t₁`. -/
def trailStart (P : List (List α)) : Option (List α) :=
  P.head?.map (fun t => t.take 2)

/-- Last vertex `P_m`: the length-two suffix of `t_m`. -/
def trailEnd (P : List (List α)) : Option (List α) :=
  P.getLast?.map (fun t => t.drop 1)

/-- The trails of `T` (§5.1, p.25) are the histories of the blocks of `B₂`; the open ones are
those whose first and last vertices differ. -/
def openTrails (B2 : Finset (Block α)) : Finset (Block α) :=
  B2.filter (fun b => trailStart b.history ≠ trailEnd b.history)

/-- `ν` (Lemma 5.4, p.25): the number of weak components of `G₂` that contain no open trail
of `T` (a trail lies in the component of its first vertex). -/
noncomputable def nu (S : Finset (List α)) (B2 : Finset (Block α)) : ℕ := by
  classical
  exact ((G2 S).weakComponents.filter (fun K =>
    ∀ b ∈ openTrails B2, ∀ v, trailStart b.history = some v →
      (G2 S).weakComponent v ≠ K)).card

/-- `contr(P)` (§5.1, p.27): `2m_P − 4` for a closed trail and `2m_P` for an open one, where
`m_P` is the number of edges of `P`. -/
def contr (P : List (List α)) : ℤ :=
  if trailStart P = trailEnd P then 2 * (P.length : ℤ) - 4 else 2 * (P.length : ℤ)

/-- `G₁` (§5.1, p.26): vertices are symbols; one edge `e_P` per trail `P ∈ T`, i.e. per block
of `B₂`, from the first to the last symbol of its current word. Parallel edges and loops are
kept. -/
def G1 (B2 : Finset (Block α)) : Multigraph (Option α) (Block α) :=
  ⟨B2, fun b => b.word.head?, fun b => b.word.getLast?⟩

end GreedySuperstring.LowerBound.Supplement


