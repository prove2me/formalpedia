-- Prove2me | Definitions.Def_BrouwerLaplacian_splitGraphOf
-- name    : BrouwerLaplacian_splitGraphOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:21.172809+00:00
-- url     : https://prove2.me/theorems/8a90f15f-f8bf-474f-989b-f6bc68eda276
-- title:
--   The split graph $G_K$ of identity (5.3)
-- statement:
--   Let $A$ be a real $n\times n$ matrix and $K\subseteq[n]$. The graph $G_K$ on $[n]$ is the split graph obtained by
--
--   1. making $K$ a clique,
--   2. making $K^{\mathrm c}$ an independent set, and
--   3. joining $i\in K$ to $j\notin K$ exactly when $A_{ij}\ge 0$.
--
--   With $A=M$ (the matrix of a projection) and $K=\{1,\dots,r\}$ this is the graph $G_r$ of the paper's identity (5.3), which links the vector $v=CM\mathbf 1$ to the centered Laplacian $L_{G_r}-rC$.
--
--   **Formalization Note** For a cross pair the entry read is $A_{ij}$ with $i$ the endpoint in $K$, which makes adjacency symmetric for every $A$; for the symmetric matrix $M$ either orientation gives the same graph. Vertices are $\mathrm{Fin}\,n$, and $K$ is any vertex set (the paper's prefix is one instance).
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, §5, proof of Lemma 5.5, p.7

import Mathlib

namespace BrouwerLaplacian

/-- **The split graph `G_K` of identity (5.3).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, §5, proof of
Lemma 5.5, p.7: "let Gᵣ be the split graph on [n] obtained by making {1, 2, . . . , r} a clique,
{r + 1, . . . , n} an independent set, and adding an edge across the cut wherever Mᵢⱼ ≥ 0."

For a real `n × n` matrix `A` and a vertex set `K`, `splitGraphOf A K` is the graph on `Fin n`
in which two distinct vertices `i ≠ j` are adjacent iff both lie in `K`, or one of them, say
`i`, lies in `K`, the other `j` does not, and `A i j ≥ 0`. Pairs outside `K` are never
adjacent.

**Formalization Note.** The paper's clique is the prefix `{1, …, r}`; here it is any vertex set
`K` (the prefix is `K = {i | i < r}` in 0-based indices). For a cross pair the entry read is
`A i j` with `i` the endpoint in `K`; for the symmetric matrix `M` of the paper this is `Mᵢⱼ`
either way, and the convention makes the adjacency symmetric for every `A`. -/
def splitGraphOf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (K : Finset (Fin n)) :
    SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((i ∈ K ∧ j ∈ K) ∨ (i ∈ K ∧ j ∉ K ∧ 0 ≤ A i j) ∨
    (j ∈ K ∧ i ∉ K ∧ 0 ≤ A j i))
  symm := ⟨fun i j h => by
    obtain ⟨hne, h⟩ := h
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨fun i h => h.1 rfl⟩

noncomputable instance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (K : Finset (Fin n)) :
    DecidableRel (splitGraphOf A K).Adj :=
  Classical.decRel _

end BrouwerLaplacian


