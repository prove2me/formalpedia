-- Prove2me | Definitions.Def_FranklKupavskii2022_EMC_resShadow
-- name    : FranklKupavskii2022_EMC_resShadow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:14:10.502287+00:00
-- url     : https://prove2.me/theorems/be91bb81-5c90-41d5-9548-f638cd96e381
-- title:
--   Index $i_F$, tail $T(F)$, layers $\mathcal G_i$ and the restricted shadow $\partial_{\mathrm{res}}$
-- statement:
--   Fix $s\ge1$ and $k\ge2$. For a $k$-set $F$ let $i_F$ be the largest $i$ with $1\le i<k$ such that
--
--   $$
--   |F\cap[i(s+1)-1]|\ge i+1 .
--   $$
--
--   The **tail** of $F$ is $T(F)=F\setminus[i_F(s+1)-1]$. For a family $\mathcal G$ of $k$-sets, the **layer** $\mathcal G_i$ is the subfamily of all $F\in\mathcal G$ with $i_F=i$, and the **restricted shadow** is
--
--   $$
--   \partial_{\mathrm{res}}\mathcal G=\{F'\in\partial\mathcal G : \exists F\in\mathcal G,\ T(F)\subseteq F'\subseteq F\}.
--   $$
--
--   For an initial family $\mathcal G$ with $\nu(\partial\mathcal G)\le s$, every member has some admissible $i$, so $\mathcal G=\bigsqcup_{i=1}^{k-1}\mathcal G_i$; the restricted shadows of the layers are the objects of Lemma 8.
--
--   **Formalization Note** One module bundles the four closely tied definitions `iF`, `tail`, `layer`, `resShadow`. If no admissible $i$ exists, $i_F$ is set to $0$ (then $T(F)=F$); this does not occur for the families the paper considers. For $i\ge1$ the index $i(s+1)-1$ involves no truncated subtraction.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Sect. 2.1, p. 4 (i_F, T(F), G_i, restricted shadow)

import Mathlib

open FinsetFamily

namespace FranklKupavskii2022.EMC

/-- The index `i_F` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1, p. 4): "For a set F, let us
denote i_F the largest i for which (13) holds", where (13) is
`|F ∩ [i(s + 1) − 1]| ≥ i + 1` with `1 ≤ i < k`.

**Formalization Note.** `[i(s+1) − 1] = Finset.Icc 1 (i * (s + 1) - 1)`; for `i ≥ 1` the natural
subtraction is exact. If no `i` with `1 ≤ i < k` satisfies (13) the value is `0` (the `sup` of the
empty set); Corollary 7 of the paper shows this does not happen for members of an initial
`k`-uniform family `G` with `ν(∂G) ≤ s` and `k ≥ 2`. -/
def iF (s k : ℕ) (F : Finset ℕ) : ℕ :=
  ((Finset.Ico 1 k).filter (fun i => i + 1 ≤ (F ∩ Finset.Icc 1 (i * (s + 1) - 1)).card)).sup id

/-- The tail `T(F) := F \ [i_F(s + 1) − 1]` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1,
p. 4). It depends only on `F` (and on the parameters `s`, `k`). -/
def tail (s k : ℕ) (F : Finset ℕ) : Finset ℕ :=
  F \ Finset.Icc 1 (iF s k F * (s + 1) - 1)

/-- The layer `G_i` (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1, p. 4): "Let us split
G := ⊔_{i=1}^{k−1} G_i, where G_i is the subfamily of all sets F satisfying i_F = i." -/
def layer (s k : ℕ) (G : Finset (Finset ℕ)) (i : ℕ) : Finset (Finset ℕ) :=
  G.filter (fun F => iF s k F = i)

/-- The restricted shadow (Frankl–Kupavskii, arXiv:1806.08855v3, Sect. 2.1, p. 4):
`∂_res G := {F′ ∈ ∂G : ∃ F ∈ G s.t. T(F) ⊂ F′ ⊂ F}` (the paper's `⊂` is non-strict inclusion).
The paper's `∂_res G_i` is `resShadow s k (layer s k G i)`. -/
def resShadow (s k : ℕ) (G : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (∂ G).filter (fun F' => ∃ F ∈ G, tail s k F ⊆ F' ∧ F' ⊆ F)

end FranklKupavskii2022.EMC


