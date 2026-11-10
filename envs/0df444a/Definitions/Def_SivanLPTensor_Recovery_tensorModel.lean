-- Prove2me | Definitions.Def_SivanLPTensor_Recovery_tensorModel
-- name    : SivanLPTensor_Recovery_tensorModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:30:23.732411+00:00
-- url     : https://prove2.me/theorems/3146d634-6f5a-4502-af2e-ff63edf05591
-- title:
--   Lovitz–Petrov condition and direct-sum factor geometry
-- statement:
--   For factor vectors $a_i^{(j)}$, let $A^{(j)}[S]$ contain the columns indexed by $S$. The LP condition is
--   $$\sum_{j=1}^m\operatorname{rank}A^{(j)}[S]\ge 2|S|+m-1\qquad(|S|\ge2).$$
--   Rank is the dimension of the span of precisely those columns. In the direct sum $X=\bigoplus_j\mathbb R^{n_j}$, each factor is embedded in its own block. The matrix $F_i$ has those $m$ embedded factors as its columns, and $\mathcal F_i$ is their span. This layer adds no full-column-rank, positivity, generic-factor, or normalization hypothesis. It builds on the separate CP interface.
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), §2, printed pp. 3–4 / PDF pp. 5–6, (1), (2), (LP), (R)

import Definitions.Def_SivanLPTensor_Recovery_cpModel

noncomputable section

namespace SivanLPTensor.Recovery
open scoped BigOperators

def columnRank {m r : ℕ} {n : Fin m → ℕ}
    (a : Factors n r) (j : Fin m) (S : Finset (Fin r)) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (a j '' (S : Set (Fin r))))

/-- (LP); no individual mode is required to have full column rank. -/
def LP {m r : ℕ} {n : Fin m → ℕ} (a : Factors n r) : Prop :=
  ∀ S : Finset (Fin r), 2 ≤ S.card →
    2 * S.card + m - 1 ≤ ∑ j, columnRank a j S

abbrev BlockIndex {m : ℕ} (n : Fin m → ℕ) := (j : Fin m) × Fin (n j)
abbrev Ambient {m : ℕ} (n : Fin m → ℕ) := BlockIndex n → ℝ

def embed {m : ℕ} {n : Fin m → ℕ} (j : Fin m)
    (v : Fin (n j) → ℝ) : Ambient n :=
  fun x => if h : x.1 = j then v (h ▸ x.2) else 0

def factorFrame {m r : ℕ} {n : Fin m → ℕ} (a : Factors n r)
    (i : Fin r) : Matrix (BlockIndex n) (Fin m) ℝ :=
  fun x j => embed j (a j i) x

def factorSpace {m r : ℕ} {n : Fin m → ℕ}
    (a : Factors n r) (i : Fin r) : Submodule ℝ (Ambient n) :=
  Submodule.span ℝ (Set.range (fun j => embed j (a j i)))


end SivanLPTensor.Recovery


