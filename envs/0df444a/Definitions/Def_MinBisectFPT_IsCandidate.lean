-- Prove2me | Definitions.Def_MinBisectFPT_IsCandidate
-- name    : MinBisectFPT_IsCandidate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:28.040335+00:00
-- url     : https://prove2.me/theorems/9a3c6615-16bf-4ba3-9503-ad2480107169
-- title:
--   Candidates
-- statement:
--   A **candidate** of $t$ is a set of the form $Y\cap\beta$, where $Y\subseteq\gamma(t)$, $|Y\cap\beta|\le q$, $|\delta(Y)|\le k$ and $H[Y]$ is connected. The definition takes $H$ and the vertex set $V(H)$ (for $H=G_t$, $V(H)=\gamma(t)$) as parameters.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), §4.2, p.14

import Mathlib
import Definitions.Def_MinBisectFPT_cutSize

open scoped Classical

namespace MinBisectFPT

/-- **Candidates.** Anand, Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC 2027 submission (manuscript sha256 8db80a52…), §4.2, p.14: "a candidate of t is a set of the form Y ∩ β, where
Y ⊆ γ(t), |Y ∩ β| ≤ q, |δ(Y)| ≤ k, and H[Y] is connected", with `VH` for `γ(t)`. -/
def IsCandidate {n : ℕ} (H : SimpleGraph (Fin n)) (VH β : Finset (Fin n)) (q k : ℕ)
    (U : Finset (Fin n)) : Prop :=
  ∃ Y, Y ⊆ VH ∧ Y ∩ β = U ∧ (Y ∩ β).card ≤ q ∧ cutSize H Y ≤ k ∧
    (H.induce (Y : Set (Fin n))).Connected

end MinBisectFPT


