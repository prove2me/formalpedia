-- Prove2me | Definitions.Def_HighDimProb_RandomMatrices_coveringNumber
-- name    : HighDimProb_RandomMatrices_coveringNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:19:47.829488+00:00
-- url     : https://prove2.me/theorems/b949c649-cf59-40ed-b142-9c25de690b5f
-- title:
--   Covering number of a subset of a metric space
-- statement:
--   This is **Definition 4.2.2** (Covering numbers): the smallest number of points needed to
--   ε-cover a set, the quantity Corollary 4.2.13 computes for the Euclidean ball and sphere.
--
--   Let $(T, d)$ be a metric space, $K \subseteq T$, $\varepsilon > 0$. The **covering number**
--   $N(K, d, \varepsilon)$ is the smallest possible cardinality of an ε-net of $K$ (companion
--   definition `IsEpsNet`).
--
--   **Formalization Note** Restricted to *finite* ε-nets (`Finset`), since that is the notion
--   the chapter actually computes with (every covering number bound in this mission is realized
--   by an explicit finite net). The value is `sInf` of the set of cardinalities of finite ε-nets
--   of $K$; if $K$ admits no finite ε-net, this set is empty and `sInf` returns Mathlib's junk
--   value $0$ — a convention that plays no role here, since `coveringNumber` is only ever
--   applied to the (compact, hence totally bounded) unit ball and unit sphere.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Definition 4.2.2, p. 81 (PDF p. 89)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_IsEpsNet

namespace HighDimProb.RandomMatrices

/-- **Definition 4.2.2** (Covering numbers), Vershynin, *High-Dimensional Probability* (2018),
p. 81. The covering number `N(K, d, ε)` is the smallest possible cardinality of an `ε`-net of
`K`, restricted here to finite nets (a `Finset`), which is the notion actually used in this
chapter (every covering number appealed to in Corollary 4.2.13 / Theorem 4.4.5 is realized by a
finite net). If no finite `ε`-net of `K` exists, `sInf` of the empty set of cardinalities
defaults to Mathlib's junk value `0`; this convention plays no role in this mission's theorems,
which only ever apply `coveringNumber` to compact (hence totally bounded) sets. -/
noncomputable def coveringNumber {T : Type*} [PseudoMetricSpace T] (K : Set T) (ε : ℝ) : ℕ :=
  sInf {c : ℕ | ∃ net : Finset T, net.card = c ∧ IsEpsNet K (↑net : Set T) ε}

end HighDimProb.RandomMatrices


