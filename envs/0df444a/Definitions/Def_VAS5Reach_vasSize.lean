-- Prove2me | Definitions.Def_VAS5Reach_vasSize
-- name    : VAS5Reach_vasSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:17.7215+00:00
-- url     : https://prove2.me/theorems/c0c12916-bb14-49a6-87f9-6b60f5e3b390
-- title:
--   Unary size $\mathrm{SIZE}(V,s,t)$ of a VAS reachability instance
-- statement:
--   For a $d$-VAS $V$ with transition set $T$ let $\|T\| := \max_{a \in T} \|a\|$ (with $\max \emptyset := 0$). The **unary-encoded size** of $V$ and of a reachability instance $(V, s, t)$ are
--   $$
--   \mathrm{SIZE}(V) := |Q| + d \cdot |T| \cdot (\|T\| + 1) + 2, \qquad \mathrm{SIZE}(V, s, t) := \mathrm{SIZE}(V) + d \cdot (\|s\| + \|t\| + 1),
--   $$
--   where a VAS has a single state, $|Q| = 1$. The helpers are `normT` ($\|T\|$) and `vasSizeV` ($\mathrm{SIZE}(V)$).
--
--   The goal theorem bounds the length of a shortest run by a power of $\mathrm{SIZE}(V, s, t)$.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 'Size and Reachability Problems', p.14 (PDF p.16); max ∅ := 0, p.13

import Mathlib
import Definitions.Def_VAS5Reach_supNorm

namespace VAS5Reach

/-- `∥T∥ := max_{a∈T} ∥a∥`, the largest max norm of a transition vector, with `max ∅ := 0`. -/
def normT {ι : Type} [Fintype ι] (T : Finset (ι → ℤ)) : ℕ :=
  T.sup supNorm

/-- The unary-encoded size of a `d`-VAS `V` with transition set `T`:
`SIZE(V) = |Q| + d·|T|·(∥T∥ + 1) + 2` with `|Q| = 1` (a VAS has a single state). -/
def vasSizeV {ι : Type} [Fintype ι] (T : Finset (ι → ℤ)) : ℕ :=
  1 + Fintype.card ι * T.card * (normT T + 1) + 2

/-- The unary size of a VAS reachability instance `(V, s, t)`:
`SIZE(V, s, t) = SIZE(V) + d·(∥s∥ + ∥t∥ + 1)` with `SIZE(V) = |Q| + d·|T|·(∥T∥ + 1) + 2`,
`|Q| = 1` and `d = Fintype.card ι`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 "Size and Reachability
Problems", printed p. 14 (PDF p. 16): "SIZE(V) := |Q| + d · |T| · (∥T∥ + 1) + 2, where
∥T∥ := max_{(p,a,q)∈T} ∥a∥ […] SIZE(V, s, t) := SIZE(V) + d · (∥s∥ + ∥t∥ + 1)"; and p. 13: "∥X∥ :=
max_{x∈X} ∥x∥ with the understanding that max ∅ := 0".

**Formalization Note** For a VAS the state set is a singleton, so `|Q| = 1`; norms are max norms in
`ℕ`. -/
def vasSize {ι : Type} [Fintype ι] (T : Finset (ι → ℤ)) (s t : ι → ℕ) : ℕ :=
  vasSizeV T + Fintype.card ι * (supNormN s + supNormN t + 1)

end VAS5Reach


