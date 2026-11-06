-- Prove2me | Definitions.Def_DetAuctions_phi
-- name    : DetAuctions_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:06.288136+00:00
-- url     : https://prove2.me/theorems/c02f99be-ca0b-447c-97a8-debe7644286d
-- title:
--   $\phi(x)=x-1+e^{-x}$
-- statement:
--   The function
--   $$\phi(x)=x-1+e^{-x},$$
--   of Eq. (26). For $x\ge0$ it is nonnegative, nondecreasing and convex (all three are asserted in Lemma 4.4). Applied to the sum of capped tails, it gives the paper's new form of the master inequality (27).
--
--   **Formalization Note** Defined on all of $\mathbb R$; every statement uses it at nonnegative arguments.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Lemma 4.4, Eq. (26), p.18 (pdf p.20)

import Mathlib

namespace DetAuctions

/-- The function `φ(x) = x − 1 + e^{−x}` of Eq. (26).

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Lemma 4.4, Eq. (26), p.18: "ϕ(x) = x − 1 + e^{−x}, for x ≥ 0 which is
nonnegative, monotone, and convex."

**Formalization Note** Defined on all of `ℝ`; every statement uses it only at arguments `≥ 0`. -/
noncomputable def phi (x : ℝ) : ℝ :=
  x - 1 + Real.exp (-x)

end DetAuctions


