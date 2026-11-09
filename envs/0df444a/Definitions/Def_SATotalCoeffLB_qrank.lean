-- Prove2me | Definitions.Def_SATotalCoeffLB_qrank
-- name    : SATotalCoeffLB_qrank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:45.88712+00:00
-- url     : https://prove2.me/theorems/e4c7d210-eb93-4532-becb-760ca3e2c36d
-- title:
--   Rank of a quadratic form
-- statement:
--   The **rank** of $a \in Q_n$, written $\operatorname{rank}(a)$, is the rank over $\mathbb F_2$ of its polar matrix $B_a$. A single form $\bar x_i \bar x_j$ has rank two.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Definition 3, p.51

import Mathlib
import Definitions.Def_SATotalCoeffLB_polar

namespace SATotalCoeffLB

/-- **The rank of a quadratic form** `rank(a)` (Definition 3, p.51, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)): the rank over `F₂` of
its polar matrix `B_a`. A single form `x̄_i x̄_j` has rank two. -/
noncomputable def qrank {n : ℕ} (a : QForm n) : ℕ := (polar a).rank

end SATotalCoeffLB


