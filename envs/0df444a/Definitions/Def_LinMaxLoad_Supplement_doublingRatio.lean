-- Prove2me | Definitions.Def_LinMaxLoad_Supplement_doublingRatio
-- name    : LinMaxLoad_Supplement_doublingRatio
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:20:57.436415+00:00
-- url     : https://prove2.me/theorems/dec1283f-3f39-4c7d-9325-ed313bde3913
-- title:
--   Doubling ratio $\sigma(S) = |S+S|/|S|$
-- statement:
--   For a finite subset $S$ of an abelian group $G$, the **doubling ratio** (usually called the doubling constant) is
--
--   $$
--   \sigma(S) := \frac{|S+S|}{|S|}, \qquad S+S = \{a+b : a, b \in S\}.
--   $$
--
--   It satisfies $\sigma(S) \ge 1$ for nonempty $S$, with equality exactly for cosets of finite subgroups; small doubling is the classical notion of additive structure. In the paper it is the first of the measures of additivity compared with the expected linear max load $m(S)$.
--
--   **Formalization Note** The value is a real number. For $S = \emptyset$ Lean's division by zero gives $\sigma(\emptyset) = 0$; the paper only applies $\sigma$ to nonempty sets.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Definition 2, item 1, p.3

import Mathlib

namespace LinMaxLoad.Supplement

open Pointwise in
/-- **Doubling ratio** `σ(S) := |S + S| / |S|` (Definition 2, item 1, p.3, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)),
where `S + S = {a + b : a, b ∈ S}` is the sumset of the finite set `S`.

**Formalization Note** The ratio is a real number; for `S = ∅` Lean's division gives `0`
(the paper only uses nonempty `S`). -/
noncomputable def doublingRatio {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G) : ℝ :=
  ((S + S).card : ℝ) / (S.card : ℝ)

end LinMaxLoad.Supplement


