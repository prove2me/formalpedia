-- Prove2me | Definitions.Def_UnionVolEst_countIn
-- name    : UnionVolEst_countIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:49.074215+00:00
-- url     : https://prove2.me/theorems/c5375039-c6b2-428e-8626-6e44bacdc799
-- title:
--   Number of points of a multiset in a set
-- statement:
--   For a finite multiset $X$ of points and a set $S$, $\mathrm{count}(X,S)$ is the number of elements of $X$, counted with multiplicity, that lie in $S$. The counts $X_j$, $Y_j$, $Z_j$ of Section 5 and $N_j$ of Lemma 26 are of this form.
--
--   **Formalization Note** The multiset is a `List`; the count does not depend on the order.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §5.2.3–5.2.5, pp.21–25; Lemma 26, p.41

import Mathlib

namespace UnionVolEst

open Classical in
/-- The number of elements of the multiset `X` (with multiplicity) lying in the set `S`, as in the
counts `X_j`, `Y_j`, `Z_j`, `Est_good`, `Est_bad` of §5.2.3–5.2.5 (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), printed pp.21–25, PDF
pp.23–27) and `N_j` of Lemma 26 (printed p.41, PDF p.43).

**Formalization Note** The multiset is a `List`; order is irrelevant to the count. -/
noncomputable def countIn {α : Type*} (X : List α) (S : Set α) : ℕ :=
  X.countP (fun x => decide (x ∈ S))

end UnionVolEst


