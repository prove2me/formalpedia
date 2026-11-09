-- Prove2me | Definitions.Def_LinMaxLoad_cosetSum
-- name    : LinMaxLoad_cosetSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:04.292521+00:00
-- url     : https://prove2.me/theorems/02b5bf9e-26dc-4d8d-9c3c-dba26e80174f
-- title:
--   Coset union $V + T$
-- statement:
--   Let $V$ be a subspace of a finite vector space $E$ and $T \subseteq E$ a finite set. The **coset union**
--
--   $$
--   V + T = \{ v + t : v \in V,\ t \in T \} = \bigcup_{t \in T} (V + t)
--   $$
--
--   is the union of the cosets of $V$ through the points of $T$. Theorem 17 covers a set $S$ by such unions $V_i + T_i$, and Lemma 7 compares the max load of $V + T$ with that of the set of cosets $T' = \{t + V : t \in T\}$ in $E/V$.
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Lemma 7, p.21; Theorem 17, p.23

import Mathlib

namespace LinMaxLoad

open Pointwise in
/-- The **coset union** `V + T = {v + t : v ∈ V, t ∈ T}` of a subspace `V` and a finite set `T`
in a finite module `E` (Theorem 17, p.23, Lemma 7, p.21, of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)),
as a finite set: the union of the cosets `V + t`, `t ∈ T`. -/
noncomputable def cosetSum {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
    (V : Submodule K E) (T : Finset E) : Finset E :=
  (Set.toFinite ((V : Set E) + (T : Set E))).toFinset

end LinMaxLoad


