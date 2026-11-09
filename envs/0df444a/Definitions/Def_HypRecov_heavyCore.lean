-- Prove2me | Definitions.Def_HypRecov_heavyCore
-- name    : HypRecov_heavyCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:32.339876+00:00
-- url     : https://prove2.me/theorems/965e03e0-cda0-4d92-901f-2e03ba21711b
-- title:
--   The heavy core $Z$ and the crossing frontier $T$ of a residual boundary
-- statement:
--   For a residual hypergraph $J$, a cut $S$ and $F=\delta_J(S)$, write $d_F(v)=|\{e\in F:v\in e\}|$. The **heavy core** is
--   $$Z=\{v:\ d_F(v)\ge M\},$$
--   and the **crossing frontier** on a shore $A$ (that is, $A=S$ or $A=V\setminus S$) is
--   $$T=\{v\in A:\ v\text{ belongs to some edge of }F\}.$$
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 5.1, p.10 (PDF p.11); Theorem 5.3, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_HypRecov_crisp

namespace HypRecov

open Classical in
/-- **The heavy core `Z` of a residual boundary.** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 5.1, p.10
(PDF p.11): "put F = δ_J(S), t = |F| ≤ K, d_F(v) = |{e ∈ F : v ∈ e}|, Z = {v : d_F(v) ≥ M}."

`heavyCore J S M` is the set of vertices lying in at least `M` edges of `δ_J(S)`. -/
noncomputable def heavyCore {n : ℕ} (J : Finset (Finset (Fin n))) (S : Finset (Fin n)) (M : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun v => M ≤ ((bdry J S).filter (fun e => v ∈ e)).card)

open Classical in
/-- **The crossing frontier on a shore.** Ibid., Theorem 5.3, p.11 (PDF p.12):
"T = {v ∈ A : v belongs to some edge of F}", for `F = δ_J(S)` and a shore `A` of `S`. -/
noncomputable def frontier {n : ℕ} (J : Finset (Finset (Fin n))) (S A : Finset (Fin n)) :
    Finset (Fin n) :=
  A.filter (fun v => ∃ e ∈ bdry J S, v ∈ e)

end HypRecov


