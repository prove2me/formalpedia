-- Prove2me | Definitions.Def_FairFacilityLoc_cutOutput
-- name    : FairFacilityLoc_cutOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:49.235131+00:00
-- url     : https://prove2.me/theorems/f1e817fe-7025-4be8-bacb-9ea9cf062ce3
-- title:
--   The cut rule: the smallest report with a winning left set
-- statement:
--   For a profile $x$, a coordinate $r$ and $t\in\mathbb R$, the **left set** of the cut is $L_r(t;x)=\{i:x_{ir}\le t\}$. Given winning sets fixed per coordinate, the cut rule returns in each coordinate $r$ the smallest report $t\in\{x_{1r},\dots,x_{nr}\}$ whose left set is winning.
--
--   **Formalization Note** The output is written with a real infimum, which returns $0$ on an empty set, so every statement about a cut-rule mechanism carries an `IsLeast` clause saying that the minimum exists and is the output. Winning sets have no profile argument.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma 3.2, p.17 (PDF p.19); §2.2, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E

namespace FairFacilityLoc

/-- The **left set** `L_r(t; x) = {i : x_{ir} ≤ t}` of the cut at `t` in coordinate `r` (§2.2, p.16, PDF
p.18). -/
noncomputable def leftSet {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (r : Fin d) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i r ≤ t

/-- The **candidate cuts** of coordinate `r`: the reports `t ∈ {x_{1r}, …, x_{nr}}` whose left set is
winning (§2.2, p.16, PDF p.18; Lemma 3.2, p.17, PDF p.19). -/
def cutCandidates {n d : ℕ} (Win : Fin d → Finset (Fin n) → Prop) (x : Fin n → GeoSemialgCSP.E d) (r : Fin d) :
    Set ℝ :=
  {t | (∃ i, x i r = t) ∧ Win r (leftSet x r t)}

/-- **The cut rule** (Yan, Zhou, manuscript, sha256 642a1268…, Lemma 3.2, p.17, PDF p.19, and (2.4), p.16,
PDF p.18): in each coordinate `r`, the smallest report whose left set is winning.

**Formalization Note.** `Win` has no profile argument, which is the printed "not on the reports". `sInf`
is the printed `min` only when the candidate set is nonempty and finite: on an empty one it returns `0`.
Every statement about a cut-rule mechanism therefore carries the clause
`IsLeast (cutCandidates Win x r) (cutOutput Win x r)`. -/
noncomputable def cutOutput {n d : ℕ} (Win : Fin d → Finset (Fin n) → Prop) (x : Fin n → GeoSemialgCSP.E d) : GeoSemialgCSP.E d :=
  WithLp.toLp 2 fun r => sInf (cutCandidates Win x r)

end FairFacilityLoc


