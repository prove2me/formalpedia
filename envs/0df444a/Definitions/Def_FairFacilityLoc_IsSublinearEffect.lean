-- Prove2me | Definitions.Def_FairFacilityLoc_IsSublinearEffect
-- name    : FairFacilityLoc_IsSublinearEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:17.772773+00:00
-- url     : https://prove2.me/theorems/8b717c4c-52be-4d5b-baf6-c86b194577a6
-- title:
--   Definition 2.2: sublinear group effect
-- statement:
--   A group effect $E$ of a group $G$ is **sublinear** if it is subadditive and positively homogeneous:
--   $$E(u+v)\le E(u)+E(v),\qquad E(tu)=tE(u)\qquad(u,v\in\mathbb R^G_{\ge0},\ t\ge0).$$
--
--   The case $t=0$ is included, so $E(0)=0$. This class contains the total, average and largest distance of a group, and $\ell_p$ norms. All results of the mission are about this class.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Definition 2.2, p.14 (PDF p.16)

import Mathlib

open scoped NNReal

namespace FairFacilityLoc

/-- **Sublinear group effect** (Yan, Zhou, manuscript, sha256 642a1268…, Definition 2.2, p.14,
PDF p.16): `E` is subadditive and positively homogeneous on `ℝ^ι_{≥0}`, the latter for every `t ≥ 0`, so
`t = 0` is included and `E 0 = 0`.

**Formalization Note.** Stated apart from `IsGroupEffect`, as printed ("a group effect `E` … is sublinear
if"). Neither continuity nor convexity is assumed. `t : ℝ≥0` is the printed `t ≥ 0`. -/
structure IsSublinearEffect {ι : Type*} (E : (ι → ℝ≥0) → ℝ≥0) : Prop where
  /-- Subadditivity. -/
  subadditive : ∀ u v : ι → ℝ≥0, E (u + v) ≤ E u + E v
  /-- Positive homogeneity, for every `t ≥ 0`. -/
  homogeneous : ∀ (t : ℝ≥0) (u : ι → ℝ≥0), E (t • u) = t * E u

end FairFacilityLoc


