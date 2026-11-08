-- Prove2me | Definitions.Def_FairFacilityLoc_IsGroupEffect
-- name    : FairFacilityLoc_IsGroupEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:14.942189+00:00
-- url     : https://prove2.me/theorems/0423be2a-f01d-4517-937f-01d96636215f
-- title:
--   Definition 2.1: group effect
-- statement:
--   A **group effect** of a group $G$ is a function $E:\mathbb R^G_{\ge0}\to\mathbb R_{\ge0}$ that is not identically zero and satisfies:
--
--   1. monotonicity: $E(u)\le E(v)$ whenever $u_i\le v_i$ for every $i\in G$;
--   2. symmetry: $E((u_{\pi(i)})_{i\in G})=E(u)$ for every $u$ and every bijection $\pi:G\to G$.
--
--   It turns the distances of a group's members to the facility into one number. Excluding the zero function excludes a group that does not care about the location.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Definition 2.1, p.14 (PDF p.16)

import Mathlib

open scoped NNReal

namespace FairFacilityLoc

/-- **Group effect** (Yan, Zhou, *Fair and Strategyproof Facility Location in Euclidean Space*,
manuscript, sha256 642a1268…, Definition 2.1, p.14, PDF p.16). A group effect of a group with member
type `ι` is a function `E : ℝ^ι_{≥0} → ℝ_{≥0}` that is not identically zero, monotone and symmetric.

**Formalization Note.** The domain `ι → ℝ≥0` and the codomain `ℝ≥0` are exactly the printed ones, so no
negative argument is ever quantified over. The members are a general type `ι`; the model uses
`ι = ↥(G j)`. `Equiv.Perm ι` is the printed "bijection π : G → G". -/
structure IsGroupEffect {ι : Type*} (E : (ι → ℝ≥0) → ℝ≥0) : Prop where
  /-- `E` is not identically zero. -/
  ne_zero : ∃ u, E u ≠ 0
  /-- (i) Monotonicity. -/
  monotone : ∀ u v : ι → ℝ≥0, (∀ i, u i ≤ v i) → E u ≤ E v
  /-- (ii) Symmetry. -/
  symmetric : ∀ (π : Equiv.Perm ι) (u : ι → ℝ≥0), E (fun i => u (π i)) = E u

end FairFacilityLoc


