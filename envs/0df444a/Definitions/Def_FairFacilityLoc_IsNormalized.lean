-- Prove2me | Definitions.Def_FairFacilityLoc_IsNormalized
-- name    : FairFacilityLoc_IsNormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:23.951443+00:00
-- url     : https://prove2.me/theorems/a1c8a4ad-d083-41ae-b936-5d906127f6b2
-- title:
--   Normalized coordinates and the capacity condition
-- statement:
--   **Normalized** data, (3.2): a finite family $W$ of nonnegative weight vectors with a vector of positive total mass, and $z\in\mathbb R^d_{\ge0}$ with $\|z\|_2=1$ and $F_W(z)=1$. The output of the mechanism sits at the origin.
--
--   **Capacity condition**: $Q_r(a)\le K_r$ for every $a\in W$ and every coordinate $r$. This is the conclusion of Lemma 3.9.
--
--   **Formalization Note** These are normalized coordinates, never facts about an arbitrary instance. The capacity condition is what separates the later steps from the mechanism, and `FairFacilityLoc.lemma_3_9` proves it for a mechanism output.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), (3.2), p.21 (PDF p.23); Lemma 3.9, p.26 (PDF p.28); family form pp.48–49 (PDF pp.50–51)

import Mathlib
import Definitions.Def_FairFacilityLoc_familyObjective
import Definitions.Def_FairFacilityLoc_capacity

namespace FairFacilityLoc

/-- **Normalized coordinates of Step 1** (Yan, Zhou, manuscript, sha256 642a1268…, (3.2), p.21, PDF p.23, for
weight families as on pp.48–49, PDF pp.50–51): a finite family of nonnegative weight vectors with a vector of
positive total mass, and `z ∈ ℝ^d_{≥0}` with `∥z∥₂ = 1` and `F_W(z) = 1`.

**Formalization Note.** The output is the origin and does not appear. These are normalized coordinates, not a
property of an arbitrary instance. -/
structure IsNormalized {n d : ℕ} (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) : Prop where
  /-- Weight vectors are nonnegative. -/
  weight_nonneg : ∀ a ∈ W, ∀ i, 0 ≤ a i
  /-- Some weight vector has positive total mass. -/
  exists_pos_mass : ∃ a ∈ W, 0 < mass a Finset.univ
  /-- `z ≥ 0`. -/
  z_nonneg : ∀ r, 0 ≤ z r
  /-- `∥z∥₂ = 1`. -/
  z_norm : ‖z‖ = 1
  /-- `F_W(z) = 1`. -/
  objective_z : familyObjective x W z = 1

/-- **The conclusion of Lemma 3.9**: `Q_r(a) ≤ K_r` for every `a ∈ W` and every coordinate `r`
(p.26, PDF p.28). Propositions 3.15, 3.24, 3.17 and Lemma 3.22 use the mechanism only through this inequality.

**Formalization Note.** It is the proved conclusion of `FairFacilityLoc.lemma_3_9` for the normalization of a
mechanism output, not a free assumption about real instances. -/
def CapacityCondition {n d : ℕ} (b : ℝ) (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) : Prop :=
  ∀ a ∈ W, ∀ r, posScore b x a r ≤ capacity b W x r

end FairFacilityLoc


