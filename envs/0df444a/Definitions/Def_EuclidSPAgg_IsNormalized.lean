-- Prove2me | Definitions.Def_EuclidSPAgg_IsNormalized
-- name    : EuclidSPAgg_IsNormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:28.479271+00:00
-- url     : https://prove2.me/theorems/6c768bf0-7e5e-4194-a750-15c71afb9f1a
-- title:
--   Normalized mechanism
-- statement:
--   A mechanism is **normalized** if it is both translation-equivariant and positively homogeneous. Within the continuous class, translation equivariance already implies positive homogeneity (Corollary 2.5), so "normalized" is shorthand used in the structural proof.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsTranslationEquivariant
import Definitions.Def_EuclidSPAgg_IsPosHomogeneous
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- A mechanism is normalized if it is both translation-equivariant and positively homogeneous
(Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)). -/
def IsNormalized {n d : ℕ} (f : Mech n d) : Prop :=
  IsTranslationEquivariant f ∧ IsPosHomogeneous f

end EuclidSPAgg


