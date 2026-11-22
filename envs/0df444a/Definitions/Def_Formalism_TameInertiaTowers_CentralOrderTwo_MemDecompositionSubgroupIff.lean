-- Prove2me | Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
-- name    : Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:53.313432+00:00
-- url     : https://prove2.me/theorems/11d1ceaf-6b55-49f0-a71d-fbac029eb2f2
-- title:
--   Mem Decomposition Subgroup Iff
-- statement:
--   Definitions and structural lemmas for Mem Decomposition Subgroup Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/MemDecompositionSubgroupIff.lean

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Subgroup
namespace Formalism.TwoAdicCyclotomicDecomposition
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
def KK (n : ℕ) : Subgroup (GalL n) :=
  (powMonoidHom 2 : (GalL n ⧸ zpowers (JJ n)) →* _).range.comap
    (QuotientGroup.mk' (zpowers (JJ n)))
lemma h4dvd (k : ℕ) : 4 ∣ 2 ^ (k + 3) := ⟨2 ^ (k + 1), by ring⟩
lemma h8dvd (k : ℕ) : 8 ∣ 2 ^ (k + 3) := ⟨2 ^ k, by ring⟩
def chi4 (k : ℕ) : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ :=
  ZMod.χ₄.toUnitHom.comp (ZMod.unitsMap (h4dvd k))
def chi8 (k : ℕ) : (ZMod (2 ^ (k + 3)))ˣ →* ℤˣ :=
  ZMod.χ₈.toUnitHom.comp (ZMod.unitsMap (h8dvd k))
def psi (k : ℕ) : GalL (k + 3) →* ℤˣ × ℤˣ × ℤˣ :=
  MonoidHom.mk' (fun g => (chi4 k g.1 * g.2.1, chi8 k g.1, g.2.1 * g.2.2)) (by
    intro a b
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show chi4 k (a.1 * b.1) * (a.2.1 * b.2.1) = (chi4 k a.1 * a.2.1) * (chi4 k b.1 * b.2.1)
      rw [map_mul, mul_mul_mul_comm]
    · show chi8 k (a.1 * b.1) = chi8 k a.1 * chi8 k b.1
      rw [map_mul]
    · show (a.2.1 * b.2.1) * (a.2.2 * b.2.2) = (a.2.1 * a.2.2) * (b.2.1 * b.2.2)
      rw [mul_mul_mul_comm])
end ModelEmbedding
open ModelEmbedding
end Formalism.TwoAdicCyclotomicDecomposition


