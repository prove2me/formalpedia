-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:28:31.385415+00:00
-- url     : https://prove2.me/theorems/a5507b25-2ecb-4aa8-b757-eaff1ca97c9f
-- title:
--   Incidence coefficients under removal of fixed coordinates
-- statement:
--   This bundle supplies incidence coefficients under removal of fixed coordinates. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/inc_sdiff.lean, selected declarations in lines 25–56; source SHA-256 5003594badc78745f66a86b7732d518b26f18aaa2a1b75ea9260e5e2412fc887; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN

-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem inc_sdiff {G J J' : Finset V} (hG : G ⊆ J) (hG' : G ⊆ J') :
    inc k (J \ G) (J' \ G) = eps k G (J \ G) * eps k G (J' \ G) * inc k J J'
-- SWARM:STATEMENT-END
:= by
  by_cases h : ∃ j, j ∉ J ∧ J' = insert j J
  · obtain ⟨j, hjJ, rfl⟩ := h
    have hjG : j ∉ G := fun hx => hjJ (hG hx)
    have hjsd : j ∉ J \ G := fun hx => hjJ (Finset.mem_sdiff.mp hx).1
    have hins : insert j J \ G = insert j (J \ G) :=
      Finset.insert_sdiff_of_notMem J hjG
    rw [hins, inc_insert hjsd, inc_insert hjJ, eps_insert hjsd, nu_sdiff_add hG j,
      pow_add]
    have h1 : eps k G (J \ G) * eps k G (J \ G) = 1 := eps_mul_self G (J \ G)
    have h2 : ((-1 : k)) ^ nu G j * (-1 : k) ^ nu G j = 1 := by
      rw [← mul_pow]; norm_num
    calc (-1 : k) ^ nu (J \ G) j
        = (eps k G (J \ G) * eps k G (J \ G)) *
            ((-1 : k) ^ nu G j * (-1 : k) ^ nu G j) * (-1 : k) ^ nu (J \ G) j := by
          rw [h1, h2, one_mul, one_mul]
      _ = eps k G (J \ G) * (eps k G (J \ G) * (-1 : k) ^ nu G j) *
            ((-1 : k) ^ nu G j * (-1 : k) ^ nu (J \ G) j) := by ring
  · rw [inc_eq_zero h, mul_zero]
    apply inc_eq_zero
    rintro ⟨j, hj, heq⟩
    have hjmem : j ∈ J' \ G := by rw [heq]; exact Finset.mem_insert_self _ _
    have hjG : j ∉ G := (Finset.mem_sdiff.mp hjmem).2
    have hjJ : j ∉ J := fun hx => hj (Finset.mem_sdiff.mpr ⟨hx, hjG⟩)
    refine h ⟨j, hjJ, ?_⟩
    calc J' = J' \ G ∪ G := (Finset.sdiff_union_of_subset hG').symm
      _ = insert j (J \ G) ∪ G := by rw [heq]
      _ = insert j ((J \ G) ∪ G) := Finset.insert_union _ _ _
      _ = insert j J := by rw [Finset.sdiff_union_of_subset hG]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


