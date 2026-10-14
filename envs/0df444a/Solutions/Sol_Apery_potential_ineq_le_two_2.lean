-- Prove2me | solution 2 for Apery.potential_ineq_le_two
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-13T15:16:10.341152+00:00
-- url     : https://prove2.me/submissions/304f62bb-4c2e-4baa-be3f-798465b653cf

import Definitions.Def_Zeta5_PotentialTableFullData
import Theorems.Thm_Apery_PotentialCertificate_table_sound
import Theorems.Thm_Apery_PotentialCertificate_TableBlock0_63_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock64_127_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock128_191_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock192_255_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock256_319_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock320_383_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock384_447_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock448_511_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock512_575_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock576_639_checked
import Theorems.Thm_Apery_PotentialCertificate_TableBlock640_683_checked

open Apery Apery.PotentialCertificate

theorem solution (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2) :
    2 * Uρ t - Vfield t ≤ M0 := by
  have hc : FullTable.certificate.Valid :=
    ⟨⟨⟨TableBlock0_63.checked, TableBlock64_127.checked, by decide +kernel⟩, ⟨TableBlock128_191.checked, ⟨TableBlock192_255.checked, TableBlock256_319.checked, by decide +kernel⟩, by decide +kernel⟩, by decide +kernel⟩, ⟨⟨TableBlock320_383.checked, ⟨TableBlock384_447.checked, TableBlock448_511.checked, by decide +kernel⟩, by decide +kernel⟩, ⟨TableBlock512_575.checked, ⟨TableBlock576_639.checked, TableBlock640_683.checked, by decide +kernel⟩, by decide +kernel⟩, by decide +kernel⟩, by decide +kernel⟩
  refine table_sound FullTable.certificate hc t ht ?_ ?_
  · change ((0 : ℚ) : ℝ) ≤ t
    exact_mod_cast ht.le
  · change t ≤ ((2 : ℚ) : ℝ)
    exact_mod_cast ht2

#print axioms solution
