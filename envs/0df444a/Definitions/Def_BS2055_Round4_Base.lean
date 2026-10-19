-- Prove2me | Definitions.Def_BS2055_Round4_Base
-- name    : BS2055_Round4_Base
-- status  : Definition
-- author  : @Leo Shaposhnik
-- created : 2026-10-17T13:39:22.870993+00:00
-- url     : https://prove2.me/theorems/4e1903e0-f5fb-4dde-9434-f73d4f9cf82f
-- title:
--   Threshold reset, initial pair budgets and common block witnesses
-- statement:
--   Define the three thresholds of three bits to accept when at least q+1 bits are true, for q=0,1,2; they are OR, majority and AND. Reset a scalar Boolean g by applying each threshold to three disjoint copies. Define the initial rejecting pair array to have diagonal $(3,2,1)$ and zero off-diagonal entries, and the accepting array to have diagonal $(1,2,3)C$ and zero off-diagonal entries. A common block witness for a family F and count n specifies that every predicate rejects zero, together with n pairwise disjoint nonempty finite coordinate sets that make every predicate accept when individually flipped at zero. Repeating each scalar block across all three child positions transports such witnesses to the reset family with the same count. The bundle also proves the thresholds' zero and all-one values.
-- source:
--   lean/round2-sharp/Round4/Base.lean; Robin Kothari, accepted proof of SensitivityCampaign.reach_205: https://prove2.me/theorems/4807ab9c-ddde-49d8-83cf-3532a7f795c3 . Upstream OpenAI/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, Apache-2.0: https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity . Verified local source commit 68fbb3b7d855f90678ac519b7ae7f59d160b3aa4: lean/round2-sharp/Round4/Result.lean, achieves_2055, lines 77-94; Arithmetic.lean, certificate_scale/certificate_slack/seed_power_gap; PairTransfer.lean, recursive_pair_zero.

/-
GENERATED FILE — MODIFIED SOURCE NOTICE
Local proof source: block-sensitivity continuation commit 032868f.
Upstream helper source: OpenAI/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Credit: Robin Kothari, accepted Prove2Me2.05 amplifier, theorem
4807ab9c-ddde-49d8-83cf-3532a7f795c3; construction adapted with
the local sharp gate refinement and complete verification.
Original modules used in this file:
  lean/round2-sharp/Round4/Base.lean
Modifications: mechanical skeleton subtraction, import rewriting,
and a root solution alias with the same elaborated theorem type.
Copied upstream files previously received only the documented Lean
conditional-proof lemma-name port; mathematical definitions and
statements were preserved. This generated file is local staging.

Upstream Apache2 license (full text):
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

import Mathlib
import Definitions.Def_BS20205_Round2_Bounds
import Definitions.Def_BS20205_Round2_GeneralSeed
import Definitions.Def_BS20205_Sharp_Arithmetic
import Definitions.Def_BS20205_Sharp_Bounds
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Iterates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Theorems.Thm_OAI_Paper320_Tournament_card_badLabelings_le
import Theorems.Thm_OAI_Paper320_Tournament_card_internalEdges
import Theorems.Thm_OAI_Paper320_Tournament_card_le_three_of_outdegree_le_one
import Theorems.Thm_OAI_Paper320_Tournament_goodLabeling_exists_of_power_bound
import Theorems.Thm_OAI_Paper320_Tournament_labelingConstraint_iff
import Theorems.Thm_OAI_Paper320_ballPredicate_sensitivityAt_zero_le
import Theorems.Thm_OAI_Paper320_blockSensitivityAt_compose_zero_le
import Theorems.Thm_OAI_Paper320_coupled_profiles_bound
import Theorems.Thm_OAI_Paper320_exists_blockSensitivityAt_family
import Theorems.Thm_OAI_Paper320_finite_certificate_20205
import Theorems.Thm_OAI_Paper320_gateNonsinks_card_of_sink
import Theorems.Thm_OAI_Paper320_initialFamily_joint
import Theorems.Thm_OAI_Paper320_le_blockSensitivityAt_of_family
import Theorems.Thm_OAI_Paper320_normalized_profiles_step
import Theorems.Thm_OAI_Paper320_quantitative_profile_bounds
import Theorems.Thm_OAI_Paper320_quantitative_separation
import Theorems.Thm_OAI_Paper320_recursive_joint_one_at
import Theorems.Thm_OAI_Paper320_recursive_joint_zero_at
import Theorems.Thm_OAI_Paper320_recursive_joint_zero_at_sharp
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_one_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at
import Theorems.Thm_OAI_Paper320_recursive_sensitivity_zero_at_sharp
import Theorems.Thm_OAI_Paper320_rowClause_repair_cases
import Theorems.Thm_OAI_Paper320_sensitivity_orCopies_le
import Theorems.Thm_OAI_Paper320_towerFamily_blocks
import Theorems.Thm_OAI_Paper320_tower_four_recurrences
import Theorems.Thm_OAI_Paper320_tower_four_recurrences_sharp
import Theorems.Thm_SensitivityCampaign_baseline
import Theorems.Thm_SensitivityCampaign_baseline_arithmetic
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_finite_certificate_log
import Theorems.Thm_SensitivityCampaign_openai_seed_bounds
import Theorems.Thm_SensitivityCampaign_reach_20205
import Definitions.Def_BS2055_Growth
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_Iterates
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_LabelingConstraints
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_BS2055_OAI_Combinatorics_Sensitivity_RecursiveBlocks



/-! Three nested thresholds preserve disjoint block witnesses while producing
zero off-diagonal pair sensitivity. This is a generic base for amplification. -/
namespace OAI.Paper320.Round4

/-- The three nonconstant increasing thresholds of three Boolean inputs. -/
def threshold (q : Fin 3) (x : Fin 3 → Bool) : Bool :=
  decide (q.val + 1 ≤ (Finset.univ.filter fun i => x i = true).card)

def flip3 (x : Fin 3 → Bool) (i : Fin 3) : Fin 3 → Bool :=
  fun j => if j = i then !(x j) else x j

set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem threshold_zero : ∀ q : Fin 3, threshold q (fun _ => false) = false := by
  decide +kernel

theorem threshold_true : ∀ q : Fin 3, threshold q (fun _ => true) = true := by
  decide +kernel

noncomputable section
open scoped Classical





def base {I : Type} (g : (I → Bool) → Bool) :
    Fin 3 → (Fin 3 × I → Bool) → Bool := fun q => compose (threshold q) g

def Z0 (q q' : Fin 3) : ℕ := if q = q' then 3 - q.val else 0

def Y0 (C : ℕ) (q q' : Fin 3) : ℕ := if q = q' then (q.val + 1) * C else 0









/-- A common normalized block family accepted by every predicate. -/
structure Blocks {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) (n : ℕ) where
  zero : ∀ q, F q (fun _ => false) = false
  sets : Fin n → Finset I
  nonempty : ∀ i, (sets i).Nonempty
  disjoint : ∀ i j, i ≠ j → Disjoint (sets i) (sets j)
  on : ∀ q i, F q (flip (fun _ => false) (sets i)) = true

/-- Repeating a child block in all three outer coordinates makes every
threshold accept, preserving the number and disjointness of blocks. -/
def baseBlocks {I : Type} (g : (I → Bool) → Bool) {n : ℕ}
    (w : Blocks (fun _ : Fin 1 => g) n) : Blocks (base g) n where
  zero q := by
    change compose (threshold q) g (fun _ => false) = false
    rw [compose_zero _ _ (w.zero 0)]
    exact threshold_zero q
  sets i := Finset.univ ×ˢ w.sets i
  nonempty i := by
    obtain ⟨j,hj⟩ := w.nonempty i
    exact ⟨(0,j),Finset.mem_product.mpr ⟨Finset.mem_univ _,hj⟩⟩
  disjoint i j hij := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp (w.disjoint i j hij)
      (Finset.mem_product.mp hp).2 (Finset.mem_product.mp hq).2
  on q i := by
    change compose (threshold q) g
      (flip (fun _ => false) (Finset.univ ×ˢ w.sets i)) = true
    have hg : g (flip (fun _ => false) (w.sets i)) ≠ g (fun _ => false) := by
      rw [w.on 0 i, w.zero 0]
      decide
    rw [compose_flip_product_zero _ _ _ _ (w.zero 0) hg]
    have hflip : flip (fun _ : Fin 3 => false) Finset.univ = fun _ => true := by
      funext j
      simp [flip]
    rw [hflip]
    exact threshold_true q







end
end OAI.Paper320.Round4


