-- Prove2me | Definitions.Def_OAIQ107D133
-- name    : OAIQ107D133
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T17:18:18.374831+00:00
-- url     : https://prove2.me/theorems/80d31f7c-595a-4623-a135-265988dabeab
-- title:
--   Definitions bundle OAIQ107D133 of the split of OpenAI, Cycle-clique Ramsey numbers
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CycleClique.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Cycle-clique Ramsey numbers*, OpenAI Math Release, September 25, 2026, result family 189, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 254 declarations of OpenAI's Lean: 240 definitions, 9 instances and 5 theorems. The definitions and types are `OAI.CycleClique.certificate_561`, `OAI.CycleClique.certificate_561_part_2`, `OAI.CycleClique.certificate_562`, `OAI.CycleClique.certificate_562_part_1`, `OAI.CycleClique.certificate_562_part_2`, `OAI.CycleClique.certificate_569_part_10_M`, `OAI.CycleClique.certificate_569_part_11_M`, `OAI.CycleClique.certificate_569_part_12_M`, `OAI.CycleClique.certificate_569_part_13_M`, `OAI.CycleClique.certificate_569_part_14_M`, `OAI.CycleClique.certificate_569_part_15_M`, `OAI.CycleClique.certificate_569_part_16_M`, `OAI.CycleClique.certificate_569_part_17_M`, `OAI.CycleClique.certificate_569_part_18_M`, `OAI.CycleClique.certificate_569_part_19_M`, `OAI.CycleClique.certificate_569_part_1_M`, `OAI.CycleClique.certificate_569_part_20_M`, `OAI.CycleClique.certificate_569_part_21_M`, `OAI.CycleClique.certificate_569_part_22_M`, `OAI.CycleClique.certificate_569_part_23_M`, `OAI.CycleClique.certificate_569_part_24_M`, `OAI.CycleClique.certificate_569_part_25_M`, `OAI.CycleClique.certificate_569_part_26_M`, `OAI.CycleClique.certificate_569_part_27_M`, `OAI.CycleClique.certificate_569_part_28_M`, `OAI.CycleClique.certificate_569_part_29_M`, `OAI.CycleClique.certificate_569_part_2_M`, `OAI.CycleClique.certificate_569_part_3_M`, `OAI.CycleClique.certificate_569_part_4_M`, `OAI.CycleClique.certificate_569_part_5_M`, `OAI.CycleClique.certificate_569_part_6_M`, `OAI.CycleClique.certificate_569_part_7_M`, `OAI.CycleClique.certificate_569_part_8_M`, `OAI.CycleClique.certificate_569_part_9_M`, `OAI.CycleClique.certificate_603`, `OAI.CycleClique.certificate_603_part_1`, `OAI.CycleClique.certificate_603_part_2`, `OAI.CycleClique.certificate_652`, `OAI.CycleClique.certificate_652_part_1`, `OAI.CycleClique.certificate_652_part_2` and 200 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Ramsey_CycleClique_CachedDecisions`, `Ramsey_CycleClique_CertificateDecisions`, `Ramsey_CycleClique_Certificates001`, `Ramsey_CycleClique_Certificates003`, `Ramsey_CycleClique_Certificates004`, `Ramsey_CycleClique_Certificates018`, `Ramsey_CycleClique_Certificates019`, `Ramsey_CycleClique_Certificates021`, `Ramsey_CycleClique_Certificates023`, `Ramsey_CycleClique_Certificates024`, `Ramsey_CycleClique_Certificates025`, `Ramsey_CycleClique_Certificates027`, `Ramsey_CycleClique_Certificates028`, `Ramsey_CycleClique_Certificates029`, `Ramsey_CycleClique_Certificates030`, `Ramsey_CycleClique_Certificates031`, `Ramsey_CycleClique_CliqueBits`, `Ramsey_CycleClique_CompactLabels`.
--
--   **Imports.** It imports the bundles `OAIQ107D020`, `OAIQ107D046`, `OAIQ107D100`, `OAIQ107D104`, `OAIQ107D109`, `OAIQ107D110`, `OAIQ107D111`, `OAIQ107D112`, `OAIQ107D113`, `OAIQ107D114`, `OAIQ107D115`, `OAIQ107D116`, `OAIQ107D117`, `OAIQ107D118`, `OAIQ107D119`, `OAIQ107D120`, `OAIQ107D121`, `OAIQ107D122`, `OAIQ107D123`, `OAIQ107D124` and `OAIQ107D125` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.CycleClique.finite_patterns_10_5`, `OAI.CycleClique.finite_patterns_11_5`, `OAI.CycleClique.finite_patterns_11_6`, `OAI.CycleClique.finite_patterns_12_6`, `OAI.CycleClique.finite_patterns_13_6`, `OAI.CycleClique.finite_patterns_13_7`, `OAI.CycleClique.finite_patterns_14_7`, `OAI.CycleClique.finite_patterns_14_8`, `OAI.CycleClique.finite_patterns_15_7`, `OAI.CycleClique.finite_patterns_15_8`, `OAI.CycleClique.finite_patterns_16_8`, `OAI.CycleClique.finite_patterns_17_8`, `OAI.CycleClique.finite_patterns_9_4`, `OAI.CycleClique.finite_range_verified`, `OAI.CycleClique.patterns_13_6_0_verified`, `OAI.CycleClique.patterns_15_7_0_verified`, `OAI.CycleClique.patterns_15_7_13_verified`, `OAI.CycleClique.patterns_15_7_1_verified`, `OAI.CycleClique.patterns_15_7_4_verified`, `OAI.CycleClique.patterns_16_8_7_verified`, `OAI.CycleClique.patterns_16_8_8_verified`, `OAI.CycleClique.patterns_17_8_0_verified`, `OAI.CycleClique.patterns_17_8_11_verified`, `OAI.CycleClique.patterns_17_8_12_verified`, `OAI.CycleClique.patterns_17_8_15_verified`, `OAI.CycleClique.patterns_17_8_16_verified`, `OAI.CycleClique.patterns_17_8_17_verified`, `OAI.CycleClique.patterns_17_8_1_verified`, `OAI.CycleClique.patterns_17_8_23_verified`, `OAI.CycleClique.patterns_17_8_24_verified`, `OAI.CycleClique.patterns_17_8_25_verified`, `OAI.CycleClique.patterns_17_8_26_verified`, `OAI.CycleClique.patterns_17_8_32_verified`, `OAI.CycleClique.patterns_17_8_35_verified`, `OAI.CycleClique.patterns_17_8_36_verified`, `OAI.CycleClique.patterns_17_8_39_verified`, `OAI.CycleClique.patterns_17_8_40_verified`, `OAI.CycleClique.patterns_17_8_41_verified`, `OAI.CycleClique.patterns_17_8_42_verified`, `OAI.CycleClique.patterns_17_8_51_verified`, `OAI.CycleClique.patterns_17_8_52_verified`, `OAI.CycleClique.patterns_17_8_53_verified` and `OAI.CycleClique.patterns_17_8_6_verified`.
-- source:
--   OpenAI, Cycle-clique Ramsey numbers, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 189; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Cycle-clique-Ramsey-numbers-September-25-2026/Cycle-clique-Ramsey-numbers-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ107D020
import Definitions.Def_OAIQ107D046
import Definitions.Def_OAIQ107D100
import Definitions.Def_OAIQ107D104
import Definitions.Def_OAIQ107D109
import Definitions.Def_OAIQ107D110
import Definitions.Def_OAIQ107D111
import Definitions.Def_OAIQ107D112
import Definitions.Def_OAIQ107D113
import Definitions.Def_OAIQ107D114
import Definitions.Def_OAIQ107D115
import Definitions.Def_OAIQ107D116
import Definitions.Def_OAIQ107D117
import Definitions.Def_OAIQ107D118
import Definitions.Def_OAIQ107D119
import Definitions.Def_OAIQ107D120
import Definitions.Def_OAIQ107D121
import Definitions.Def_OAIQ107D122
import Definitions.Def_OAIQ107D123
import Definitions.Def_OAIQ107D124
import Definitions.Def_OAIQ107D125

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CertificateDecisions
attribute [-instance] _root_.OAI.CycleClique.compactLabelCycleValid _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem compactMatrixBits_spec (M : ForbiddenMatrix) (i j d : ℕ) :
    (compactMatrixBits M).testBit (compactTriple i j d) = true ↔ (i,j,d) ∈ M := by
  induction M with
  | nil => simp [compactMatrixBits]
  | cons c M ih =>
    rcases c with ⟨a,b,e⟩
    simp only [compactMatrixBits, Nat.testBit_lor, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq, compactTriple_injective, ih,
      List.mem_cons, Prod.mk.injEq]
    tauto

instance (priority := high) compactMatrixEntry (M : ForbiddenMatrix) (i j d : ℕ) :
    Decidable (matrixEntry M i j d) :=
  decidable_of_iff ((compactMatrixBits M).testBit (compactTriple i j d) = true ∨
    (compactMatrixBits M).testBit (compactTriple j i d) = true)
    (by simp only [compactMatrixBits_spec, matrixEntry])

instance (priority := high) compactExcluded (n : ℕ) (M : ForbiddenMatrix)
    (i lo hi : ℕ) (Z : Finset ℕ) : Decidable (Excluded n M i lo hi Z) := by
  unfold Excluded
  infer_instance

instance (priority := high) compactBallValid (k t n : ℕ) (M : ForbiddenMatrix) (i : ℕ)
    (B : BallCertificate) : Decidable (B.Valid k t n M i) :=
  match B with
  | .zero Z b u => by unfold BallCertificate.Valid; infer_instance
  | .succ p Z b u => by
    unfold BallCertificate.Valid
    exact @instDecidableAnd _ _ (compactBallValid k t n M i p) inferInstance

instance (priority := high) compactPackingOptionValid (k t n : ℕ)
    (M : ForbiddenMatrix) (o : PackingOption) : Decidable (o.Valid k t n M) := by
  cases o <;> unfold PackingOption.Valid <;> infer_instance

instance (priority := high) compactPackingCompatible (M : ForbiddenMatrix)
    (a b : PackingOption) : Decidable (a.Compatible M b) := by
  unfold PackingOption.Compatible
  infer_instance

instance (priority := high) compactPackingValid (k t n : ℕ)
    (M : ForbiddenMatrix) (P : Finset PackingOption) : Decidable (PackingValid k t n M P) := by
  unfold PackingValid
  infer_instance

instance (priority := high) compactMatrixCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold FiniteCertificate.Valid; infer_instance
  | .forbid i j d R N => by
    unfold FiniteCertificate.Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (compactMatrixCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (compactMatrixCertificateValid k t n q E L e ((i,j,d)::M) N)))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CompactLabels
attribute [-instance] _root_.OAI.CycleClique.instAssociativeNatLor_solutions _root_.OAI.CycleClique.instCommutativeNatLor_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

instance (priority := high) compactAllCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  match C with
  | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold FiniteCertificate.Valid; infer_instance
  | .forbid i j d R N => by
    unfold FiniteCertificate.Valid
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ (compactAllCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
        (compactAllCertificateValid k t n q E L e ((i,j,d)::M) N)))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CliqueBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem qBits_spec (q : Finset ℕ) (i : ℕ) : (qBits q).testBit i = true ↔ i ∈ q := by
  induction q using Finset.induction_on with
  | empty => simp [qBits]
  | @insert a s ha ih =>
    simp only [qBits, Finset.fold_insert ha]
    change ((2^a ||| qBits s).testBit i = true) ↔ _
    simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, ih, Finset.mem_insert]
    tauto

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_CachedDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def qCachedLabelValidBool (n : ℕ) (q : Finset ℕ) (bits : ℕ)
    (C : List (List ℕ)) : Bool :=
  compactNodupLabels C.flatten && C.flatten.all (fun i => decide (i < n)) &&
  C.all (fun c => !c.isEmpty &&
    compactChainLabels (fun a b => bits.testBit (Nat.pair a b) ||
      bits.testBit (Nat.pair b a)) c &&
    compactChainLabels (fun a b => (!(qBits q).testBit a) || (!(qBits q).testBit b)) c &&
    c.head?.all (fun a => (qBits q).testBit a) &&
    c.getLast?.all (fun a => (qBits q).testBit a)) &&
  decide (∀ i ∈ q, i ∈ C.flatten)

theorem qCachedLabelValidBool_spec (n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (C : List (List ℕ)) :
    qCachedLabelValidBool n q (globalEdgeBits E) C = true ↔ LabelValid n q E C :=
  by
    have hf (i : ℕ) : (qBits q).testBit i = false ↔ i ∉ q := by
      rw [Bool.eq_false_iff]
      exact not_congr (qBits_spec q i)
    unfold LabelValid
    simp only [qCachedLabelValidBool, Bool.and_eq_true, compactNodupLabels_spec,
      List.all_eq_true, decide_eq_true_eq, compactChainLabels_spec,
      Bool.or_eq_true, globalEdgeBits_spec, qBits_spec, Option.all_eq_true,
      Bool.not_eq_true', hf, List.isEmpty_eq_false_iff, Option.mem_def]
    simp only [and_assoc]
    rfl

theorem qCachedCycleValidBool_spec (n k : ℕ) (E : List (ℕ × ℕ)) (C : List ℕ) :
    qCachedCycleValidBool n k (globalEdgeBits E) C = true ↔ LabelCycleValid n k E C := by
  simp only [qCachedCycleValidBool, LabelCycleValid, Bool.and_eq_true,
    compactNodupLabels_spec, decide_eq_true_eq, List.all_eq_true,
    compactChainLabels_spec, Bool.or_eq_true, globalEdgeBits_spec,
    Option.all_eq_true, labelAdj, Option.mem_def, and_assoc]
  simp only [or_comm]
  rfl

def qCachedCertificateBool (k t n : ℕ) (q : Finset ℕ) (bits : ℕ) (L e : ℕ)
    (M : ForbiddenMatrix) : FiniteCertificate → Bool
  | .system C => qCachedLabelValidBool n q bits C && decide (Improvement k t L e C)
  | .cycle C => qCachedCycleValidBool n k bits C
  | .packing P => decide (PackingValid k t n M P)
  | .edge i j => decide (i < n) && decide (j < n) &&
      (bits.testBit (Nat.pair i j) || bits.testBit (Nat.pair j i)) &&
      decide (matrixEntry M i j 0)
  | .forbid i j d R N => decide (i < n) && decide (j < n) &&
      qCachedCertificateBool k t (n+d) q
        (bits ||| globalEdgeBits (pathEdges (pathLabels n i j d))) L e M R &&
      qCachedCertificateBool k t n q bits L e ((i,j,d)::M) N

theorem qCachedCertificateBool_spec (k t n : ℕ) (q : Finset ℕ) (E : List (ℕ × ℕ))
    (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    qCachedCertificateBool k t n q (globalEdgeBits E) L e M C = true ↔
      C.Valid k t n q E L e M := by
  induction C generalizing n E M with
  | system C => simp [qCachedCertificateBool, FiniteCertificate.Valid, qCachedLabelValidBool_spec]
  | cycle C => exact qCachedCycleValidBool_spec n k E C
  | packing P => simp [qCachedCertificateBool, FiniteCertificate.Valid]
  | edge i j =>
    simp [qCachedCertificateBool, FiniteCertificate.Valid, globalEdgeBits_spec, labelAdj, and_assoc]
  | forbid i j d R N ihR ihN =>
    simp only [qCachedCertificateBool, Bool.and_eq_true, decide_eq_true_eq]
    rw [← qCacheEdgeBits_append, ← augmentedEdges, ihR, ihN]
    simp only [FiniteCertificate.Valid, and_assoc]

instance (priority := high) qCachedCertificateValid (k t n : ℕ) (q : Finset ℕ)
    (E : List (ℕ × ℕ)) (L e : ℕ) (M : ForbiddenMatrix) (C : FiniteCertificate) :
    Decidable (C.Valid k t n q E L e M) :=
  decidable_of_iff _ (qCachedCertificateBool_spec k t n q E L e M C)

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_9_part_1_M : ForbiddenMatrix := ((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((0,1,1) :: (certificate_9_M))))))))))))))))

noncomputable def certificate_9_part_2_M : ForbiddenMatrix := ((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((0,2,0) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,2,4) :: (certificate_9_part_1_M))))))))))))))))

noncomputable def certificate_9_part_3_M : ForbiddenMatrix := ((1,3,2) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((2,4,0) :: (((1,2,5) :: (((0,4,4) :: (certificate_9_part_2_M))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_66_part_1_M : ForbiddenMatrix := ((0,2,2) :: (((0,1,6) :: (((0,1,5) :: (((0,1,4) :: (((0,1,2) :: (((0,3,1) :: (((0,2,1) :: (((0,1,1) :: (certificate_66_M))))))))))))))))

noncomputable def certificate_66_part_2_M : ForbiddenMatrix := ((1,2,5) :: (((1,2,4) :: (((1,2,2) :: (((1,2,1) :: (((0,4,1) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (certificate_66_part_1_M))))))))))))))))

noncomputable def certificate_66_part_3_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((2,4,1) :: (((2,3,1) :: (((1,4,1) :: (((1,3,1) :: (((1,2,6) :: (certificate_66_part_2_M))))))))))))))

noncomputable def certificate_66_part_4_M : ForbiddenMatrix := ((0,4,3) :: (((0,4,2) :: (((0,4,0) :: (((2,4,1) :: (((2,3,1) :: (((1,4,1) :: (((1,3,1) :: (((1,2,6) :: (certificate_66_part_2_M))))))))))))))))

noncomputable def certificate_66_part_5_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((2,6,1) :: (((1,6,1) :: (((0,6,1) :: (((0,4,5) :: (((0,4,4) :: (certificate_66_part_4_M))))))))))))))

noncomputable def certificate_66_part_6_M : ForbiddenMatrix := ((0,3,3) :: (((0,3,2) :: (((0,5,0) :: (((2,6,1) :: (((1,6,1) :: (((0,6,1) :: (((0,4,5) :: (((0,4,4) :: (certificate_66_part_4_M))))))))))))))))

noncomputable def certificate_66_part_7_M : ForbiddenMatrix := ((1,3,5) :: (((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((0,7,1) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (certificate_66_part_6_M))))))))))))))))

noncomputable def certificate_66_part_8_M : ForbiddenMatrix := ((3,6,0) :: (((1,4,0) :: (((0,1,3) :: (((3,4,1) :: (((2,3,2) :: (((1,7,1) :: (((1,3,6) :: (certificate_66_part_7_M))))))))))))))

noncomputable def certificate_66_part_9_M : ForbiddenMatrix := ((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((3,4,1) :: (((2,3,2) :: (((1,7,1) :: (((1,3,6) :: (certificate_66_part_7_M))))))))))))))))

noncomputable def certificate_66_part_10_M : ForbiddenMatrix := ((1,5,1) :: (((1,2,3) :: (((0,2,3) :: (((0,1,3) :: (((1,5,0) :: (((1,4,0) :: (((0,5,5) :: (certificate_66_part_9_M))))))))))))))

noncomputable def certificate_66_part_11_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,3) :: (((2,5,0) :: (((2,4,0) :: (((1,5,0) :: (((1,4,0) :: (((0,5,5) :: (certificate_66_part_9_M))))))))))))))

noncomputable def certificate_66_part_12_M : ForbiddenMatrix := ((4,5,2) :: (((4,5,1) :: (((3,5,0) :: (((2,5,0) :: (((2,4,0) :: (((1,5,0) :: (((1,4,0) :: (((0,5,5) :: (certificate_66_part_9_M))))))))))))))))

noncomputable def certificate_66_part_2 : FiniteCertificate := .forbid 1 2 6 (.system [[0],[1,8,9,10,11,12,13,2],[3],[7]]) (.forbid 1 3 1 (.system [[0],[1,8,3,4,5,6,7],[2]]) (.forbid 1 4 1 (.system [[0],[1,8,4,5,6,7],[2],[3]]) (.forbid 2 3 1 (.system [[0],[1],[2,8,3,4,5,6,7]]) (.forbid 2 4 1 (.system [[0],[1],[2,8,4,5,6,7],[3]]) (.forbid 0 4 0 (.forbid 0 1 3 (.cycle [0,4,3,2,7,1,10,9,8]) (.forbid 0 2 3 (.cycle [0,4,3,1,7,2,10,9,8]) (certificate_66_part_3))) (.forbid 0 4 2 (.system [[0,8,9,4,5,6,7],[1],[2],[3]]) (.forbid 0 4 3 (.system [[0,8,9,10,4,3],[1],[2],[7]]) (certificate_66_part_4))))))))

noncomputable def certificate_66_part_1 : FiniteCertificate := .forbid 0 2 4 (.system [[0,8,9,10,11,2],[1],[3],[7]]) (.forbid 0 2 5 (.system [[0,8,9,10,11,12,2],[1],[3],[7]]) (.forbid 0 2 6 (.system [[0,8,9,10,11,12,13,2],[1],[3],[7]]) (.forbid 0 4 1 (.system [[0,8,4,5,6,7],[1],[2],[3]]) (.forbid 1 2 1 (.system [[0],[1,8,2],[3,4,5,6,7]]) (.forbid 1 2 2 (.system [[0],[1,8,9,2],[3,4,5,6,7]]) (.forbid 1 2 4 (.system [[0],[1,8,9,10,11,2],[3],[7]]) (.forbid 1 2 5 (.system [[0],[1,8,9,10,11,12,2],[3],[7]]) (certificate_66_part_2))))))))

noncomputable def certificate_66 : FiniteCertificate := .forbid 0 1 1 (.system [[0,8,1],[2],[3,4,5,6,7]]) (.forbid 0 2 1 (.system [[0,8,2],[1],[3,4,5,6,7]]) (.forbid 0 3 1 (.system [[0,8,3,4,5,6,7],[1],[2]]) (.forbid 0 1 2 (.system [[0,8,9,1],[2],[3,4,5,6,7]]) (.forbid 0 1 4 (.system [[0,8,9,10,11,1],[2],[3],[7]]) (.forbid 0 1 5 (.system [[0,8,9,10,11,12,1],[2],[3],[7]]) (.forbid 0 1 6 (.system [[0,8,9,10,11,12,13,1],[2],[3],[7]]) (.forbid 0 2 2 (.system [[0,8,9,2],[1],[3,4,5,6,7]]) (certificate_66_part_1))))))))

noncomputable def certificate_69 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1,2,3],[4,5,6]]) (.forbid 0 1 2 (.system [[0,7,8,1],[3],[4],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1],[3],[4],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1],[3],[4],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1],[3],[4],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1],[3],[4],[6]]) (.forbid 0 2 1 (.system [[0,7,2,1],[3],[4],[6]]) (.forbid 0 2 2 (.system [[0,7,8,2,1],[3],[4],[6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2,1],[3],[4],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2,1],[3],[4],[6]]) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2,1],[3],[4],[6]]) (.forbid 0 2 6 (.system [[0,7,8,9,10,11,12,2,1],[3],[4],[6]]) (.forbid 0 3 1 (.system [[0,7,3,2,1],[4,5,6]]) (.forbid 0 4 1 (.system [[0,7,4,5,6],[1,2,3]]) (.forbid 1 2 1 (.system [[0],[1,7,2,3],[4],[6]]) (.forbid 1 2 2 (.system [[0],[1,7,8,2,3],[4],[6]]) (.forbid 1 2 3 (.system [[0],[1,7,8,9,2,3],[4],[6]]) (.forbid 1 2 4 (.system [[0],[1,7,8,9,10,2,3],[4],[6]]) (.forbid 1 2 5 (.system [[0],[1,7,8,9,10,11,2,3],[4],[6]]) (.forbid 1 2 6 (.system [[0],[1,7,8,9,10,11,12,2,3],[4],[6]]) (certificate_69_part_0))))))))))))))))))))

noncomputable def certificate_73 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1],[2],[3],[4],[5]]) (.forbid 0 1 2 (.system [[0,6,7,1],[2],[3],[4],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1],[2],[3],[4],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[2],[3],[4],[5]]) (.forbid 0 1 5 (.system [[0,6,7,8,9,10,1],[2],[3],[4],[5]]) (.forbid 0 1 6 (.system [[0,6,7,8,9,10,11,1],[2],[3],[4],[5]]) (.forbid 0 2 1 (.system [[0,6,2],[1],[3],[4],[5]]) (.forbid 0 2 2 (.system [[0,6,7,2],[1],[3],[4],[5]]) (.forbid 0 2 3 (.system [[0,6,7,8,2],[1],[3],[4],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2],[1],[3],[4],[5]]) (.forbid 0 2 5 (.system [[0,6,7,8,9,10,2],[1],[3],[4],[5]]) (.forbid 0 2 6 (.system [[0,6,7,8,9,10,11,2],[1],[3],[4],[5]]) (.forbid 0 3 1 (.system [[0,6,3],[1],[2],[4],[5]]) (.forbid 0 4 1 (.system [[0,6,4],[1],[2],[3],[5]]) (.forbid 1 2 1 (.system [[0],[1,6,2],[3],[4],[5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2],[3],[4],[5]]) (.forbid 1 2 3 (.system [[0],[1,6,7,8,2],[3],[4],[5]]) (.forbid 1 2 4 (.system [[0],[1,6,7,8,9,2],[3],[4],[5]]) (.forbid 1 2 5 (.system [[0],[1,6,7,8,9,10,2],[3],[4],[5]]) (.forbid 1 2 6 (.system [[0],[1,6,7,8,9,10,11,2],[3],[4],[5]]) (certificate_73_part_0))))))))))))))))))))

noncomputable def certificate_74 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1],[2],[3],[4,5,6]]) (.forbid 0 1 2 (.system [[0,7,8,1],[2],[3],[4],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1],[2],[3],[4],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1],[2],[3],[4],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1],[2],[3],[4],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1],[2],[3],[4],[6]]) (.forbid 0 2 1 (.system [[0,7,2],[1],[3],[4,5,6]]) (.forbid 0 2 2 (.system [[0,7,8,2],[1],[3],[4],[6]]) (.forbid 0 2 3 (.system [[0,7,8,9,2],[1],[3],[4],[6]]) (.forbid 0 2 4 (.system [[0,7,8,9,10,2],[1],[3],[4],[6]]) (.forbid 0 2 5 (.system [[0,7,8,9,10,11,2],[1],[3],[4],[6]]) (.forbid 0 2 6 (.system [[0,7,8,9,10,11,12,2],[1],[3],[4],[6]]) (.forbid 0 3 1 (.system [[0,7,3],[1],[2],[4,5,6]]) (.forbid 0 3 2 (.system [[0,7,8,3],[1],[2],[4],[6]]) (.forbid 0 4 1 (.system [[0,7,4,5,6],[1],[2],[3]]) (.forbid 0 5 1 (.system [[0,7,5,4],[1],[2],[3],[6]]) (.forbid 1 2 1 (.system [[0],[1,7,2],[3],[4,5,6]]) (.forbid 1 2 2 (.system [[0],[1,7,8,2],[3],[4],[6]]) (.forbid 1 2 3 (.system [[0],[1,7,8,9,2],[3],[4],[6]]) (.forbid 1 2 4 (.system [[0],[1,7,8,9,10,2],[3],[4],[6]]) (certificate_74_part_0))))))))))))))))))))

noncomputable def certificate_81 : FiniteCertificate := .forbid 0 1 1 (.system [[0,4,1],[2],[3]]) (.forbid 0 1 2 (.system [[0,4,5,1],[2],[3]]) (.forbid 0 1 3 (.system [[0,4,5,6,1],[2],[3]]) (.forbid 0 1 4 (.system [[0,4,5,6,7,1],[2],[3]]) (.forbid 0 2 1 (.system [[0,4,2],[1],[3]]) (.forbid 0 2 2 (.system [[0,4,5,2],[1],[3]]) (.forbid 0 2 3 (.system [[0,4,5,6,2],[1],[3]]) (.forbid 0 2 4 (.system [[0,4,5,6,7,2],[1],[3]]) (.forbid 0 3 1 (.system [[0,4,3],[1],[2]]) (.forbid 0 3 2 (.system [[0,4,5,3],[1],[2]]) (.forbid 0 3 3 (.system [[0,4,5,6,3],[1],[2]]) (.forbid 0 3 4 (.system [[0,4,5,6,7,3],[1],[2]]) (.forbid 1 2 1 (.system [[0],[1,4,2],[3]]) (.forbid 1 2 2 (.system [[0],[1,4,5,2],[3]]) (.forbid 1 2 3 (.system [[0],[1,4,5,6,2],[3]]) (.forbid 1 2 4 (.system [[0],[1,4,5,6,7,2],[3]]) (.forbid 1 3 1 (.system [[0],[1,4,3],[2]]) (.forbid 1 3 2 (.system [[0],[1,4,5,3],[2]]) (.forbid 1 3 3 (.system [[0],[1,4,5,6,3],[2]]) (.forbid 1 3 4 (.system [[0],[1,4,5,6,7,3],[2]]) (certificate_81_part_0))))))))))))))))))))

noncomputable def certificate_82 : FiniteCertificate := .forbid 0 1 1 (.system [[0,5,1],[2,3,4]]) (.forbid 0 1 2 (.system [[0,5,6,1],[2],[4]]) (.forbid 0 1 3 (.system [[0,5,6,7,1],[2],[4]]) (.forbid 0 1 4 (.system [[0,5,6,7,8,1],[2],[4]]) (.forbid 0 2 1 (.system [[0,5,2,3,4],[1]]) (.forbid 0 2 2 (.system [[0,5,6,2],[1],[4]]) (.forbid 0 2 3 (.system [[0,5,6,7,2],[1],[4]]) (.forbid 0 2 4 (.system [[0,5,6,7,8,2],[1],[4]]) (.forbid 0 3 1 (.system [[0,5,3,2],[1],[4]]) (.forbid 0 3 2 (.system [[0,5,6,3,2],[1],[4]]) (.forbid 0 3 3 (.system [[0,5,6,7,3,2],[1],[4]]) (.forbid 0 3 4 (.system [[0,5,6,7,8,3,2],[1],[4]]) (.forbid 1 2 1 (.system [[0],[1,5,2,3,4]]) (.forbid 1 2 2 (.system [[0],[1,5,6,2],[4]]) (.forbid 1 2 3 (.system [[0],[1,5,6,7,2],[4]]) (.forbid 1 2 4 (.system [[0],[1,5,6,7,8,2],[4]]) (.forbid 1 3 1 (.system [[0],[1,5,3,2],[4]]) (.forbid 1 3 2 (.system [[0],[1,5,6,3,2],[4]]) (.forbid 1 3 3 (.system [[0],[1,5,6,7,3,2],[4]]) (.forbid 1 3 4 (.system [[0],[1,5,6,7,8,3,2],[4]]) (certificate_82_part_0))))))))))))))))))))

noncomputable def certificate_83 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1],[2,3,4,5]]) (.forbid 0 1 2 (.system [[0,6,7,1],[2,3,4,5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1],[2],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1],[2],[5]]) (.forbid 0 2 1 (.system [[0,6,2,3,4,5],[1]]) (.forbid 0 2 2 (.system [[0,6,7,2,3,4,5],[1]]) (.forbid 0 2 3 (.system [[0,6,7,8,2],[1],[5]]) (.forbid 0 2 4 (.system [[0,6,7,8,9,2],[1],[5]]) (.forbid 0 3 1 (.system [[0,6,3,4,5],[1],[2]]) (.forbid 0 3 2 (.system [[0,6,7,3,2],[1],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3,2],[1],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3,2],[1],[5]]) (.forbid 1 2 1 (.system [[0],[1,6,2,3,4,5]]) (.forbid 1 2 2 (.system [[0],[1,6,7,2,3,4,5]]) (.forbid 1 2 3 (.system [[0],[1,6,7,8,2],[5]]) (.forbid 1 2 4 (.system [[0],[1,6,7,8,9,2],[5]]) (.forbid 1 3 1 (.system [[0],[1,6,3,4,5],[2]]) (.forbid 1 3 2 (.system [[0],[1,6,7,3,2],[5]]) (.forbid 1 3 3 (.system [[0],[1,6,7,8,3,2],[5]]) (.forbid 1 3 4 (.system [[0],[1,6,7,8,9,3,2],[5]]) (certificate_83_part_0))))))))))))))))))))

noncomputable def certificate_85_part_1_M : ForbiddenMatrix := ((0,2,5) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (((0,1,6) :: (((0,1,5) :: (((0,1,2) :: (((0,1,1) :: (certificate_85_M))))))))))))))))

noncomputable def certificate_85_part_2_M : ForbiddenMatrix := ((1,2,1) :: (((0,3,6) :: (((0,3,5) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,2,6) :: (certificate_85_part_1_M))))))))))))))))

noncomputable def certificate_85_part_3_M : ForbiddenMatrix := ((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,6) :: (((1,2,5) :: (((1,2,3) :: (((1,2,2) :: (certificate_85_part_2_M))))))))))))))))

noncomputable def certificate_85_part_4_M : ForbiddenMatrix := ((0,1,3) :: (((2,3,4) :: (((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,3,6) :: (((1,3,5) :: (certificate_85_part_3_M))))))))))))))

noncomputable def certificate_85_part_5_M : ForbiddenMatrix := ((0,6,1) :: (((0,4,0) :: (((2,3,4) :: (((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,3,6) :: (((1,3,5) :: (certificate_85_part_3_M))))))))))))))))

noncomputable def certificate_85_part_6_M : ForbiddenMatrix := ((1,6,3) :: (((1,6,2) :: (((1,6,1) :: (((0,6,6) :: (((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (certificate_85_part_5_M))))))))))))))))

noncomputable def certificate_85_part_7_M : ForbiddenMatrix := ((5,6,1) :: (((3,6,6) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((1,6,6) :: (((1,6,5) :: (((1,6,4) :: (certificate_85_part_6_M))))))))))))))))

noncomputable def certificate_85_part_8_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,4) :: (((0,1,3) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (certificate_85_part_7_M))))))))))))))

noncomputable def certificate_85_part_9_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((0,5,0) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (certificate_85_part_7_M))))))))))))))

noncomputable def certificate_85_part_10_M : ForbiddenMatrix := ((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((0,5,0) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (certificate_85_part_7_M))))))))))))))))

noncomputable def certificate_85_part_11_M : ForbiddenMatrix := ((0,2,4) :: (((0,1,4) :: (((0,1,3) :: (((1,4,2) :: (((1,4,1) :: (((1,4,0) :: (((0,5,4) :: (certificate_85_part_10_M))))))))))))))

noncomputable def certificate_85_part_12_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((1,5,0) :: (((1,4,2) :: (((1,4,1) :: (((1,4,0) :: (((0,5,4) :: (certificate_85_part_10_M))))))))))))))

noncomputable def certificate_85_part_13_M : ForbiddenMatrix := ((4,5,1) :: (((1,5,2) :: (((1,5,1) :: (((1,5,0) :: (((1,4,2) :: (((1,4,1) :: (((1,4,0) :: (((0,5,4) :: (certificate_85_part_10_M))))))))))))))))

noncomputable def certificate_85_part_10 : FiniteCertificate := .forbid 0 5 4 (.system [[0,8,9,10,11,5,4,3,2],[1],[7]]) (.forbid 1 4 0 (.forbid 0 1 3 (.cycle [0,2,7,6,5,4,1,10,9,8]) (.forbid 0 1 4 (.cycle [0,7,2,3,4,1,11,10,9,8]) (.forbid 0 2 4 (.cycle [0,7,1,4,3,2,11,10,9,8]) (.forbid 1 2 4 (.cycle [1,4,5,6,7,2,11,10,9,8]) (.forbid 2 3 5 (.cycle [2,0,1,4,3,12,11,10,9,8]) (.forbid 2 3 6 (.cycle [2,1,4,3,13,12,11,10,9,8]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 2 1) {1,2,3} 5 2) ∅ 11 3), .ball 1 (.succ (.succ (.zero ∅ 2 1) {0,2,3} 5 2) ∅ 11 3), .ball 2 (.succ (.succ (.zero ∅ 2 1) {0,1,3} 5 2) ∅ 11 3), .ball 3 (.succ (.succ (.zero ∅ 2 1) {0,1,2} 5 2) ∅ 11 3)}))))))) (.forbid 1 4 1 (.forbid 0 1 3 (.cycle [0,7,2,3,4,8,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,2,3,4,8,1,12,11,10,9]) (.forbid 3 6 1 (.cycle [3,2,0,7,1,8,4,5,6,9]) (.forbid 3 6 2 (.cycle [3,2,0,1,8,4,5,6,10,9]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,6} 5 2) ∅ 10 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,6} 5 2) ∅ 10 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,6} 5 2) ∅ 10 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,3,5} 5 2) ∅ 10 3)}))))) (.forbid 1 4 2 (.system [[0],[1,8,9,4,5,6,7],[2]]) (.forbid 1 5 0 (.forbid 0 1 3 (.cycle [0,7,2,3,4,5,1,10,9,8]) (.forbid 0 1 4 (.cycle [0,2,3,4,5,1,11,10,9,8]) (.forbid 0 2 4 (.cycle [0,1,5,4,3,2,11,10,9,8]) (certificate_85_part_11)))) (.forbid 1 5 1 (.forbid 0 1 3 (.cycle [0,2,3,4,5,8,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,7,6,5,8,1,12,11,10,9]) (certificate_85_part_12))) (.forbid 1 5 2 (.system [[0],[1,8,9,5,4,3,2],[7]]) (.forbid 4 5 1 (.system [[0],[1],[2,3,4,8,5,6,7]]) (certificate_85_part_13))))))))

noncomputable def certificate_85_part_7 : FiniteCertificate := .forbid 0 4 1 (.forbid 0 1 3 (.cycle [0,8,4,3,2,7,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,8,4,3,2,1,12,11,10,9]) (.forbid 3 6 1 (.cycle [3,2,1,7,0,8,4,5,6,9]) (.forbid 3 6 2 (.cycle [3,2,1,0,8,4,5,6,10,9]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,3,6} 5 2) ∅ 10 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,3,6} 5 2) ∅ 10 3), .ball 3 (.succ (.succ (.zero ∅ 1 1) {0,1,2,6} 5 2) ∅ 10 3), .ball 6 (.succ (.succ (.zero ∅ 1 1) {0,1,3,5} 5 2) ∅ 10 3)}))))) (.forbid 0 4 2 (.system [[0,8,9,4,5,6,7],[1],[2]]) (.forbid 0 4 3 (.system [[0,8,9,10,4,3,2],[1],[7]]) (.forbid 0 4 4 (.system [[0,8,9,10,11,4,3,2],[1],[7]]) (.forbid 0 5 0 (.forbid 0 1 3 (.cycle [0,5,4,3,2,7,1,10,9,8]) (.forbid 0 1 4 (.cycle [0,5,4,3,2,1,11,10,9,8]) (.forbid 0 2 4 (.cycle [0,5,6,7,1,2,11,10,9,8]) (certificate_85_part_8)))) (.forbid 0 5 1 (.forbid 0 1 3 (.cycle [0,8,5,4,3,2,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,8,5,6,7,1,12,11,10,9]) (certificate_85_part_9))) (.forbid 0 5 2 (.system [[0,8,9,5,4,3,2],[1],[7]]) (.forbid 0 5 3 (.system [[0,8,9,10,5,4,3,2],[1],[7]]) (certificate_85_part_10))))))))

noncomputable def certificate_85_part_6 : FiniteCertificate := .forbid 1 6 4 (.system [[0],[1,8,9,10,11,6,5,4,3,2],[7]]) (.forbid 1 6 5 (.system [[0],[1,8,9,10,11,12,6,7],[2]]) (.forbid 1 6 6 (.system [[0],[1,8,9,10,11,12,13,6,7],[2]]) (.forbid 3 6 3 (.system [[0],[1],[2,3,8,9,10,6,7]]) (.forbid 3 6 4 (.system [[0],[1],[2,3,8,9,10,11,6,7]]) (.forbid 3 6 5 (.system [[0],[1],[2,3,8,9,10,11,12,6,7]]) (.forbid 3 6 6 (.system [[0],[1],[2,3,8,9,10,11,12,13,6,7]]) (.forbid 5 6 1 (.system [[0],[1],[2,3,4,5,8,6,7]]) (certificate_85_part_7))))))))

noncomputable def certificate_85_part_5 : FiniteCertificate := .forbid 0 6 2 (.system [[0,8,9,6,5,4,3,2],[1],[7]]) (.forbid 0 6 3 (.system [[0,8,9,10,6,5,4,3,2],[1],[7]]) (.forbid 0 6 4 (.system [[0,8,9,10,11,6,5,4,3,2],[1],[7]]) (.forbid 0 6 5 (.system [[0,8,9,10,11,12,6,7],[1],[2]]) (.forbid 0 6 6 (.system [[0,8,9,10,11,12,13,6,7],[1],[2]]) (.forbid 1 6 1 (.system [[0],[1,8,6,5,4,3,2],[7]]) (.forbid 1 6 2 (.system [[0],[1,8,9,6,5,4,3,2],[7]]) (.forbid 1 6 3 (.system [[0],[1,8,9,10,6,5,4,3,2],[7]]) (certificate_85_part_6))))))))

noncomputable def certificate_85_part_3 : FiniteCertificate := .forbid 1 3 5 (.system [[0],[1,8,9,10,11,12,3,2],[7]]) (.forbid 1 3 6 (.system [[0],[1,8,9,10,11,12,13,3,2],[7]]) (.forbid 2 3 1 (.system [[0],[1],[2,8,3,4,5,6,7]]) (.forbid 2 3 2 (.system [[0],[1],[2,8,9,3,4,5,6,7]]) (.forbid 2 3 3 (.system [[0],[1],[2,8,9,10,3,4,5,6,7]]) (.forbid 2 3 4 (.system [[0],[1],[2,8,9,10,11,3,4,5,6,7]]) (.forbid 0 4 0 (.forbid 0 1 3 (.cycle [0,4,5,6,7,2,1,10,9,8]) (certificate_85_part_4)) (.forbid 0 6 1 (.system [[0,8,6,5,4,3,2],[1],[7]]) (certificate_85_part_5))))))))

noncomputable def certificate_85_part_2 : FiniteCertificate := .forbid 1 2 2 (.system [[0],[1,8,9,2,3,4,5,6,7]]) (.forbid 1 2 3 (.system [[0],[1,8,9,10,2,3,4,5,6,7]]) (.forbid 1 2 5 (.system [[0],[1,8,9,10,11,12,2],[7]]) (.forbid 1 2 6 (.system [[0],[1,8,9,10,11,12,13,2],[7]]) (.forbid 1 3 1 (.system [[0],[1,8,3,4,5,6,7],[2]]) (.forbid 1 3 2 (.system [[0],[1,8,9,3,4,5,6,7],[2]]) (.forbid 1 3 3 (.system [[0],[1,8,9,10,3,4,5,6,7],[2]]) (.forbid 1 3 4 (.system [[0],[1,8,9,10,11,3,2],[7]]) (certificate_85_part_3))))))))

noncomputable def certificate_85_part_1 : FiniteCertificate := .forbid 0 2 6 (.system [[0,8,9,10,11,12,13,2],[1],[7]]) (.forbid 0 3 1 (.system [[0,8,3,4,5,6,7],[1],[2]]) (.forbid 0 3 2 (.system [[0,8,9,3,4,5,6,7],[1],[2]]) (.forbid 0 3 3 (.system [[0,8,9,10,3,4,5,6,7],[1],[2]]) (.forbid 0 3 4 (.system [[0,8,9,10,11,3,2],[1],[7]]) (.forbid 0 3 5 (.system [[0,8,9,10,11,12,3,2],[1],[7]]) (.forbid 0 3 6 (.system [[0,8,9,10,11,12,13,3,2],[1],[7]]) (.forbid 1 2 1 (.system [[0],[1,8,2,3,4,5,6,7]]) (certificate_85_part_2))))))))

noncomputable def certificate_85 : FiniteCertificate := .forbid 0 1 1 (.system [[0,8,1],[2,3,4,5,6,7]]) (.forbid 0 1 2 (.system [[0,8,9,1],[2,3,4,5,6,7]]) (.forbid 0 1 5 (.system [[0,8,9,10,11,12,1],[2],[7]]) (.forbid 0 1 6 (.system [[0,8,9,10,11,12,13,1],[2],[7]]) (.forbid 0 2 1 (.system [[0,8,2,3,4,5,6,7],[1]]) (.forbid 0 2 2 (.system [[0,8,9,2,3,4,5,6,7],[1]]) (.forbid 0 2 3 (.system [[0,8,9,10,2,3,4,5,6,7],[1]]) (.forbid 0 2 5 (.system [[0,8,9,10,11,12,2],[1],[7]]) (certificate_85_part_1))))))))

noncomputable def certificate_86_part_1_M : ForbiddenMatrix := ((0,7,1) :: (((0,1,6) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,2,2) :: (((0,2,1) :: (((0,1,1) :: (certificate_86_M))))))))))))))))

noncomputable def certificate_86_part_2_M : ForbiddenMatrix := ((1,3,3) :: (((1,3,2) :: (((1,3,1) :: (((1,2,1) :: (((0,7,6) :: (((0,7,5) :: (((0,7,3) :: (((0,7,2) :: (certificate_86_part_1_M))))))))))))))))

noncomputable def certificate_86_part_3_M : ForbiddenMatrix := ((0,1,2) :: (((6,7,1) :: (((1,7,6) :: (((1,7,5) :: (((1,7,3) :: (((1,7,2) :: (((1,7,1) :: (certificate_86_part_2_M))))))))))))))

noncomputable def certificate_86_part_4_M : ForbiddenMatrix := ((0,4,0) :: (((6,7,1) :: (((1,7,6) :: (((1,7,5) :: (((1,7,3) :: (((1,7,2) :: (((1,7,1) :: (certificate_86_part_2_M))))))))))))))

noncomputable def certificate_86_part_5_M : ForbiddenMatrix := ((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,7,4) :: (((0,3,0) :: (((0,1,3) :: (((0,1,2) :: (certificate_86_part_4_M))))))))))))))))

noncomputable def certificate_86_part_6_M : ForbiddenMatrix := ((3,7,1) :: (((3,7,0) :: (((2,9,0) :: (((2,7,1) :: (((1,9,2) :: (((1,9,1) :: (((1,9,0) :: (((0,9,5) :: (certificate_86_part_5_M))))))))))))))))

noncomputable def certificate_86_part_7_M : ForbiddenMatrix := ((0,4,1) :: (((0,4,0) :: (((6,7,1) :: (((1,7,6) :: (((1,7,5) :: (((1,7,3) :: (((1,7,2) :: (((1,7,1) :: (certificate_86_part_2_M))))))))))))))))

noncomputable def certificate_86_part_8_M : ForbiddenMatrix := ((0,1,3) :: (((0,1,2) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (((0,2,6) :: (((0,4,2) :: (certificate_86_part_7_M))))))))))))))

noncomputable def certificate_86_part_9_M : ForbiddenMatrix := ((2,3,2) :: (((2,3,1) :: (((1,4,0) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (((0,2,6) :: (((0,4,2) :: (certificate_86_part_7_M))))))))))))))))

noncomputable def certificate_86_part_10_M : ForbiddenMatrix := ((0,1,3) :: (((0,1,2) :: (((1,3,6) :: (((1,3,5) :: (((0,3,6) :: (((0,3,5) :: (((2,3,3) :: (certificate_86_part_9_M))))))))))))))

noncomputable def certificate_86_part_11_M : ForbiddenMatrix := ((3,4,1) :: (((0,6,0) :: (((1,3,6) :: (((1,3,5) :: (((0,3,6) :: (((0,3,5) :: (((2,3,3) :: (certificate_86_part_9_M))))))))))))))

noncomputable def certificate_86_part_12_M : ForbiddenMatrix := ((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,5,0) :: (((0,3,4) :: (((0,1,3) :: (((0,1,2) :: (certificate_86_part_11_M))))))))))))))))

noncomputable def certificate_86_part_13_M : ForbiddenMatrix := ((3,9,2) :: (((3,9,1) :: (((3,9,0) :: (((2,9,0) :: (((1,9,2) :: (((1,9,1) :: (((1,9,0) :: (((0,9,5) :: (certificate_86_part_12_M))))))))))))))))

noncomputable def certificate_86_part_14_M : ForbiddenMatrix := ((0,6,1) :: (((3,4,1) :: (((0,6,0) :: (((1,3,6) :: (((1,3,5) :: (((0,3,6) :: (((0,3,5) :: (((2,3,3) :: (certificate_86_part_9_M))))))))))))))))

noncomputable def certificate_86_part_15_M : ForbiddenMatrix := ((1,8,2) :: (((1,8,1) :: (((0,8,2) :: (((0,8,1) :: (((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (certificate_86_part_14_M))))))))))))))))

noncomputable def certificate_86_part_16_M : ForbiddenMatrix := ((0,5,0) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((7,8,3) :: (((7,8,2) :: (((7,8,1) :: (certificate_86_part_15_M))))))))))))))

noncomputable def certificate_86_part_17_M : ForbiddenMatrix := ((1,7,0) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,8,4) :: (((0,8,3) :: (((0,7,4) :: (((0,7,0) :: (certificate_86_part_16_M))))))))))))))))

noncomputable def certificate_86_part_18_M : ForbiddenMatrix := ((5,8,0) :: (((3,9,0) :: (((3,8,1) :: (((3,7,2) :: (((3,7,1) :: (((3,7,0) :: (((2,7,0) :: (((1,9,1) :: (certificate_86_part_17_M))))))))))))))))

noncomputable def certificate_86_part_19_M : ForbiddenMatrix := ((0,7,4) :: (((0,5,0) :: (((4,7,3) :: (((1,6,1) :: (((7,8,3) :: (((7,8,2) :: (((7,8,1) :: (certificate_86_part_15_M))))))))))))))

noncomputable def certificate_86_part_20_M : ForbiddenMatrix := ((3,7,0) :: (((1,9,0) :: (((0,9,5) :: (((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,9,0) :: (certificate_86_part_19_M))))))))))))))))

noncomputable def certificate_86_part_21_M : ForbiddenMatrix := ((7,9,1) :: (((5,9,0) :: (((4,9,2) :: (((4,9,1) :: (((4,7,2) :: (((4,7,1) :: (((3,9,0) :: (((3,7,1) :: (certificate_86_part_20_M))))))))))))))))

noncomputable def certificate_86_part_22_M : ForbiddenMatrix := ((0,5,4) :: (((0,5,3) :: (((2,6,1) :: (((4,7,3) :: (((1,6,1) :: (((7,8,3) :: (((7,8,2) :: (((7,8,1) :: (certificate_86_part_15_M))))))))))))))))

noncomputable def certificate_86_part_23_M : ForbiddenMatrix := ((0,5,2) :: (((0,5,1) :: (((0,5,0) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((0,5,5) :: (certificate_86_part_22_M))))))))))))))

noncomputable def certificate_86_part_24_M : ForbiddenMatrix := ((1,9,0) :: (((1,5,0) :: (((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,9,0) :: (((0,7,4) :: (certificate_86_part_23_M))))))))))))))))

noncomputable def certificate_86_part_25_M : ForbiddenMatrix := ((5,9,2) :: (((5,9,1) :: (((5,9,0) :: (((5,7,1) :: (((4,7,1) :: (((4,7,0) :: (((2,9,0) :: (((2,5,0) :: (certificate_86_part_24_M))))))))))))))))

noncomputable def certificate_86_part_26_M : ForbiddenMatrix := ((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((3,6,1) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((0,5,5) :: (certificate_86_part_22_M))))))))))))))))

noncomputable def certificate_86_part_27_M : ForbiddenMatrix := ((3,5,0) :: (((1,3,0) :: (((0,9,2) :: (((0,9,1) :: (((0,9,0) :: (((0,3,4) :: (((0,3,0) :: (certificate_86_part_26_M))))))))))))))

noncomputable def certificate_86_part_28_M : ForbiddenMatrix := ((3,6,6) :: (((0,6,6) :: (((3,4,2) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (certificate_86_part_26_M))))))))))))))

noncomputable def certificate_86_part_29_M : ForbiddenMatrix := ((4,7,0) :: (((3,6,6) :: (((0,6,6) :: (((3,4,2) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (certificate_86_part_26_M))))))))))))))))

noncomputable def certificate_86_part_30_M : ForbiddenMatrix := ((0,2,4) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((1,2,2) :: (((0,5,0) :: (certificate_86_part_29_M))))))))))))))

noncomputable def certificate_86_part_31_M : ForbiddenMatrix := ((2,5,0) :: (((1,9,1) :: (((1,3,0) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,3,4) :: (((0,3,0) :: (certificate_86_part_30_M))))))))))))))))

noncomputable def certificate_86_part_32_M : ForbiddenMatrix := ((3,9,2) :: (((3,9,1) :: (((3,7,2) :: (((3,7,1) :: (((3,7,0) :: (((3,5,0) :: (((2,9,1) :: (((2,7,1) :: (certificate_86_part_31_M))))))))))))))))

noncomputable def certificate_86_part_33_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,2) :: (((1,4,1) :: (((1,2,2) :: (((0,5,0) :: (certificate_86_part_29_M))))))))))))))

noncomputable def certificate_86_part_34_M : ForbiddenMatrix := ((3,7,6) :: (((3,7,5) :: (((3,7,4) :: (((3,4,3) :: (((1,6,0) :: (((1,4,1) :: (((1,2,2) :: (((0,5,0) :: (certificate_86_part_29_M))))))))))))))))

noncomputable def certificate_86_part_35_M : ForbiddenMatrix := ((0,9,0) :: (((0,5,2) :: (((0,5,1) :: (((0,3,4) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_86_part_34_M))))))))))))))

noncomputable def certificate_86_part_36_M : ForbiddenMatrix := ((3,9,0) :: (((3,5,1) :: (((1,9,0) :: (((1,5,0) :: (((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (certificate_86_part_35_M))))))))))))))))

noncomputable def certificate_86_part_37_M : ForbiddenMatrix := ((3,7,1) :: (((0,7,4) :: (((0,3,4) :: (((4,7,1) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_86_part_34_M))))))))))))))

noncomputable def certificate_86_part_38_M : ForbiddenMatrix := ((4,7,4) :: (((6,7,3) :: (((6,7,2) :: (((2,6,0) :: (((4,7,1) :: (((3,5,4) :: (((3,5,3) :: (((3,5,2) :: (certificate_86_part_34_M))))))))))))))))

noncomputable def certificate_86_part_39_M : ForbiddenMatrix := ((1,7,0) :: (((0,9,2) :: (((0,9,1) :: (((0,9,0) :: (((0,7,4) :: (((0,7,0) :: (((4,7,5) :: (certificate_86_part_38_M))))))))))))))

noncomputable def certificate_86_part_40_M : ForbiddenMatrix := ((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((2,5,0) :: (((6,8,2) :: (((6,8,1) :: (((4,7,5) :: (certificate_86_part_38_M))))))))))))))

noncomputable def certificate_86_part_41_M : ForbiddenMatrix := ((0,5,1) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((2,5,0) :: (((6,8,2) :: (((6,8,1) :: (((4,7,5) :: (certificate_86_part_38_M))))))))))))))))

noncomputable def certificate_86_part_42_M : ForbiddenMatrix := ((3,7,1) :: (((3,6,0) :: (((2,7,1) :: (((0,7,4) :: (((0,3,4) :: (((0,1,3) :: (((0,1,2) :: (certificate_86_part_41_M))))))))))))))

noncomputable def certificate_86_part_43_M : ForbiddenMatrix := ((0,5,2) :: (((0,3,4) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((3,5,1) :: (((1,5,1) :: (certificate_86_part_41_M))))))))))))))

noncomputable def certificate_86_part_44_M : ForbiddenMatrix := ((4,7,6) :: (((0,4,6) :: (((2,7,0) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((3,5,1) :: (((1,5,1) :: (certificate_86_part_41_M))))))))))))))))

noncomputable def certificate_86_part_45_M : ForbiddenMatrix := ((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,9,0) :: (((0,3,4) :: (((0,2,3) :: (((3,5,0) :: (certificate_86_part_44_M))))))))))))))

noncomputable def certificate_86_part_46_M : ForbiddenMatrix := ((3,9,1) :: (((3,9,0) :: (((3,7,0) :: (((2,9,2) :: (((2,9,1) :: (((1,9,0) :: (((0,9,5) :: (((0,9,4) :: (certificate_86_part_45_M))))))))))))))))

noncomputable def certificate_86_part_47_M : ForbiddenMatrix := ((3,6,2) :: (((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (((3,6,0) :: (((4,8,1) :: (((3,5,0) :: (certificate_86_part_44_M))))))))))))))

noncomputable def certificate_86_part_48_M : ForbiddenMatrix := ((5,7,1) :: (((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (((3,6,0) :: (((4,8,1) :: (((3,5,0) :: (certificate_86_part_44_M))))))))))))))

noncomputable def certificate_86_part_49_M : ForbiddenMatrix := ((3,8,0) :: (((5,7,1) :: (((5,6,3) :: (((5,6,2) :: (((5,6,1) :: (((3,6,0) :: (((4,8,1) :: (((3,5,0) :: (certificate_86_part_44_M))))))))))))))))

noncomputable def certificate_86_part_2 : FiniteCertificate := .forbid 1 7 1 (.system [[0],[1,9,7,6,5,4,3,2],[8]]) (.forbid 1 7 2 (.system [[0],[1,9,10,7,6,5,4,3,2],[8]]) (.forbid 1 7 3 (.system [[0],[1,9,10,11,7,6,5,4,3,2],[8]]) (.forbid 1 7 5 (.system [[0],[1,9,10,11,12,13,7,8],[2]]) (.forbid 1 7 6 (.system [[0],[1,9,10,11,12,13,14,7,8],[2]]) (.forbid 6 7 1 (.system [[0],[1],[2,3,4,5,6,9,7,8]]) (.forbid 0 4 0 (.forbid 0 1 2 (.cycle [0,4,5,6,7,8,2,1,10,9]) (certificate_86_part_3)) (.forbid 0 4 1 (certificate_86_part_4) (certificate_86_part_7))))))))

noncomputable def certificate_86_part_1 : FiniteCertificate := .forbid 0 7 2 (.system [[0,9,10,7,6,5,4,3,2],[1],[8]]) (.forbid 0 7 3 (.system [[0,9,10,11,7,6,5,4,3,2],[1],[8]]) (.forbid 0 7 5 (.system [[0,9,10,11,12,13,7,8],[1],[2]]) (.forbid 0 7 6 (.system [[0,9,10,11,12,13,14,7,8],[1],[2]]) (.forbid 1 2 1 (.system [[0],[1,9,2,3,4,5,6,7,8]]) (.forbid 1 3 1 (.system [[0],[1,9,3,4,5,6,7,8],[2]]) (.forbid 1 3 2 (.system [[0],[1,9,10,3,4,5,6,7,8],[2]]) (.forbid 1 3 3 (.system [[0],[1,9,10,11,3,4,5,6,7,8],[2]]) (certificate_86_part_2))))))))

noncomputable def certificate_86 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1],[2,3,4,5,6,7,8]]) (.forbid 0 2 1 (.system [[0,9,2,3,4,5,6,7,8],[1]]) (.forbid 0 2 2 (.system [[0,9,10,2,3,4,5,6,7,8],[1]]) (.forbid 0 3 1 (.system [[0,9,3,4,5,6,7,8],[1],[2]]) (.forbid 0 3 2 (.system [[0,9,10,3,4,5,6,7,8],[1],[2]]) (.forbid 0 3 3 (.system [[0,9,10,11,3,4,5,6,7,8],[1],[2]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1],[2],[8]]) (.forbid 0 7 1 (.system [[0,9,7,6,5,4,3,2],[1],[8]]) (certificate_86_part_1))))))))

noncomputable def certificate_89 : FiniteCertificate := .forbid 0 1 1 (.system [[0,8,1,2,3,4,5,6,7]]) (.forbid 0 1 2 (.system [[0,8,9,1],[3,4,5,6,7]]) (.forbid 0 1 3 (.system [[0,8,9,10,1],[3,4,5,6,7]]) (.forbid 0 1 4 (.system [[0,8,9,10,11,1],[3],[7]]) (.forbid 0 1 5 (.system [[0,8,9,10,11,12,1],[3],[7]]) (.forbid 0 1 6 (.system [[0,8,9,10,11,12,13,1],[3],[7]]) (.forbid 0 2 1 (.system [[0,8,2,1],[3,4,5,6,7]]) (.forbid 0 2 2 (.system [[0,8,9,2,1],[3,4,5,6,7]]) (.forbid 0 2 3 (.system [[0,8,9,10,2,1],[3],[7]]) (.forbid 0 2 4 (.system [[0,8,9,10,11,2,1],[3],[7]]) (.forbid 0 2 5 (.system [[0,8,9,10,11,12,2,1],[3],[7]]) (.forbid 0 2 6 (.system [[0,8,9,10,11,12,13,2,1],[3],[7]]) (.forbid 0 4 1 (.system [[0,8,4,5,6,7],[1],[3]]) (.forbid 0 4 2 (.system [[0,8,9,4,5,6,7],[1],[3]]) (.forbid 0 4 3 (.system [[0,8,9,10,4,3],[1],[7]]) (.forbid 0 4 4 (.system [[0,8,9,10,11,4,3],[1],[7]]) (.forbid 0 4 5 (.system [[0,8,9,10,11,12,4,3],[1],[7]]) (.forbid 0 4 6 (.system [[0,8,9,10,11,12,13,4,3],[1],[7]]) (.forbid 1 2 1 (.system [[0],[1,8,2,3,4,5,6,7]]) (.forbid 1 2 2 (.system [[0],[1,8,9,2,3,4,5,6,7]]) (certificate_89_part_0))))))))))))))))))))

noncomputable def certificate_90_part_1_M : ForbiddenMatrix := ((0,1,6) :: (((0,1,5) :: (((0,1,2) :: (((0,1,1) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (certificate_90_M))))))))))))))))

noncomputable def certificate_90_part_2_M : ForbiddenMatrix := ((1,2,1) :: (((0,4,6) :: (((0,4,5) :: (((0,2,6) :: (((0,2,5) :: (((0,2,4) :: (((0,2,2) :: (((0,2,1) :: (certificate_90_part_1_M))))))))))))))))

noncomputable def certificate_90_part_3_M : ForbiddenMatrix := ((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((1,4,1) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((1,2,2) :: (certificate_90_part_2_M))))))))))))))))

noncomputable def certificate_90_part_4_M : ForbiddenMatrix := ((2,4,5) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (((2,3,1) :: (((1,4,6) :: (((1,4,5) :: (certificate_90_part_3_M))))))))))))))))

noncomputable def certificate_90_part_5_M : ForbiddenMatrix := ((1,2,3) :: (((0,6,1) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((3,4,1) :: (((2,4,6) :: (certificate_90_part_4_M))))))))))))))

noncomputable def certificate_90_part_6_M : ForbiddenMatrix := ((0,3,1) :: (((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((0,5,0) :: (((3,4,1) :: (((2,4,6) :: (certificate_90_part_4_M))))))))))))))

noncomputable def certificate_90_part_7_M : ForbiddenMatrix := ((1,6,1) :: (((1,2,3) :: (((0,9,5) :: (((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,4,0) :: (certificate_90_part_6_M))))))))))))))))

noncomputable def certificate_90_part_8_M : ForbiddenMatrix := ((2,9,1) :: (((2,9,0) :: (((1,9,5) :: (((1,9,4) :: (((1,9,3) :: (((1,9,2) :: (((1,9,1) :: (((1,9,0) :: (certificate_90_part_7_M))))))))))))))))

noncomputable def certificate_90_part_9_M : ForbiddenMatrix := ((1,7,1) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,5,1) :: (((0,5,0) :: (((3,4,1) :: (((2,4,6) :: (certificate_90_part_4_M))))))))))))))))

noncomputable def certificate_90_part_10_M : ForbiddenMatrix := ((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,1,4) :: (((0,1,3) :: (((0,6,0) :: (certificate_90_part_9_M))))))))))))))

noncomputable def certificate_90_part_11_M : ForbiddenMatrix := ((1,9,5) :: (((1,9,4) :: (((1,9,3) :: (((1,9,2) :: (((1,9,1) :: (((1,9,0) :: (((1,5,1) :: (((0,9,5) :: (certificate_90_part_10_M))))))))))))))))

noncomputable def certificate_90_part_12_M : ForbiddenMatrix := ((0,8,3) :: (((0,8,2) :: (((0,8,1) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,6,0) :: (certificate_90_part_9_M))))))))))))))))

noncomputable def certificate_90_part_13_M : ForbiddenMatrix := ((4,8,2) :: (((4,8,1) :: (((1,8,1) :: (((0,1,4) :: (((0,1,3) :: (((1,8,3) :: (((1,8,2) :: (certificate_90_part_12_M))))))))))))))

noncomputable def certificate_90_part_14_M : ForbiddenMatrix := ((0,2,3) :: (((0,1,4) :: (((0,1,3) :: (((0,7,1) :: (((0,7,0) :: (((1,8,3) :: (((1,8,2) :: (certificate_90_part_12_M))))))))))))))

noncomputable def certificate_90_part_15_M : ForbiddenMatrix := ((0,1,4) :: (((0,1,3) :: (((1,5,0) :: (((0,7,1) :: (((0,7,0) :: (((1,8,3) :: (((1,8,2) :: (certificate_90_part_12_M))))))))))))))

noncomputable def certificate_90_part_16_M : ForbiddenMatrix := ((0,3,3) :: (((0,3,2) :: (((1,6,0) :: (((1,5,0) :: (((0,7,1) :: (((0,7,0) :: (((1,8,3) :: (((1,8,2) :: (certificate_90_part_12_M))))))))))))))))

noncomputable def certificate_90_part_17_M : ForbiddenMatrix := ((3,4,3) :: (((3,4,2) :: (((2,3,6) :: (((2,3,5) :: (((2,3,4) :: (((2,3,2) :: (((0,3,6) :: (((0,3,5) :: (certificate_90_part_16_M))))))))))))))))

noncomputable def certificate_90_part_18_M : ForbiddenMatrix := ((3,4,5) :: (((2,3,3) :: (((1,3,1) :: (((0,3,4) :: (((0,3,1) :: (((0,2,3) :: (((3,4,4) :: (certificate_90_part_17_M))))))))))))))

noncomputable def certificate_90_part_19_M : ForbiddenMatrix := ((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((2,5,0) :: (((2,4,0) :: (((3,4,4) :: (certificate_90_part_17_M))))))))))))))

noncomputable def certificate_90_part_20_M : ForbiddenMatrix := ((4,6,0) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((2,5,0) :: (((2,4,0) :: (((3,4,4) :: (certificate_90_part_17_M))))))))))))))))

noncomputable def certificate_90_part_21_M : ForbiddenMatrix := ((5,7,2) :: (((2,7,1) :: (((0,7,6) :: (((0,7,5) :: (((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,5,5) :: (certificate_90_part_20_M))))))))))))))))

noncomputable def certificate_90_part_22_M : ForbiddenMatrix := ((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,9,0) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (certificate_90_part_21_M))))))))))))))

noncomputable def certificate_90_part_23_M : ForbiddenMatrix := ((5,9,1) :: (((5,7,1) :: (((5,7,0) :: (((3,9,0) :: (((3,5,0) :: (((2,9,0) :: (((1,9,0) :: (((0,9,4) :: (certificate_90_part_22_M))))))))))))))))

noncomputable def certificate_90_part_24_M : ForbiddenMatrix := ((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((4,6,1) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (certificate_90_part_21_M))))))))))))))

noncomputable def certificate_90_part_25_M : ForbiddenMatrix := ((4,7,0) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((4,6,1) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (certificate_90_part_21_M))))))))))))))))

noncomputable def certificate_90_part_12 : FiniteCertificate := .forbid 1 8 2 (.system [[0],[1,9,10,8,7,6,5,4,3]]) (.forbid 1 8 3 (.system [[0],[1,9,10,11,8,7,6,5,4,3]]) (.forbid 0 7 0 (.forbid 0 1 3 (.cycle [0,7,6,5,4,3,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,7,8,3,2,1,12,11,10,9]) (.forbid 1 8 1 (.cycle [1,2,3,4,5,6,7,0,8,9]) (.forbid 4 8 1 (.cycle [4,5,6,7,0,1,2,3,8,9]) (.forbid 4 8 2 (.cycle [4,5,6,7,0,1,3,8,10,9]) (certificate_90_part_13)))))) (.forbid 0 7 1 (.system [[0,9,7,6,5,4,3],[1],[8]]) (.forbid 1 5 0 (.forbid 0 1 3 (.cycle [0,3,8,7,6,5,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,8,3,4,5,1,12,11,10,9]) (.forbid 0 2 3 (.cycle [0,8,1,5,4,3,2,11,10,9]) (certificate_90_part_14)))) (.forbid 1 6 0 (.forbid 0 1 3 (.cycle [0,8,3,4,5,6,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,3,4,5,6,1,12,11,10,9]) (certificate_90_part_15))) (.forbid 0 3 2 (.system [[0,9,10,3,4,5,6,7,8],[1]]) (.forbid 0 3 3 (.system [[0,9,10,11,3,4,5,6,7,8],[1]]) (certificate_90_part_16))))))))

noncomputable def certificate_90_part_9 : FiniteCertificate := .forbid 0 6 0 (.forbid 0 1 3 (.cycle [0,6,5,4,3,2,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,6,5,4,3,1,12,11,10,9]) (.forbid 0 2 3 (.cycle [0,6,5,4,3,1,2,11,10,9]) (.forbid 1 2 3 (.cycle [1,0,6,5,4,3,2,11,10,9]) (.packing {.ball 0 (.succ (.succ (.zero ∅ 1 1) {1,2,4,5} 5 2) ∅ 10 3), .ball 1 (.succ (.succ (.zero ∅ 1 1) {0,2,4,7} 5 2) ∅ 10 3), .ball 2 (.succ (.succ (.zero ∅ 1 1) {0,1,3,4} 5 2) ∅ 10 3), .ball 4 (.succ (.succ (.zero ∅ 1 1) {0,1,2,3} 5 2) ∅ 10 3)}))))) (.forbid 0 6 1 (.forbid 0 1 3 (.cycle [0,9,6,5,4,3,1,12,11,10]) (.forbid 0 1 4 (.cycle [0,9,6,7,8,1,13,12,11,10]) (.forbid 0 9 1 (.cycle [0,8,1,2,3,4,5,6,9,10]) (.forbid 0 9 2 (.cycle [0,1,2,3,4,5,6,9,11,10]) (.forbid 0 9 3 (.cycle [0,1,3,4,5,6,9,12,11,10]) (.forbid 0 9 4 (.cycle [0,1,8,7,6,9,13,12,11,10]) (certificate_90_part_10))))))) (.forbid 0 6 2 (.system [[0,9,10,6,5,4,3],[1],[8]]) (.forbid 0 6 3 (.system [[0,9,10,11,6,5,4,3],[1],[8]]) (.forbid 0 6 4 (.system [[0,9,10,11,12,6,5,4,3],[1],[8]]) (.forbid 0 8 1 (.system [[0,9,8,7,6,5,4,3,2,1]]) (.forbid 0 8 2 (.system [[0,9,10,8,7,6,5,4,3],[1]]) (.forbid 0 8 3 (.system [[0,9,10,11,8,7,6,5,4,3],[1]]) (certificate_90_part_12))))))))

noncomputable def certificate_90_part_4 : FiniteCertificate := .forbid 2 4 6 (.system [[0],[1,2,9,10,11,12,13,14,4,3],[8]]) (.forbid 3 4 1 (.system [[0],[1],[3,9,4,5,6,7,8]]) (.forbid 0 5 0 (.forbid 0 1 3 (.cycle [0,5,6,7,8,3,1,11,10,9]) (.forbid 0 1 4 (.cycle [0,5,4,3,2,1,12,11,10,9]) (.forbid 0 2 3 (.cycle [0,5,4,3,8,1,2,11,10,9]) (.forbid 0 6 1 (.cycle [0,5,4,3,2,1,8,7,6,9]) (.forbid 1 2 3 (.cycle [1,8,0,5,4,3,2,11,10,9]) (certificate_90_part_5)))))) (.forbid 0 5 1 (.forbid 0 1 3 (.cycle [0,9,5,4,3,2,1,12,11,10]) (.forbid 0 1 4 (.cycle [0,9,5,4,3,1,13,12,11,10]) (.forbid 0 2 3 (.cycle [0,9,5,4,3,1,2,12,11,10]) (.forbid 0 3 1 (.cycle [0,9,5,6,7,8,1,2,3,10]) (certificate_90_part_6))))) (.forbid 0 5 2 (.system [[0,9,10,5,6,7,8],[1],[3]]) (.forbid 0 5 3 (.system [[0,9,10,11,5,4,3],[1],[8]]) (.forbid 0 5 4 (.system [[0,9,10,11,12,5,4,3],[1],[8]]) (.forbid 1 7 1 (.system [[0],[1,9,7,6,5,4,3],[8]]) (certificate_90_part_9))))))))

noncomputable def certificate_90_part_3 : FiniteCertificate := .forbid 1 4 5 (.system [[0],[1,9,10,11,12,13,4,3],[8]]) (.forbid 1 4 6 (.system [[0],[1,9,10,11,12,13,14,4,3],[8]]) (.forbid 2 3 1 (.system [[0],[1,2,9,3,4,5,6,7,8]]) (.forbid 2 4 1 (.system [[0],[1,2,9,4,5,6,7,8],[3]]) (.forbid 2 4 2 (.system [[0],[1,2,9,10,4,5,6,7,8],[3]]) (.forbid 2 4 3 (.system [[0],[1,2,9,10,11,4,3],[8]]) (.forbid 2 4 4 (.system [[0],[1,2,9,10,11,12,4,3],[8]]) (.forbid 2 4 5 (.system [[0],[1,2,9,10,11,12,13,4,3],[8]]) (certificate_90_part_4))))))))

noncomputable def certificate_90_part_2 : FiniteCertificate := .forbid 1 2 2 (.system [[0],[1,9,10,2,3,4,5,6,7,8]]) (.forbid 1 2 4 (.system [[0],[1,9,10,11,12,2,3],[8]]) (.forbid 1 2 5 (.system [[0],[1,9,10,11,12,13,2,3],[8]]) (.forbid 1 2 6 (.system [[0],[1,9,10,11,12,13,14,2,3],[8]]) (.forbid 1 4 1 (.system [[0],[1,9,4,5,6,7,8],[3]]) (.forbid 1 4 2 (.system [[0],[1,9,10,4,5,6,7,8],[3]]) (.forbid 1 4 3 (.system [[0],[1,9,10,11,4,5,6,7,8],[3]]) (.forbid 1 4 4 (.system [[0],[1,9,10,11,12,4,3],[8]]) (certificate_90_part_3))))))))

noncomputable def certificate_90_part_1 : FiniteCertificate := .forbid 0 2 1 (.system [[0,9,2,1],[3,4,5,6,7,8]]) (.forbid 0 2 2 (.system [[0,9,10,2,3,4,5,6,7,8],[1]]) (.forbid 0 2 4 (.system [[0,9,10,11,12,2,1],[3],[8]]) (.forbid 0 2 5 (.system [[0,9,10,11,12,13,2,1],[3],[8]]) (.forbid 0 2 6 (.system [[0,9,10,11,12,13,14,2,1],[3],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4,3],[1],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4,3],[1],[8]]) (.forbid 1 2 1 (.system [[0],[1,9,2,3,4,5,6,7,8]]) (certificate_90_part_2))))))))

noncomputable def certificate_90 : FiniteCertificate := .forbid 0 4 1 (.system [[0,9,4,5,6,7,8],[1],[3]]) (.forbid 0 4 2 (.system [[0,9,10,4,5,6,7,8],[1],[3]]) (.forbid 0 4 3 (.system [[0,9,10,11,4,5,6,7,8],[1],[3]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4,3],[1],[8]]) (.forbid 0 1 1 (.system [[0,9,1,2,3,4,5,6,7,8]]) (.forbid 0 1 2 (.system [[0,9,10,1],[3,4,5,6,7,8]]) (.forbid 0 1 5 (.system [[0,9,10,11,12,13,1],[3],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1],[3],[8]]) (certificate_90_part_1))))))))

noncomputable def certificate_93 : FiniteCertificate := .forbid 0 1 1 (.system [[0,6,1,2],[3],[5]]) (.forbid 0 1 2 (.system [[0,6,7,1,2],[3],[5]]) (.forbid 0 1 3 (.system [[0,6,7,8,1,2],[3],[5]]) (.forbid 0 1 4 (.system [[0,6,7,8,9,1,2],[3],[5]]) (.forbid 0 3 1 (.system [[2,1,0,6,3,4,5]]) (.forbid 0 3 2 (.system [[0,6,7,3],[2],[5]]) (.forbid 0 3 3 (.system [[0,6,7,8,3],[2],[5]]) (.forbid 0 3 4 (.system [[0,6,7,8,9,3],[2],[5]]) (.forbid 0 4 1 (.system [[0,6,4,3],[2],[5]]) (.forbid 0 4 2 (.system [[0,6,7,4,3],[2],[5]]) (.forbid 0 4 3 (.system [[0,6,7,8,4,3],[2],[5]]) (.forbid 0 4 4 (.system [[0,6,7,8,9,4,3],[2],[5]]) (.forbid 1 3 1 (.system [[0,1,6,3],[2],[5]]) (.forbid 1 3 2 (.system [[0,1,6,7,3],[2],[5]]) (.forbid 1 3 3 (.system [[0,1,6,7,8,3],[2],[5]]) (.forbid 1 3 4 (.system [[0,1,6,7,8,9,3],[2],[5]]) (.forbid 1 4 1 (.system [[0,1,6,4,3],[2],[5]]) (.forbid 1 4 2 (.system [[0,1,6,7,4,3],[2],[5]]) (.forbid 1 4 3 (.system [[0,1,6,7,8,4,3],[2],[5]]) (.forbid 1 4 4 (.system [[0,1,6,7,8,9,4,3],[2],[5]]) (certificate_93_part_0))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_96_part_1_M : ForbiddenMatrix := ((0,1,4) :: (((0,4,6) :: (((0,4,5) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (((0,4,1) :: (((0,1,1) :: (certificate_96_M))))))))))))))))

noncomputable def certificate_96_part_2_M : ForbiddenMatrix := ((0,7,1) :: (((0,3,6) :: (((0,3,5) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,1,6) :: (((0,1,5) :: (certificate_96_part_1_M))))))))))))))))

noncomputable def certificate_96_part_3_M : ForbiddenMatrix := ((1,4,2) :: (((1,4,1) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,3,2) :: (((1,3,1) :: (((1,2,1) :: (certificate_96_part_2_M))))))))))))))))

noncomputable def certificate_96_part_4_M : ForbiddenMatrix := ((3,4,2) :: (((3,4,1) :: (((2,4,1) :: (((2,3,1) :: (((1,4,6) :: (((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (certificate_96_part_3_M))))))))))))))))

noncomputable def certificate_96_part_5_M : ForbiddenMatrix := ((3,4,5) :: (((1,3,3) :: (((0,3,4) :: (((0,1,3) :: (((0,1,2) :: (((3,4,4) :: (((3,4,3) :: (certificate_96_part_4_M))))))))))))))

noncomputable def certificate_96_part_6_M : ForbiddenMatrix := ((1,6,2) :: (((1,6,1) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((0,5,0) :: (((3,4,4) :: (((3,4,3) :: (certificate_96_part_4_M))))))))))))))))

noncomputable def certificate_96_part_7_M : ForbiddenMatrix := ((2,6,2) :: (((2,3,6) :: (((2,3,5) :: (((2,3,3) :: (((2,3,2) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (certificate_96_part_6_M))))))))))))))))

noncomputable def certificate_96_part_8_M : ForbiddenMatrix := ((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((2,7,1) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_96_part_7_M))))))))))))))

noncomputable def certificate_96_part_9_M : ForbiddenMatrix := ((2,6,1) :: (((2,6,0) :: (((2,3,4) :: (((1,6,0) :: (((1,4,0) :: (((1,3,3) :: (((1,2,3) :: (((1,2,2) :: (certificate_96_part_8_M))))))))))))))))

noncomputable def certificate_96_part_10_M : ForbiddenMatrix := ((0,5,1) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((2,7,1) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (certificate_96_part_7_M))))))))))))))))

noncomputable def certificate_96_part_11_M : ForbiddenMatrix := ((0,7,6) :: (((0,7,5) :: (((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (certificate_96_part_10_M))))))))))))))))

noncomputable def certificate_96_part_12_M : ForbiddenMatrix := ((3,7,5) :: (((3,7,4) :: (((1,7,6) :: (((1,7,5) :: (((1,7,4) :: (((1,7,3) :: (((1,7,2) :: (((1,7,1) :: (certificate_96_part_11_M))))))))))))))))

noncomputable def certificate_96_part_13_M : ForbiddenMatrix := ((3,7,2) :: (((3,7,1) :: (((1,3,3) :: (((0,3,4) :: (((0,1,3) :: (((0,1,2) :: (((3,7,6) :: (certificate_96_part_12_M))))))))))))))

noncomputable def certificate_96_part_14_M : ForbiddenMatrix := ((2,5,2) :: (((1,5,5) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (((1,5,1) :: (((0,6,0) :: (((3,7,6) :: (certificate_96_part_12_M))))))))))))))))

noncomputable def certificate_96_part_15_M : ForbiddenMatrix := ((5,7,2) :: (((2,7,5) :: (((2,7,4) :: (((2,7,3) :: (((2,7,2) :: (((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (certificate_96_part_14_M))))))))))))))))

noncomputable def certificate_96_part_16_M : ForbiddenMatrix := ((2,5,0) :: (((1,7,0) :: (((1,5,0) :: (((1,2,3) :: (((1,2,2) :: (((5,7,4) :: (((5,7,3) :: (certificate_96_part_15_M))))))))))))))

noncomputable def certificate_96_part_17_M : ForbiddenMatrix := ((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((5,7,4) :: (((5,7,3) :: (certificate_96_part_15_M))))))))))))))

noncomputable def certificate_96_part_18_M : ForbiddenMatrix := ((1,5,0) :: (((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((5,7,4) :: (((5,7,3) :: (certificate_96_part_15_M))))))))))))))))

noncomputable def certificate_96_part_19_M : ForbiddenMatrix := ((3,7,1) :: (((1,3,3) :: (((0,3,4) :: (((0,1,3) :: (((0,1,2) :: (((2,5,0) :: (((1,6,0) :: (certificate_96_part_18_M))))))))))))))

noncomputable def certificate_96_part_20_M : ForbiddenMatrix := ((0,5,5) :: (((4,5,4) :: (((4,5,3) :: (((4,5,2) :: (((4,5,1) :: (((2,6,0) :: (((2,5,0) :: (((1,6,0) :: (certificate_96_part_18_M))))))))))))))))

noncomputable def certificate_96_part_21_M : ForbiddenMatrix := ((1,9,0) :: (((0,9,4) :: (((0,9,3) :: (((0,9,2) :: (((0,9,1) :: (((0,9,0) :: (((5,7,5) :: (certificate_96_part_20_M))))))))))))))

noncomputable def certificate_96_part_22_M : ForbiddenMatrix := ((5,9,3) :: (((5,9,2) :: (((5,9,1) :: (((5,7,1) :: (((5,7,0) :: (((3,9,0) :: (((3,5,0) :: (((2,9,0) :: (certificate_96_part_21_M))))))))))))))))

noncomputable def certificate_96_part_23_M : ForbiddenMatrix := ((5,6,2) :: (((5,6,1) :: (((4,6,5) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (((4,6,1) :: (((5,7,5) :: (certificate_96_part_20_M))))))))))))))))

noncomputable def certificate_96_part_15 : FiniteCertificate := .forbid 5 7 3 (.system [[0],[2],[3,4,5,9,10,11,7,8]]) (.forbid 5 7 4 (.system [[0],[2],[3,4,5,9,10,11,12,7,8]]) (.forbid 0 6 1 (.forbid 1 2 2 (.cycle [1,0,9,6,5,4,3,2,11,10]) (.forbid 1 2 3 (.cycle [1,0,9,6,7,8,2,12,11,10]) (.forbid 1 5 0 (.cycle [1,0,9,6,7,8,2,3,4,5]) (.forbid 1 7 0 (.cycle [1,0,9,6,5,4,3,2,8,7]) (.forbid 2 5 0 (.cycle [2,1,0,9,6,7,8,3,4,5]) (certificate_96_part_16)))))) (.forbid 0 6 2 (.system [[0,9,10,6,5,4,3],[2],[8]]) (.forbid 0 6 3 (.system [[0,9,10,11,6,5,4,3],[2],[8]]) (.forbid 0 6 4 (.system [[0,9,10,11,12,6,5,4,3],[2],[8]]) (.forbid 0 6 5 (.system [[0,9,10,11,12,13,6,5,4,3],[2],[8]]) (.forbid 1 5 0 (certificate_96_part_17) (certificate_96_part_18))))))))

noncomputable def certificate_96_part_14 : FiniteCertificate := .forbid 2 5 3 (.system [[0],[2,9,10,11,5,4,3],[8]]) (.forbid 2 5 4 (.system [[0],[2,9,10,11,12,5,4,3],[8]]) (.forbid 2 5 5 (.system [[0],[2,9,10,11,12,13,5,4,3],[8]]) (.forbid 2 7 2 (.system [[0],[2,9,10,7,6,5,4,3],[8]]) (.forbid 2 7 3 (.system [[0],[2,9,10,11,7,6,5,4,3],[8]]) (.forbid 2 7 4 (.system [[0],[2,9,10,11,12,7,6,5,4,3],[8]]) (.forbid 2 7 5 (.system [[0],[2,9,10,11,12,13,7,8],[3]]) (.forbid 5 7 2 (.system [[0],[2],[3,4,5,9,10,7,8]]) (certificate_96_part_15))))))))

noncomputable def certificate_96_part_12 : FiniteCertificate := .forbid 3 7 6 (.system [[0],[2],[3,9,10,11,12,13,14,7,8]]) (.forbid 0 6 0 (.forbid 0 1 2 (.cycle [0,6,5,4,3,8,2,1,10,9]) (.forbid 0 1 3 (.cycle [0,6,5,4,3,2,1,11,10,9]) (.forbid 0 3 4 (.cycle [0,6,7,8,2,3,12,11,10,9]) (.forbid 1 3 3 (.cycle [1,0,6,7,8,2,3,11,10,9]) (.forbid 3 7 1 (.cycle [3,4,5,6,0,1,2,8,7,9]) (.forbid 3 7 2 (.cycle [3,4,5,6,0,2,8,7,10,9]) (certificate_96_part_13))))))) (.forbid 1 5 1 (.system [[0,1,9,5,6,7,8],[2],[3]]) (.forbid 1 5 2 (.system [[0,1,9,10,5,4,3],[2],[8]]) (.forbid 1 5 3 (.system [[0,1,9,10,11,5,4,3],[2],[8]]) (.forbid 1 5 4 (.system [[0,1,9,10,11,12,5,4,3],[2],[8]]) (.forbid 1 5 5 (.system [[0,1,9,10,11,12,13,5,4,3],[2],[8]]) (.forbid 2 5 2 (.system [[0],[2,9,10,5,6,7,8],[3]]) (certificate_96_part_14))))))))

noncomputable def certificate_96_part_11 : FiniteCertificate := .forbid 1 7 1 (.system [[0,1,9,7,6,5,4,3],[2],[8]]) (.forbid 1 7 2 (.system [[0,1,9,10,7,6,5,4,3],[2],[8]]) (.forbid 1 7 3 (.system [[0,1,9,10,11,7,6,5,4,3],[2],[8]]) (.forbid 1 7 4 (.system [[0,1,9,10,11,12,7,8],[2],[3]]) (.forbid 1 7 5 (.system [[0,1,9,10,11,12,13,7,8],[2],[3]]) (.forbid 1 7 6 (.system [[0,1,9,10,11,12,13,14,7,8],[2],[3]]) (.forbid 3 7 4 (.system [[0],[2],[3,9,10,11,12,7,8]]) (.forbid 3 7 5 (.system [[0],[2],[3,9,10,11,12,13,7,8]]) (certificate_96_part_12))))))))

noncomputable def certificate_96_part_10 : FiniteCertificate := .forbid 0 5 2 (.system [[0,9,10,5,6,7,8],[2],[3]]) (.forbid 0 5 3 (.system [[0,9,10,11,5,4,3],[2],[8]]) (.forbid 0 5 4 (.system [[0,9,10,11,12,5,4,3],[2],[8]]) (.forbid 0 7 2 (.system [[0,9,10,7,6,5,4,3],[2],[8]]) (.forbid 0 7 3 (.system [[0,9,10,11,7,6,5,4,3],[2],[8]]) (.forbid 0 7 4 (.system [[0,9,10,11,12,7,6,5,4,3],[2],[8]]) (.forbid 0 7 5 (.system [[0,9,10,11,12,13,7,8],[2],[3]]) (.forbid 0 7 6 (.system [[0,9,10,11,12,13,14,7,8],[2],[3]]) (certificate_96_part_11))))))))

noncomputable def certificate_96_part_7 : FiniteCertificate := .forbid 2 6 3 (.system [[0],[2,9,10,11,6,5,4,3],[8]]) (.forbid 2 6 4 (.system [[0],[2,9,10,11,12,6,5,4,3],[8]]) (.forbid 2 6 5 (.system [[0],[2,9,10,11,12,13,6,5,4,3],[8]]) (.forbid 2 7 1 (.system [[0],[2,9,7,6,5,4,3],[8]]) (.forbid 3 6 3 (.system [[0],[2],[3,9,10,11,6,7,8]]) (.forbid 3 6 4 (.system [[0],[2],[3,9,10,11,12,6,7,8]]) (.forbid 3 6 5 (.system [[0],[2],[3,9,10,11,12,13,6,7,8]]) (.forbid 0 5 1 (certificate_96_part_8) (certificate_96_part_10))))))))

noncomputable def certificate_96_part_6 : FiniteCertificate := .forbid 1 6 3 (.system [[0,1,9,10,11,6,5,4,3],[2],[8]]) (.forbid 1 6 4 (.system [[0,1,9,10,11,12,6,5,4,3],[2],[8]]) (.forbid 1 6 5 (.system [[0,1,9,10,11,12,13,6,7,8],[2],[3]]) (.forbid 2 3 2 (.system [[0],[2,9,10,3,4,5,6,7,8]]) (.forbid 2 3 3 (.system [[0],[2,9,10,11,3,4,5,6,7,8]]) (.forbid 2 3 5 (.system [[0],[2,9,10,11,12,13,3],[8]]) (.forbid 2 3 6 (.system [[0],[2,9,10,11,12,13,14,3],[8]]) (.forbid 2 6 2 (.system [[0],[2,9,10,6,5,4,3],[8]]) (certificate_96_part_7))))))))

noncomputable def certificate_96_part_4 : FiniteCertificate := .forbid 3 4 3 (.system [[0],[2],[3,9,10,11,4,5,6,7,8]]) (.forbid 3 4 4 (.system [[0],[2],[3,9,10,11,12,4,5,6,7,8]]) (.forbid 0 5 0 (.forbid 0 1 2 (.cycle [0,5,6,7,8,3,2,1,10,9]) (.forbid 0 1 3 (.cycle [0,5,4,3,8,2,1,11,10,9]) (.forbid 0 3 4 (.cycle [0,5,6,7,8,3,12,11,10,9]) (.forbid 1 3 3 (.cycle [1,0,5,6,7,8,3,11,10,9]) (.forbid 3 4 5 (.cycle [3,2,0,5,4,13,12,11,10,9]) (certificate_96_part_5)))))) (.forbid 1 2 4 (.system [[0,1,9,10,11,12,2],[3],[8]]) (.forbid 1 2 5 (.system [[0,1,9,10,11,12,13,2],[3],[8]]) (.forbid 1 2 6 (.system [[0,1,9,10,11,12,13,14,2],[3],[8]]) (.forbid 1 6 1 (.system [[0,1,9,6,5,4,3],[2],[8]]) (.forbid 1 6 2 (.system [[0,1,9,10,6,5,4,3],[2],[8]]) (certificate_96_part_6))))))))

noncomputable def certificate_96_part_3 : FiniteCertificate := .forbid 1 4 3 (.system [[0,1,9,10,11,4,3],[2],[8]]) (.forbid 1 4 4 (.system [[0,1,9,10,11,12,4,3],[2],[8]]) (.forbid 1 4 5 (.system [[0,1,9,10,11,12,13,4,3],[2],[8]]) (.forbid 1 4 6 (.system [[0,1,9,10,11,12,13,14,4,3],[2],[8]]) (.forbid 2 3 1 (.system [[0,1,2,9,3,4,5,6,7,8]]) (.forbid 2 4 1 (.system [[0],[2,9,4,5,6,7,8],[3]]) (.forbid 3 4 1 (.system [[0],[2],[3,9,4,5,6,7,8]]) (.forbid 3 4 2 (.system [[0],[2],[3,9,10,4,5,6,7,8]]) (certificate_96_part_4))))))))

noncomputable def certificate_96_part_2 : FiniteCertificate := .forbid 1 2 1 (.system [[0,1,9,2],[3,4,5,6,7,8]]) (.forbid 1 3 1 (.system [[0,1,9,3,4,5,6,7,8],[2]]) (.forbid 1 3 2 (.system [[0,1,9,10,3,4,5,6,7,8],[2]]) (.forbid 1 3 4 (.system [[0,1,9,10,11,12,3],[2],[8]]) (.forbid 1 3 5 (.system [[0,1,9,10,11,12,13,3],[2],[8]]) (.forbid 1 3 6 (.system [[0,1,9,10,11,12,13,14,3],[2],[8]]) (.forbid 1 4 1 (.system [[0,1,9,4,5,6,7,8],[2],[3]]) (.forbid 1 4 2 (.system [[0,1,9,10,4,5,6,7,8],[2],[3]]) (certificate_96_part_3))))))))

noncomputable def certificate_96_part_1 : FiniteCertificate := .forbid 0 1 5 (.system [[0,9,10,11,12,13,1,2],[3],[8]]) (.forbid 0 1 6 (.system [[0,9,10,11,12,13,14,1,2],[3],[8]]) (.forbid 0 3 1 (.system [[2,1,0,9,3,4,5,6,7,8]]) (.forbid 0 3 2 (.system [[0,9,10,3,4,5,6,7,8],[2]]) (.forbid 0 3 3 (.system [[0,9,10,11,3,4,5,6,7,8],[2]]) (.forbid 0 3 5 (.system [[0,9,10,11,12,13,3],[2],[8]]) (.forbid 0 3 6 (.system [[0,9,10,11,12,13,14,3],[2],[8]]) (.forbid 0 7 1 (.system [[0,9,7,6,5,4,3],[2],[8]]) (certificate_96_part_2))))))))

noncomputable def certificate_96 : FiniteCertificate := .forbid 0 1 1 (.system [[0,9,1,2],[3,4,5,6,7,8]]) (.forbid 0 4 1 (.system [[0,9,4,5,6,7,8],[2],[3]]) (.forbid 0 4 2 (.system [[0,9,10,4,5,6,7,8],[2],[3]]) (.forbid 0 4 3 (.system [[0,9,10,11,4,5,6,7,8],[2],[3]]) (.forbid 0 4 4 (.system [[0,9,10,11,12,4,3],[2],[8]]) (.forbid 0 4 5 (.system [[0,9,10,11,12,13,4,3],[2],[8]]) (.forbid 0 4 6 (.system [[0,9,10,11,12,13,14,4,3],[2],[8]]) (.forbid 0 1 4 (.system [[0,9,10,11,12,1,2],[3],[8]]) (certificate_96_part_1))))))))

noncomputable def certificate_97 : FiniteCertificate := .forbid 0 1 1 (.system [[0,7,1,2,3,4],[6]]) (.forbid 0 1 2 (.system [[0,7,8,1,2],[4],[6]]) (.forbid 0 1 3 (.system [[0,7,8,9,1,2],[4],[6]]) (.forbid 0 1 4 (.system [[0,7,8,9,10,1,2],[4],[6]]) (.forbid 0 1 5 (.system [[0,7,8,9,10,11,1,2],[4],[6]]) (.forbid 0 1 6 (.system [[0,7,8,9,10,11,12,1,2],[4],[6]]) (.forbid 0 3 1 (.system [[0,7,3,2],[4,5,6]]) (.forbid 0 3 2 (.system [[0,7,8,3,2],[4],[6]]) (.forbid 0 3 3 (.system [[0,7,8,9,3,2],[4],[6]]) (.forbid 0 3 4 (.system [[0,7,8,9,10,3,2],[4],[6]]) (.forbid 0 3 5 (.system [[0,7,8,9,10,11,3,2],[4],[6]]) (.forbid 0 3 6 (.system [[0,7,8,9,10,11,12,3,2],[4],[6]]) (.forbid 0 5 1 (.system [[2,1,0,7,5,4],[6]]) (.forbid 0 5 2 (.system [[0,7,8,5,4],[2],[6]]) (.forbid 0 5 3 (.system [[0,7,8,9,5,4],[2],[6]]) (.forbid 0 5 4 (.system [[0,7,8,9,10,5,4],[2],[6]]) (.forbid 0 5 5 (.system [[0,7,8,9,10,11,5,4],[2],[6]]) (.forbid 0 5 6 (.system [[0,7,8,9,10,11,12,5,4],[2],[6]]) (.forbid 1 3 1 (.system [[0,1,7,3,2],[4],[6]]) (.forbid 1 3 2 (.system [[0,1,7,8,3,2],[4],[6]]) (certificate_97_part_0))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates018
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_561_part_2 : FiniteCertificate := .forbid 0 5 3 (.system [[0,12,13,14,5,4],[1],[2],[8,9,10,11]]) (.forbid 0 5 4 (.system [[0,12,13,14,15,5,4,3,2],[1],[8],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5,4],[1],[2],[8],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5,4],[1],[2],[8],[11]]) (.forbid 0 7 1 (.system [[0,12,7,6,5,4],[1],[2],[8,9,10,11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3,4,5,6,7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2],[4,5,6,7,8,9,10,11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2],[4,5,6,7,8],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2],[4,5,6,7,8],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2,3,4],[8],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2],[4],[8],[11]]) (.forbid 1 3 1 (.system [[0],[1,12,3,2],[4,5,6,7,8,9,10,11]]) (.forbid 1 3 2 (.system [[0],[1,12,13,3,2],[4,5,6,7,8],[11]]) (.forbid 1 3 3 (.system [[0],[1,12,13,14,3,2],[4,5,6,7,8],[11]]) (.forbid 1 3 4 (.system [[0],[1,12,13,14,15,3,2],[4,5,6,7,8],[11]]) (.forbid 1 3 5 (.system [[0],[1,12,13,14,15,16,3,2],[4],[8],[11]]) (.forbid 1 3 6 (.system [[0],[1,12,13,14,15,16,17,3,2],[4],[8],[11]]) (.forbid 1 5 1 (.system [[0],[1,12,5,6,7,8,9,10,11],[2],[4]]) (.forbid 1 5 2 (.system [[0],[1,12,13,5,6,7,8],[2,3,4],[11]]) (.forbid 1 5 3 (.system [[0],[1,12,13,14,5,4],[2],[8,9,10,11]]) (certificate_561_part_1))))))))))))))))))))

noncomputable def certificate_561 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2,3,4,5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2],[4,5,6,7,8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2],[4,5,6,7,8],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2],[4,5,6,7,8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2,3,4],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[4],[8],[11]]) (.forbid 0 2 1 (.system [[0,12,2,3,4,5,6,7,8,9,10,11],[1]]) (.forbid 0 2 2 (.system [[0,12,13,2],[1],[4,5,6,7,8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2],[1],[4,5,6,7,8],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2],[1],[4,5,6,7,8],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2,3,4],[1],[8],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[4],[8],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2],[1],[4,5,6,7,8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3,2],[1],[4,5,6,7,8],[11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,2],[1],[4,5,6,7,8],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3,2],[1],[4,5,6,7,8],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3,2],[1],[4],[8],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3,2],[1],[4],[8],[11]]) (.forbid 0 5 1 (.system [[0,12,5,6,7,8,9,10,11],[1],[2],[4]]) (.forbid 0 5 2 (.system [[0,12,13,5,6,7,8],[1],[2,3,4],[11]]) (certificate_561_part_2))))))))))))))))))))

noncomputable def certificate_562_part_1 : FiniteCertificate := .forbid 1 5 3 (.system [[0],[1,13,14,15,5,4],[2],[8,9,10,11,12]]) (.forbid 1 5 4 (.system [[0],[1,13,14,15,16,5,4],[2],[8,9,10,11,12]]) (.forbid 1 5 5 (.system [[0],[1,13,14,15,16,17,5,4,3,2],[8],[12]]) (.forbid 1 5 6 (.system [[0],[1,13,14,15,16,17,18,5,4],[2],[8],[12]]) (.forbid 1 7 1 (.system [[0],[1,13,7,6,5,4],[2],[8,9,10,11,12]]) (.forbid 1 9 1 (.system [[0],[1,13,9,10,11,12],[2],[4,5,6,7,8]]) (.forbid 2 3 1 (.system [[0],[1],[2,13,3,4,5,6,7,8,9,10,11,12]]) (.forbid 2 3 2 (.system [[0],[1],[2,13,14,3,4,5,6,7,8,9,10,11,12]]) (.forbid 2 3 3 (.system [[0],[1],[2,13,14,15,3,4,5,6,7,8],[12]]) (.forbid 2 3 4 (.system [[0],[1],[2,13,14,15,16,3,4,5,6,7,8],[12]]) (.forbid 2 3 5 (.system [[0],[1],[2,13,14,15,16,17,3,4,5,6,7,8],[12]]) (.forbid 2 3 6 (.system [[0],[1],[2,13,14,15,16,17,18,3,4],[8],[12]]) (.forbid 2 5 1 (.system [[0],[1],[2,13,5,6,7,8,9,10,11,12],[4]]) (.forbid 2 5 2 (.system [[0],[1],[2,13,14,5,6,7,8,9,10,11,12],[4]]) (.forbid 2 5 3 (.system [[0],[1],[2,13,14,15,5,4],[8,9,10,11,12]]) (.forbid 2 5 4 (.system [[0],[1],[2,13,14,15,16,5,4],[8,9,10,11,12]]) (.forbid 2 5 5 (.system [[0],[1],[2,13,14,15,16,17,5,4],[8,9,10,11,12]]) (.forbid 2 5 6 (.system [[0],[1],[2,13,14,15,16,17,18,5,4],[8],[12]]) (.forbid 2 7 1 (.system [[0],[1],[2,13,7,6,5,4],[8,9,10,11,12]]) (.forbid 2 9 1 (.system [[0],[1],[2,13,9,10,11,12],[4,5,6,7,8]]) (certificate_562_part_0))))))))))))))))))))

noncomputable def certificate_562_part_2 : FiniteCertificate := .forbid 0 5 3 (.system [[0,13,14,15,5,4],[1],[2],[8,9,10,11,12]]) (.forbid 0 5 4 (.system [[0,13,14,15,16,5,4],[1],[2],[8,9,10,11,12]]) (.forbid 0 5 5 (.system [[0,13,14,15,16,17,5,4,3,2],[1],[8],[12]]) (.forbid 0 5 6 (.system [[0,13,14,15,16,17,18,5,4],[1],[2],[8],[12]]) (.forbid 0 7 1 (.system [[0,13,7,6,5,4],[1],[2],[8,9,10,11,12]]) (.forbid 0 9 1 (.system [[0,13,9,10,11,12],[1],[2],[4,5,6,7,8]]) (.forbid 1 2 1 (.system [[0],[1,13,2,3,4,5,6,7,8,9,10,11,12]]) (.forbid 1 2 2 (.system [[0],[1,13,14,2],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 2 3 (.system [[0],[1,13,14,15,2],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 2 4 (.system [[0],[1,13,14,15,16,2],[4,5,6,7,8],[12]]) (.forbid 1 2 5 (.system [[0],[1,13,14,15,16,17,2],[4,5,6,7,8],[12]]) (.forbid 1 2 6 (.system [[0],[1,13,14,15,16,17,18,2,3,4],[8],[12]]) (.forbid 1 3 1 (.system [[0],[1,13,3,2],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 3 2 (.system [[0],[1,13,14,3,2],[4,5,6,7,8,9,10,11,12]]) (.forbid 1 3 3 (.system [[0],[1,13,14,15,3,2],[4,5,6,7,8],[12]]) (.forbid 1 3 4 (.system [[0],[1,13,14,15,16,3,2],[4,5,6,7,8],[12]]) (.forbid 1 3 5 (.system [[0],[1,13,14,15,16,17,3,2],[4,5,6,7,8],[12]]) (.forbid 1 3 6 (.system [[0],[1,13,14,15,16,17,18,3,2],[4],[8],[12]]) (.forbid 1 5 1 (.system [[0],[1,13,5,6,7,8,9,10,11,12],[2],[4]]) (.forbid 1 5 2 (.system [[0],[1,13,14,5,6,7,8,9,10,11,12],[2],[4]]) (certificate_562_part_1))))))))))))))))))))

noncomputable def certificate_562 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1],[2,3,4,5,6,7,8,9,10,11,12]]) (.forbid 0 1 2 (.system [[0,13,14,1],[2],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1],[2],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1],[2],[4,5,6,7,8],[12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1],[2],[4,5,6,7,8],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1],[2,3,4],[8],[12]]) (.forbid 0 2 1 (.system [[0,13,2,3,4,5,6,7,8,9,10,11,12],[1]]) (.forbid 0 2 2 (.system [[0,13,14,2],[1],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 2 3 (.system [[0,13,14,15,2],[1],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 2 4 (.system [[0,13,14,15,16,2],[1],[4,5,6,7,8],[12]]) (.forbid 0 2 5 (.system [[0,13,14,15,16,17,2],[1],[4,5,6,7,8],[12]]) (.forbid 0 2 6 (.system [[0,13,14,15,16,17,18,2,3,4],[1],[8],[12]]) (.forbid 0 3 1 (.system [[0,13,3,2],[1],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 3 2 (.system [[0,13,14,3,2],[1],[4,5,6,7,8,9,10,11,12]]) (.forbid 0 3 3 (.system [[0,13,14,15,3,2],[1],[4,5,6,7,8],[12]]) (.forbid 0 3 4 (.system [[0,13,14,15,16,3,2],[1],[4,5,6,7,8],[12]]) (.forbid 0 3 5 (.system [[0,13,14,15,16,17,3,2],[1],[4,5,6,7,8],[12]]) (.forbid 0 3 6 (.system [[0,13,14,15,16,17,18,3,2],[1],[4],[8],[12]]) (.forbid 0 5 1 (.system [[0,13,5,6,7,8,9,10,11,12],[1],[2],[4]]) (.forbid 0 5 2 (.system [[0,13,14,5,6,7,8,9,10,11,12],[1],[2],[4]]) (certificate_562_part_2))))))))))))))))))))

noncomputable def certificate_569_part_1_M : ForbiddenMatrix := ((0,1,5) :: (((0,1,4) :: (((0,1,3) :: (((0,1,1) :: (((0,2,4) :: (((0,2,3) :: (((0,2,2) :: (((0,2,1) :: (certificate_569_M))))))))))))))))

noncomputable def certificate_569_part_2_M : ForbiddenMatrix := ((0,3,5) :: (((0,3,4) :: (((0,3,3) :: (((0,3,2) :: (((0,3,1) :: (((0,2,6) :: (((0,2,5) :: (((0,1,6) :: (certificate_569_part_1_M))))))))))))))))

noncomputable def certificate_569_part_3_M : ForbiddenMatrix := ((0,6,5) :: (((0,6,4) :: (((0,6,3) :: (((0,6,2) :: (((0,6,1) :: (((0,5,1) :: (((0,4,1) :: (((0,3,6) :: (certificate_569_part_2_M))))))))))))))))

noncomputable def certificate_569_part_4_M : ForbiddenMatrix := ((1,3,1) :: (((1,2,6) :: (((1,2,5) :: (((1,2,4) :: (((1,2,3) :: (((1,2,2) :: (((1,2,1) :: (((0,6,6) :: (certificate_569_part_3_M))))))))))))))))

noncomputable def certificate_569_part_5_M : ForbiddenMatrix := ((1,6,1) :: (((1,5,1) :: (((1,4,1) :: (((1,3,6) :: (((1,3,5) :: (((1,3,4) :: (((1,3,3) :: (((1,3,2) :: (certificate_569_part_4_M))))))))))))))))

noncomputable def certificate_569_part_6_M : ForbiddenMatrix := ((2,3,3) :: (((2,3,2) :: (((2,3,1) :: (((1,6,6) :: (((1,6,5) :: (((1,6,4) :: (((1,6,3) :: (((1,6,2) :: (certificate_569_part_5_M))))))))))))))))

noncomputable def certificate_569_part_7_M : ForbiddenMatrix := ((2,6,6) :: (((2,6,5) :: (((2,6,4) :: (((2,6,3) :: (((2,6,2) :: (((2,6,1) :: (((2,3,6) :: (((2,3,5) :: (certificate_569_part_6_M))))))))))))))))

noncomputable def certificate_569_part_8_M : ForbiddenMatrix := ((3,7,1) :: (((3,6,6) :: (((3,6,5) :: (((3,6,4) :: (((3,6,3) :: (((3,6,2) :: (((3,6,1) :: (((3,4,1) :: (certificate_569_part_7_M))))))))))))))))

noncomputable def certificate_569_part_9_M : ForbiddenMatrix := ((0,5,6) :: (((0,5,5) :: (((0,5,4) :: (((0,5,3) :: (((0,5,2) :: (((0,3,0) :: (((5,6,1) :: (((4,6,1) :: (certificate_569_part_8_M))))))))))))))))

noncomputable def certificate_569_part_10_M : ForbiddenMatrix := ((2,5,5) :: (((2,5,4) :: (((2,5,3) :: (((1,5,6) :: (((1,5,5) :: (((1,5,4) :: (((1,5,3) :: (((1,5,2) :: (certificate_569_part_9_M))))))))))))))))

noncomputable def certificate_569_part_11_M : ForbiddenMatrix := ((5,6,6) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((4,5,1) :: (((2,7,1) :: (certificate_569_part_10_M))))))))))))))

noncomputable def certificate_569_part_12_M : ForbiddenMatrix := ((0,4,0) :: (((5,6,6) :: (((5,6,5) :: (((5,6,4) :: (((5,6,3) :: (((5,6,2) :: (((4,5,1) :: (((2,7,1) :: (certificate_569_part_10_M))))))))))))))))

noncomputable def certificate_569_part_13_M : ForbiddenMatrix := ((0,7,5) :: (((0,7,4) :: (((0,7,3) :: (((0,7,2) :: (((0,7,1) :: (((0,4,4) :: (((0,4,3) :: (((0,4,2) :: (certificate_569_part_12_M))))))))))))))))

noncomputable def certificate_569_part_14_M : ForbiddenMatrix := ((2,7,2) :: (((1,7,6) :: (((1,7,5) :: (((1,7,4) :: (((1,7,3) :: (((1,7,2) :: (((1,7,1) :: (((0,7,6) :: (certificate_569_part_13_M))))))))))))))))

noncomputable def certificate_569_part_15_M : ForbiddenMatrix := ((6,7,3) :: (((6,7,2) :: (((6,7,1) :: (((4,7,1) :: (((2,7,6) :: (((2,7,5) :: (((2,7,4) :: (((2,7,3) :: (certificate_569_part_14_M))))))))))))))))

noncomputable def certificate_569_part_16_M : ForbiddenMatrix := ((3,7,4) :: (((3,7,3) :: (((3,7,2) :: (((0,8,0) :: (((0,7,0) :: (((6,7,6) :: (((6,7,5) :: (((6,7,4) :: (certificate_569_part_15_M))))))))))))))))

noncomputable def certificate_569_part_17_M : ForbiddenMatrix := ((2,5,6) :: (((2,5,2) :: (((2,5,1) :: (((0,1,2) :: (((0,9,0) :: (((3,7,6) :: (((3,7,5) :: (certificate_569_part_16_M))))))))))))))

noncomputable def certificate_569_part_18_M : ForbiddenMatrix := ((3,5,2) :: (((2,4,0) :: (((2,11,1) :: (((1,7,0) :: (((1,4,0) :: (((0,9,0) :: (((3,7,6) :: (((3,7,5) :: (certificate_569_part_16_M))))))))))))))))

noncomputable def certificate_569_part_19_M : ForbiddenMatrix := ((5,7,6) :: (((5,7,5) :: (((5,7,4) :: (((5,7,3) :: (((5,7,2) :: (((5,7,1) :: (((3,5,4) :: (((3,5,3) :: (certificate_569_part_18_M))))))))))))))))

noncomputable def certificate_569_part_20_M : ForbiddenMatrix := ((3,7,0) :: (((3,6,0) :: (((3,5,5) :: (((3,5,1) :: (((3,5,0) :: (((1,3,0) :: (((5,11,1) :: (certificate_569_part_19_M))))))))))))))

noncomputable def certificate_569_part_21_M : ForbiddenMatrix := ((0,1,2) :: (((2,7,0) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (((5,11,1) :: (certificate_569_part_19_M))))))))))))))

noncomputable def certificate_569_part_22_M : ForbiddenMatrix := ((2,8,0) :: (((2,7,0) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (((5,11,1) :: (certificate_569_part_19_M))))))))))))))

noncomputable def certificate_569_part_23_M : ForbiddenMatrix := ((2,9,0) :: (((2,8,0) :: (((2,7,0) :: (((2,4,4) :: (((2,4,3) :: (((2,4,2) :: (((2,4,1) :: (((5,11,1) :: (certificate_569_part_19_M))))))))))))))))

noncomputable def certificate_569_part_24_M : ForbiddenMatrix := ((1,4,5) :: (((1,4,4) :: (((1,4,3) :: (((1,4,2) :: (((0,4,6) :: (((0,4,5) :: (((3,6,0) :: (((2,10,0) :: (certificate_569_part_23_M))))))))))))))))

noncomputable def certificate_569_part_25_M : ForbiddenMatrix := ((0,1,2) :: (((3,4,6) :: (((3,4,5) :: (((3,4,3) :: (((3,4,2) :: (((2,4,6) :: (((1,4,6) :: (certificate_569_part_24_M))))))))))))))

noncomputable def certificate_569_part_26_M : ForbiddenMatrix := ((3,7,0) :: (((3,4,6) :: (((3,4,5) :: (((3,4,3) :: (((3,4,2) :: (((2,4,6) :: (((1,4,6) :: (certificate_569_part_24_M))))))))))))))

noncomputable def certificate_569_part_27_M : ForbiddenMatrix := ((4,6,0) :: (((3,7,0) :: (((3,4,6) :: (((3,4,5) :: (((3,4,3) :: (((3,4,2) :: (((2,4,6) :: (((1,4,6) :: (certificate_569_part_24_M))))))))))))))))

noncomputable def certificate_569_part_28_M : ForbiddenMatrix := ((2,5,1) :: (((2,3,4) :: (((0,1,2) :: (((3,5,6) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (certificate_569_part_27_M))))))))))))))

noncomputable def certificate_569_part_29_M : ForbiddenMatrix := ((4,7,4) :: (((4,7,3) :: (((4,7,2) :: (((4,7,0) :: (((3,5,6) :: (((4,6,4) :: (((4,6,3) :: (((4,6,2) :: (certificate_569_part_27_M))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates019
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_603_part_1 : FiniteCertificate := .forbid 1 5 4 (.system [[0],[1,12,13,14,15,5,4,3],[6],[7],[11]]) (.forbid 1 5 5 (.system [[0],[1,12,13,14,15,16,5,4,3],[6],[7],[11]]) (.forbid 1 5 6 (.system [[0],[1,12,13,14,15,16,17,5,4,3],[6],[7],[11]]) (.forbid 1 7 1 (.system [[0],[6,5,4,3,2,1,12,7,8,9,10,11]]) (.forbid 2 3 1 (.system [[0],[1,2,12,3,4,5,6],[7,8,9,10,11]]) (.forbid 2 4 1 (.system [[0],[1,2,12,4,3],[6],[7,8,9,10,11]]) (.forbid 2 4 2 (.system [[0],[1,2,12,13,4,3],[6],[7,8,9,10,11]]) (.forbid 2 4 3 (.system [[0],[1,2,12,13,14,4,3],[6],[7,8,9,10,11]]) (.forbid 2 4 4 (.system [[0],[1,2,12,13,14,15,4,3],[6],[7],[11]]) (.forbid 2 4 5 (.system [[0],[1,2,12,13,14,15,16,4,3],[6],[7],[11]]) (.forbid 2 4 6 (.system [[0],[1,2,12,13,14,15,16,17,4,3],[6],[7],[11]]) (.forbid 2 5 1 (.system [[0],[1,2,12,5,4,3],[6],[7,8,9,10,11]]) (.forbid 2 5 2 (.system [[0],[1,2,12,13,5,4,3],[6],[7,8,9,10,11]]) (.forbid 2 5 3 (.system [[0],[1,2,12,13,14,5,4,3],[6],[7],[11]]) (.forbid 2 5 4 (.system [[0],[1,2,12,13,14,15,5,4,3],[6],[7],[11]]) (.forbid 2 5 5 (.system [[0],[1,2,12,13,14,15,16,5,4,3],[6],[7],[11]]) (.forbid 2 5 6 (.system [[0],[1,2,12,13,14,15,16,17,5,4,3],[6],[7],[11]]) (.forbid 3 4 1 (.system [[0],[1],[3,12,4,5,6],[7,8,9,10,11]]) (.forbid 4 5 1 (.system [[0],[1],[3,4,12,5,6],[7,8,9,10,11]]) (.forbid 4 5 2 (.system [[0],[1],[3,4,12,13,5,6],[7,8,9,10,11]]) (certificate_603_part_0))))))))))))))))))))

noncomputable def certificate_603_part_2 : FiniteCertificate := .forbid 0 5 3 (.system [[0,12,13,14,5,4,3,2,1],[6],[7],[11]]) (.forbid 0 5 4 (.system [[0,12,13,14,15,5,4,3],[1],[6],[7],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5,4,3],[1],[6],[7],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5,4,3],[1],[6],[7],[11]]) (.forbid 0 6 1 (.system [[0,12,6,5,4,3,2,1],[7,8,9,10,11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3,4,5,6],[7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2,3],[6],[7,8,9,10,11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2,3,4,5,6],[7],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2,3,4,5,6],[7],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2,3],[6],[7],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2,3],[6],[7],[11]]) (.forbid 1 4 1 (.system [[0],[1,12,4,5,6],[3],[7,8,9,10,11]]) (.forbid 1 4 2 (.system [[0],[1,12,13,4,3],[6],[7,8,9,10,11]]) (.forbid 1 4 3 (.system [[0],[1,12,13,14,4,3],[6],[7,8,9,10,11]]) (.forbid 1 4 4 (.system [[0],[1,12,13,14,15,4,3],[6],[7,8,9,10,11]]) (.forbid 1 4 5 (.system [[0],[1,12,13,14,15,16,4,3],[6],[7],[11]]) (.forbid 1 4 6 (.system [[0],[1,12,13,14,15,16,17,4,3],[6],[7],[11]]) (.forbid 1 5 1 (.system [[0],[1,12,5,4,3],[6],[7,8,9,10,11]]) (.forbid 1 5 2 (.system [[0],[1,12,13,5,4,3],[6],[7,8,9,10,11]]) (.forbid 1 5 3 (.system [[0],[1,12,13,14,5,4,3],[6],[7,8,9,10,11]]) (certificate_603_part_1))))))))))))))))))))

noncomputable def certificate_603 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1,2,3,4,5,6],[7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[3,4,5,6],[7,8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[3],[6],[7,8,9,10,11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[3,4,5,6],[7],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1,2,3],[6],[7],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[3],[6],[7],[11]]) (.forbid 0 2 1 (.system [[0,12,2,1],[3,4,5,6],[7,8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2,1],[3],[6],[7,8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2,1],[3,4,5,6],[7],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2,1],[3,4,5,6],[7],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2,1],[3],[6],[7],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2,1],[3],[6],[7],[11]]) (.forbid 0 4 1 (.system [[0,12,4,5,6],[1],[3],[7,8,9,10,11]]) (.forbid 0 4 2 (.system [[0,12,13,4,3],[1],[6],[7,8,9,10,11]]) (.forbid 0 4 3 (.system [[0,12,13,14,4,3],[1],[6],[7,8,9,10,11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4,3,2,1],[6],[7],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4,3],[1],[6],[7],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4,3],[1],[6],[7],[11]]) (.forbid 0 5 1 (.system [[0,12,5,4,3],[1],[6],[7,8,9,10,11]]) (.forbid 0 5 2 (.system [[0,12,13,5,4,3],[1],[6],[7,8,9,10,11]]) (certificate_603_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates021
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_652_part_1 : FiniteCertificate := .forbid 1 7 3 (.system [[0,1,12,13,14,7,6],[2,3,4],[8],[11]]) (.forbid 1 7 4 (.system [[0,1,12,13,14,15,7,6],[2],[4],[8],[11]]) (.forbid 1 7 5 (.system [[0,1,12,13,14,15,16,7,6],[2],[4],[8],[11]]) (.forbid 1 7 6 (.system [[0,1,12,13,14,15,16,17,7,6],[2],[4],[8],[11]]) (.forbid 2 3 1 (.system [[0,1,2,12,3,4,5,6],[8,9,10,11]]) (.forbid 2 5 1 (.system [[0,1,2,12,5,4],[6,7,8,9,10,11]]) (.forbid 2 7 1 (.system [[0,1,2,12,7,6,5,4],[8,9,10,11]]) (.forbid 3 5 1 (.system [[0,1,2,3,12,5,4],[6],[8,9,10,11]]) (.forbid 3 5 2 (.system [[0],[2,3,12,13,5,4],[6],[8,9,10,11]]) (.forbid 3 5 3 (.system [[0,1,2,3,12,13,14,5,4],[6],[8],[11]]) (.forbid 3 5 4 (.system [[0],[2,3,12,13,14,15,5,4],[6],[8],[11]]) (.forbid 3 5 5 (.system [[0],[2,3,12,13,14,15,16,5,4],[6],[8],[11]]) (.forbid 3 5 6 (.system [[0],[2,3,12,13,14,15,16,17,5,4],[6],[8],[11]]) (.forbid 3 7 1 (.system [[0,1,2,3,12,7,6],[4],[8,9,10,11]]) (.forbid 3 7 2 (.system [[0],[2,3,12,13,7,6],[4],[8,9,10,11]]) (.forbid 3 7 3 (.system [[0,1,2,3,12,13,14,7,6],[4],[8],[11]]) (.forbid 3 7 4 (.system [[0],[2,3,12,13,14,15,7,6],[4],[8],[11]]) (.forbid 3 7 5 (.system [[0],[2,3,12,13,14,15,16,7,6],[4],[8],[11]]) (.forbid 3 7 6 (.system [[0],[2,3,12,13,14,15,16,17,7,6],[4],[8],[11]]) (.forbid 5 7 1 (.system [[0,1,2],[4,5,12,7,6],[8,9,10,11]]) (certificate_652_part_0))))))))))))))))))))

noncomputable def certificate_652_part_2 : FiniteCertificate := .forbid 0 7 3 (.system [[0,12,13,14,7,6],[2],[4],[8,9,10,11]]) (.forbid 0 7 4 (.system [[2,1,0,12,13,14,15,7,6],[4],[8],[11]]) (.forbid 0 7 5 (.system [[0,12,13,14,15,16,7,6],[2],[4],[8],[11]]) (.forbid 0 7 6 (.system [[0,12,13,14,15,16,17,7,6],[2],[4],[8],[11]]) (.forbid 0 9 1 (.system [[6,5,4,3,2,1,0,12,9,10,11],[8]]) (.forbid 1 2 1 (.system [[0,1,12,2,3,4,5,6],[8,9,10,11]]) (.forbid 1 3 1 (.system [[0,1,12,3,2],[4,5,6],[8,9,10,11]]) (.forbid 1 3 2 (.system [[0,1,12,13,3,2],[4],[6],[8,9,10,11]]) (.forbid 1 3 3 (.system [[0,1,12,13,14,3,2],[4,5,6],[8],[11]]) (.forbid 1 3 4 (.system [[0,1,12,13,14,15,3,2],[4],[6],[8],[11]]) (.forbid 1 3 5 (.system [[0,1,12,13,14,15,16,3,2],[4],[6],[8],[11]]) (.forbid 1 3 6 (.system [[0,1,12,13,14,15,16,17,3,2],[4],[6],[8],[11]]) (.forbid 1 5 1 (.system [[0,1,12,5,4,3,2],[6],[8,9,10,11]]) (.forbid 1 5 2 (.system [[0,1,12,13,5,4],[2],[6],[8,9,10,11]]) (.forbid 1 5 3 (.system [[0,1,12,13,14,5,4,3,2],[6],[8],[11]]) (.forbid 1 5 4 (.system [[0,1,12,13,14,15,5,4],[2],[6],[8],[11]]) (.forbid 1 5 5 (.system [[0,1,12,13,14,15,16,5,4],[2],[6],[8],[11]]) (.forbid 1 5 6 (.system [[0,1,12,13,14,15,16,17,5,4],[2],[6],[8],[11]]) (.forbid 1 7 1 (.system [[0,1,12,7,6],[2,3,4],[8,9,10,11]]) (.forbid 1 7 2 (.system [[0,1,12,13,7,6],[2],[4],[8,9,10,11]]) (certificate_652_part_1))))))))))))))))))))

noncomputable def certificate_652 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1,2,3,4,5,6],[8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1,2,3,4],[6],[8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1,2],[4],[6],[8,9,10,11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1,2,3,4],[6],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1,2],[4],[6],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1,2],[4],[6],[8],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2],[4,5,6,7,8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3,2],[4,5,6],[8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,2],[4],[6],[8,9,10,11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3,2],[4,5,6],[8],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3,2],[4],[6],[8],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3,2],[4],[6],[8],[11]]) (.forbid 0 5 1 (.system [[2,1,0,12,5,4],[6,7,8,9,10,11]]) (.forbid 0 5 2 (.system [[2,1,0,12,13,5,4],[6],[8,9,10,11]]) (.forbid 0 5 3 (.system [[0,12,13,14,5,4],[2],[6],[8,9,10,11]]) (.forbid 0 5 4 (.system [[2,1,0,12,13,14,15,5,4],[6],[8],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5,4],[2],[6],[8],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5,4],[2],[6],[8],[11]]) (.forbid 0 7 1 (.system [[4,3,2,1,0,12,7,6],[8,9,10,11]]) (.forbid 0 7 2 (.system [[2,1,0,12,13,7,6],[4],[8,9,10,11]]) (certificate_652_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates023
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_711 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2],[3,4,5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2],[3,4,5,6],[8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2],[3,4,5,6],[8],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2],[3,4,5,6],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2],[3],[6],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[3],[6],[8],[11]]) (.forbid 0 2 1 (.system [[0,12,2],[1],[3,4,5,6,7,8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2],[1],[3,4,5,6],[8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2],[1],[3,4,5,6],[8],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2],[1],[3,4,5,6],[8],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2],[1],[3],[6],[8],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[3],[6],[8],[11]]) (.forbid 0 3 1 (.system [[0,12,3,4,5,6,7,8,9,10,11],[1],[2]]) (.forbid 0 3 2 (.system [[0,12,13,3,4,5,6],[1],[2],[8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,4,5,6],[1],[2],[8],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3,4,5,6],[1],[2],[8],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3],[1],[2],[6],[8],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3],[1],[2],[6],[8],[11]]) (.forbid 0 4 1 (.system [[0,12,4,5,6],[1],[2],[3],[8,9,10,11]]) (.forbid 0 4 2 (.system [[0,12,13,4,3],[1],[2],[6],[8,9,10,11]]) (certificate_711_part_2))))))))))))))))))))

noncomputable def certificate_716_part_1 : FiniteCertificate := .forbid 1 5 3 (.system [[0],[1,11,12,13,5],[2,3,4],[7],[10]]) (.forbid 1 5 4 (.system [[0],[1,11,12,13,14,5],[2],[4],[7],[10]]) (.forbid 1 5 5 (.system [[0],[1,11,12,13,14,15,5],[2],[4],[7],[10]]) (.forbid 1 5 6 (.system [[0],[1,11,12,13,14,15,16,5],[2],[4],[7],[10]]) (.forbid 2 3 1 (.system [[0],[1],[2,11,3,4],[5],[7,8,9,10]]) (.forbid 2 3 2 (.system [[0],[1],[2,11,12,3,4],[5,6,7],[10]]) (.forbid 2 3 3 (.system [[0],[1],[2,11,12,13,3,4],[5],[7],[10]]) (.forbid 2 3 4 (.system [[0],[1],[2,11,12,13,14,3,4],[5],[7],[10]]) (.forbid 2 3 5 (.system [[0],[1],[2,11,12,13,14,15,3,4],[5],[7],[10]]) (.forbid 2 3 6 (.system [[0],[1],[2,11,12,13,14,15,16,3,4],[5],[7],[10]]) (.forbid 2 5 1 (.system [[0],[1],[4,3,2,11,5,6,7,8,9,10]]) (.forbid 2 5 2 (.system [[0],[1],[2,11,12,5],[4],[7,8,9,10]]) (.forbid 2 5 3 (.system [[0],[1],[4,3,2,11,12,13,5],[7],[10]]) (.forbid 2 5 4 (.system [[0],[1],[2,11,12,13,14,5],[4],[7],[10]]) (.forbid 2 5 5 (.system [[0],[1],[2,11,12,13,14,15,5],[4],[7],[10]]) (.forbid 2 5 6 (.system [[0],[1],[2,11,12,13,14,15,16,5],[4],[7],[10]]) (.forbid 2 6 1 (.system [[0],[1],[2,11,6,5],[4],[7,8,9,10]]) (.forbid 3 4 1 (.system [[0],[1],[2,3,11,4],[5],[7,8,9,10]]) (.forbid 3 5 1 (.system [[0],[1],[2,3,11,5],[4],[7,8,9,10]]) (.forbid 3 5 2 (.system [[0],[1],[2,3,11,12,5,6,7],[4],[10]]) (certificate_716_part_0))))))))))))))))))))

noncomputable def certificate_716_part_2 : FiniteCertificate := .forbid 0 5 2 (.system [[0,11,12,5],[1],[2],[4],[7,8,9,10]]) (.forbid 0 5 3 (.system [[0,11,12,13,5],[1],[2,3,4],[7],[10]]) (.forbid 0 5 4 (.system [[0,11,12,13,14,5],[1],[2],[4],[7],[10]]) (.forbid 0 5 5 (.system [[0,11,12,13,14,15,5],[1],[2],[4],[7],[10]]) (.forbid 0 5 6 (.system [[0,11,12,13,14,15,16,5],[1],[2],[4],[7],[10]]) (.forbid 1 2 1 (.system [[0],[1,11,2,3,4],[5,6,7,8,9,10]]) (.forbid 1 2 2 (.system [[0],[1,11,12,2],[4],[5],[7,8,9,10]]) (.forbid 1 2 3 (.system [[0],[1,11,12,13,2,3,4],[5],[7],[10]]) (.forbid 1 2 4 (.system [[0],[1,11,12,13,14,2],[4],[5],[7],[10]]) (.forbid 1 2 5 (.system [[0],[1,11,12,13,14,15,2],[4],[5],[7],[10]]) (.forbid 1 2 6 (.system [[0],[1,11,12,13,14,15,16,2],[4],[5],[7],[10]]) (.forbid 1 3 1 (.system [[0],[1,11,3,2],[4],[5],[7,8,9,10]]) (.forbid 1 3 2 (.system [[0],[1,11,12,3,2],[4],[5,6,7],[10]]) (.forbid 1 3 3 (.system [[0],[1,11,12,13,3,2],[4],[5],[7],[10]]) (.forbid 1 3 4 (.system [[0],[1,11,12,13,14,3,2],[4],[5],[7],[10]]) (.forbid 1 3 5 (.system [[0],[1,11,12,13,14,15,3,2],[4],[5],[7],[10]]) (.forbid 1 3 6 (.system [[0],[1,11,12,13,14,15,16,3,2],[4],[5],[7],[10]]) (.forbid 1 4 1 (.system [[0],[1,11,4,3,2],[5,6,7,8,9,10]]) (.forbid 1 5 1 (.system [[0],[1,11,5,6,7,8,9,10],[2,3,4]]) (.forbid 1 5 2 (.system [[0],[1,11,12,5],[2],[4],[7,8,9,10]]) (certificate_716_part_1))))))))))))))))))))

noncomputable def certificate_716 : FiniteCertificate := .forbid 0 1 1 (.system [[0,11,1],[2,3,4],[5,6,7,8,9,10]]) (.forbid 0 1 2 (.system [[0,11,12,1],[2],[4],[5],[7,8,9,10]]) (.forbid 0 1 3 (.system [[0,11,12,13,1],[2,3,4],[5],[7],[10]]) (.forbid 0 1 4 (.system [[0,11,12,13,14,1],[2],[4],[5],[7],[10]]) (.forbid 0 1 5 (.system [[0,11,12,13,14,15,1],[2],[4],[5],[7],[10]]) (.forbid 0 1 6 (.system [[0,11,12,13,14,15,16,1],[2],[4],[5],[7],[10]]) (.forbid 0 2 1 (.system [[0,11,2,3,4],[1],[5,6,7,8,9,10]]) (.forbid 0 2 2 (.system [[0,11,12,2],[1],[4],[5],[7,8,9,10]]) (.forbid 0 2 3 (.system [[0,11,12,13,2,3,4],[1],[5],[7],[10]]) (.forbid 0 2 4 (.system [[0,11,12,13,14,2],[1],[4],[5],[7],[10]]) (.forbid 0 2 5 (.system [[0,11,12,13,14,15,2],[1],[4],[5],[7],[10]]) (.forbid 0 2 6 (.system [[0,11,12,13,14,15,16,2],[1],[4],[5],[7],[10]]) (.forbid 0 3 1 (.system [[0,11,3,2],[1],[4],[5],[7,8,9,10]]) (.forbid 0 3 2 (.system [[0,11,12,3,2],[1],[4],[5,6,7],[10]]) (.forbid 0 3 3 (.system [[0,11,12,13,3,2],[1],[4],[5],[7],[10]]) (.forbid 0 3 4 (.system [[0,11,12,13,14,3,2],[1],[4],[5],[7],[10]]) (.forbid 0 3 5 (.system [[0,11,12,13,14,15,3,2],[1],[4],[5],[7],[10]]) (.forbid 0 3 6 (.system [[0,11,12,13,14,15,16,3,2],[1],[4],[5],[7],[10]]) (.forbid 0 4 1 (.system [[0,11,4,3,2],[1],[5,6,7,8,9,10]]) (.forbid 0 5 1 (.system [[0,11,5,6,7,8,9,10],[1],[2,3,4]]) (certificate_716_part_2))))))))))))))))))))

noncomputable def certificate_725 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2,3,4,5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2,3,4],[6],[8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2],[4],[6],[8,9,10,11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2,3,4],[6],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2],[4],[6],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[4],[6],[8],[11]]) (.forbid 0 2 1 (.system [[0,12,2,3,4,5,6,7,8,9,10,11],[1]]) (.forbid 0 2 2 (.system [[0,12,13,2,3,4],[1],[6],[8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2],[1],[4],[6],[8,9,10,11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2,3,4],[1],[6],[8],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2],[1],[4],[6],[8],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[4],[6],[8],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2],[1],[4,5,6],[8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3,2],[1],[4],[6],[8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,2],[1],[4,5,6],[8],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3,2],[1],[4],[6],[8],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3,2],[1],[4],[6],[8],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3,2],[1],[4],[6],[8],[11]]) (.forbid 0 5 1 (.system [[0,12,5,4,3,2],[1],[6],[8,9,10,11]]) (.forbid 0 5 2 (.system [[0,12,13,5,4],[1],[2],[6],[8,9,10,11]]) (certificate_725_part_2))))))))))))))))))))

noncomputable def certificate_727_part_1 : FiniteCertificate := .forbid 1 5 3 (.system [[0],[1,12,13,14,5,4,3,2],[6],[9],[11]]) (.forbid 1 5 4 (.system [[0],[1,12,13,14,15,5,4],[2],[6],[9],[11]]) (.forbid 1 5 5 (.system [[0],[1,12,13,14,15,16,5,4],[2],[6],[9],[11]]) (.forbid 1 5 6 (.system [[0],[1,12,13,14,15,16,17,5,4],[2],[6],[9],[11]]) (.forbid 1 7 1 (.system [[0],[1,12,7,8,9],[2,3,4,5,6],[11]]) (.forbid 1 8 1 (.system [[0],[1,12,8,7,6,5,4,3,2],[9],[11]]) (.forbid 2 3 1 (.system [[0],[1],[2,12,3,4,5,6,7,8,9],[11]]) (.forbid 2 3 2 (.system [[0],[1],[2,12,13,3,4],[6,7,8,9],[11]]) (.forbid 2 3 3 (.system [[0],[1],[2,12,13,14,3,4,5,6],[9],[11]]) (.forbid 2 3 4 (.system [[0],[1],[2,12,13,14,15,3,4],[6],[9],[11]]) (.forbid 2 3 5 (.system [[0],[1],[2,12,13,14,15,16,3,4],[6],[9],[11]]) (.forbid 2 3 6 (.system [[0],[1],[2,12,13,14,15,16,17,3,4],[6],[9],[11]]) (.forbid 2 5 1 (.system [[0],[1],[2,12,5,4],[6,7,8,9,10,11]]) (.forbid 2 5 2 (.system [[0],[1],[2,12,13,5,4],[6,7,8,9],[11]]) (.forbid 2 5 3 (.system [[0],[1],[2,12,13,14,5,4],[6,7,8,9],[11]]) (.forbid 2 5 4 (.system [[0],[1],[2,12,13,14,15,5,4],[6],[9],[11]]) (.forbid 2 5 5 (.system [[0],[1],[2,12,13,14,15,16,5,4],[6],[9],[11]]) (.forbid 2 5 6 (.system [[0],[1],[2,12,13,14,15,16,17,5,4],[6],[9],[11]]) (.forbid 2 7 1 (.system [[0],[1],[6,5,4,3,2,12,7,8,9],[11]]) (.forbid 2 8 1 (.system [[0],[1],[4,3,2,12,8,7,6],[9,10,11]]) (certificate_727_part_0))))))))))))))))))))

noncomputable def certificate_727_part_2 : FiniteCertificate := .forbid 0 5 3 (.system [[0,12,13,14,5,4,3,2],[1],[6],[9],[11]]) (.forbid 0 5 4 (.system [[0,12,13,14,15,5,4],[1],[2],[6],[9],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5,4],[1],[2],[6],[9],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5,4],[1],[2],[6],[9],[11]]) (.forbid 0 7 1 (.system [[0,12,7,8,9],[1],[2,3,4,5,6],[11]]) (.forbid 0 8 1 (.system [[0,12,8,7,6,5,4,3,2],[1],[9],[11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3,4,5,6,7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2,3,4],[6,7,8,9],[11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2],[4],[6,7,8,9],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2,3,4],[6],[9],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2],[4],[6],[9],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2],[4],[6],[9],[11]]) (.forbid 1 3 1 (.system [[0],[1,12,3,2],[4,5,6,7,8,9],[11]]) (.forbid 1 3 2 (.system [[0],[1,12,13,3,2],[4],[6,7,8,9],[11]]) (.forbid 1 3 3 (.system [[0],[1,12,13,14,3,2],[4,5,6],[9],[11]]) (.forbid 1 3 4 (.system [[0],[1,12,13,14,15,3,2],[4],[6],[9],[11]]) (.forbid 1 3 5 (.system [[0],[1,12,13,14,15,16,3,2],[4],[6],[9],[11]]) (.forbid 1 3 6 (.system [[0],[1,12,13,14,15,16,17,3,2],[4],[6],[9],[11]]) (.forbid 1 5 1 (.system [[0],[1,12,5,4,3,2],[6,7,8,9],[11]]) (.forbid 1 5 2 (.system [[0],[1,12,13,5,4],[2],[6,7,8,9],[11]]) (certificate_727_part_1))))))))))))))))))))

noncomputable def certificate_727 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2,3,4,5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2,3,4],[6,7,8,9],[11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2],[4],[6,7,8,9],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2,3,4],[6],[9],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2],[4],[6],[9],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[4],[6],[9],[11]]) (.forbid 0 2 1 (.system [[0,12,2,3,4,5,6,7,8,9,10,11],[1]]) (.forbid 0 2 2 (.system [[0,12,13,2,3,4],[1],[6,7,8,9],[11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2],[1],[4],[6,7,8,9],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2,3,4],[1],[6],[9],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2],[1],[4],[6],[9],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[4],[6],[9],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2],[1],[4,5,6,7,8,9],[11]]) (.forbid 0 3 2 (.system [[0,12,13,3,2],[1],[4],[6,7,8,9],[11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3,2],[1],[4,5,6],[9],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3,2],[1],[4],[6],[9],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3,2],[1],[4],[6],[9],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3,2],[1],[4],[6],[9],[11]]) (.forbid 0 5 1 (.system [[0,12,5,4,3,2],[1],[6,7,8,9],[11]]) (.forbid 0 5 2 (.system [[0,12,13,5,4],[1],[2],[6,7,8,9],[11]]) (certificate_727_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates024
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_742_part_2 : FiniteCertificate := .forbid 0 5 2 (.system [[0,12,13,5,4],[1],[3],[6],[8,9,10,11]]) (.forbid 0 5 3 (.system [[0,12,13,14,5,4],[1,2,3],[6],[8],[11]]) (.forbid 0 5 4 (.system [[0,12,13,14,15,5,4],[1],[3],[6],[8],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5,4],[1],[3],[6],[8],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5,4],[1],[3],[6],[8],[11]]) (.forbid 0 7 1 (.system [[0,12,7,6],[1,2,3],[4],[8,9,10,11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3],[4,5,6],[8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2,3],[4],[6],[8,9,10,11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2,3],[4,5,6],[8],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2,3],[4],[6],[8],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2,3],[4],[6],[8],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2,3],[4],[6],[8],[11]]) (.forbid 1 4 1 (.system [[0],[3,2,1,12,4,5,6,7,8,9,10,11]]) (.forbid 1 4 2 (.system [[0],[3,2,1,12,13,4],[6],[8,9,10,11]]) (.forbid 1 4 3 (.system [[0],[1,12,13,14,4],[3],[6],[8,9,10,11]]) (.forbid 1 4 4 (.system [[0],[3,2,1,12,13,14,15,4],[6],[8],[11]]) (.forbid 1 4 5 (.system [[0],[1,12,13,14,15,16,4],[3],[6],[8],[11]]) (.forbid 1 4 6 (.system [[0],[1,12,13,14,15,16,17,4],[3],[6],[8],[11]]) (.forbid 1 5 1 (.system [[0],[3,2,1,12,5,4],[6],[8,9,10,11]]) (.forbid 1 5 2 (.system [[0],[1,12,13,5,4],[3],[6],[8,9,10,11]]) (certificate_742_part_1))))))))))))))))))))

noncomputable def certificate_742 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1,2,3],[4,5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1,2,3],[4],[6],[8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[3],[4],[6],[8,9,10,11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1,2,3],[4],[6],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[3],[4],[6],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[3],[4],[6],[8],[11]]) (.forbid 0 2 1 (.system [[0,12,2,1],[3],[4,5,6],[8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2,1],[3],[4],[6],[8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2,1],[3],[4,5,6],[8],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2,1],[3],[4],[6],[8],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2,1],[3],[4],[6],[8],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2,1],[3],[4],[6],[8],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2,1],[4,5,6,7,8,9,10,11]]) (.forbid 0 4 1 (.system [[0,12,4,5,6,7,8,9,10,11],[1,2,3]]) (.forbid 0 4 2 (.system [[0,12,13,4],[1,2,3],[6],[8,9,10,11]]) (.forbid 0 4 3 (.system [[0,12,13,14,4],[1],[3],[6],[8,9,10,11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4],[1,2,3],[6],[8],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4],[1],[3],[6],[8],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4],[1],[3],[6],[8],[11]]) (.forbid 0 5 1 (.system [[0,12,5,4],[1,2,3],[6],[8,9,10,11]]) (certificate_742_part_2))))))))))))))))))))

noncomputable def certificate_744_part_1 : FiniteCertificate := .forbid 1 5 3 (.system [[0],[3,2,1,12,13,14,5,4],[6],[9],[11]]) (.forbid 1 5 4 (.system [[0],[1,12,13,14,15,5,4],[3],[6],[9],[11]]) (.forbid 1 5 5 (.system [[0],[1,12,13,14,15,16,5,4],[3],[6],[9],[11]]) (.forbid 1 5 6 (.system [[0],[1,12,13,14,15,16,17,5,4],[3],[6],[9],[11]]) (.forbid 1 7 1 (.system [[0],[3,2,1,12,7,8,9],[4,5,6],[11]]) (.forbid 1 8 1 (.system [[0],[3,2,1,12,8,7,6,5,4],[9],[11]]) (.forbid 2 3 1 (.system [[0],[1,2,12,3],[4,5,6,7,8,9],[11]]) (.forbid 2 4 1 (.system [[0],[1,2,12,4,5,6,7,8,9],[3],[11]]) (.forbid 2 4 2 (.system [[0],[1,2,12,13,4],[3],[6,7,8,9],[11]]) (.forbid 2 4 3 (.system [[0],[1,2,12,13,14,4,5,6],[3],[9],[11]]) (.forbid 2 4 4 (.system [[0],[1,2,12,13,14,15,4],[3],[6],[9],[11]]) (.forbid 2 4 5 (.system [[0],[1,2,12,13,14,15,16,4],[3],[6],[9],[11]]) (.forbid 2 4 6 (.system [[0],[1,2,12,13,14,15,16,17,4],[3],[6],[9],[11]]) (.forbid 2 5 1 (.system [[0],[1,2,12,5,4],[3],[6,7,8,9],[11]]) (.forbid 2 5 2 (.system [[0],[1,2,12,13,5,4],[3],[6,7,8,9],[11]]) (.forbid 2 5 3 (.system [[0],[1,2,12,13,14,5,4],[3],[6],[9],[11]]) (.forbid 2 5 4 (.system [[0],[1,2,12,13,14,15,5,4],[3],[6],[9],[11]]) (.forbid 2 5 5 (.system [[0],[1,2,12,13,14,15,16,5,4],[3],[6],[9],[11]]) (.forbid 2 5 6 (.system [[0],[1,2,12,13,14,15,16,17,5,4],[3],[6],[9],[11]]) (.forbid 2 6 1 (.system [[0],[1,2,12,6,7,8,9,10,11],[3],[4]]) (certificate_744_part_0))))))))))))))))))))

noncomputable def certificate_744_part_2 : FiniteCertificate := .forbid 0 5 2 (.system [[0,12,13,5,4],[1],[3],[6,7,8,9],[11]]) (.forbid 0 5 3 (.system [[0,12,13,14,5,4],[1,2,3],[6],[9],[11]]) (.forbid 0 5 4 (.system [[0,12,13,14,15,5,4],[1],[3],[6],[9],[11]]) (.forbid 0 5 5 (.system [[0,12,13,14,15,16,5,4],[1],[3],[6],[9],[11]]) (.forbid 0 5 6 (.system [[0,12,13,14,15,16,17,5,4],[1],[3],[6],[9],[11]]) (.forbid 0 7 1 (.system [[0,12,7,8,9],[1,2,3],[4,5,6],[11]]) (.forbid 1 2 1 (.system [[0],[1,12,2,3],[4,5,6,7,8,9],[11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2,3],[4],[6,7,8,9],[11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2,3],[4,5,6],[9],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2,3],[4],[6],[9],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2,3],[4],[6],[9],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2,3],[4],[6],[9],[11]]) (.forbid 1 4 1 (.system [[0],[3,2,1,12,4,5,6,7,8,9,10,11]]) (.forbid 1 4 2 (.system [[0],[3,2,1,12,13,4],[6,7,8,9],[11]]) (.forbid 1 4 3 (.system [[0],[1,12,13,14,4],[3],[6,7,8,9],[11]]) (.forbid 1 4 4 (.system [[0],[3,2,1,12,13,14,15,4],[6],[9],[11]]) (.forbid 1 4 5 (.system [[0],[1,12,13,14,15,16,4],[3],[6],[9],[11]]) (.forbid 1 4 6 (.system [[0],[1,12,13,14,15,16,17,4],[3],[6],[9],[11]]) (.forbid 1 5 1 (.system [[0],[3,2,1,12,5,4],[6,7,8,9],[11]]) (.forbid 1 5 2 (.system [[0],[1,12,13,5,4],[3],[6,7,8,9],[11]]) (certificate_744_part_1))))))))))))))))))))

noncomputable def certificate_744 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1,2,3],[4,5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1,2,3],[4],[6,7,8,9],[11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[3],[4],[6,7,8,9],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1,2,3],[4],[6],[9],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[3],[4],[6],[9],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[3],[4],[6],[9],[11]]) (.forbid 0 2 1 (.system [[0,12,2,1],[3],[4,5,6,7,8,9],[11]]) (.forbid 0 2 2 (.system [[0,12,13,2,1],[3],[4],[6,7,8,9],[11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2,1],[3],[4,5,6],[9],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2,1],[3],[4],[6],[9],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2,1],[3],[4],[6],[9],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2,1],[3],[4],[6],[9],[11]]) (.forbid 0 3 1 (.system [[0,12,3,2,1],[4,5,6,7,8,9,10,11]]) (.forbid 0 4 1 (.system [[0,12,4,5,6,7,8,9,10,11],[1,2,3]]) (.forbid 0 4 2 (.system [[0,12,13,4],[1,2,3],[6,7,8,9],[11]]) (.forbid 0 4 3 (.system [[0,12,13,14,4],[1],[3],[6,7,8,9],[11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4],[1,2,3],[6],[9],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4],[1],[3],[6],[9],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4],[1],[3],[6],[9],[11]]) (.forbid 0 5 1 (.system [[0,12,5,4],[1,2,3],[6,7,8,9],[11]]) (certificate_744_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates025
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_768_part_1 : FiniteCertificate := .forbid 1 6 1 (.system [[0,1,12,6,5],[2],[3],[7],[8,9,10,11]]) (.forbid 1 6 2 (.system [[0,1,12,13,6,5,4,3],[2],[7],[8],[11]]) (.forbid 1 6 3 (.system [[0,1,12,13,14,6,5],[2],[3],[7],[8],[11]]) (.forbid 1 6 4 (.system [[0,1,12,13,14,15,6,5],[2],[3],[7],[8],[11]]) (.forbid 1 6 5 (.system [[0,1,12,13,14,15,16,6,5],[2],[3],[7],[8],[11]]) (.forbid 1 6 6 (.system [[0,1,12,13,14,15,16,17,6,5],[2],[3],[7],[8],[11]]) (.forbid 2 3 1 (.system [[0,1,2,12,3,4,5,6,7],[8,9,10,11]]) (.forbid 2 4 1 (.system [[0,1,2,12,4,3],[5],[7],[8,9,10,11]]) (.forbid 2 6 1 (.system [[0,1,2,12,6,5],[3],[7],[8,9,10,11]]) (.forbid 3 4 1 (.system [[0,1,2],[3,12,4,5],[7],[8,9,10,11]]) (.forbid 3 4 2 (.system [[0],[2],[3,12,13,4,5],[7],[8,9,10,11]]) (.forbid 3 4 3 (.system [[0,1,2],[3,12,13,14,4,5],[7],[8],[11]]) (.forbid 3 4 4 (.system [[0],[2],[3,12,13,14,15,4,5],[7],[8],[11]]) (.forbid 3 4 5 (.system [[0],[2],[3,12,13,14,15,16,4,5],[7],[8],[11]]) (.forbid 3 4 6 (.system [[0],[2],[3,12,13,14,15,16,17,4,5],[7],[8],[11]]) (.forbid 3 6 1 (.system [[0,1,2],[3,12,6,5],[7],[8,9,10,11]]) (.forbid 3 6 2 (.system [[0],[2],[3,12,13,6,5],[7],[8,9,10,11]]) (.forbid 3 6 3 (.system [[0,1,2],[3,12,13,14,6,5],[7],[8],[11]]) (.forbid 3 6 4 (.system [[0],[2],[3,12,13,14,15,6,5],[7],[8],[11]]) (.forbid 3 6 5 (.system [[0],[2],[3,12,13,14,15,16,6,5],[7],[8],[11]]) (certificate_768_part_0))))))))))))))))))))

noncomputable def certificate_768_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[2,1,0,12,13,14,6,5],[3],[7],[8],[11]]) (.forbid 0 6 4 (.system [[0,12,13,14,15,6,5],[2],[3],[7],[8],[11]]) (.forbid 0 6 5 (.system [[0,12,13,14,15,16,6,5],[2],[3],[7],[8],[11]]) (.forbid 0 6 6 (.system [[0,12,13,14,15,16,17,6,5],[2],[3],[7],[8],[11]]) (.forbid 0 7 1 (.system [[2,1,0,12,7,6,5,4,3],[8,9,10,11]]) (.forbid 0 8 1 (.system [[2,1,0,12,8,9,10,11],[3,4,5,6,7]]) (.forbid 1 2 1 (.system [[0,1,12,2],[3,4,5],[7],[8,9,10,11]]) (.forbid 1 3 1 (.system [[0,1,12,3,4,5],[2],[7],[8,9,10,11]]) (.forbid 1 3 2 (.system [[0,1,12,13,3],[2],[5],[7],[8,9,10,11]]) (.forbid 1 3 3 (.system [[0,1,12,13,14,3,4,5],[2],[7],[8],[11]]) (.forbid 1 3 4 (.system [[0,1,12,13,14,15,3],[2],[5],[7],[8],[11]]) (.forbid 1 3 5 (.system [[0,1,12,13,14,15,16,3],[2],[5],[7],[8],[11]]) (.forbid 1 3 6 (.system [[0,1,12,13,14,15,16,17,3],[2],[5],[7],[8],[11]]) (.forbid 1 4 1 (.system [[0,1,12,4,3],[2],[5],[7],[8,9,10,11]]) (.forbid 1 4 2 (.system [[0,1,12,13,4,3],[2],[5,6,7],[8],[11]]) (.forbid 1 4 3 (.system [[0,1,12,13,14,4,3],[2],[5],[7],[8],[11]]) (.forbid 1 4 4 (.system [[0,1,12,13,14,15,4,3],[2],[5],[7],[8],[11]]) (.forbid 1 4 5 (.system [[0,1,12,13,14,15,16,4,3],[2],[5],[7],[8],[11]]) (.forbid 1 4 6 (.system [[0,1,12,13,14,15,16,17,4,3],[2],[5],[7],[8],[11]]) (.forbid 1 5 1 (.system [[0,1,12,5,4,3],[2],[7],[8,9,10,11]]) (certificate_768_part_1))))))))))))))))))))

noncomputable def certificate_768 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1,2],[3,4,5],[7],[8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1,2],[3],[5],[7],[8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1,2],[3,4,5],[7],[8],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1,2],[3],[5],[7],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1,2],[3],[5],[7],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1,2],[3],[5],[7],[8],[11]]) (.forbid 0 3 1 (.system [[2,1,0,12,3,4,5,6,7],[8,9,10,11]]) (.forbid 0 3 2 (.system [[2,1,0,12,13,3],[5],[7],[8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3],[2],[5],[7],[8,9,10,11]]) (.forbid 0 3 4 (.system [[2,1,0,12,13,14,15,3],[5],[7],[8],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3],[2],[5],[7],[8],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3],[2],[5],[7],[8],[11]]) (.forbid 0 4 1 (.system [[2,1,0,12,4,3],[5],[7],[8,9,10,11]]) (.forbid 0 4 2 (.system [[0,12,13,4,3],[2],[5],[7],[8,9,10,11]]) (.forbid 0 4 3 (.system [[2,1,0,12,13,14,4,3],[5],[7],[8],[11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4,3],[2],[5],[7],[8],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4,3],[2],[5],[7],[8],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4,3],[2],[5],[7],[8],[11]]) (.forbid 0 6 1 (.system [[2,1,0,12,6,5],[3],[7],[8,9,10,11]]) (.forbid 0 6 2 (.system [[0,12,13,6,5],[2],[3],[7],[8,9,10,11]]) (certificate_768_part_2))))))))))))))))))))

noncomputable def certificate_798_part_2 : FiniteCertificate := .forbid 0 4 3 (.system [[0,12,13,14,4,5,6],[1],[2],[3],[8],[11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4],[1],[2],[3],[6],[8],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4],[1],[2],[3],[6],[8],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4],[1],[2],[3],[6],[8],[11]]) (.forbid 0 5 1 (.system [[0,12,5,4],[1],[2],[3],[6],[8,9,10,11]]) (.forbid 0 7 1 (.system [[0,12,7,6],[1],[2],[3],[4],[8,9,10,11]]) (.forbid 0 9 1 (.system [[0,12,9,10,11],[1],[2],[3],[4,5,6],[8]]) (.forbid 1 2 1 (.system [[0],[1,12,2],[3],[4,5,6,7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2],[3],[4],[6],[8,9,10,11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2],[3],[4,5,6],[8],[11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2],[3],[4],[6],[8],[11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2],[3],[4],[6],[8],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2],[3],[4],[6],[8],[11]]) (.forbid 1 3 1 (.system [[0],[1,12,3],[2],[4,5,6,7,8,9,10,11]]) (.forbid 1 3 2 (.system [[0],[1,12,13,3],[2],[4],[6],[8,9,10,11]]) (.forbid 1 3 3 (.system [[0],[1,12,13,14,3],[2],[4,5,6],[8],[11]]) (.forbid 1 3 4 (.system [[0],[1,12,13,14,15,3],[2],[4],[6],[8],[11]]) (.forbid 1 3 5 (.system [[0],[1,12,13,14,15,16,3],[2],[4],[6],[8],[11]]) (.forbid 1 3 6 (.system [[0],[1,12,13,14,15,16,17,3],[2],[4],[6],[8],[11]]) (.forbid 1 4 1 (.system [[0],[1,12,4,5,6,7,8,9,10,11],[2],[3]]) (certificate_798_part_1))))))))))))))))))))

noncomputable def certificate_798 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2],[3],[4,5,6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2],[3],[4],[6],[8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2],[3],[4,5,6],[8],[11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2],[3],[4],[6],[8],[11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2],[3],[4],[6],[8],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[3],[4],[6],[8],[11]]) (.forbid 0 2 1 (.system [[0,12,2],[1],[3],[4,5,6,7,8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2],[1],[3],[4],[6],[8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2],[1],[3],[4,5,6],[8],[11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2],[1],[3],[4],[6],[8],[11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2],[1],[3],[4],[6],[8],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[3],[4],[6],[8],[11]]) (.forbid 0 3 1 (.system [[0,12,3],[1],[2],[4,5,6,7,8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3],[1],[2],[4],[6],[8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3],[1],[2],[4,5,6],[8],[11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3],[1],[2],[4],[6],[8],[11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3],[1],[2],[4],[6],[8],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3],[1],[2],[4],[6],[8],[11]]) (.forbid 0 4 1 (.system [[0,12,4,5,6,7,8,9,10,11],[1],[2],[3]]) (.forbid 0 4 2 (.system [[0,12,13,4],[1],[2],[3],[6],[8,9,10,11]]) (certificate_798_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates027
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_858_part_1 : FiniteCertificate := .forbid 0 4 3 (.system [[0,11,12,13,4,3],[1],[2],[5],[6],[10]]) (.forbid 0 4 4 (.system [[0,11,12,13,14,4,3],[1],[2],[5],[6],[10]]) (.forbid 0 4 5 (.system [[0,11,12,13,14,15,4,3],[1],[2],[5],[6],[10]]) (.forbid 0 4 6 (.system [[0,11,12,13,14,15,16,4,3],[1],[2],[5],[6],[10]]) (.forbid 1 2 1 (.system [[0],[1,11,2],[3,4,5],[6,7,8,9,10]]) (.forbid 1 2 2 (.system [[0],[1,11,12,2],[3],[5],[6,7,8,9,10]]) (.forbid 1 2 3 (.system [[0],[1,11,12,13,2],[3],[5],[6,7,8,9,10]]) (.forbid 1 2 4 (.system [[0],[1,11,12,13,14,2],[3],[5],[6],[10]]) (.forbid 1 2 5 (.system [[0],[1,11,12,13,14,15,2],[3],[5],[6],[10]]) (.forbid 1 2 6 (.system [[0],[1,11,12,13,14,15,16,2],[3],[5],[6],[10]]) (.forbid 1 3 1 (.system [[0],[1,11,3,4,5],[2],[6,7,8,9,10]]) (.forbid 1 3 2 (.system [[0],[1,11,12,3],[2],[5],[6,7,8,9,10]]) (.forbid 1 3 3 (.system [[0],[1,11,12,13,3],[2],[5],[6,7,8,9,10]]) (.forbid 1 3 4 (.system [[0],[1,11,12,13,14,3],[2],[5],[6],[10]]) (.forbid 1 3 5 (.system [[0],[1,11,12,13,14,15,3],[2],[5],[6],[10]]) (.forbid 1 3 6 (.system [[0],[1,11,12,13,14,15,16,3],[2],[5],[6],[10]]) (.forbid 1 4 1 (.system [[0],[1,11,4,3],[2],[5],[6,7,8,9,10]]) (.forbid 1 4 2 (.system [[0],[1,11,12,4,3],[2],[5],[6,7,8,9,10]]) (.forbid 1 4 3 (.system [[0],[1,11,12,13,4,3],[2],[5],[6],[10]]) (.forbid 1 4 4 (.system [[0],[1,11,12,13,14,4,3],[2],[5],[6],[10]]) (certificate_858_part_0))))))))))))))))))))

noncomputable def certificate_858 : FiniteCertificate := .forbid 0 1 1 (.system [[0,11,1],[2],[3,4,5],[6,7,8,9,10]]) (.forbid 0 1 2 (.system [[0,11,12,1],[2],[3],[5],[6,7,8,9,10]]) (.forbid 0 1 3 (.system [[0,11,12,13,1],[2],[3],[5],[6,7,8,9,10]]) (.forbid 0 1 4 (.system [[0,11,12,13,14,1],[2],[3],[5],[6],[10]]) (.forbid 0 1 5 (.system [[0,11,12,13,14,15,1],[2],[3],[5],[6],[10]]) (.forbid 0 1 6 (.system [[0,11,12,13,14,15,16,1],[2],[3],[5],[6],[10]]) (.forbid 0 2 1 (.system [[0,11,2],[1],[3,4,5],[6,7,8,9,10]]) (.forbid 0 2 2 (.system [[0,11,12,2],[1],[3],[5],[6,7,8,9,10]]) (.forbid 0 2 3 (.system [[0,11,12,13,2],[1],[3],[5],[6,7,8,9,10]]) (.forbid 0 2 4 (.system [[0,11,12,13,14,2],[1],[3],[5],[6],[10]]) (.forbid 0 2 5 (.system [[0,11,12,13,14,15,2],[1],[3],[5],[6],[10]]) (.forbid 0 2 6 (.system [[0,11,12,13,14,15,16,2],[1],[3],[5],[6],[10]]) (.forbid 0 3 1 (.system [[0,11,3,4,5],[1],[2],[6,7,8,9,10]]) (.forbid 0 3 2 (.system [[0,11,12,3],[1],[2],[5],[6,7,8,9,10]]) (.forbid 0 3 3 (.system [[0,11,12,13,3],[1],[2],[5],[6,7,8,9,10]]) (.forbid 0 3 4 (.system [[0,11,12,13,14,3],[1],[2],[5],[6],[10]]) (.forbid 0 3 5 (.system [[0,11,12,13,14,15,3],[1],[2],[5],[6],[10]]) (.forbid 0 3 6 (.system [[0,11,12,13,14,15,16,3],[1],[2],[5],[6],[10]]) (.forbid 0 4 1 (.system [[0,11,4,3],[1],[2],[5],[6,7,8,9,10]]) (.forbid 0 4 2 (.system [[0,11,12,4,3],[1],[2],[5],[6,7,8,9,10]]) (certificate_858_part_1))))))))))))))))))))

noncomputable def certificate_859_part_1 : FiniteCertificate := .forbid 1 4 4 (.system [[0],[1,12,13,14,15,4,3],[2],[5],[6],[11]]) (.forbid 1 4 5 (.system [[0],[1,12,13,14,15,16,4,3],[2],[5],[6],[11]]) (.forbid 1 4 6 (.system [[0],[1,12,13,14,15,16,17,4,3],[2],[5],[6],[11]]) (.forbid 1 5 1 (.system [[0],[1,12,5,4,3],[2],[6,7,8,9,10,11]]) (.forbid 2 3 1 (.system [[0],[1],[2,12,3,4,5],[6,7,8,9,10,11]]) (.forbid 2 3 2 (.system [[0],[1],[2,12,13,3],[5],[6,7,8,9,10,11]]) (.forbid 2 3 3 (.system [[0],[1],[2,12,13,14,3],[5],[6,7,8,9,10,11]]) (.forbid 2 3 4 (.system [[0],[1],[2,12,13,14,15,3],[5],[6,7,8,9,10,11]]) (.forbid 2 3 5 (.system [[0],[1],[2,12,13,14,15,16,3],[5],[6],[11]]) (.forbid 2 3 6 (.system [[0],[1],[2,12,13,14,15,16,17,3],[5],[6],[11]]) (.forbid 2 4 1 (.system [[0],[1],[2,12,4,3],[5],[6,7,8,9,10,11]]) (.forbid 2 4 2 (.system [[0],[1],[2,12,13,4,3],[5],[6,7,8,9,10,11]]) (.forbid 2 4 3 (.system [[0],[1],[2,12,13,14,4,3],[5],[6,7,8,9,10,11]]) (.forbid 2 4 4 (.system [[0],[1],[2,12,13,14,15,4,3],[5],[6],[11]]) (.forbid 2 4 5 (.system [[0],[1],[2,12,13,14,15,16,4,3],[5],[6],[11]]) (.forbid 2 4 6 (.system [[0],[1],[2,12,13,14,15,16,17,4,3],[5],[6],[11]]) (.forbid 2 5 1 (.system [[0],[1],[2,12,5,4,3],[6,7,8,9,10,11]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,12,4,5],[6,7,8,9,10,11]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,12,13,4,5],[6,7,8,9,10,11]]) (.forbid 3 4 3 (.system [[0],[1],[2],[3,12,13,14,4,5],[6,7,8,9,10,11]]) (certificate_859_part_0))))))))))))))))))))

noncomputable def certificate_859_part_2 : FiniteCertificate := .forbid 0 4 3 (.system [[0,12,13,14,4,3],[1],[2],[5],[6,7,8,9,10,11]]) (.forbid 0 4 4 (.system [[0,12,13,14,15,4,3],[1],[2],[5],[6],[11]]) (.forbid 0 4 5 (.system [[0,12,13,14,15,16,4,3],[1],[2],[5],[6],[11]]) (.forbid 0 4 6 (.system [[0,12,13,14,15,16,17,4,3],[1],[2],[5],[6],[11]]) (.forbid 0 5 1 (.system [[0,12,5,4,3],[1],[2],[6,7,8,9,10,11]]) (.forbid 1 2 1 (.system [[0],[1,12,2],[3,4,5],[6,7,8,9,10,11]]) (.forbid 1 2 2 (.system [[0],[1,12,13,2],[3],[5],[6,7,8,9,10,11]]) (.forbid 1 2 3 (.system [[0],[1,12,13,14,2],[3],[5],[6,7,8,9,10,11]]) (.forbid 1 2 4 (.system [[0],[1,12,13,14,15,2],[3],[5],[6,7,8,9,10,11]]) (.forbid 1 2 5 (.system [[0],[1,12,13,14,15,16,2],[3],[5],[6],[11]]) (.forbid 1 2 6 (.system [[0],[1,12,13,14,15,16,17,2],[3],[5],[6],[11]]) (.forbid 1 3 1 (.system [[0],[1,12,3,4,5],[2],[6,7,8,9,10,11]]) (.forbid 1 3 2 (.system [[0],[1,12,13,3],[2],[5],[6,7,8,9,10,11]]) (.forbid 1 3 3 (.system [[0],[1,12,13,14,3],[2],[5],[6,7,8,9,10,11]]) (.forbid 1 3 4 (.system [[0],[1,12,13,14,15,3],[2],[5],[6,7,8,9,10,11]]) (.forbid 1 3 5 (.system [[0],[1,12,13,14,15,16,3],[2],[5],[6],[11]]) (.forbid 1 3 6 (.system [[0],[1,12,13,14,15,16,17,3],[2],[5],[6],[11]]) (.forbid 1 4 1 (.system [[0],[1,12,4,3],[2],[5],[6,7,8,9,10,11]]) (.forbid 1 4 2 (.system [[0],[1,12,13,4,3],[2],[5],[6,7,8,9,10,11]]) (.forbid 1 4 3 (.system [[0],[1,12,13,14,4,3],[2],[5],[6,7,8,9,10,11]]) (certificate_859_part_1))))))))))))))))))))

noncomputable def certificate_859 : FiniteCertificate := .forbid 0 1 1 (.system [[0,12,1],[2],[3,4,5],[6,7,8,9,10,11]]) (.forbid 0 1 2 (.system [[0,12,13,1],[2],[3],[5],[6,7,8,9,10,11]]) (.forbid 0 1 3 (.system [[0,12,13,14,1],[2],[3],[5],[6,7,8,9,10,11]]) (.forbid 0 1 4 (.system [[0,12,13,14,15,1],[2],[3],[5],[6,7,8,9,10,11]]) (.forbid 0 1 5 (.system [[0,12,13,14,15,16,1],[2],[3],[5],[6],[11]]) (.forbid 0 1 6 (.system [[0,12,13,14,15,16,17,1],[2],[3],[5],[6],[11]]) (.forbid 0 2 1 (.system [[0,12,2],[1],[3,4,5],[6,7,8,9,10,11]]) (.forbid 0 2 2 (.system [[0,12,13,2],[1],[3],[5],[6,7,8,9,10,11]]) (.forbid 0 2 3 (.system [[0,12,13,14,2],[1],[3],[5],[6,7,8,9,10,11]]) (.forbid 0 2 4 (.system [[0,12,13,14,15,2],[1],[3],[5],[6,7,8,9,10,11]]) (.forbid 0 2 5 (.system [[0,12,13,14,15,16,2],[1],[3],[5],[6],[11]]) (.forbid 0 2 6 (.system [[0,12,13,14,15,16,17,2],[1],[3],[5],[6],[11]]) (.forbid 0 3 1 (.system [[0,12,3,4,5],[1],[2],[6,7,8,9,10,11]]) (.forbid 0 3 2 (.system [[0,12,13,3],[1],[2],[5],[6,7,8,9,10,11]]) (.forbid 0 3 3 (.system [[0,12,13,14,3],[1],[2],[5],[6,7,8,9,10,11]]) (.forbid 0 3 4 (.system [[0,12,13,14,15,3],[1],[2],[5],[6,7,8,9,10,11]]) (.forbid 0 3 5 (.system [[0,12,13,14,15,16,3],[1],[2],[5],[6],[11]]) (.forbid 0 3 6 (.system [[0,12,13,14,15,16,17,3],[1],[2],[5],[6],[11]]) (.forbid 0 4 1 (.system [[0,12,4,3],[1],[2],[5],[6,7,8,9,10,11]]) (.forbid 0 4 2 (.system [[0,12,13,4,3],[1],[2],[5],[6,7,8,9,10,11]]) (certificate_859_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates028
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_888_part_2 : FiniteCertificate := .forbid 0 8 6 (.system [[0,14,15,16,17,18,19,8],[1],[2],[3,4,5,6,7],[13]]) (.forbid 0 9 1 (.system [[0,14,9,10,11,12,13],[1],[2],[3,4,5,6,7],[8]]) (.forbid 0 9 2 (.system [[0,14,15,9,10,11,12,13],[1],[2],[3,4,5,6,7],[8]]) (.forbid 0 9 3 (.system [[0,14,15,16,9,10,11,12,13],[1],[2],[3],[7],[8]]) (.forbid 0 9 4 (.system [[0,14,15,16,17,9,8],[1],[2],[3,4,5,6,7],[13]]) (.forbid 0 9 5 (.system [[0,14,15,16,17,18,9,8],[1],[2],[3,4,5,6,7],[13]]) (.forbid 0 9 6 (.system [[0,14,15,16,17,18,19,9,8],[1],[2],[3],[7],[13]]) (.forbid 1 3 1 (.system [[0],[1,14,3,4,5,6,7],[2],[8,9,10,11,12,13]]) (.forbid 1 4 1 (.system [[0],[1,14,4,5,6,7],[2],[3],[8,9,10,11,12,13]]) (.forbid 1 8 1 (.system [[0],[1,14,8,9,10,11,12,13],[2],[3,4,5,6,7]]) (.forbid 1 9 1 (.system [[0],[1,14,9,10,11,12,13],[2],[3,4,5,6,7],[8]]) (.forbid 2 3 1 (.system [[0],[1],[2,14,3,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 2 4 1 (.system [[0],[1],[2,14,4,5,6,7],[3],[8,9,10,11,12,13]]) (.forbid 2 8 1 (.system [[0],[1],[2,14,8,9,10,11,12,13],[3,4,5,6,7]]) (.forbid 2 9 1 (.system [[0],[1],[2,14,9,10,11,12,13],[3,4,5,6,7],[8]]) (.forbid 3 4 1 (.system [[0],[1],[2],[3,14,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 3 4 2 (.system [[0],[1],[2],[3,14,15,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 3 4 3 (.system [[0],[1],[2],[3,14,15,16,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 3 4 4 (.system [[0],[1],[2],[3,14,15,16,17,4,5,6,7],[8],[13]]) (.forbid 3 4 5 (.system [[0],[1],[2],[3,14,15,16,17,18,4,5,6,7],[8],[13]]) (certificate_888_part_1))))))))))))))))))))

noncomputable def certificate_888 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1],[2],[3,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 0 2 1 (.system [[0,14,2],[1],[3,4,5,6,7],[8,9,10,11,12,13]]) (.forbid 0 3 1 (.system [[0,14,3,4,5,6,7],[1],[2],[8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,4,5,6,7],[1],[2],[8,9,10,11,12,13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,4,5,6,7],[1],[2],[8,9,10,11,12,13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,4,5,6,7],[1],[2],[8],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,4,5,6,7],[1],[2],[8],[13]]) (.forbid 0 4 1 (.system [[0,14,4,5,6,7],[1],[2],[3],[8,9,10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,5,6,7],[1],[2],[3],[8,9,10,11,12,13]]) (.forbid 0 4 3 (.system [[0,14,15,16,4,3],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,3],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[1],[2],[7],[8],[13]]) (.forbid 0 6 1 (.system [[0,14,6,5,4,3],[1],[2],[7],[8,9,10,11,12,13]]) (.forbid 0 8 1 (.system [[0,14,8,9,10,11,12,13],[1],[2],[3,4,5,6,7]]) (.forbid 0 8 2 (.system [[0,14,15,8,9,10,11,12,13],[1],[2],[3,4,5,6,7]]) (.forbid 0 8 3 (.system [[0,14,15,16,8,9,10,11,12,13],[1],[2],[3,4,5,6,7]]) (.forbid 0 8 4 (.system [[0,14,15,16,17,8,9,10,11,12,13],[1],[2],[3],[7]]) (.forbid 0 8 5 (.system [[0,14,15,16,17,18,8],[1],[2],[3,4,5,6,7],[13]]) (certificate_888_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates029
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_911_part_2 : FiniteCertificate := .forbid 0 5 3 (.system [[0,14,15,16,5,4],[1],[2],[6,7,8,9,10],[13]]) (.forbid 0 5 4 (.system [[0,14,15,16,17,5,4],[1],[2],[6,7,8,9,10],[13]]) (.forbid 0 5 5 (.system [[0,14,15,16,17,18,5,4,3,2],[1],[6],[10],[13]]) (.forbid 0 5 6 (.system [[0,14,15,16,17,18,19,5,4],[1],[2],[6],[10],[13]]) (.forbid 0 7 1 (.system [[0,14,7,8,9,10,11,12,13],[1],[2,3,4],[6]]) (.forbid 0 9 1 (.system [[0,14,9,8,7,6],[1],[2,3,4],[10,11,12,13]]) (.forbid 0 11 1 (.system [[0,14,11,12,13],[1],[2,3,4],[6,7,8,9,10]]) (.forbid 1 2 1 (.system [[0],[1,14,2,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2],[4],[6,7,8,9,10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2,3,4],[6,7,8,9,10],[13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2],[4],[6,7,8,9,10],[13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2],[4],[6,7,8,9,10],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2,3,4],[6],[10],[13]]) (.forbid 1 3 1 (.system [[0],[1,14,3,2],[4],[6,7,8,9,10,11,12,13]]) (.forbid 1 3 2 (.system [[0],[1,14,15,3,2],[4,5,6,7,8,9,10],[13]]) (.forbid 1 3 3 (.system [[0],[1,14,15,16,3,2],[4],[6,7,8,9,10],[13]]) (.forbid 1 3 4 (.system [[0],[1,14,15,16,17,3,2],[4],[6,7,8,9,10],[13]]) (.forbid 1 3 5 (.system [[0],[1,14,15,16,17,18,3,2],[4,5,6],[10],[13]]) (.forbid 1 3 6 (.system [[0],[1,14,15,16,17,18,19,3,2],[4],[6],[10],[13]]) (.forbid 1 5 1 (.system [[0],[1,14,5,4],[2],[6,7,8,9,10,11,12,13]]) (certificate_911_part_1))))))))))))))))))))

noncomputable def certificate_911 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1],[2,3,4,5,6,7,8,9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[2],[4],[6,7,8,9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1],[2,3,4],[6,7,8,9,10],[13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[2],[4],[6,7,8,9,10],[13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[2],[4],[6,7,8,9,10],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1],[2,3,4],[6],[10],[13]]) (.forbid 0 2 1 (.system [[0,14,2,3,4,5,6,7,8,9,10,11,12,13],[1]]) (.forbid 0 2 2 (.system [[0,14,15,2],[1],[4],[6,7,8,9,10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2,3,4],[1],[6,7,8,9,10],[13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2],[1],[4],[6,7,8,9,10],[13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2],[1],[4],[6,7,8,9,10],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2,3,4],[1],[6],[10],[13]]) (.forbid 0 3 1 (.system [[0,14,3,2],[1],[4],[6,7,8,9,10,11,12,13]]) (.forbid 0 3 2 (.system [[0,14,15,3,2],[1],[4,5,6,7,8,9,10],[13]]) (.forbid 0 3 3 (.system [[0,14,15,16,3,2],[1],[4],[6,7,8,9,10],[13]]) (.forbid 0 3 4 (.system [[0,14,15,16,17,3,2],[1],[4],[6,7,8,9,10],[13]]) (.forbid 0 3 5 (.system [[0,14,15,16,17,18,3,2],[1],[4,5,6],[10],[13]]) (.forbid 0 3 6 (.system [[0,14,15,16,17,18,19,3,2],[1],[4],[6],[10],[13]]) (.forbid 0 5 1 (.system [[0,14,5,4],[1],[2],[6,7,8,9,10,11,12,13]]) (.forbid 0 5 2 (.system [[0,14,15,5,4,3,2],[1],[6,7,8,9,10],[13]]) (certificate_911_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates030
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_934_part_2 : FiniteCertificate := .forbid 0 5 2 (.system [[0,13,14,5,4],[1],[3],[6],[7,8,9,10,11,12]]) (.forbid 0 5 3 (.system [[0,13,14,15,5,4],[1],[3],[6],[7,8,9,10,11,12]]) (.forbid 0 5 4 (.system [[0,13,14,15,16,5,4],[1,2,3],[6],[7],[12]]) (.forbid 0 5 5 (.system [[0,13,14,15,16,17,5,4],[1],[3],[6],[7],[12]]) (.forbid 0 5 6 (.system [[0,13,14,15,16,17,18,5,4],[1],[3],[6],[7],[12]]) (.forbid 0 6 1 (.system [[0,13,6,5,4],[1,2,3],[7,8,9,10,11,12]]) (.forbid 1 2 1 (.system [[0],[1,13,2,3],[4],[6],[7,8,9,10,11,12]]) (.forbid 1 2 2 (.system [[0],[1,13,14,2,3],[4],[6],[7,8,9,10,11,12]]) (.forbid 1 2 3 (.system [[0],[1,13,14,15,2,3],[4],[6],[7,8,9,10,11,12]]) (.forbid 1 2 4 (.system [[0],[1,13,14,15,16,2,3],[4,5,6],[7],[12]]) (.forbid 1 2 5 (.system [[0],[1,13,14,15,16,17,2,3],[4],[6],[7],[12]]) (.forbid 1 2 6 (.system [[0],[1,13,14,15,16,17,18,2,3],[4],[6],[7],[12]]) (.forbid 1 4 1 (.system [[0],[3,2,1,13,4,5,6],[7,8,9,10,11,12]]) (.forbid 1 4 2 (.system [[0],[1,13,14,4],[3],[6],[7,8,9,10,11,12]]) (.forbid 1 4 3 (.system [[0],[1,13,14,15,4],[3],[6],[7,8,9,10,11,12]]) (.forbid 1 4 4 (.system [[0],[1,13,14,15,16,4],[3],[6],[7,8,9,10,11,12]]) (.forbid 1 4 5 (.system [[0],[3,2,1,13,14,15,16,17,4],[6],[7],[12]]) (.forbid 1 4 6 (.system [[0],[1,13,14,15,16,17,18,4],[3],[6],[7],[12]]) (.forbid 1 5 1 (.system [[0],[1,13,5,4],[3],[6],[7,8,9,10,11,12]]) (.forbid 1 5 2 (.system [[0],[1,13,14,5,4],[3],[6],[7,8,9,10,11,12]]) (certificate_934_part_1))))))))))))))))))))

noncomputable def certificate_934 : FiniteCertificate := .forbid 0 1 1 (.system [[0,13,1,2,3],[4,5,6],[7,8,9,10,11,12]]) (.forbid 0 1 2 (.system [[0,13,14,1],[3],[4],[6],[7,8,9,10,11,12]]) (.forbid 0 1 3 (.system [[0,13,14,15,1],[3],[4],[6],[7,8,9,10,11,12]]) (.forbid 0 1 4 (.system [[0,13,14,15,16,1],[3],[4],[6],[7,8,9,10,11,12]]) (.forbid 0 1 5 (.system [[0,13,14,15,16,17,1,2,3],[4],[6],[7],[12]]) (.forbid 0 1 6 (.system [[0,13,14,15,16,17,18,1],[3],[4],[6],[7],[12]]) (.forbid 0 2 1 (.system [[0,13,2,1],[3],[4],[6],[7,8,9,10,11,12]]) (.forbid 0 2 2 (.system [[0,13,14,2,1],[3],[4],[6],[7,8,9,10,11,12]]) (.forbid 0 2 3 (.system [[0,13,14,15,2,1],[3],[4],[6],[7,8,9,10,11,12]]) (.forbid 0 2 4 (.system [[0,13,14,15,16,2,1],[3],[4,5,6],[7],[12]]) (.forbid 0 2 5 (.system [[0,13,14,15,16,17,2,1],[3],[4],[6],[7],[12]]) (.forbid 0 2 6 (.system [[0,13,14,15,16,17,18,2,1],[3],[4],[6],[7],[12]]) (.forbid 0 3 1 (.system [[0,13,3,2,1],[4,5,6],[7,8,9,10,11,12]]) (.forbid 0 4 1 (.system [[0,13,4,5,6],[1,2,3],[7,8,9,10,11,12]]) (.forbid 0 4 2 (.system [[0,13,14,4],[1],[3],[6],[7,8,9,10,11,12]]) (.forbid 0 4 3 (.system [[0,13,14,15,4],[1],[3],[6],[7,8,9,10,11,12]]) (.forbid 0 4 4 (.system [[0,13,14,15,16,4],[1],[3],[6],[7,8,9,10,11,12]]) (.forbid 0 4 5 (.system [[0,13,14,15,16,17,4],[1,2,3],[6],[7],[12]]) (.forbid 0 4 6 (.system [[0,13,14,15,16,17,18,4],[1],[3],[6],[7],[12]]) (.forbid 0 5 1 (.system [[0,13,5,4],[1],[3],[6],[7,8,9,10,11,12]]) (certificate_934_part_2))))))))))))))))))))

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates031
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def certificate_969_part_2 : FiniteCertificate := .forbid 0 6 3 (.system [[0,14,15,16,6,5],[1],[3],[8],[9,10,11,12,13]]) (.forbid 0 6 4 (.system [[0,14,15,16,17,6,5],[1],[3],[8],[9,10,11,12,13]]) (.forbid 0 6 5 (.system [[0,14,15,16,17,18,6,5],[1,2,3],[8],[9],[13]]) (.forbid 0 6 6 (.system [[0,14,15,16,17,18,19,6,5],[1],[3],[8],[9],[13]]) (.forbid 0 7 1 (.system [[0,14,7,6,5],[1,2,3],[8],[9,10,11,12,13]]) (.forbid 0 8 1 (.system [[0,14,8,7,6,5,4,3,2,1],[9,10,11,12,13]]) (.forbid 0 9 1 (.system [[0,14,9,10,11,12,13],[1,2,3,4,5,6,7,8]]) (.forbid 1 2 1 (.system [[0],[1,14,2,3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 2 2 (.system [[0],[1,14,15,2,3,4,5],[8],[9,10,11,12,13]]) (.forbid 1 2 3 (.system [[0],[1,14,15,16,2,3],[5],[8],[9,10,11,12,13]]) (.forbid 1 2 4 (.system [[0],[1,14,15,16,17,2,3],[5,6,7,8],[9],[13]]) (.forbid 1 2 5 (.system [[0],[1,14,15,16,17,18,2,3,4,5],[8],[9],[13]]) (.forbid 1 2 6 (.system [[0],[1,14,15,16,17,18,19,2,3],[5],[8],[9],[13]]) (.forbid 1 4 1 (.system [[0],[1,14,4,3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 4 2 (.system [[0],[1,14,15,4,3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 1 4 3 (.system [[0],[1,14,15,16,4,3],[5],[8],[9,10,11,12,13]]) (.forbid 1 4 4 (.system [[0],[1,14,15,16,17,4,3],[5,6,7,8],[9],[13]]) (.forbid 1 4 5 (.system [[0],[1,14,15,16,17,18,4,3],[5,6,7,8],[9],[13]]) (.forbid 1 4 6 (.system [[0],[1,14,15,16,17,18,19,4,3],[5],[8],[9],[13]]) (.forbid 1 6 1 (.system [[0],[3,2,1,14,6,7,8],[5],[9,10,11,12,13]]) (certificate_969_part_1))))))))))))))))))))

noncomputable def certificate_969 : FiniteCertificate := .forbid 0 1 1 (.system [[0,14,1,2,3,4,5,6,7,8],[9,10,11,12,13]]) (.forbid 0 1 2 (.system [[0,14,15,1],[3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 1 3 (.system [[0,14,15,16,1,2,3],[5],[8],[9,10,11,12,13]]) (.forbid 0 1 4 (.system [[0,14,15,16,17,1],[3],[5],[8],[9,10,11,12,13]]) (.forbid 0 1 5 (.system [[0,14,15,16,17,18,1],[3],[5,6,7,8],[9],[13]]) (.forbid 0 1 6 (.system [[0,14,15,16,17,18,19,1,2,3],[5],[8],[9],[13]]) (.forbid 0 2 1 (.system [[0,14,2,1],[3],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 2 2 (.system [[0,14,15,2,1],[3,4,5],[8],[9,10,11,12,13]]) (.forbid 0 2 3 (.system [[0,14,15,16,2,1],[3],[5],[8],[9,10,11,12,13]]) (.forbid 0 2 4 (.system [[0,14,15,16,17,2,1],[3],[5,6,7,8],[9],[13]]) (.forbid 0 2 5 (.system [[0,14,15,16,17,18,2,1],[3,4,5],[8],[9],[13]]) (.forbid 0 2 6 (.system [[0,14,15,16,17,18,19,2,1],[3],[5],[8],[9],[13]]) (.forbid 0 4 1 (.system [[0,14,4,3],[1],[5,6,7,8],[9,10,11,12,13]]) (.forbid 0 4 2 (.system [[0,14,15,4,3,2,1],[5],[8],[9,10,11,12,13]]) (.forbid 0 4 3 (.system [[0,14,15,16,4,3],[1],[5],[8],[9,10,11,12,13]]) (.forbid 0 4 4 (.system [[0,14,15,16,17,4,3],[1],[5,6,7,8],[9],[13]]) (.forbid 0 4 5 (.system [[0,14,15,16,17,18,4,3,2,1],[5],[8],[9],[13]]) (.forbid 0 4 6 (.system [[0,14,15,16,17,18,19,4,3],[1],[5],[8],[9],[13]]) (.forbid 0 6 1 (.system [[0,14,6,7,8],[1,2,3],[5],[9,10,11,12,13]]) (.forbid 0 6 2 (.system [[0,14,15,6,5],[1,2,3],[8],[9,10,11,12,13]]) (certificate_969_part_2))))))))))))))))))))

end CycleClique

end OAI
end


