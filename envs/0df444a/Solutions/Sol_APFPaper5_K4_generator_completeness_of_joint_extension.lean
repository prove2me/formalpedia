-- Prove2me | solution 1 for APFPaper5.K4.generator_completeness_of_joint_extension
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:10:38.746202+00:00
-- url     : https://prove2.me/submissions/c7fdcad5-a0c4-4179-9537-328b785d7133

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_completeness_from_composition
title: If every admitted map of one part extends to joint states, every admitted map of two held components is built from turns and recombinations
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K4_JointCarrier. Author's ruling of 2026-11-13: route C.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model of composition. Carries hroot as in
 Thm_APFPaper5_K3_generator_completeness.
statement: (actOnFirst_additiveHomogeneous, actOnFirst_quarter, actOnFirst_pair) the map of joint states that
 acts on the first part alone is additive and homogeneous, commutes with the quarter turn of the joint
 state, and on a product is the product with the first part mapped.
 (commuting_extends_as_map, built_extends_as_map, built_extends) an additive homogeneous map that commutes
 with the quarter turn extends to joint states; so does every map built from turns and recombinations.
 (generator_completeness_of_joint_extension, generator_completeness_of_joint_map_extension) let the admitted
 maps contain the built maps, be closed under doing one after another, and each be additive, homogeneous,
 leave the total cost unchanged and the common turn unseen. If every admitted map extends to joint states,
 every admitted map is built from turns and recombinations.
reading: the exclusion of the rate flip needs no clause of its own. It follows from a nonnegative cost on the
 joint carrier, once a map of a part must also act on a joint state.
not_claimed: that composites at an interface are this carrier; that every admitted map of a part extends to
 joint states there; the composition clause; any K.
-/
import Definitions.Def_APFPaper5_K4_JointCarrier
import Theorems.Thm_APFPaper5_K4_jointFlip_recDiag
import Theorems.Thm_APFPaper5_K4_flipped_part_record_value
import Theorems.Thm_APFPaper5_K4_no_nonneg_flipped_part_record
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend
import Theorems.Thm_APFPaper5_K4_recDiag_jointQuarter
import Theorems.Thm_APFPaper5_K4_linear_of_additive_quarter_unseen
import Theorems.Thm_APFPaper5_K4_extendsToJoint_of_map
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend_as_map
import Theorems.Thm_APFPaper5_K3_built_has_inverse
import Theorems.Thm_APFPaper5_K3_generator_completeness_of_no_flip
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

theorem actOnFirst_additiveHomogeneous (u v : Held2) : JointAdditiveHomogeneous (actOnFirst u v) :=
  ⟨fun p q => by apply Joint.ext <;> dsimp only [actOnFirst, jointAdd] <;> ring,
   fun r p => by apply Joint.ext <;> dsimp only [actOnFirst, jointSmul] <;> ring⟩

theorem actOnFirst_quarter (u v : Held2) (p : Joint) :
    actOnFirst u v (jointQuarter p) = jointQuarter (actOnFirst u v p) := by
  apply Joint.ext <;> dsimp only [actOnFirst, jointQuarter] <;> ring

theorem actOnFirst_pair (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hJ : CommutesWithQuarter T) (h k : Held2) :
    actOnFirst (T ⟨1, 0, 0, 0⟩) (T ⟨0, 0, 1, 0⟩) (pair h k) = pair (T h) k := by
  rw [expand_of_commutes T hlin hJ h]
  apply Joint.ext <;> dsimp only [actOnFirst, pair, add2, smul2, commonTurn] <;> ring

theorem commuting_extends_as_map (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (hJ : CommutesWithQuarter T) : ExtendsToJointMap T :=
  ⟨actOnFirst (T ⟨1, 0, 0, 0⟩) (T ⟨0, 0, 1, 0⟩), actOnFirst_additiveHomogeneous _ _,
    fun p => by rw [actOnFirst_quarter, recDiag_jointQuarter],
    fun h k => by rw [actOnFirst_pair T hlin hJ h k]⟩

theorem built_extends_as_map (U : Held2 → Held2) (hU : BuiltFromTurns U) : ExtendsToJointMap U :=
  commuting_extends_as_map U (built_additiveHomogeneous U hU) (built_commutes_quarter U hU)

theorem built_extends (U : Held2 → Held2) (hU : BuiltFromTurns U) : ExtendsToJoint U :=
  extendsToJoint_of_map U (built_extends_as_map U hU)

theorem generator_completeness_of_joint_extension
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hbuilt : ∀ U : Held2 → Held2, BuiltFromTurns U → U ∈ Adm)
    (hcomp : ∀ S ∈ Adm, ∀ T ∈ Adm, (fun h => S (T h)) ∈ Adm)
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hext : ∀ T ∈ Adm, ExtendsToJoint T) : ∀ T ∈ Adm, BuiltFromTurns T :=
  generator_completeness_of_no_flip hroot Adm hbuilt hcomp hadm
    (fun hmem => rateFlip_does_not_extend (hext rateFlip hmem))

theorem generator_completeness_of_joint_map_extension
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) (Adm : Set (Held2 → Held2))
    (hbuilt : ∀ U : Held2 → Held2, BuiltFromTurns U → U ∈ Adm)
    (hcomp : ∀ S ∈ Adm, ∀ T ∈ Adm, (fun h => S (T h)) ∈ Adm)
    (hadm : ∀ T ∈ Adm, AdditiveHomogeneous T ∧ PreservesTotalCost T ∧ CommonTurnUnseenAfter T)
    (hext : ∀ T ∈ Adm, ExtendsToJointMap T) : ∀ T ∈ Adm, BuiltFromTurns T :=
  generator_completeness_of_joint_extension hroot Adm hbuilt hcomp hadm
    (fun T hT => extendsToJoint_of_map T (hext T hT))

end APFPaper5.K4


theorem solution :
∀
  (hroot :
    ∀ (t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Exists.{1} Real fun (r : Real) =>
          And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
            (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t))
  (Adm : Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
  (hbuilt :
    ∀ (U : APFPaper5.K3.Held2 → APFPaper5.K3.Held2),
      APFPaper5.K3.BuiltFromTurns U →
        @Membership.mem.{0, 0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)
          (Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
          (@Set.instMembership.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)) Adm U)
  (hcomp :
    ∀ (S : APFPaper5.K3.Held2 → APFPaper5.K3.Held2),
      @Membership.mem.{0, 0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)
          (Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
          (@Set.instMembership.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)) Adm S →
        ∀ (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2),
          @Membership.mem.{0, 0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)
              (Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
              (@Set.instMembership.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)) Adm T →
            @Membership.mem.{0, 0} ((h : APFPaper5.K3.Held2) → APFPaper5.K3.Held2)
              (Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
              (@Set.instMembership.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)) Adm fun (h : APFPaper5.K3.Held2) =>
              S (T h))
  (hadm :
    ∀ (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2),
      @Membership.mem.{0, 0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)
          (Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
          (@Set.instMembership.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)) Adm T →
        And (APFPaper5.K3.AdditiveHomogeneous T)
          (And (APFPaper5.K3.PreservesTotalCost T) (APFPaper5.K3.CommonTurnUnseenAfter T)))
  (hext :
    ∀ (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2),
      @Membership.mem.{0, 0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)
          (Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
          (@Set.instMembership.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)) Adm T →
        APFPaper5.K4.ExtendsToJoint T)
  (T : APFPaper5.K3.Held2 → APFPaper5.K3.Held2),
  @Membership.mem.{0, 0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2) (Set.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2))
      (@Set.instMembership.{0} (APFPaper5.K3.Held2 → APFPaper5.K3.Held2)) Adm T →
    APFPaper5.K3.BuiltFromTurns T := by
  exact @APFPaper5.K4.generator_completeness_of_joint_extension
