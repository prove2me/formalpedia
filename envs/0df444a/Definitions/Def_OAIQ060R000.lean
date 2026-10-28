-- Prove2me | Definitions.Def_OAIQ060R000
-- name    : OAIQ060R000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:48:12.078977+00:00
-- url     : https://prove2.me/theorems/4915ac0f-d091-4f13-a662-d06783e4fcd9
-- title:
--   Definitions bundle OAIQ060R000 of the split of OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 570 declarations of OpenAI's Lean: 347 definitions, 6 inductive types or structures, 6 instances and 211 theorems. The definitions and types are `OAI.SharpLogRamsey.AffineIncidence.carrier`, `OAI.SharpLogRamsey.AffineIncidence.onLine`, `OAI.SharpLogRamsey.AffineIncidence.pencil`, `OAI.SharpLogRamsey.AffineIncidence.poorPoints`, `OAI.SharpLogRamsey.AffineIncidence.richPoints`, `OAI.SharpLogRamsey.CoprimeCombination.combinationMap`, `OAI.SharpLogRamsey.FlatnessCore.branchPoint`, `OAI.SharpLogRamsey.FlatnessCore.branchTangent`, `OAI.SharpLogRamsey.FlatnessCore.flatnessPolynomial`, `OAI.SharpLogRamsey.FlatnessCore.jetIdeal`, `OAI.SharpLogRamsey.FlatnessCore.scaledTangent`, `OAI.SharpLogRamsey.GenericCoordinates.base`, `OAI.SharpLogRamsey.GenericCoordinates.direction`, `OAI.SharpLogRamsey.GenericCoordinates.first`, `OAI.SharpLogRamsey.GenericCoordinates.line`, `OAI.SharpLogRamsey.GenericCoordinates.shear`, `OAI.SharpLogRamsey.ImplicitBranch.liftZ`, `OAI.SharpLogRamsey.Interpolation.Box`, `OAI.SharpLogRamsey.Interpolation.exponent`, `OAI.SharpLogRamsey.LineFlatness.hessian`, `OAI.SharpLogRamsey.LineFlatness.restrictLine`, `OAI.SharpLogRamsey.LineFlatness.scaledTangent`, `OAI.SharpLogRamsey.NonplaneCertificate.Index`, `OAI.SharpLogRamsey.NonplaneCertificate.flatFamily`, `OAI.SharpLogRamsey.PolynomialCoordinates.Triple`, `OAI.SharpLogRamsey.PolynomialCoordinates.change`, `OAI.SharpLogRamsey.PolynomialCoordinates.changeHom`, `OAI.SharpLogRamsey.PolynomialCoordinates.encode`, `OAI.SharpLogRamsey.PolynomialCoordinates.unchangeHom`, `OAI.SharpLogRamsey.RamseyProperty`, `OAI.SharpLogRamsey.Sampling.count`, `OAI.SharpLogRamsey.Sampling.degreeMass`, `OAI.SharpLogRamsey.Sampling.internalDegree`, `OAI.SharpLogRamsey.Sampling.selected`, `OAI.SharpLogRamsey.Sampling.weight`, `OAI.SharpLogRamsey.Translation.translate`, `OAI.SharpLogRamsey.TriangleFree.Admissible`, `OAI.SharpLogRamsey.TriangleFree.Z`, `OAI.SharpLogRamsey.TriangleFree.available`, `OAI.SharpLogRamsey.TriangleFree.closed` and 313 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `RamseyFive_Bounds_UpperSet`, `RamseyFive_Decoding_OffFiberPairs`, `RamseyFive_Decoding_PairPoints`, `RamseyFive_Entropy_BlockReveal`, `RamseyFive_Entropy_BlockSelected`, `RamseyFive_Entropy_CapDecoder`, `RamseyFive_Entropy_ClassExtraction`, `RamseyFive_Entropy_ClassSelection`, `RamseyFive_Entropy_CollisionSampling`, `RamseyFive_Entropy_ConditionPullback`, `RamseyFive_Entropy_ConditionalSampling`, `RamseyFive_Entropy_ContextDescription`, `RamseyFive_Entropy_CountedExtraction`, `RamseyFive_Entropy_DescriptionClean`, `RamseyFive_Entropy_EntropyCrossEntropy`, `RamseyFive_Entropy_EventMass`, `RamseyFive_Entropy_EventWeight`, `RamseyFive_Entropy_FiniteGrowth`, `RamseyFive_Entropy_FiniteKernels`, `RamseyFive_Entropy_FinitePiLaw`, `RamseyFive_Entropy_FreshProcess`, `RamseyFive_Entropy_FreshPublicFamily`, `RamseyFive_Entropy_GenericFreshCost`, `RamseyFive_Entropy_GoodEndpoints`, `RamseyFive_Entropy_GoodIndexThreshold`, `RamseyFive_Entropy_GoodPairScores`, `RamseyFive_Entropy_GoodRepresentative`, `RamseyFive_Entropy_GuardedNodeOriginal`, `RamseyFive_Entropy_HighEndpointCutoffs`, `RamseyFive_Entropy_History`, `RamseyFive_Entropy_HistoryCylinder`, `RamseyFive_Entropy_Hits`, `RamseyFive_Entropy_IndependentSampling`, `RamseyFive_Entropy_IndependentTargetLoss`, `RamseyFive_Entropy_Law`, `RamseyFive_Entropy_LevelCellSubset`, `RamseyFive_Entropy_LocalNodeLaw`, `RamseyFive_Entropy_LogSum`, `RamseyFive_Entropy_Map`, `RamseyFive_Entropy_MapFst`, `RamseyFive_Entropy_MarkedActualBudget`, `RamseyFive_Entropy_OptionComposition`, `RamseyFive_Entropy_OrderedExtraction`, `RamseyFive_Entropy_OrderedReciprocalLaw`, `RamseyFive_Entropy_OriginalHistoryPrivate`, `RamseyFive_Entropy_OriginalLevelLaw`, `RamseyFive_Entropy_PermissibleLevels`, `RamseyFive_Entropy_PreRoundDeletion`, `RamseyFive_Entropy_PreparedWindows`, `RamseyFive_Entropy_ReciprocalLossBudget`, `RamseyFive_Entropy_Rectangle`, `RamseyFive_Entropy_Repair`, `RamseyFive_Entropy_RepresentativeSet`, `RamseyFive_Entropy_RevealDomains`, `RamseyFive_Entropy_ScoreFiniteCost`, `RamseyFive_Entropy_SequentialLaw`, `RamseyFive_Entropy_SplitLaw`, `RamseyFive_Entropy_SubsetDeficit`, `RamseyFive_Entropy_SubsetMixture`, `RamseyFive_Entropy_Swap`, `RamseyFive_Entropy_TargetLoss`, `RamseyFive_Entropy_UniformCutoff`, `RamseyFive_Entropy_UniformHistory`, `RamseyFive_Entropy_UnionMarking`, `RamseyFive_Entropy_UnusedRepresentative`, `RamseyFive_Entropy_WindowPosterior`, `RamseyFive_Entropy_WindowReadiness`, `RamseyFive_Geometry_BaseSmallLaw`, `RamseyFive_Geometry_CoreGeometry`, `RamseyFive_Geometry_Cores`, `RamseyFive_Geometry_Failure`, `RamseyFive_Geometry_GeneralReversedCode`, `RamseyFive_Geometry_GeometricRestriction`, `RamseyFive_Geometry_ProjectiveEquiv`, `RamseyFive_Geometry_RectangleTransport`, `RamseyFive_Geometry_SplitEquiv`, `RamseyFive_Geometry_StreamGeometry`, `RamseyFive_Geometry_SubspacePointsEquiv`, `RamseyFive_Iteration_StageState`, `RamseyFive_Marking_ChooseLevel`, `RamseyFive_Marking_DomainTransport`, `RamseyFive_Marking_ReciprocalLevelProducer`, `RamseyFive_Marking_ScanRecord`, `RamseyFive_Marking_ScanRecordPresent`, `RamseyFive_Marking_State`, `RamseyFive_Marking_TwoScan`, `RamseyFive_Probability_CellMass`, `RamseyFive_Streams_DependentPrivateStream`, `RamseyFive_Streams_SelectedTuple`, `RamseyFive_Trees_Windows`, `SharpRamsey_Bounds_SumFiberCenter`, `SharpRamsey_Bounds_Upper`, `SharpRamsey_Entropy_AnchorEventsRealized`, `SharpRamsey_Entropy_CompleteProgramWeight`, `SharpRamsey_Entropy_ComponentLabelWitness`, `SharpRamsey_Entropy_ExternalMass`, `SharpRamsey_Entropy_ForcedHits`, `SharpRamsey_Entropy_HighMoments`, `SharpRamsey_Entropy_LargeCard`, `SharpRamsey_Entropy_MakePair`, `SharpRamsey_Entropy_NewEvents`, `SharpRamsey_Entropy_PatchNotMem`, `SharpRamsey_Entropy_PoissonLaw`, `SharpRamsey_Entropy_SinglesUnique`, `SharpRamsey_Entropy_TruncatedTupleIntegrable`, `SharpRamsey_Entropy_TwoAnchorCrossCost`, `SharpRamsey_Entropy_WitnessList`, `SharpRamsey_Geometry_HessianTangent`, `SharpRamsey_Geometry_RichLines`, `SharpRamsey_Geometry_ScaledTangentDot`, `SharpRamsey_Geometry_TotalDegreeCombination`, `SharpRamsey_Geometry_Triple`, `SharpRamsey_Geometry_Weight`, `SharpRamsey_Model`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ060R002` and `OAIQ060R003`; the statements `OAI.SharpRamseyFive.ScoreGeometry.eventually_high_peel_exceptions`, `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_exceptions` and `OAI.SharpRamseyFive.ScoreGeometry.eventually_literal_plane_half_exceptions`; the proofs of `OAI.SharpRamseyFive.ProjectiveRichLines.quantitative_card_mul_le` and `OAI.SharpRamseyFive.main`.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ060_R5.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SubspacePointsEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def Incident (a : ℙ K V) (b : ℙ K (Module.Dual K V)) : Prop :=
  a.submodule ≤ LinearMap.ker b.rep

def RadialLine (x : ℙ K V) :=
  {W : Submodule K V // finrank K W = 2 ∧ x.submodule ≤ W}

namespace RadialLine

section RadialMass

open scoped Classical

variable [FiniteDimensional K V] {x : ℙ K V} [Fintype (RadialLine x)]

noncomputable def inFlat (W : Submodule K V) : Finset (RadialLine x) := by
  classical
  exact Finset.univ.filter (fun l => l.val ≤ W)

noncomputable def trainingOnLine (X : Finset {y : ℙ K V // x ≠ y})
    (l : RadialLine x) : Finset {y : ℙ K V // x ≠ y} := by
  classical
  exact X.filter (fun y => y.val.submodule ≤ l.val)

end RadialMass

open scoped BigOperators Classical

end RadialLine

open scoped Classical

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Bounds_UpperSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

noncomputable def upperSet (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (l : ℕ) :=
  Finset.univ.filter fun y => finrank K (W y)≤l

noncomputable def levelSet (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (l : ℕ) :=
  Finset.univ.filter fun y => finrank K (W y)=l

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_OffFiberPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.NondominantOverlap
open Module ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (x : ℙ K V)

noncomputable def onPlane (X : Finset {y : ℙ K V // x ≠ y}) (A : Submodule K V) :=
  X.filter fun y => y.val.submodule ≤ A

end SharpRamseyFive.NondominantOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_PairPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ActualOverlap
open Module ProjectiveIncidence NondominantOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K]
  (x : ℙ K V)

noncomputable def pairPoints (X : Finset {y : ℙ K V // x ≠ y})
    (A B : Submodule K V) := onPlane x X (A ⊓ B)

noncomputable def richRadials [Fintype (RadialLine x)]
    (X : Finset {y : ℙ K V // x ≠ y}) (W : Submodule K V) (M : ℕ) :=
  (RadialLine.inFlat W).filter fun l => M ≤ (RadialLine.trainingOnLine X l).card

end SharpRamseyFive.ActualOverlap

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a,0 ≤ mass a
  sum_one : ∑ a,mass a = 1

instance instCoeFunLawForallReal {α : Type*} [Fintype α] : CoeFun (Law α) (fun _ => α → ℝ) := ⟨Law.mass⟩

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def entropy (p : α → ℝ) : ℝ := -∑ a,p a*Real.log (p a)
noncomputable def divergence (p q : α → ℝ) : ℝ := ∑ a,p a*Real.log (p a/q a)

lemma mass_le_one (p : Law α) (a : α) : p a ≤ 1 := by
  rw [←p.sum_one]
  exact Finset.single_le_sum (fun b _ => p.nonneg b) (Finset.mem_univ a)

lemma entropy_nonneg (p : Law α) : 0 ≤ entropy p := by
  unfold entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro a _
  by_cases h : p a=0
  · simp [h]
  · exact mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
      (Real.log_nonpos ((lt_of_le_of_ne (p.nonneg a) (Ne.symm h)).le) (mass_le_one p a))

lemma point_log_ratio (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : 0 < p → 0 < q) : p-q ≤ p*Real.log (p/q) := by
  by_cases h : p=0
  · simp [h,hq]
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm h)
    have hq' := hpq hp'
    have hl := Real.log_le_sub_one_of_pos (div_pos hq' hp')
    have hm := mul_le_mul_of_nonneg_left hl hp
    rw [Real.log_div (ne_of_gt hq') (ne_of_gt hp')] at hm
    rw [Real.log_div h (ne_of_gt hq')]
    have he : p*(q/p-1)=q-p := by field_simp
    rw [he] at hm
    nlinarith

theorem divergence_nonneg (p q : Law α) (hpq : ∀ a,0 < p a → 0 < q a) :
    0 ≤ divergence p q := by
  have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    point_log_ratio (p a) (q a) (p.nonneg a) (q.nonneg a) (hpq a))
  simpa only [Finset.sum_sub_distrib,p.sum_one,q.sum_one,sub_self,divergence] using h

theorem entropy_le_log_card (p : Law α) : entropy p ≤ Real.log (Fintype.card α) := by
  have hne : Nonempty α := by
    by_contra h
    have : IsEmpty α := not_nonempty_iff.mp h
    simpa using p.sum_one
  let := hne
  have hc : 0 < (Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  let u : Law α := ⟨fun _ => 1/Fintype.card α,fun _ => by positivity,by simp [ne_of_gt hc]⟩
  have hd := divergence_nonneg p u (fun _ _ => by dsimp [u]; positivity)
  have he : divergence p u = -entropy p+Real.log (Fintype.card α) := by
    unfold divergence entropy
    calc
      _ = ∑ a,(p a*Real.log (p a)+p a*Real.log (Fintype.card α)) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : p a=0
        · simp [h]
        · dsimp [u]
          rw [div_div_eq_mul_div,div_one,Real.log_mul h (ne_of_gt hc)]
          ring
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,p.sum_one]; ring
  linarith

noncomputable def first (p : Law (α × β)) : Law α where
  mass a := ∑ b,p (a,b)
  nonneg a := Finset.sum_nonneg fun b _ => p.nonneg (a,b)
  sum_one := by rw [←Fintype.sum_prod_type]; exact p.sum_one

noncomputable def second (p : Law (α × β)) : Law β where
  mass b := ∑ a,p (a,b)
  nonneg b := Finset.sum_nonneg fun a _ => p.nonneg (a,b)
  sum_one := by rw [Finset.sum_comm,←Fintype.sum_prod_type]; exact p.sum_one

noncomputable def product (p : Law α) (q : Law β) : Law (α × β) where
  mass z := p z.1*q z.2
  nonneg z := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_one := by rw [Fintype.sum_prod_type]; simp only [←Finset.mul_sum,q.sum_one,mul_one,p.sum_one]

lemma le_first (p : Law (α × β)) (a : α) (b : β) : p (a,b) ≤ first p a :=
  Finset.single_le_sum (fun c _ => p.nonneg (a,c)) (Finset.mem_univ b)
lemma le_second (p : Law (α × β)) (a : α) (b : β) : p (a,b) ≤ second p b :=
  Finset.single_le_sum (fun c _ => p.nonneg (c,b)) (Finset.mem_univ a)

lemma ac_product (p : Law (α × β)) (z : α × β) (hz : 0 < p z) :
    0 < product (first p) (second p) z :=
  mul_pos (hz.trans_le (le_first p _ _)) (hz.trans_le (le_second p _ _))

theorem mutual_information (p : Law (α × β)) :
    divergence p (product (first p) (second p)) =
      entropy (first p)+entropy (second p)-entropy p := by
  have hterm (z : α × β) : p z*Real.log (p z/product (first p) (second p) z) =
      p z*Real.log (p z)-p z*Real.log (first p z.1)-p z*Real.log (second p z.2) := by
    by_cases hz : p z=0
    · simp [hz]
    · have hp : 0 < p z := lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)
      have h1 : first p z.1 ≠ 0 := ne_of_gt (hp.trans_le (le_first p _ _))
      have h2 : second p z.2 ≠ 0 := ne_of_gt (hp.trans_le (le_second p _ _))
      change _ = _
      dsimp [product]
      rw [Real.log_div hz (mul_ne_zero h1 h2),Real.log_mul h1 h2]
      ring
  have hs1 : (∑ z : α × β,p z*Real.log (first p z.1)) =
      ∑ a,first p a*Real.log (first p a) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    rw [←Finset.sum_mul]
    rfl
  have hs2 : (∑ z : α × β,p z*Real.log (second p z.2)) =
      ∑ b,second p b*Real.log (second p b) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    rw [←Finset.sum_mul]
    rfl
  simp only [divergence,hterm,Finset.sum_sub_distrib,hs1,hs2,entropy]
  ring

lemma entropy_subadditive (p : Law (α × β)) :
    entropy p ≤ entropy (first p)+entropy (second p) := by
  have := divergence_nonneg p (product (first p) (second p)) (ac_product p)
  rw [mutual_information] at this
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Map
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] lemma Law.ext {p q : Law α} (h : p.mass=q.mass) : p=q := by
  cases p
  cases q
  cases h
  rfl

noncomputable def map (p : Law α) (f : α → β) : Law β where
  mass b := ∑ a, if f a=b then p a else 0
  nonneg b := Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact p.nonneg a
    · exact le_rfl
  sum_one := by
    rw [Finset.sum_comm]
    classical
    simpa using p.sum_one

lemma sum_map (p : Law α) (f : α → β) (w : β → ℝ) :
    (∑ b,map p f b*w b) = ∑ a,p a*w (f a) := by
  change (∑ b,(∑ a,if f a=b then p a else 0)*w b)=_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  classical
  simp [ite_mul]

lemma map_id (p : Law α) : map p id = p := by
  apply Law.ext
  funext a
  classical
  simp [map]

lemma map_comp (p : Law α) (f : α → β) (g : β → γ) :
    map (map p f) g = map p (g ∘ f) := by
  apply Law.ext
  funext c
  change (∑ b,if g b=c then map p f b else 0)=_
  have h := sum_map p f (fun b => if g b=c then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,map,Function.comp_apply] using h

lemma map_mass_image (p : Law α) (f : α → β) (hf : Function.Injective f) (a : α) :
    map p f (f a)=p a := by
  change (∑ b,if f b=f a then p b else 0)=_
  classical
  simp [hf.eq_iff]

lemma entropy_map_injective (p : Law α) (f : α → β) (hf : Function.Injective f) :
    entropy (map p f)=entropy p := by
  unfold entropy
  rw [sum_map]
  simp only [map_mass_image p f hf]

noncomputable def pair (p : Law α) (f : α → β) (g : α → γ) : Law (β × γ) :=
  map p (fun a => (f a,g a))

lemma first_pair (p : Law α) (f : α → β) (g : α → γ) : first (pair p f g)=map p f := by
  apply Law.ext
  funext b
  simp only [first,pair,map]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a=b
  · simp [h,Prod.mk.injEq]
  · simp [h,Prod.mk.injEq]

lemma second_pair (p : Law α) (f : α → β) (g : α → γ) : second (pair p f g)=map p g := by
  apply Law.ext
  funext c
  simp only [second,pair,map]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : g a=c
  · simp [h,Prod.mk.injEq]
  · simp [h,Prod.mk.injEq]

noncomputable def fiber (p : Law (α × β)) (a : α) : Law β :=
  if h : 0 < first p a then
    { mass := fun b => p (a,b)/first p a
      nonneg := fun b => div_nonneg (p.nonneg _) h.le
      sum_one := by rw [←Finset.sum_div]; exact div_self (ne_of_gt h) }
  else second p

lemma mass_eq_first_mul_fiber (p : Law (α × β)) (a : α) (b : β) :
    p (a,b)=first p a*fiber p a b := by
  by_cases h : 0 < first p a
  · simp only [fiber,dite_eq_left h]
    field_simp
  · have hz : first p a=0 := le_antisymm (le_of_not_gt h) ((first p).nonneg a)
    have hpz : p (a,b)=0 := le_antisymm ((le_first p a b).trans_eq hz) (p.nonneg _)
    simp only [hpz,hz,zero_mul]

lemma log_mass_split (p : Law (α × β)) (a : α) (b : β) :
    p (a,b)*Real.log (p (a,b)) =
      p (a,b)*Real.log (first p a)+
      first p a*(fiber p a b*Real.log (fiber p a b)) := by
  by_cases h : p (a,b)=0
  · rw [h,zero_mul,zero_mul,zero_add]
    have hprod := mass_eq_first_mul_fiber p a b
    rw [h] at hprod
    rw [←mul_assoc,←hprod,zero_mul]
  · have hp : 0 < p (a,b) := lt_of_le_of_ne (p.nonneg _) (Ne.symm h)
    have h1 : first p a ≠ 0 := ne_of_gt (hp.trans_le (le_first p a b))
    have h2 : fiber p a b ≠ 0 := by
      intro hz
      rw [mass_eq_first_mul_fiber p a b,hz,mul_zero] at h
      exact h rfl
    conv_lhs => rw [mass_eq_first_mul_fiber p a b,Real.log_mul h1 h2]
    rw [mass_eq_first_mul_fiber p a b]
    ring

theorem entropy_chain (p : Law (α × β)) :
    entropy p = entropy (first p)+∑ a,first p a*entropy (fiber p a) := by
  have hlog : (∑ a,∑ b,p (a,b)*Real.log (first p a)) =
      ∑ a,first p a*Real.log (first p a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [←Finset.sum_mul]
    rfl
  simp only [entropy,Fintype.sum_prod_type,log_mass_split,Finset.sum_add_distrib,
    hlog,←Finset.mul_sum,mul_neg,Finset.sum_neg_distrib]
  ring

lemma entropy_first_le (p : Law (α × β)) : entropy (first p) ≤ entropy p := by
  rw [entropy_chain]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ =>
    mul_nonneg ((first p).nonneg _) (entropy_nonneg _))

lemma entropy_map_le (p : Law α) (f : α → β) : entropy (map p f) ≤ entropy p := by
  have h := entropy_first_le (pair p f id)
  rw [first_pair] at h
  rw [pair,entropy_map_injective p (fun a => (f a,id a)) (by
    intro a b hab
    exact congrArg Prod.snd hab)] at h
  exact h

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EventMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def eventMass (p : Law α) (E : Finset α) : ℝ := ∑ a ∈ E,p a

noncomputable def iid (p : Law α) (ι : Type*) [Fintype ι] [DecidableEq ι] : Law (ι → α) where
  mass x := ∏ i,p (x i)
  nonneg x := Finset.prod_nonneg fun i _ => p.nonneg (x i)
  sum_one := by
    classical
    rw [←Fintype.prod_sum]
    simp only [p.sum_one,Finset.prod_const_one]

noncomputable def firstAccepted (E : Finset α) : {n : ℕ} → (Fin n → α) → Option α
  | 0,_ => none
  | _+1,x => if x 0∈E then some (x 0) else firstAccepted E (fun i => x i.succ)

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FinitePiLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι→Type*} [∀i,Fintype (β i)]

noncomputable def piLaw (p : ∀i,Law (β i)) : Law (∀i,β i) where
  mass x := ∏i,p i (x i)
  nonneg x := Finset.prod_nonneg fun i _=>(p i).nonneg _
  sum_one := by rw [←Fintype.prod_sum];simp only [(p _).sum_one,Finset.prod_const_one]

end

open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

lemma entropy_le_cross_subprob (p : Law α) (r : α→ℝ)
    (hr : ∀a,0 < r a) (hs : ∑a,r a≤1) :
    entropy p ≤ -∑a,p a*Real.log (r a) := by
  have hh := Finset.sum_le_sum (fun a (_ : a∈Finset.univ)=>
    point_log_ratio (p a) (r a) (p.nonneg _) (hr _).le (fun _=>hr _))
  have he : (∑a,p a*Real.log (p a/r a))=
      (∑a,p a*Real.log (p a))-(∑a,p a*Real.log (r a)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hz : p a=0
    · simp [hz]
    · rw [Real.log_div hz (hr _).ne'];ring
  rw [Finset.sum_sub_distrib,p.sum_one,he] at hh
  dsimp only [entropy]
  linarith

lemma finite_geometric_mass (z : α→ℕ) (hz : Function.Injective z)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r≤1) :
    (∑a,(1-r)*r^(z a))≤1 := by
  let S := Finset.univ.image z
  let N := S.sup id+1
  have hsub : S⊆Finset.range N := by
    intro n hn
    apply Finset.mem_range.mpr
    have := Finset.le_sup (f:=id) hn
    dsimp only [id] at this
    dsimp only [N]
    omega
  have he (m : ℕ) : (∑n∈Finset.range m,(1-r)*r^n)=1-r^m := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ,ih,pow_succ];ring
  have hi : (∑a,(1-r)*r^(z a))=∑n∈S,(1-r)*r^n := by
    dsimp only [S]
    rw [Finset.sum_image]
    exact fun a _ b _ h=>hz h
  rw [hi]
  calc
    _ ≤ ∑n∈Finset.range N,(1-r)*r^n := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _=>mul_nonneg (sub_nonneg.mpr hr1) (pow_nonneg hr _))
    _ = 1-r^N := he N
    _ ≤ 1 := by linarith [pow_nonneg hr N]

theorem integer_entropy (p : Law α) (z : α→ℕ) (hz : Function.Injective z)
    (M : ℝ) (hM : 0<M) (hm : (∑a,p a*(z a:ℝ))≤M) :
    entropy p≤Real.log (M+1)+1 := by
  let r := M/(M+1)
  have hMp : 0<M+1 := by linarith
  have hr : 0 < r := div_pos hM hMp
  have hr1 : r<1 := (div_lt_one hMp).mpr (by linarith)
  have hs := finite_geometric_mass z hz r hr.le hr1.le
  have hh := entropy_le_cross_subprob p (fun a=>(1-r)*r^(z a))
    (fun a=>mul_pos (sub_pos.mpr hr1) (pow_pos hr _)) hs
  have he : (∑a,p a*Real.log ((1-r)*r^(z a)))=
      Real.log (1-r)+(∑a,p a*(z a:ℝ))*Real.log r := by
    simp only [Real.log_mul (sub_pos.mpr hr1).ne' (pow_ne_zero _ hr.ne'),Real.log_pow]
    simp only [mul_add,Finset.sum_add_distrib,←mul_assoc,←Finset.sum_mul,p.sum_one,one_mul]
  rw [he] at hh
  have hlogr : Real.log r≤0 := Real.log_nonpos hr.le hr1.le
  have hm' := mul_le_mul_of_nonpos_right hm hlogr
  have h1 : 1-r=1/(M+1) := by dsimp only [r];field_simp;ring
  have hl1 : Real.log (1-r)= -Real.log (M+1) := by
    rw [h1,Real.log_div one_ne_zero hMp.ne',Real.log_one,zero_sub]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hMp hM)
  have hlr : Real.log ((M+1)/M)= -Real.log r := by
    rw [Real.log_div hMp.ne' hM.ne']
    dsimp only [r]
    rw [Real.log_div hM.ne' hMp.ne']
    ring
  rw [hlr] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hM.le
  have heq : M*((M+1)/M-1)=1 := by field_simp;ring
  rw [heq] at hmul
  rw [hl1] at hh
  nlinarith

noncomputable def atomLevel (p : Law α) (a : α) : ℕ := ⌊-Real.log (p a)⌋₊
noncomputable def levelRange (p : Law α) : Finset ℕ := Finset.univ.image (atomLevel p)
abbrev Level (p : Law α) := ↥(levelRange p)
noncomputable def levelIndex (p : Law α) (a : α) : Level p :=
  ⟨atomLevel p a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
noncomputable def levelLaw (p : Law α) : Law (Level p) := map p (levelIndex p)
noncomputable def levelCell (p : Law α) (n : Level p) : Finset α :=
  Finset.univ.filter (fun a=>0<p a ∧ atomLevel p a=n.val)

lemma mem_levelCell (p : Law α) (n : Level p) (a : α) :
    a∈levelCell p n ↔ 0<p a ∧ atomLevel p a=n.val := by simp [levelCell]

lemma atomLevel_le (p : Law α) (a : α) : (atomLevel p a:ℝ)≤ -Real.log (p a) := by
  exact Nat.floor_le (neg_nonneg.mpr (Real.log_nonpos (p.nonneg _) (mass_le_one p a)))

lemma atomLevel_lt (p : Law α) (a : α) : -Real.log (p a)<(atomLevel p a:ℝ)+1 :=
  Nat.lt_floor_add_one _

lemma level_mean_le_entropy (p : Law α) :
    (∑n : Level p,levelLaw p n*(n.val:ℝ))≤entropy p := by
  unfold levelLaw
  rw [sum_map]
  calc
    _ ≤ ∑a,p a*(-Real.log (p a)) := Finset.sum_le_sum fun a _=>
      mul_le_mul_of_nonneg_left (atomLevel_le p a) (p.nonneg _)
    _ = entropy p := by simp [entropy,mul_neg]

theorem endpoint_level_entropy (p : Law α) (M : ℝ) (hM : 0<M)
    (hp : entropy p≤M) : entropy (levelLaw p)≤Real.log (M+1)+1 :=
  integer_entropy (levelLaw p) Subtype.val Subtype.val_injective M hM
    ((level_mean_le_entropy p).trans hp)

lemma level_mass (p : Law α) (n : Level p) :
    levelLaw p n=∑a∈levelCell p n,p a := by
  simp only [levelLaw,map,levelCell,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p a=0
  · simp [hp]
  · have hp0 : 0<p a := lt_of_le_of_ne (p.nonneg _) (Ne.symm hp)
    simp only [hp0,true_and]
    have he : levelIndex p a=n ↔ atomLevel p a=n.val := Subtype.ext_iff
    by_cases h : atomLevel p a=n.val <;> simp [he,h]

lemma same_level_ratio (p : Law α) (n : Level p) {a b : α}
    (ha : a∈levelCell p n) (hb : b∈levelCell p n) :
    p b≤Real.exp 1*p a := by
  obtain ⟨ha0,hae⟩ := (mem_levelCell p n a).mp ha
  obtain ⟨hb0,hbe⟩ := (mem_levelCell p n b).mp hb
  have h₁ := atomLevel_le p b
  have h₂ := atomLevel_lt p a
  rw [hae] at h₂
  rw [hbe] at h₁
  have hl : Real.log (p b)≤1+Real.log (p a) := by linarith
  have he := Real.exp_le_exp.mpr hl
  simpa only [Real.exp_add,Real.exp_log ha0,Real.exp_log hb0] using he

lemma level_mass_bound (p : Law α) (n : Level p) {a : α}
    (ha : a∈levelCell p n) :
    levelLaw p n≤(levelCell p n).card*Real.exp 1*p a := by
  rw [level_mass]
  calc
    _ ≤ ∑b∈levelCell p n,Real.exp 1*p a :=
      Finset.sum_le_sum (fun b hb=>same_level_ratio p n ha hb)
    _ = _ := by simp [mul_assoc]

noncomputable def conditionOn (p : Law α) (E : Finset α) (hE : 0<eventMass p E) : Law α where
  mass a := if a∈E then p a/eventMass p E else 0
  nonneg a := by
    split
    · exact div_nonneg (p.nonneg _) hE.le
    · exact le_refl 0
  sum_one := by rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,
    ←Finset.sum_div];exact div_self hE.ne'

lemma conditionOn_apply (p : Law α) (E : Finset α) (hE : 0<eventMass p E) (a : α) :
    conditionOn p E hE a=if a∈E then p a/eventMass p E else 0 := rfl

theorem good_level_domination (p : Law α) (Good : Finset α) (E : Finset (Level p))
    (hE : (1:ℝ)/2≤eventMass (levelLaw p) E)
    (hhalf : ∀n∈E,(levelCell p n).card≤2*(levelCell p n∩Good).card) (a : α) :
    let c := conditionOn (levelLaw p) E (by linarith : 0<eventMass (levelLaw p) E)
    (∑n : Level p,c n*(if a∈levelCell p n∩Good then 1/((levelCell p n∩Good).card:ℝ) else 0))
      ≤4*Real.exp 1*p a := by
  dsimp only
  have hZ : 0<eventMass (levelLaw p) E := by linarith
  have hpa := p.nonneg a
  calc
    _ ≤ ∑n : Level p,if levelIndex p a=n then 4*Real.exp 1*p a else 0 := by
      apply Finset.sum_le_sum
      intro n _
      rw [conditionOn_apply]
      by_cases hn : n∈E
      · rw [ite_eq_left hn]
        by_cases ha : a∈levelCell p n∩Good
        · rw [ite_eq_left ha]
          have ham := (Finset.mem_inter.mp ha).1
          have he : levelIndex p a=n := Subtype.ext ((mem_levelCell p n a).mp ham).2
          rw [ite_eq_left he]
          have hcard : (0:ℝ)<(levelCell p n∩Good).card := by
            exact_mod_cast Finset.card_pos.mpr ⟨a,ha⟩
          have hm := level_mass_bound p n ham
          have hh : ((levelCell p n).card:ℝ)≤2*(levelCell p n∩Good).card := by exact_mod_cast hhalf n hn
          have h₁ := mul_le_mul_of_nonneg_right hh (mul_nonneg (Real.exp_pos 1).le (p.nonneg a))
          have h₂ := mul_le_mul_of_nonneg_right hE
            (by positivity : (0:ℝ)≤4*Real.exp 1*p a*(levelCell p n∩Good).card)
          rw [div_mul_div_comm,mul_one]
          apply (div_le_iff₀ (mul_pos hZ hcard)).mpr
          nlinarith
        · rw [ite_eq_right ha,mul_zero]
          split <;> positivity
      · rw [ite_eq_right hn,zero_mul]
        split <;> positivity
    _ = _ := by simp

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Hits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def hits {n : ℕ} (H : Finset α) (x : Fin n → α) : ℝ :=
  ∑ i,if x i∈H then 1 else 0

end
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def uniformOn (A : Finset α) (hA : A.Nonempty) : Law α where
  mass a := if a∈A then (A.card:ℝ)⁻¹ else 0
  nonneg a := by split_ifs <;> positivity
  sum_one := by
    have hc : (A.card:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hA)
    rw [←Finset.sum_filter,Finset.filter_univ_mem,Finset.sum_const,nsmul_eq_mul,mul_inv_cancel₀ hc]

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SequentialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def adaptiveLaw (p : Law α) (next : α→Law β) : Law (α×β) where
  mass ab := p ab.1*next ab.1 ab.2
  nonneg ab := mul_nonneg (p.nonneg _) ((next _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type,←Finset.mul_sum,(next _).sum_one,mul_one]
    exact p.sum_one

lemma map_positive (p : Law α) (f : α→β) (b : β) (hb : 0 < map p f b) :
    ∃a,0<p a ∧ f a=b := by
  change 0<(∑a,if f a=b then p a else 0) at hb
  have hn (a : α) (_ : a∈Finset.univ) : 0 ≤ (if f a=b then p a else 0) := by
    split_ifs
    · exact p.nonneg a
    · rfl
  obtain ⟨a,_,ha⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp hb
  by_cases he : f a=b
  · exact ⟨a,by simpa [he] using ha,he⟩
  · simp [he] at ha

noncomputable def pureLaw (a : α) : Law α where
  mass b := if b=a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  sum_one := by simp

end

open MeasureTheory
open scoped Classical BigOperators
variable {Ω α : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α]

noncomputable def finiteImageLaw (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α) : Law α where
  mass a := μ.real {ω | f ω=a}
  nonneg a := measureReal_nonneg
  sum_one := by
    have hd : Pairwise (fun a b : α=>Disjoint {ω | f ω=a} {ω | f ω=b}) := by
      intro a b hab
      apply Set.disjoint_left.mpr
      intro ω ha hb
      exact hab (ha.symm.trans hb)
    have he : (⋃a : α,{ω | f ω=a})=Set.univ := by ext ω;simp
    have hh := measureReal_iUnion_fintype (μ:=μ) hd
      (fun a=>Set.Countable.measurableSet (Set.to_countable _))
    rw [he,probReal_univ] at hh
    exact hh.symm

noncomputable def chooseMessage (P : Ω→α→Prop) (ω : Ω) : Option α :=
  if h : ∃a,P ω a then some h.choose else none

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HistoryCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def uniformType (α : Type*) [Fintype α] [Nonempty α] : Law α :=
  uniformOn Finset.univ Finset.univ_nonempty

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LogSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

lemma map_first (p : Law (α × β)) : map p Prod.fst=first p := by
  apply Law.ext
  funext a
  simp only [map,first,Fintype.sum_prod_type]
  classical
  rw [Finset.sum_comm]
  simp

lemma map_second (p : Law (α × β)) : map p Prod.snd=second p := by
  apply Law.ext
  funext b
  simp only [map,second,Fintype.sum_prod_type]
  classical
  simp

end

open scoped BigOperators Classical
variable {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

noncomputable def mapSnd (p : Law (α × β)) (f : β → γ) : Law (α × γ) :=
  map p (fun z => (z.1,f z.2))

lemma mapSnd_mass (p : Law (α × β)) (f : β → γ) (a : α) (c : γ) :
    mapSnd p f (a,c) = ∑ b,if f b=c then p (a,b) else 0 := by
  simp only [mapSnd,map,Fintype.sum_prod_type,Prod.mk.injEq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : f b=c <;> simp [h]

lemma first_mapSnd (p : Law (α × β)) (f : β → γ) : first (mapSnd p f)=first p := by
  change first (pair p Prod.fst (f ∘ Prod.snd))=_
  rw [first_pair,map_first]

lemma second_mapSnd (p : Law (α × β)) (f : β → γ) : second (mapSnd p f)=map (second p) f := by
  change second (pair p Prod.fst (f ∘ Prod.snd))=_
  rw [second_pair,←map_comp,map_second]

lemma fiber_mapSnd (p : Law (α × β)) (f : β → γ) (a : α) :
    fiber (mapSnd p f) a = map (fiber p a) f := by
  by_cases h : 0 < first p a
  · apply Law.ext
    funext c
    simp only [fiber,first_mapSnd,dite_eq_left h]
    change mapSnd p f (a,c)/first p a=∑ b,if f b=c then p (a,b)/first p a else 0
    rw [mapSnd_mass,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  · simp only [fiber,first_mapSnd,dite_eq_right h,second_mapSnd]

noncomputable def totalCorrelation (p : Law (ι → β)) : ℝ :=
  (∑ i,entropy (map p (fun x => x i)))-entropy p

noncomputable def information (p : Law (α × β)) : ℝ :=
  entropy (first p)+entropy (second p)-entropy p

lemma information_nonneg (p : Law (α × β)) : 0 ≤ information p := by
  dsimp [information]
  linarith [entropy_subadditive p]

noncomputable def independent (p : ι → Law β) : Law (ι → β) where
  mass x := ∏ i,p i (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (p i).nonneg _
  sum_one := by
    rw [←Fintype.prod_sum]
    simp only [Law.sum_one,Finset.prod_const_one]

lemma map_eval_mass_pos (p : Law (ι → β)) (x : ι → β) (hx : 0<p x) (i : ι) :
    0 < map p (fun z => z i) (x i) := by
  apply hx.trans_le
  change p x≤∑ z,if z i=x i then p z else 0
  have hh := Finset.single_le_sum (s := Finset.univ) (a := x)
    (f := fun z => if z i=x i then p z else 0) (fun z _ => by split_ifs; exact p.nonneg _; rfl)
    (Finset.mem_univ x)
  simpa using hh

theorem totalCorrelation_nonneg (p : Law (ι → β)) : 0≤totalCorrelation p := by
  let q : Law (ι → β) := independent (fun i => map p (fun z => z i))
  have hac (x : ι → β) (hx : 0<p x) : 0<q x :=
    Finset.prod_pos (fun i _ => map_eval_mass_pos p x hx i)
  have hd := divergence_nonneg p q hac
  have hpq (x : ι → β) : p x*Real.log (p x/q x) =
      p x*Real.log (p x)-∑ i,p x*Real.log (map p (fun z => z i) (x i)) := by
    by_cases h : p x=0
    · simp only [h,zero_mul,Finset.sum_const_zero,sub_zero]
    · have hx : 0<p x := lt_of_le_of_ne (p.nonneg x) (Ne.symm h)
      rw [Real.log_div h (ne_of_gt (hac x hx))]
      have he : Real.log (q x)=∑ i,Real.log (map p (fun z => z i) (x i)) := by
        apply Real.log_prod
        intro i _
        exact ne_of_gt (map_eval_mass_pos p x hx i)
      rw [he,mul_sub,Finset.mul_sum]
  have he : divergence p q=totalCorrelation p := by
    simp only [divergence,hpq,Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    have hm (i : ι) : (∑ x,p x*Real.log (map p (fun z => z i) (x i))) =
        -entropy (map p (fun z => z i)) := by
      rw [←sum_map p (fun z => z i) (fun b => Real.log (map p (fun z => z i) b))]
      simp only [entropy,neg_neg]
    simp only [hm,Finset.sum_neg_distrib,totalCorrelation,entropy]
    ring
  rwa [he] at hd

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SplitLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {ι β : Type*} [Fintype ι] [Fintype β]

noncomputable local instance instDecidableEqSubtypeMemFinset_solutions (E : Finset ι) : DecidableEq E := Classical.decEq _

noncomputable def reveal (p : Law (ι → β)) (E : Finset ι) : Law ((E → β) × (ι → β)) :=
  pair p (fun x i => x i.val) id

lemma second_reveal (p : Law (ι → β)) (E : Finset ι) :
    second (reveal p E) = p := by rw [reveal,second_pair,map_id]

end

open scoped BigOperators Classical
variable {ι β : Type} [Fintype ι] [Fintype β]

noncomputable local instance instDecidableEqSubtypeMemFinset_solutions_1_rc9f2bd_1 (E : Finset ι) : DecidableEq E := Classical.decEq _
noncomputable def revealCost (p : Law (ι → β)) (E : Finset ι) : ℝ :=
  ∑ i∈Eᶜ,information (mapSnd (reveal p E) (fun x => x i))

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RepresentativeSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical NNReal
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]

noncomputable local instance instDecidableEqSumProd_solutions : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

noncomputable local instance instDecidableEqSubtypeSumProdMemFinset_solutions_rc9f2bd_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
noncomputable def representativeSet (s : B → A) : Finset ((B × A) ⊕ T) :=
  Finset.univ.image fun b => Sum.inl (b,s b)

noncomputable def coordinateInformation (p : Law (((B × A) ⊕ T) → β))
    (i j : (B × A) ⊕ T) : ℝ≥0 :=
  ⟨information (pair p (fun x => x j) (fun x => x i)),information_nonneg _⟩

noncomputable def blockInformation (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (b : B) (a : A) : ℝ≥0 :=
  (Finset.univ.erase b).sup fun c => coordinateInformation p (Sum.inl (b,a)) (Sum.inl (c,s c))

noncomputable def middleInformation (p : Law (((B × A) ⊕ T) → β))
    (s : B → A) (t : T) : ℝ≥0 :=
  Finset.univ.sup fun c => coordinateInformation p (Sum.inr t) (Sum.inl (c,s c))

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UnusedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
local instance instDecidableEqSumProd_solutions_1 : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

end

open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

def mean (p : Law α) (f : α → ℝ) : ℝ := ∑ a, p a * f a
lemma mean_const (p : Law α) (c : ℝ) : mean p (fun _ => c) = c := by
  rw [mean, ←Finset.sum_mul, p.sum_one, one_mul]
lemma mean_sub (p : Law α) (f g : α → ℝ) : mean p (fun a => f a - g a) = mean p f - mean p g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]
lemma mean_congr (p : Law α) {f g : α → ℝ} (h : ∀ a, f a = g a) : mean p f = mean p g := by
  exact Finset.sum_congr rfl fun a _ => congrArg (fun x => p a*x) (h a)
lemma mean_map (p : Law α) (g : α → β) (f : β → ℝ) : mean (map p g) f = mean p (fun a => f (g a)) := by
  simp only [mean, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp
lemma mean_adaptive (p : Law α) (q : α → Law β) (f : α × β → ℝ) :
    mean (adaptiveLaw p q) f = mean p (fun a => mean (q a) (fun b => f (a,b))) := by
  simp only [mean, adaptiveLaw, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BlockReveal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance instDecidableEqSumProd_solutions_2 : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

local instance instDecidableEqSubtypeSumProdMemFinset_solutions_2_rc9f2bd_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
def freshBlockLaw (S : B → Finset A) : Law (B → A) :=
  piLaw fun b => if h : (S b).Nonempty then uniformOn (S b) h else uniformType A

def eraseBlock (S : B → Finset A) (s : B → A) : B → Finset A := fun b => (S b).erase (s b)

def blockAllInformation (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (s : B → A) : ℝ :=
  (∑ b, ∑ a ∈ S b, (blockInformation p s b a : ℝ)) +
    ∑ t, (middleInformation p s t : ℝ)

def blockRoundMean
    (J : Law (((B × A) ⊕ T) → β) → (B → Finset A) → (B → A) → ℝ)
    (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A) : (n : ℕ) → Fin n → ℝ
  | 0 => Fin.elim0
  | n+1 => Fin.cases (mean (freshBlockLaw S) (J p S)) (fun i =>
      mean (freshBlockLaw S) (fun s => mean (first (reveal p (representativeSet s)))
        (fun a => blockRoundMean J (fiber (reveal p (representativeSet s)) a)
          (eraseBlock S s) n i)))

end
end

open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def support (p : Law α) : Finset α := Finset.univ.filter fun a => 0 < p a

lemma mem_support (p : Law α) (a : α) : a ∈ support p ↔ 0 < p a := by simp [support]

lemma outside_support (p : Law α) {a : α} (ha : a ∉ support p) : p a=0 := by
  exact le_antisymm (le_of_not_gt (fun h => ha ((mem_support p a).mpr h))) (p.nonneg a)

noncomputable def supportLaw (p : Law α) : Law (support p) where
  mass a := p a.val
  nonneg a := p.nonneg _
  sum_one := by
    rw [Finset.sum_coe_sort (support p)]
    calc
      _ = ∑ a,p a := Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => outside_support p ha)
      _ = 1 := p.sum_one

lemma map_supportLaw (p : Law α) : map (supportLaw p) Subtype.val = p := by
  apply Law.ext
  funext a
  change (∑ b : support p,if b.val=a then p b.val else 0)=p a
  rw [Finset.sum_coe_sort (support p) (fun b : α => if b=a then p b else 0)]
  by_cases h : a ∈ support p
  · simp [h]
  · have hz := outside_support p h
    simp [h,hz]

theorem entropy_le_log_support (p : Law α) : entropy p ≤ Real.log (support p).card := by
  have hh := entropy_le_log_card (supportLaw p)
  have he := entropy_map_injective (supportLaw p) Subtype.val Subtype.val_injective
  rw [map_supportLaw] at he
  rw [←he] at hh
  simpa only [Fintype.card_coe] using hh

lemma entropy_support_cap (p : Law α) (N : ℝ) (hN : (support p).card ≤ N) :
    entropy p ≤ Real.log N := by
  have hc : (0:ℝ) < (support p).card := by
    have he : Nonempty (support p) := by
      by_contra h
      have : IsEmpty (support p) := not_nonempty_iff.mp h
      simpa using (supportLaw p).sum_one
    have hh : 0<(support p).card := by simpa only [Fintype.card_coe] using Fintype.card_pos_iff.mpr he
    exact_mod_cast hh
  exact (entropy_le_log_support p).trans (Real.log_le_log hc hN)

noncomputable def eventProbability (p : Law α) (S : Finset α) : ℝ := ∑ a ∈ S,p a

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_RevealDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι β : Type*} [Fintype ι] [Fintype β]
local instance instDecidableEq_solutions : DecidableEq ι := Classical.decEq _
local instance instDecidableEqSubtypeMemFinset_solutions_2 (E : Finset ι) : DecidableEq E := Classical.decEq _

lemma mean_mono_pos {α : Type*} [Fintype α] (p : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < p a → f a ≤ g a) : mean p f ≤ mean p g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hz : p a = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (h a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz))) (p.nonneg a)

lemma reveal_positive (p : Law (ι → β)) (E : Finset ι) (a : E → β) (x : ι → β)
    (h : 0 < reveal p E (a,x)) : 0 < p x ∧ (fun i : E => x i.val) = a := by
  obtain ⟨y,hy,he⟩ := map_positive p (fun y => ((fun i : E => y i.val),y)) (a,x) h
  have hxy : y = x := congrArg Prod.snd he
  subst y
  exact ⟨hy,congrArg Prod.fst he⟩

lemma fiber_reveal_support (p : Law (ι → β)) (E : Finset ι) (a : E → β)
    (x : ι → β) (hx : 0 < fiber (reveal p E) a x) : 0 < p x := by
  by_cases ha : 0 < first (reveal p E) a
  · apply (reveal_positive p E a x _).1
    rw [mass_eq_first_mul_fiber]
    exact mul_pos ha hx
  · simpa only [fiber, dite_eq_right ha, second_reveal] using hx

def InDomains (p : Law (ι → β)) (D : ι → Finset β) : Prop :=
  ∀ x, 0 < p x → ∀ i, x i ∈ D i

lemma InDomains.entropy_cap {p : Law (ι → β)} {D : ι → Finset β}
    (h : InDomains p D) (J : ℝ) (hJ : ∀ i, Real.log (D i).card ≤ J) (i : ι) :
    entropy (map p (fun x => x i)) ≤ J := by
  apply le_trans (entropy_support_cap _ (D i).card _) (hJ i)
  exact_mod_cast Finset.card_le_card (show support (map p (fun x => x i)) ⊆ D i from by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := map_positive p (fun x => x i) b ((mem_support _ _).mp hb)
    exact h x hx i)

def FixedOutside (p : Law (ι → β)) (U : Finset ι) : Prop :=
  ∀ i, i ∉ U → ∃ b, ∀ x, 0 < p x → x i = b

lemma constant_coordinate_entropy (p : Law (ι → β)) (i : ι) (b : β)
    (h : ∀ x, 0 < p x → x i = b) : entropy (map p (fun x => x i)) = 0 := by
  apply le_antisymm _ (entropy_nonneg _)
  calc
    _ ≤ Real.log (1 : ℝ) := entropy_support_cap _ 1 (by
      have hs : support (map p (fun x => x i)) ⊆ {b} := by
        intro c hc
        obtain ⟨x,hx,rfl⟩ := map_positive p (fun x => x i) c ((mem_support _ _).mp hc)
        simp only [Finset.mem_singleton]
        exact h x hx
      have := Finset.card_le_card hs
      simpa using (Nat.cast_le (α := ℝ)).mpr this)
    _ = 0 := Real.log_one

lemma FixedOutside.entropy_zero {p : Law (ι → β)} {U : Finset ι}
    (h : FixedOutside p U) (i : ι) (hi : i ∉ U) : entropy (map p (fun x => x i)) = 0 := by
  obtain ⟨b,hb⟩ := h i hi
  exact constant_coordinate_entropy p i b hb

lemma FixedOutside.entropy_le_sum {p : Law (ι → β)} {U : Finset ι}
    (h : FixedOutside p U) : entropy p ≤ ∑ i ∈ U, entropy (map p (fun x => x i)) := by
  have ht := totalCorrelation_nonneg p
  have he : (∑ i, entropy (map p (fun x => x i))) =
      ∑ i ∈ U, entropy (map p (fun x => x i)) := by
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => h.entropy_zero i hi)).symm
  change 0 ≤ (∑ i, entropy (map p (fun x => x i))) - entropy p at ht
  rw [he] at ht
  exact sub_nonneg.mp ht

def activeDeficit (p : Law (ι → β)) (U : Finset ι) (J : ℝ) : ℝ :=
  U.card * J - entropy p

def marginalDeficit (p : Law (ι → β)) (U : Finset ι) (J : ℝ) : ℝ :=
  ∑ i ∈ U, (J - entropy (map p (fun x => x i)))

end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance instDecidableEqSumProd_solutions_3 : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

local instance instDecidableEqSubtypeSumProdMemFinset_solutions_3_rc9f2bd_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
def blockActive (S : B → Finset A) : Finset ((B × A) ⊕ T) :=
  Finset.univ.filter fun i => Sum.elim (fun z : B × A => z.2 ∈ S z.1) (fun _ => True) i

def blockAllDeficit (J : ℝ) (p : Law (((B × A) ⊕ T) → β)) (S : B → Finset A)
    (_s : B → A) : ℝ := marginalDeficit p (blockActive S) J

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_BlockSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma conditionOn_le (p : Law α) (E : Finset α) (hE : 0<eventMass p E) (a : α) :
    conditionOn p E hE a≤p a/eventMass p E := by
  rw [conditionOn_apply]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (p.nonneg a) hE.le

lemma conditionOn_positive (p : Law α) (E : Finset α) (hE : 0<eventMass p E)
    (a : α) (ha : 0 < conditionOn p E hE a) : a∈E ∧ 0<p a := by
  rw [conditionOn_apply] at ha
  split_ifs at ha with he
  · exact ⟨he,(div_pos_iff.mp ha).resolve_right (fun hn=>hE.not_gt hn.2) |>.1⟩
  · exact (lt_irrefl 0 ha).elim

lemma map_conditionOn_le (p : Law α) (E : Finset α) (hE : 0<eventMass p E)
    (f : α→β) (b : β) :
    map (conditionOn p E hE) f b ≤ map p f b / eventMass p E := by
  change (∑ a,if f a=b then conditionOn p E hE a else 0)≤
    (∑ a,if f a=b then p a else 0)/eventMass p E
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact conditionOn_le p E hE a
  · simp only [zero_div,le_refl]

lemma mean_exists_ge (p : Law α) (f : α→ℝ) :
    ∃ a,0<p a ∧ mean p f≤f a := by
  by_contra! h
  have hex : ∃ a,0<p a := by
    have := p.sum_one
    by_contra! hn
    have hz : ∀ a,p a=0 := fun a=>le_antisymm (hn a) (p.nonneg a)
    simp [hz] at this
  obtain ⟨a,ha⟩:=hex
  have hh : mean p f< mean p (fun _=>mean p f) := by
    apply Finset.sum_lt_sum
    · intro b _
      by_cases hb : 0<p b
      · exact mul_le_mul_of_nonneg_left (h b hb).le (p.nonneg b)
      · have hz : p b=0 := le_antisymm (le_of_not_gt hb) (p.nonneg b)
        simp [hz]
    · exact ⟨a,Finset.mem_univ _,mul_lt_mul_of_pos_left (h a ha) ha⟩
  rw [mean_const] at hh
  exact (lt_irrefl _ hh)

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CapDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}

lemma firstAccepted_index {n : ℕ} (E : Finset A) (t : Fin n→A) {a : A}
    (ha : firstAccepted E t=some a) : ∃i,t i=a ∧ a∈E := by
  induction n with
  | zero => simp [firstAccepted] at ha
  | succ n ih =>
    rw [firstAccepted] at ha
    split_ifs at ha with h
    · have he := Option.some.inj ha
      exact ⟨0,he,he ▸ h⟩
    · obtain ⟨i,hi,hm⟩ := ih _ ha
      exact ⟨i.succ,hi,hm⟩

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def sigmaLaw {A : Type*} [Fintype A] {B : A→Type*} [∀ a,Fintype (B a)]
    (p : Law A) (q : ∀ a,Law (B a)) : Law (Sigma B) where
  mass z := p z.1*q z.1 z.2
  nonneg z := mul_nonneg (p.nonneg _) ((q z.1).nonneg _)
  sum_one := by rw [Fintype.sum_sigma]; simp only [←Finset.mul_sum,(q _).sum_one,mul_one,p.sum_one]

lemma mean_sigma {A : Type*} [Fintype A] {B : A→Type*} [∀ a,Fintype (B a)]
    (p : Law A) (q : ∀ a,Law (B a)) (f : Sigma B→ℝ) :
    mean (sigmaLaw p q) f=mean p (fun a=>mean (q a) (fun b=>f ⟨a,b⟩)) := by
  simp only [mean,sigmaLaw,Fintype.sum_sigma,Finset.mul_sum,mul_assoc]

lemma map_adaptive_first (p : Law α) (q : α→Law β) :
    map (adaptiveLaw p q) Prod.fst=p := by
  apply Law.ext
  funext a
  simp only [map,adaptiveLaw,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel,←Finset.mul_sum,(q _).sum_one,mul_one]
  simp

lemma fiber_adaptive (p : Law α) (q : α→Law β) (a : α) (ha : 0<p a) :
    fiber (adaptiveLaw p q) a=q a := by
  have hf : first (adaptiveLaw p q)=p := by
    apply Law.ext
    funext a
    simp only [first,adaptiveLaw,←Finset.mul_sum,(q a).sum_one,mul_one]
  apply Law.ext
  funext b
  have hh:=mass_eq_first_mul_fiber (adaptiveLaw p q) a b
  rw [hf] at hh
  change p a*q a b=p a*fiber (adaptiveLaw p q) a b at hh
  exact (mul_left_cancel₀ ha.ne' hh).symm

lemma adaptive_stream (p : Law α) (q : α→Law β) (s : α→γ) :
    map (adaptiveLaw p q) (fun z=>s z.1)=map p s := by
  change map (adaptiveLaw p q) (s ∘ Prod.fst)=map p s
  rw [←map_comp,map_adaptive_first]

lemma Law.ext_mean (p q : Law α) (h : ∀ f,mean p f=mean q f) : p=q := by
  apply Law.ext
  funext a
  have hh:=h (fun b=>if b=a then 1 else 0)
  simpa only [mean,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

lemma adaptive_reconstruct (q : Law (α×β)) :
    adaptiveLaw (first q) (fiber q)=q := by
  apply Law.ext
  funext z
  exact (mass_eq_first_mul_fiber q z.1 z.2).symm

def liftObserved (p : Law α) (x : α→β) (q : Law (β×γ)) : Law (α×γ) :=
  adaptiveLaw p (fun a=>fiber q (x a))

end

open scoped Classical BigOperators
variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance blockHistIndexDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _
local instance blockHistSubtypeDecEq (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _

def BlockHistory (B A T β : Type) [Fintype B] [Fintype A] [Fintype T] : ℕ→Type
  | 0 => Unit
  | n+1 => Σ s : B→A, (representativeSet (T:=T) s→β)×BlockHistory B A T β n

instance blockHistoryFintype : (n : ℕ)→Fintype (BlockHistory B A T β n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => by
    letI := blockHistoryFintype n
    exact inferInstanceAs (Fintype (Σ s : B→A,
      (representativeSet (T:=T) s→β)×BlockHistory B A T β n))

def historyPosterior (p : Law (((B×A)⊕T)→β)) :
    {n : ℕ}→BlockHistory B A T β n→Law (((B×A)⊕T)→β)
  | 0,_ => p
  | _n+1,h => historyPosterior (fiber (reveal p (representativeSet h.1)) h.2.1) h.2.2

def historyUnused (S : B→Finset A) : {n : ℕ}→BlockHistory B A T β n→B→Finset A
  | 0,_ => S
  | _n+1,h => historyUnused (eraseBlock S h.1) h.2.2

def historyLaw (p : Law (((B×A)⊕T)→β)) (S : B→Finset A) :
    (n : ℕ)→Law (BlockHistory B A T β n)
  | 0 => uniformType Unit
  | n+1 => sigmaLaw (freshBlockLaw S) fun s=>
      adaptiveLaw (first (reveal p (representativeSet s))) fun a=>
        historyLaw (fiber (reveal p (representativeSet s)) a) (eraseBlock S s) n

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EntropyCrossEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

theorem entropy_le_cross_entropy (p : Law α) (q : α → ℝ)
    (hq : ∀ a,0≤q a) (hs : ∑ a,q a≤1) (hac : ∀ a,0<p a → 0<q a) :
    entropy p≤ -(∑ a,p a*Real.log (q a)) := by
  have hh:=Finset.sum_le_sum (fun a (_ : a∈Finset.univ) =>
    point_log_ratio (p a) (q a) (p.nonneg a) (hq a) (hac a))
  rw [Finset.sum_sub_distrib,p.sum_one] at hh
  have he (a : α) : p a*Real.log (p a/q a)=p a*Real.log (p a)-p a*Real.log (q a) := by
    by_cases hz : p a=0
    · simp [hz]
    · rw [Real.log_div hz (ne_of_gt (hac a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz)))),mul_sub]
  simp only [he,Finset.sum_sub_distrib] at hh
  unfold entropy
  linarith

theorem option_entropy_bound (p : Law (Option β)) (S : Finset β) (N : ℝ)
    (hN : 1≤N) (hS : (S.card:ℝ)≤N)
    (hsupp : ∀ b,0<p (some b) → b∈S) :
    entropy p≤Real.log 2+(∑ b,p (some b))*Real.log N := by
  have hN0 : 0<N := zero_lt_one.trans_le hN
  let q : Option β → ℝ := fun o => match o with
    | none => 1/2
    | some b => if b∈S then 1/(2*N) else 0
  have hqsum : (∑ o,q o)=1/2+(S.card:ℝ)/(2*N) := by
    simp only [Fintype.sum_option,q]
    simp [div_eq_mul_inv]
  have hqnon (o : Option β) : 0≤q o := by
    cases o with
    | none => norm_num [q]
    | some b => simp only [q]; split_ifs <;> positivity
  have hqsumle : ∑ o,q o≤1 := by
    rw [hqsum]
    have hh : (S.card:ℝ)/(2*N)≤1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have hac (o : Option β) (ho : 0<p o) : 0<q o := by
    cases o with
    | none => norm_num [q]
    | some b => simp only [q,ite_eq_left (hsupp b ho)]; positivity
  have hb:=entropy_le_cross_entropy p q hqnon hqsumle hac
  have hlog : Real.log (1/(2*N))= -Real.log 2-Real.log N := by
    rw [Real.log_div (by norm_num) (by positivity),Real.log_one,
      Real.log_mul (by norm_num) (ne_of_gt hN0)]
    ring
  have hsome (b : β) : p (some b)*Real.log (q (some b))=
      p (some b)*(-Real.log 2-Real.log N) := by
    by_cases hz : p (some b)=0
    · simp only [hz,zero_mul]
    · rw [show q (some b)=1/(2*N) by
        exact ite_eq_left (hsupp b (lt_of_le_of_ne (p.nonneg _) (Ne.symm hz))),hlog]
  have hnone : Real.log (q none)= -Real.log 2 := by
    change Real.log (1/2)=_
    rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  simp only [Fintype.sum_option,hsome,hnone,←Finset.sum_mul] at hb
  have hsum : p none+∑ b,p (some b)=1 := by simpa only [Fintype.sum_option] using p.sum_one
  have hsumlog := congrArg (fun x : ℝ => x*Real.log 2) hsum
  nlinarith

end

section
open scoped BigOperators Classical
variable {α β ι μ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype μ]

noncomputable def present (o : Option β) : ℝ := match o with
  | none => 0 | some _ => 1

lemma present_sum (p : Law α) (f : α → Option β) :
    (∑ b,map p f (some b))=∑ a,p a*present (f a) := by
  rw [←sum_map p f present]
  simp only [Fintype.sum_option,present,mul_zero,mul_one,zero_add]

theorem marked_entropy (p : Law α) (f : α → ι → Option β)
    (S : ι → Finset β) (N : ℝ) (hN : 1≤N) (hS : ∀ i,(S i).card≤N)
    (hsupp : ∀ a,0<p a → ∀ i b,f a i=some b → b∈S i) :
    entropy (map p f)≤(Fintype.card ι:ℝ)*Real.log 2+
      (∑ a,p a*(∑ i,present (f a i)))*Real.log N := by
  have hi (i : ι) : entropy (map p (fun a => f a i))≤Real.log 2+
      (∑ a,p a*present (f a i))*Real.log N := by
    rw [←present_sum p (fun a => f a i)]
    apply option_entropy_bound _ (S i) N hN (hS i)
    intro b hb
    by_contra hnot
    have hz : map p (fun a => f a i) (some b)=0 := by
      apply Finset.sum_eq_zero
      intro a _
      split_ifs with he
      · exact le_antisymm (le_of_not_gt (fun hpos => hnot (hsupp a hpos i b he))) (p.nonneg a)
      · rfl
    linarith
  have hc:=totalCorrelation_nonneg (map p f)
  simp only [totalCorrelation,map_comp,Function.comp_def] at hc
  have hh:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Finset.sum_mul] at hh
  rw [Finset.sum_comm (f := fun i a => p a*present (f a i))] at hh
  simp only [←Finset.mul_sum] at hh
  linarith

theorem marked_mask_entropy (p : Law α) (mask : α → μ) (f : α → ι → Option β)
    (S : ι → Finset β) (N : ℝ) (hN : 1≤N) (hS : ∀ i,(S i).card≤N)
    (hsupp : ∀ a,0<p a → ∀ i b,f a i=some b → b∈S i) :
    entropy (pair p mask f)≤Real.log (Fintype.card μ)+(Fintype.card ι:ℝ)*Real.log 2+
      (∑ a,p a*(∑ i,present (f a i)))*Real.log N := by
  have hh:=entropy_subadditive (pair p mask f)
  rw [first_pair,second_pair] at hh
  have hmask:=entropy_le_log_card (map p mask)
  have hf:=marked_entropy p f S N hN hS hsupp
  linarith

end

open scoped BigOperators Classical
variable {α β ι μ κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype μ] [Fintype κ]

lemma sum_fiber (p : Law (κ × α)) (g : α → ℝ) :
    (∑ c,first p c*(∑ a,fiber p c a*g a))=∑ a,second p a*g a := by
  simp only [Finset.mul_sum,←mul_assoc,←mass_eq_first_mul_fiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_mul]
  rfl

theorem conditional_marked_entropy (p : Law (κ × α))
    (mask : α → μ) (f : α → ι → Option β)
    (S : κ → ι → Finset β) (N : ℝ) (hN : 1≤N)
    (hS : ∀ c i,((S c i).card:ℝ)≤N)
    (hsupp : ∀ c a,0<p (c,a) → ∀ i b,f a i=some b → b∈S c i) :
    (∑ c,first p c*entropy (pair (fiber p c) mask f))≤
      Real.log (Fintype.card μ)+(Fintype.card ι:ℝ)*Real.log 2+
        (∑ a,second p a*(∑ i,present (f a i)))*Real.log N := by
  have hh (c : κ) : first p c*entropy (pair (fiber p c) mask f)≤
      first p c*(Real.log (Fintype.card μ)+(Fintype.card ι:ℝ)*Real.log 2+
        (∑ a,fiber p c a*(∑ i,present (f a i)))*Real.log N) := by
    by_cases hc : first p c=0
    · simp only [hc,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ ((first p).nonneg c)
      apply marked_mask_entropy _ mask f (S c) N hN (hS c)
      intro a ha i b he
      apply hsupp c a _ i b he
      rw [mass_eq_first_mul_fiber]
      exact mul_pos (lt_of_le_of_ne ((first p).nonneg c) (Ne.symm hc)) ha
  apply (Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => hh c)).trans_eq
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul]
  rw [(first p).sum_one,one_mul,one_mul]
  simp only [←mul_assoc]
  rw [←Finset.sum_mul,sum_fiber]

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UnionMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β ι κ : Type*} [Fintype α] [Fintype β] [Fintype ι] [Fintype κ]
local instance unionMarkingDecEq : DecidableEq ι := Classical.decEq _

abbrev RankTypes := (Fin 5 × Fin 5) × Bool × Bool

def unionMask (r : α → ι → RankTypes) (E₁ E₂ : α → Finset ι)
    (x : α) (i : ι) : RankTypes × Bool × Bool :=
  (r x i,decide (i∈E₁ x),decide (i∈E₂ x))

end

open scoped Classical BigOperators
variable {α κ μ : Type*} [Fintype α] [Fintype κ] [Fintype μ]

def withMessage (p : Law (κ × α)) (M : α → μ) : Law ((κ × μ) × α) :=
  map p (fun z => ((z.1,M z.2),z.2))

lemma first_withMessage (p : Law (κ × α)) (M : α → μ) :
    first (withMessage p M)=mapSnd p M := by
  rw [←map_first,withMessage,map_comp]
  rfl

lemma entropy_withMessage (p : Law (κ × α)) (M : α → μ) :
    entropy (withMessage p M)=entropy p := by
  apply entropy_map_injective
  intro z w h
  have h1 : z.1=w.1 := congrArg (fun u : (κ×μ)×α => u.1.1) h
  have h2 : z.2=w.2 := congrArg (fun u : (κ×μ)×α => u.2) h
  exact Prod.ext h1 h2

lemma mean_withMessage_label (p : Law (κ × α)) (M : α → μ) (g : μ → ℝ) :
    mean (first (withMessage p M)) (fun z => g z.2)=
      mean (second p) (fun x => g (M x)) := by
  rw [first_withMessage,←map_second p,mapSnd,mean_map,mean_map]

lemma withMessage_support (p : Law (κ × α)) (M : α → μ)
    (c : κ) (m : μ) (x : α) (hx : 0<withMessage p M ((c,m),x)) :
    0<p (c,x) ∧ M x=m := by
  obtain ⟨z,hz,he⟩ := map_positive p (fun z => ((z.1,M z.2),z.2)) ((c,m),x) hx
  have hz1 : z.1=c := congrArg (fun u => u.1.1) he
  have hz2 : z.2=x := congrArg Prod.snd he
  have hzm : M z.2=m := congrArg (fun u => u.1.2) he
  have hz' : z=(c,x) := Prod.ext hz1 hz2
  subst z
  exact ⟨hz,hzm⟩

lemma fiber_withMessage_support (p : Law (κ × α)) (M : α → μ)
    (c : κ) (m : μ) (hm : 0<first (withMessage p M) (c,m))
    (x : α) (hx : 0<fiber (withMessage p M) (c,m) x) :
    0<p (c,x) ∧ M x=m := by
  apply withMessage_support
  rw [mass_eq_first_mul_fiber]
  exact mul_pos hm hx

variable {ι β : Type*} [Fintype ι] [Fintype β]

theorem message_deficit_bound (p : Law (κ × (ι → β))) (M : (ι → β) → μ)
    (U : μ → Finset ι) (h : (ι → β) → ℝ) (J L C : ℝ)
    (hcard : ∀ x,((U (M x)).card:ℝ)+h x=Fintype.card ι)
    (hcost : mean (first p) (fun c=>entropy (map (fiber p c) M)) ≤
      C+mean (second p) h*L) :
    mean (first (withMessage p M))
        (fun z=>activeDeficit (fiber (withMessage p M) z) (U z.2) J) ≤
      (Fintype.card ι:ℝ)*J-entropy (second p)+entropy (first p)+C+
        mean (second p) h*(L-J) := by
  have hi : entropy (first (withMessage p M)) ≤
      entropy (first p)+C+mean (second p) h*L := by
    rw [first_withMessage,entropy_chain,first_mapSnd]
    simp only [fiber_mapSnd]
    change entropy (first p)+mean (first p) (fun c=>entropy (map (fiber p c) M)) ≤ _
    linarith
  have hh := entropy_chain (withMessage p M)
  rw [entropy_withMessage] at hh
  have hsecond := entropy_map_le p Prod.snd
  rw [map_second] at hsecond
  have hc : mean (first (withMessage p M)) (fun z=>((U z.2).card:ℝ)) =
      (Fintype.card ι:ℝ)-mean (second p) h := by
    rw [mean_withMessage_label p M (fun m=>((U m).card:ℝ))]
    calc
      _ = mean (second p) (fun x=>(Fintype.card ι:ℝ)-h x) :=
        mean_congr _ (fun x=>by linarith [hcard x])
      _ = _ := by rw [mean_sub,mean_const]
  have he : mean (first (withMessage p M))
        (fun z=>activeDeficit (fiber (withMessage p M) z) (U z.2) J) =
      ((Fintype.card ι:ℝ)-mean (second p) h)*J-
        mean (first (withMessage p M)) (fun z=>entropy (fiber (withMessage p M) z)) := by
    simp only [activeDeficit,mean,mul_sub,Finset.sum_sub_distrib,←mul_assoc,
      ←Finset.sum_mul]
    exact congrArg (fun u=>u*J-∑ z,first (withMessage p M) z *
      entropy (fiber (withMessage p M) z)) hc
  rw [he]
  change entropy p = entropy (first (withMessage p M))+
    mean (first (withMessage p M)) (fun z=>entropy (fiber (withMessage p M) z)) at hh
  nlinarith
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {ι β : Type*} [Fintype ι] [Fintype β]
local instance subsetDeficitDecEq : DecidableEq ι := Classical.decEq _
local instance subsetDeficitSubDecEq (S : Finset ι) : DecidableEq S := Classical.decEq _

lemma entropy_subset_split (p : Law (ι → β)) (S : Finset ι) :
    entropy p ≤ entropy (map p (fun x => fun i : S => x i.val)) +
      ∑ i∈Sᶜ,entropy (map p (fun x => x i)) := by
  let f := fun x : ι → β => fun i : S => x i.val
  let g := fun x : ι → β => fun i : (Sᶜ : Finset ι) => x i.val
  have hinj : Function.Injective (fun x => (f x,g x)) := by
    intro x y h
    funext i
    by_cases hi : i∈S
    · exact congrFun (congrArg Prod.fst h) ⟨i,hi⟩
    · exact congrFun (congrArg Prod.snd h) ⟨i,Finset.mem_compl.mpr hi⟩
  have hh := entropy_subadditive (pair p f g)
  rw [show entropy (pair p f g)=entropy p from entropy_map_injective p _ hinj,
    first_pair,second_pair] at hh
  have ht := totalCorrelation_nonneg (map p g)
  simp only [totalCorrelation,map_comp,Function.comp_def] at ht
  have he : (∑ i : (Sᶜ : Finset ι),entropy (map p (fun x => g x i))) =
      ∑ i∈Sᶜ,entropy (map p (fun x => x i)) := by
    exact Finset.sum_coe_sort Sᶜ (fun i => entropy (map p (fun x => x i)))
  rw [he] at ht
  linarith

theorem subset_deficit_le_active (p : Law (ι → β)) (U S : Finset ι)
    (hSU : S⊆U) (hf : FixedOutside p U) (J : ℝ)
    (hc : ∀ i∈U,entropy (map p (fun x => x i))≤J) :
    (S.card:ℝ)*J-entropy (map p (fun x => fun i : S => x i.val)) ≤
      activeDeficit p U J := by
  have hh := entropy_subset_split p S
  have he : (∑ i∈Sᶜ,entropy (map p (fun x => x i))) =
      ∑ i∈U\S,entropy (map p (fun x => x i)) := by
    symm
    apply Finset.sum_subset
    · intro i hi
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
    · intro i hi hnot
      apply hf.entropy_zero
      intro hU
      exact hnot (Finset.mem_sdiff.mpr ⟨hU,Finset.mem_compl.mp hi⟩)
  rw [he] at hh
  have hb : (∑ i∈U\S,entropy (map p (fun x => x i))) ≤ ((U\S).card:ℝ)*J := by
    calc
      _ ≤ ∑ i∈U\S,J := Finset.sum_le_sum fun i hi => hc i (Finset.mem_sdiff.mp hi).1
      _ = _ := by simp
  have hn : ((U\S).card:ℝ)+(S.card:ℝ)=U.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hSU
  calc
    _ ≤ (S.card:ℝ)*J + ((U\S).card:ℝ)*J - entropy p := by linarith
    _ = activeDeficit p U J := by
      dsimp [activeDeficit]
      rw [←add_mul,add_comm (S.card:ℝ),hn]
end

open scoped Classical BigOperators
variable {ι β κ : Type*} [Fintype ι] [Fintype β] [Fintype κ]
local instance unionPosteriorDecEq : DecidableEq ι := Classical.decEq _

abbrev UnionTranscript (ι β : Type*) :=
  (ι → RankTypes × Bool × Bool) × (ι → Option β)

def unspecified (m : UnionTranscript ι β) : Finset ι :=
  Finset.univ.filter fun i=>m.2 i=none

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClassSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {Ω ι κ : Type*} [Fintype Ω] [Fintype κ] [Nonempty κ]

def classPositions (S : Finset ι) (c : ι → κ) (a : κ) : Finset ι := S.filter (fun i=>c i=a)

variable {α β : Type*} [Fintype α] [Fintype β]

def conditionContext (p : Law (α×β)) (E : Finset α) (hE : 0 < eventMass (first p) E) :
    Law (α×β) := adaptiveLaw (conditionOn (first p) E hE) (fiber p)

lemma conditionContext_fiber (p : Law (α×β)) (E : Finset α)
    (hE : 0 < eventMass (first p) E) (a : α) (ha : 0 < conditionOn (first p) E hE a) :
    fiber (conditionContext p E hE) a=fiber p a := fiber_adaptive _ _ _ ha

end

open scoped Classical BigOperators
variable {I J β κ : Type*} [Fintype I] [Fintype J] [Fintype β] [Fintype κ]
local instance contextRestrictJDecEq : DecidableEq J := Classical.decEq _
local instance contextRestrictIDecEq_rc9f2bd_1 : DecidableEq I := Classical.decEq _
local instance contextRestrictSubtypeDecEq (S : Finset I) : DecidableEq S := Classical.decEq _

def embeddingRange (f : J↪I) : Finset I := Finset.univ.image f

def embeddingRangeEquiv (f : J↪I) : J≃embeddingRange f :=
  Equiv.ofBijective (fun j=>⟨f j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun a b h=>f.injective (congrArg Subtype.val h),by
      intro z
      obtain ⟨j,_,hj⟩:=Finset.mem_image.mp z.property
      exact ⟨j,Subtype.ext hj⟩⟩

omit [Fintype I] in
lemma embeddingRange_card (f : J↪I) : (embeddingRange f).card=Fintype.card J := by
  unfold embeddingRange
  rw [Finset.card_image_of_injective _ f.injective,Finset.card_univ]

lemma entropy_reindex_range (p : Law (I→β)) (f : J↪I) :
    entropy (map p (fun x=>x ∘ f))=
      entropy (map p (fun x=>fun i : embeddingRange f=>x i.val)) := by
  let e:=embeddingRangeEquiv f
  have hinj : Function.Injective (fun x : embeddingRange f→β=>x ∘ e) := by
    intro x y h
    funext i
    obtain ⟨j,rfl⟩:=e.surjective i
    exact congrFun h j
  have hh:=entropy_map_injective (map p (fun x=>fun i : embeddingRange f=>x i.val))
    (fun x=>x ∘ e) hinj
  rw [map_comp] at hh
  exact hh

theorem reindexed_deficit_le (p : Law (I→β)) (U : Finset I) (f : J↪I)
    (hf : ∀ j,f j∈U) (hfix : FixedOutside p U) (cap : ℝ)
    (hc : ∀ i∈U,entropy (map p (fun x=>x i)) ≤ cap) :
    Fintype.card J*cap-entropy (map p (fun x=>x ∘ f))≤activeDeficit p U cap := by
  rw [entropy_reindex_range,←embeddingRange_card f]
  apply subset_deficit_le_active p U _ _ hfix cap hc
  intro i hi
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hi
  exact hf j

def selectByContext (p : Law (κ×(I→β))) (f : κ→J→I) : Law (κ×(J→β)) :=
  map p (fun z=>(z.1,z.2 ∘ f z.1))

lemma selectByContext_adaptive (p : Law (κ×(I→β))) (f : κ→J→I) :
    selectByContext p f=adaptiveLaw (first p) (fun c=>map (fiber p c) (fun x=>x ∘ f c)) := by
  apply Law.ext_mean
  intro g
  rw [selectByContext,mean_map,mean_adaptive]
  simp_rw [mean_map]
  have he:=congrArg (fun q=>mean q (fun z=>g (z.1,z.2 ∘ f z.1))) (adaptive_reconstruct p)
  rw [mean_adaptive] at he
  exact he.symm

lemma selectByContext_first (p : Law (κ×(I→β))) (f : κ→J→I) :
    first (selectByContext p f)=first p := by
  rw [selectByContext_adaptive]
  apply Law.ext
  funext c
  simp only [first,adaptiveLaw,←Finset.mul_sum,(map (fiber p c) _).sum_one,mul_one]

lemma selectByContext_fiber (p : Law (κ×(I→β))) (f : κ→J→I)
    (c : κ) (hc : 0<first p c) :
    fiber (selectByContext p f) c=map (fiber p c) (fun x=>x ∘ f c) := by
  rw [selectByContext_adaptive]
  exact fiber_adaptive _ _ _ hc

theorem selectByContext_deficit (p : Law (κ×(I→β))) (U : κ→Finset I)
    (f : κ→J↪I) (cap : ℝ) (hsel : ∀ c,0<first p c→∀ j,f c j∈U c)
    (hfix : ∀ c,0<first p c→FixedOutside (fiber p c) (U c))
    (hc : ∀ c,0<first p c→∀ i∈U c,entropy (map (fiber p c) (fun x=>x i)) ≤ cap) :
    mean (first (selectByContext p (fun c=>(f c : J→I))))
      (fun c=>Fintype.card J*cap-entropy (fiber (selectByContext p (fun c=>(f c : J→I))) c))≤
      mean (first p) (fun c=>activeDeficit (fiber p c) (U c) cap) := by
  rw [selectByContext_first]
  apply mean_mono_pos
  intro c hp
  rw [selectByContext_fiber _ _ _ hp]
  exact reindexed_deficit_le _ _ _ (hsel c hp) (hfix c hp) cap (hc c hp)

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped BigOperators Classical
open FiniteEntropy
variable {α ι : Type*} [Fintype α] [Fintype ι]

variable {N l : ℕ}

noncomputable def matching (I : {I : Finset (Fin N) // I.card=l})
    (f : Fin l → α) : Finset (Fin N → α) :=
  Finset.univ.filter fun s => ∀ j,s (I.val.orderEmbOfFin I.property j) = f j

noncomputable def occurrences (f : Fin l → α) : Finset (Fin N → α) :=
  Finset.univ.biUnion fun I : {I : Finset (Fin N) // I.card=l} => matching I f

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]

def retainedIndices {n l : ℕ} (hl : l≤n) (S : Finset (Fin n)) : Fin l ↪o Fin n :=
  if h : l≤S.card then (Fin.castLEOrderEmb h).trans (S.orderEmbOfFin rfl)
  else Fin.castLEOrderEmb hl

lemma retainedIndices_mem {n l : ℕ} (hl : l≤n) (S : Finset (Fin n))
    (hs : l≤S.card) (i : Fin l) : retainedIndices hl S i∈S := by
  simp only [retainedIndices,dite_eq_left hs,RelEmbedding.coe_trans,Function.comp_apply]
  exact S.orderEmbOfFin_mem rfl _

def retainedTuple {n l : ℕ} (hl : l≤n) (x : Fin n→β) (S : Finset (Fin n)) : Fin l→β :=
  x ∘ retainedIndices hl S

lemma retainedTuple_occurs {n l : ℕ} (hl : l≤n) (x : Fin n→β) (S : Finset (Fin n)) :
    x∈SelectedTuple.occurrences (retainedTuple hl x S) := by
  let e := retainedIndices hl S
  let I : Finset (Fin n) := Finset.univ.map e.toEmbedding
  have hI : I.card=l := by simp [I]
  have he : I.orderEmbOfFin hI=e := by
    symm
    apply Finset.orderEmbOfFin_unique' hI
    intro j
    simp [I]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨I,hI⟩,Finset.mem_univ _,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,fun j=>by rw [he];rfl⟩

local instance extractedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClassExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {κ α β : Type*} [Fintype κ] [Fintype α] [Fintype β]
local instance classExtractβDE : DecidableEq β := Classical.decEq _
local instance classExtractFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

local instance classExtractκDE_rc9f2bd_1 : DecidableEq κ := Classical.decEq _
local instance classExtractαDE_rc9f2bd_1 : DecidableEq α := Classical.decEq _
lemma conditionOn_mean_le_pos (p : Law α) (E : Finset α) (hE : 0 < eventMass p E)
    (f : α→ℝ) (hf : ∀ a,0 < p a → 0 ≤ f a) :
    mean (conditionOn p E hE) f ≤ mean p f/eventMass p E := by
  simp only [mean,Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : 0 < p a
  · simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right (conditionOn_le p E hE a) (hf a hp)
  · have hz : p a=0 := le_antisymm (le_of_not_gt hp) (p.nonneg a)
    have hz' : conditionOn p E hE a=0 := by simp [conditionOn_apply,hz]
    simp only [hz,hz',zero_mul,zero_div,le_refl]

lemma conditionContext_first (p : Law (κ×α)) (E : Finset κ)
    (hE : 0 < eventMass (first p) E) :
    first (conditionContext p E hE)=conditionOn (first p) E hE := by
  apply Law.ext
  funext c
  simp only [conditionContext,first,adaptiveLaw,←Finset.mul_sum,(fiber p c).sum_one,mul_one]

def selectedClassIndices {n l : ℕ} (hl : l ≤ n) (U : κ→Finset (Fin n))
    (code : κ→Fin n→α) (a : α) (c : κ) : Fin l ↪o Fin n :=
  retainedIndices hl (classPositions (U c) (code c) a)

def selectedClassEvent {n : ℕ} (l : ℕ) (U : κ→Finset (Fin n))
    (code : κ→Fin n→α) (a : α) : Finset κ :=
  Finset.univ.filter fun c=>l ≤ (classPositions (U c) (code c) a).card

omit [Fintype α] in
lemma selectedClassIndices_properties {n l : ℕ} (hl : l ≤ n) (U : κ→Finset (Fin n))
    (code : κ→Fin n→α) (a : α) (c : κ) (hc : c∈selectedClassEvent l U code a)
    (i : Fin l) : selectedClassIndices hl U code a c i∈U c ∧
      code c (selectedClassIndices hl U code a c i)=a := by
  have hi:=retainedIndices_mem hl (classPositions (U c) (code c) a)
    (Finset.mem_filter.mp hc).2 i
  exact Finset.mem_filter.mp hi

omit [Fintype α] in
theorem selectedClass_deficit {n l : ℕ} (hl : l ≤ n) (p : Law (κ×(Fin n→β)))
    (U : κ→Finset (Fin n)) (code : κ→Fin n→α) (a : α)
    (hE : 0 < eventMass (first p) (selectedClassEvent l U code a)) (J : ℝ)
    (hnonneg : ∀ c,0 < first p c → 0 ≤ activeDeficit (fiber p c) (U c) J)
    (hfix : ∀ c,0 < first p c → FixedOutside (fiber p c) (U c))
    (hcap : ∀ c,0 < first p c → ∀ i∈U c,entropy (map (fiber p c) (fun x=>x i)) ≤ J) :
    let q:=conditionContext p (selectedClassEvent l U code a) hE
    let f:=fun c=>(selectedClassIndices hl U code a c).toEmbedding
    mean (first (selectByContext q (fun c=>(f c : Fin l→Fin n))))
      (fun c=>(l:ℝ)*J-entropy (fiber (selectByContext q (fun c=>(f c : Fin l→Fin n))) c)) ≤
      mean (first p) (fun c=>activeDeficit (fiber p c) (U c) J)/
        eventMass (first p) (selectedClassEvent l U code a) := by
  dsimp only
  let E:=selectedClassEvent l U code a
  let q:=conditionContext p E hE
  have hpos (c : κ) (hc : 0 < first q c) : c∈E ∧ 0 < first p c := by
    rw [conditionContext_first] at hc
    exact conditionOn_positive (first p) E hE c hc
  have hfib (c : κ) (hc : 0 < first q c) : fiber q c=fiber p c := by
    apply conditionContext_fiber
    rwa [←conditionContext_first]
  have hh:=selectByContext_deficit q U
    (fun c=>(selectedClassIndices hl U code a c).toEmbedding) J
    (fun c hc i=>(selectedClassIndices_properties hl U code a c (hpos c hc).1 i).1)
    (fun c hc=>by rw [hfib c hc];exact hfix c (hpos c hc).2)
    (fun c hc i hi=>by rw [hfib c hc];exact hcap c (hpos c hc).2 i hi)
  simp only [Fintype.card_fin] at hh
  apply hh.trans
  calc
    _ = mean (conditionOn (first p) E hE) (fun c=>activeDeficit (fiber p c) (U c) J) := by
      rw [←conditionContext_first]
      apply le_antisymm <;> apply mean_mono_pos
      · intro c hc; rw [hfib c hc]
      · intro c hc; rw [hfib c hc]
    _ ≤ _ := conditionOn_mean_le_pos (first p) E hE _ hnonneg
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CollisionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T : Type} [Fintype B] [Fintype A] [Fintype T] [Nonempty A]
local instance collisionSamplingDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

def otherCollision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (s : B → A) (b : B) (a : A) : ℝ :=
  ∑ d ∈ Finset.univ.erase b,c (Sum.inl (b,a)) (Sum.inl (d,s d))

def middleCollision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (s : B → A) (t : T) : ℝ := ∑ d,c (Sum.inr t) (Sum.inl (d,s d))

def allCollision (c : ((B × A) ⊕ T) → ((B × A) ⊕ T) → ℝ)
    (S : B → Finset A) (s : B → A) : ℝ :=
  (∑ b,∑ a∈S b,otherCollision c s b a)+∑ t,middleCollision c s t

end

open scoped Classical BigOperators

def badIndexIndicator (δ g d e : ℝ) : ℝ := if d<δ ∨ e<g then 1 else 0

lemma badIndexIndicator_nonneg (δ g d e : ℝ) : 0≤badIndexIndicator δ g d e := by
  unfold badIndexIndicator
  split_ifs <;> norm_num

lemma badIndexIndicator_eq_zero {δ g d e : ℝ} (h : badIndexIndicator δ g d e=0) :
    δ≤d ∧ g≤e := by
  unfold badIndexIndicator at h
  split_ifs at h with hh
  · norm_num at h
  · push Not at hh
    exact hh

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]
local instance goodDeleteIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _

def indexInformation (p : Law (((B×A)⊕T)→β)) (s : B→A) : ((B×A)⊕T)→ℝ :=
  Sum.elim (fun z=>(blockInformation p s z.1 z.2 : ℝ)) (fun t=>(middleInformation p s t : ℝ))

def indexCollision (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (s : B→A) : ((B×A)⊕T)→ℝ :=
  Sum.elim (fun z=>otherCollision c s z.1 z.2) (middleCollision c s)

def indexBad (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (s : B→A) (i : ((B×A)⊕T)) : ℝ :=
  badIndexIndicator (J-entropy (map p (fun x=>x i)))
    (indexInformation p s i+indexCollision c s i) d e

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ConditionPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {α β γ κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ]

def eventPreimage (f : α→β) (E : Finset β) : Finset α :=
  Finset.univ.filter fun a=>f a∈E

omit [Fintype β] in
lemma mem_eventPreimage (f : α→β) (E : Finset β) (a : α) :
    a∈eventPreimage f E ↔ f a∈E := by
  simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and]

lemma eventMass_map_preimage (p : Law α) (f : α→β) (E : Finset β) :
    eventMass (map p f) E=eventMass p (eventPreimage f E) := by
  have hm:=mean_map p f (fun b=>if b∈E then 1 else 0)
  simpa only [mean,mul_ite,mul_one,mul_zero,eventMass,eventPreimage,Finset.sum_filter,
    Finset.sum_ite_mem,Finset.univ_inter] using hm

lemma conditionOn_mean_exact (p : Law α) (E : Finset α) (h : 0<eventMass p E)
    (f : α→ℝ) : mean (conditionOn p E h) f=
      mean p (fun a=>if a∈E then f a else 0)/eventMass p E := by
  simp only [mean,Finset.sum_div,conditionOn_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a∈E <;> simp only [ha,ite_true,ite_false,mul_zero,zero_mul,zero_div,
    div_mul_eq_mul_div]

lemma map_condition_pullback (p : Law α) (f : α→β) (E : Finset β)
    (h : 0<eventMass (map p f) E) :
    map (conditionOn p (eventPreimage f E) (by rwa [←eventMass_map_preimage])) f=
      conditionOn (map p f) E h := by
  apply Law.ext_mean
  intro g
  rw [mean_map,conditionOn_mean_exact,conditionOn_mean_exact,mean_map]
  congr 1
  · apply mean_congr
    intro a
    simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and]
  · exact (eventMass_map_preimage p f E).symm

lemma conditionContext_eq_pullback (p : Law (κ×α)) (E : Finset κ)
    (h : 0<eventMass (first p) E) :
    conditionContext p E h=
      conditionOn p (eventPreimage Prod.fst E) (by rwa [←eventMass_map_preimage,map_first]) := by
  apply Law.ext
  funext z
  simp only [conditionContext,adaptiveLaw,conditionOn_apply,eventPreimage,
    Finset.mem_filter,Finset.mem_univ,true_and]
  have he:=eventMass_map_preimage p Prod.fst E
  dsimp only [eventPreimage] at he
  rw [←he,map_first]
  split_ifs
  · rw [div_mul_eq_mul_div,←mass_eq_first_mul_fiber]
  · simp only [zero_mul]

end

open scoped Classical BigOperators
variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]

lemma conditionContext_pair (p : Law α) (c : α→κ) (x : α→β) (E : Finset κ)
    (h : 0<eventMass (map p c) E) :
    pair (conditionOn p (eventPreimage c E) (by rwa [←eventMass_map_preimage])) c x=
      conditionContext (pair p c x) E (by simpa only [first_pair] using h) := by
  have hmass : eventMass (pair p c x) (eventPreimage Prod.fst E)=eventMass (map p c) E := by
    rw [←eventMass_map_preimage,map_first,first_pair]
  have he : eventPreimage (fun a=>(c a,x a)) (eventPreimage Prod.fst E)=eventPreimage c E := by
    ext a
    simp only [eventPreimage,Finset.mem_filter,Finset.mem_univ,true_and]
  have hh:=map_condition_pullback p (fun a=>(c a,x a)) (eventPreimage Prod.fst E)
    (by change 0<eventMass (pair p c x) (eventPreimage Prod.fst E); rwa [hmass])
  simp only [he] at hh
  rw [conditionContext_eq_pullback]
  exact hh

lemma selected_pair (p : Law α) (c : α→κ) {I J : Type*} [Fintype I] [Fintype J]
    (x : α→I→β) (f : κ→J→I) :
    selectByContext (pair p c x) f=pair p c (fun a=>x a ∘ f (c a)) := by
  rw [selectByContext,pair,map_comp]
  rfl
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SubsetMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def uniformWeight (S : Finset α) (a : α) : ℝ :=
  if a∈S then 1/(S.card:ℝ) else 0
noncomputable def relationMass (R : α→β→Prop) (f : α→ℝ) (g : β→ℝ) : ℝ :=
  ∑z∈Finset.univ.filter (fun z : α×β=>R z.1 z.2),f z.1*g z.2

end

open scoped BigOperators Classical

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Swap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

noncomputable def swap (p : Law (α × β)) : Law (β × α) where
  mass z := p (z.2,z.1)
  nonneg z := p.nonneg _
  sum_one := by rw [Fintype.sum_prod_type,Finset.sum_comm,←Fintype.sum_prod_type]; exact p.sum_one

@[simp] lemma swap_mass (p : Law (α × β)) (b : β) (a : α) : swap p (b,a)=p (a,b) := rfl
@[simp] lemma first_swap (p : Law (α × β)) : first (swap p)=second p := by
  apply Law.ext
  rfl

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Failure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {α β : Type*} [Fintype α] [Fintype β]

noncomputable def failure (p : Law α) (v : α → V) (f : Module.Dual K V) : ℝ :=
  ∑ a,if f (v a)≠0 then p a else 0

noncomputable def core (p : Law α) (v : α → V) (ρ : ℝ) : Submodule K V :=
  ⨅ f : {f : Module.Dual K V // failure p v f≤ρ},LinearMap.ker f.val

noncomputable def capture (p : Law α) (v : α → V) (ρ : ℝ) : ℝ :=
  ∑ a,if v a∈core (K := K) p v ρ then p a else 0

end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_EventWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]
noncomputable def eventWeight (p : Law α) (E : α → Prop) : ℝ :=
  ∑ a,if E a then p a else 0
lemma eventWeight_nonneg (p : Law α) (E : α → Prop) : 0≤eventWeight p E := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact p.nonneg a
  · exact le_rfl
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def freshRejection (R : α→β→Prop) (q : ℝ)
    (W : Finset α) (hW : W.Nonempty) (h N : ℕ) (E : Finset (Fin h→α)) (b : β) : ℝ :=
  eventMass (map (iid (iid (uniformOn W hW) (Fin h)) (Fin N)) (firstAccepted E (n:=N)))
    ((Finset.univ.filter (fun x=>(1/(5*q))*h ≤ hits (Finset.univ.filter (fun a=>R a b)) x)).image some)

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_PoissonLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section PairWitnesses

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def witnessRequirements (T : Finset κ) (S : Finset ι) (f : T → S) : Finset (κ × ι) :=
  T.attach.image (fun r => (r.val, (f r).val))

def dictionary (C : Finset (κ × ι)) : Finset ι := C.image Prod.snd

abbrev AnchorChoice (C : Finset (κ × ι)) (S : Finset ι) :=
  {i // i ∈ S ∩ dictionary C} ⊕ (κ × {i // i ∈ S \ dictionary C})

def AnchorChoice.direction {C : Finset (κ × ι)} {S : Finset ι} : AnchorChoice C S → ι
  | .inl d => d.val
  | .inr rd => rd.2.val

def AnchorChoice.requirements {C : Finset (κ × ι)} {S : Finset ι} :
    AnchorChoice C S → Finset (κ × ι)
  | .inl _ => ∅
  | .inr rd => {(rd.1, rd.2.val)}

end PairWitnesses
end SharpRamseyFive.StaticCertificates
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_TwoAnchorCrossCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

open scoped BigOperators
namespace SharpRamseyFive.CertificateEnumeration

universe u v
variable {S : Type u} {A : Type v}

section Dependent
variable (C : S → Type v) (step : (s : S) → C s → S)

def DWord : ℕ → S → Type v
  | 0, _ => PUnit
  | n + 1, s => (a : C s) × DWord n (step s a)

instance flat_HighMomentRecovered_5 [∀ s, Fintype (C s)] (n : ℕ) (s : S) : Fintype (DWord C step n s) := by
  induction n generalizing s with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((a : C s) × DWord C step n (step s a)))

def dFinish : {n : ℕ} → (s : S) → DWord C step n s → S
  | 0, s, _ => s
  | _ + 1, s, w => dFinish (step s w.1) w.2

noncomputable def dWeight (cost : (s : S) → C s → ℝ) :
    {n : ℕ} → (s : S) → DWord C step n s → ℝ
  | 0, _, _ => 1
  | _ + 1, s, w => cost s w.1 * dWeight cost (step s w.1) w.2

def dCharge (c : (s : S) → C s → ℤ) :
    {n : ℕ} → (s : S) → DWord C step n s → ℤ
  | 0, _, _ => 0
  | _ + 1, s, w => c s w.1 + dCharge c (step s w.1) w.2

end Dependent

end SharpRamseyFive.CertificateEnumeration

namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]

abbrev State (V H D B : Type*) := (V → H) × Finset (B × D)

variable (lines : H → Finset D)

abbrev RootChoice := V × H
abbrev OneChoice (s : State V H D B) :=
  (_v : V) × (u : V) × (x : AnchorChoice s.2 (lines (s.1 u))) ×
    {h : H // x.direction ∈ lines h}
abbrev TwoChoice (s : State V H D B) :=
  (_v : V) × (u : V) × (w : V) ×
    (x : AnchorChoice s.2 (lines (s.1 u))) ×
    (y : AnchorChoice s.2 (lines (s.1 w))) ×
    {h : H // x.direction ≠ y.direction ∧ x.direction ∈ lines h ∧ y.direction ∈ lines h}
abbrev PairDirections (s : State V H D B) (h h' : H) :=
  (lines h ∩ lines h') \ dictionary s.2
abbrev PairChoice (K : ℕ) (s : State V H D B) :=
  (_v : V) × (_u : V) × (h : H) × (h' : {h' : H // h' ≠ h}) ×
    (T : {T : Finset B // T ∈ (Finset.univ : Finset B).powersetCard K}) ×
      (T.val → PairDirections lines s h h'.val)
abbrev Action (K : ℕ) (s : State V H D B) :=
  RootChoice (V := V) (H := H) ⊕ OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s

noncomputable instance actionFintype (K : ℕ) (s : State V H D B) :
    Fintype (Action lines K s) := by
  letI : Fintype (RootChoice (V := V) (H := H)) := inferInstance
  letI : Fintype (OneChoice lines s) := inferInstance
  letI : Fintype (TwoChoice lines s) := inferInstance
  letI : Fintype (PairChoice lines K s) := inferInstance
  exact inferInstanceAs (Fintype (RootChoice (V := V) (H := H) ⊕
    OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s))

end SharpRamseyFive.WeightedPrograms
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_NewEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)
def newEvents (K : ℕ) (s : State V H D B) : Action lines K s → Finset (B × D)
  | .inl _ => ∅
  | .inr (.inl c) => c.2.2.1.requirements
  | .inr (.inr (.inl c)) => c.2.2.2.1.requirements ∪ c.2.2.2.2.1.requirements
  | .inr (.inr (.inr c)) => witnessRequirements c.2.2.2.2.1.val
      (PairDirections lines s c.2.2.1 c.2.2.2.1.val) c.2.2.2.2.2

def newValues (K : ℕ) (s : State V H D B) : Action lines K s → V → H
  | .inl c => Function.update s.1 c.1 c.2
  | .inr (.inl c) => Function.update s.1 c.1 c.2.2.2.val
  | .inr (.inr (.inl c)) => Function.update s.1 c.1 c.2.2.2.2.2.val
  | .inr (.inr (.inr c)) =>
      Function.update (Function.update s.1 c.1 c.2.2.1) c.2.1 c.2.2.2.1.val

def advance (K : ℕ) (s : State V H D B) (a : Action lines K s) : State V H D B :=
  (newValues lines K s a, s.2 ∪ newEvents lines K s a)

def degree (K : ℕ) (s : State V H D B) : Action lines K s → ℕ
  | .inr (.inr (.inr _)) => 2
  | _ => 1

def actionCharge (K : ℕ) (s : State V H D B) : Action lines K s → ℤ
  | .inl _ => -8
  | .inr (.inr (.inl _)) => 1
  | _ => 0

end SharpRamseyFive.WeightedPrograms

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_WitnessList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]

section SharedHitGeometry

open scoped Classical

variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

noncomputable def sharedBatches (s : V → Finset D) (hit : B → D → Prop) (v u : V) : Finset B :=
  Finset.univ.filter (fun r => ∃ d ∈ s v ∩ s u, hit r d)

noncomputable def touchedBatches (s : V → Finset D) (hit : B → D → Prop) (v : V) : Finset B :=
  Finset.univ.filter (fun r => ∃ u, u ≠ v ∧ r ∈ sharedBatches s hit v u)

noncomputable def encodedDirections (s : V → Finset D) (E : Finset V) : Finset D :=
  E.biUnion s

def paidDirections (C : Finset (B × D)) : Finset D := C.image Prod.snd

def Realized (hit : B → D → Prop) (C : Finset (B × D)) : Prop :=
  ∀ p ∈ C, hit p.1 p.2

def DictionaryInvariant (s : V → Finset D) (E : Finset V) (C : Finset (B × D)) : Prop :=
  paidDirections C ⊆ encodedDirections s E

end SharedHitGeometry
end SharpRamseyFive.ResidualCertificate
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_AnchorEventsRealized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators

variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

 def Agrees (f : V → H) (E : Finset V) (s : State V H D B) : Prop :=
  ∀ v ∈ E, s.1 v = f v

noncomputable def anchorName (C : Finset (B × D)) (S : Finset D)
    (d : D) (hd : d ∈ S) (r : B) : AnchorChoice C S :=
  if he : d ∈ dictionary C then .inl ⟨d, Finset.mem_inter.mpr ⟨hd, he⟩⟩
  else .inr (r, ⟨d, Finset.mem_sdiff.mpr ⟨hd, he⟩⟩)

 def Enabled (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s) : Prop :=
  ∀ c : OneChoice lines s, a = .inr (.inl c) → low = true

 def Coherent (f : V → H) (hit : B → D → Prop) (K : ℕ)
    (E : Finset V) (s : State V H D B) : Prop :=
  Agrees f E s ∧ DictionaryInvariant (fun v => lines (f v)) E s.2 ∧
    Realized hit s.2 ∧ s.2.card ≤ K * E.card
end SharpRamseyFive.CertificateCover
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_MakePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

abbrev Word (K : ℕ) := DWord (Action (V := V) (B := B) lines K) (advance lines K)
abbrev finish (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :=
  dFinish (Action lines K) (advance lines K) s w
abbrev charge (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :=
  dCharge (Action lines K) (advance lines K) (actionCharge lines K) s w

 def degreeSum (K : ℕ) : {n : ℕ} → (s : State V H D B) → Word lines K n s → ℕ
  | 0, _, _ => 0
  | _ + 1, s, w => degree lines K s w.1 + degreeSum K (advance lines K s w.1) w.2

 def TraceOK (K : ℕ) (low : Bool) :
    {n : ℕ} → (s : State V H D B) → Word lines K n s → Prop
  | 0, _, _ => True
  | _ + 1, s, w => s.2.card ≤ K * Fintype.card V ∧
      Enabled lines K low s w.1 ∧ TraceOK K low (advance lines K s w.1) w.2

 def append (K : ℕ) {m : ℕ} : {n : ℕ} → (s : State V H D B) →
    (w : Word lines K n s) → Word lines K m (finish lines K s w) → Word lines K (m + n) s
  | 0, _, _, w' => w'
  | _ + 1, s, w, w' => ⟨w.1, append K (advance lines K s w.1) w.2 w'⟩

 def Segment (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E F : Finset V) (s : State V H D B) {n : ℕ} (w : Word lines K n s) : Prop :=
  Coherent lines f hit K F (finish lines K s w) ∧
    F.card = E.card + degreeSum lines K s w ∧ TraceOK lines K low s w

abbrev AllPrograms (K : ℕ) (E : Finset V) (s : State V H D B) :=
  (n : Fin (Fintype.card V - E.card + 1)) × Word lines K n.val s

 def CompleteProgram (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (c : AllPrograms lines K E s) : Prop :=
  TraceOK lines K low s c.2 ∧ 0 ≤ charge lines K s c.2 ∧
    degreeSum lines K s c.2 = Fintype.card V - E.card

noncomputable def completePrograms (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B) :=
  {c : AllPrograms lines K E s // CompleteProgram lines K low E s c}

noncomputable instance completePrograms_fintype (K : ℕ) (low : Bool) (E : Finset V)
    (s : State V H D B) : Fintype (completePrograms lines K low E s) := by
  classical
  unfold completePrograms
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
end SharpRamseyFive.CertificateCover
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_HighMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.PoissonScore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def batchMeasure (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

def emptyEvent (s : Finset ι) : Set (ι → ℕ) :=
  (s : Set ι).pi (fun _ => {0})

noncomputable def emptyIndicator (s : Finset ι) (ω : ι → ℕ) : ℝ :=
  (emptyEvent s).indicator (fun _ => 1) ω

noncomputable def mass (rate : ι → ℝ≥0) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, (rate i : ℝ)

noncomputable def centeredFactor (s : Finset ι) (b : ℝ) (ω : ι → ℕ) : ℝ :=
  emptyIndicator s ω - b

noncomputable def scoreTerm {R : ℕ} (s : Finset ι) (b : ℝ) (own : Fin R → Bool)
    (ω : Fin R → ι → ℕ) : ℝ :=
  ∏ r, if own r then centeredFactor s b (ω r) else 0

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

section ComponentGeometry

variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def strongGraph (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ) :
    SimpleGraph H where
  Adj h k := h ≠ k ∧ t < mass rate (s h ∩ s k)
  symm := ⟨by
    intro h k hk
    exact ⟨hk.1.symm, by simpa only [Finset.inter_comm] using hk.2⟩⟩
  loopless := ⟨by intro h hh; exact hh.1 rfl⟩

def External (rate : ι → ℝ≥0) (s : H → Finset ι) (t : ℝ) (i : ι) : Prop :=
  ∃ h k : H, i ∈ s h ∧ i ∈ s k ∧
    (strongGraph rate s t).connectedComponentMk h ≠
      (strongGraph rate s t).connectedComponentMk k

noncomputable def externalPart (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (h : H) : Finset ι := by
  classical
  exact (s h).filter (External rate s t)

end ComponentGeometry
end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ExternalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
section ComponentGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def componentLabel (rate : ι → ℝ≥0) (s : H → Finset ι)
    (t : ℝ) (i : ι) : Option (strongGraph rate s t).ConnectedComponent := by
  classical
  exact if hi : ∃ h, i ∈ s h then
    if External rate s t i then none else
      some ((strongGraph rate s t).connectedComponentMk hi.choose)
    else none

end ComponentGeometry

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
variable (label : D → Option C) (R : ℕ)

abbrev Block (c : Option C) := {i : Fin R × D // label i.2 = c}
noncomputable def fill (c : C) (z : Block label R none → ℕ)
    (x : Block label R (some c) → ℕ) (r : Fin R) (d : D) : ℕ :=
  if he : label d = none then z ⟨(r,d), he⟩ else
    if hi : label d = some c then x ⟨(r,d), hi⟩ else 0

noncomputable def lineTrunc (J : ℕ) (ω : Fin R → ℕ) : ℝ :=
  if (Finset.univ.filter (fun r => ω r ≠ 0)).card < J then 1 else 0

noncomputable def blockTrunc (J : ℕ) (c : Option C) (ω : Block label R c → ℕ) : ℝ :=
  ∏ d : {d : D // label d = c}, lineTrunc R J (fun r => ω ⟨(r,d), d.property⟩)

variable (color : V → C) (s : V → Finset D) (b : ℝ) (own : V → Fin R → Bool)

noncomputable def componentFactor (J : ℕ) (c : C)
    (z : Block label R none → ℕ) (x : Block label R (some c) → ℕ) : ℝ :=
  blockTrunc label R J (some c) x *
    ∏ v : {v : V // color v = c}, scoreTerm (s v) b (own v) (fill label R c z x)

abbrev IntDir (c : C) := {d : D // label d = some c}

noncomputable def inside (c : C) (S : Finset D) : Finset (IntDir label c) :=
  Finset.univ.filter (fun d => d.val ∈ S)

noncomputable def touched (_c : C) (S : Finset D) (z : Block label R none → ℕ)
    (r : Fin R) : Bool :=
  decide (∃ d : {d : D // label d = none}, d.val ∈ S ∧ z ⟨(r,d), d.property⟩ ≠ 0)

noncomputable def unblock (c : C) (x : Block label R (some c) → ℕ) :
    Fin R → IntDir label c → ℕ := fun r d => x ⟨(r,d), d.property⟩

noncomputable def blockCoords (c : C) : (Fin R × IntDir label c) ≃ Block label R (some c) where
  toFun i := ⟨(i.1,i.2), i.2.property⟩
  invFun i := (i.1.1, ⟨i.1.2, i.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def unblockEquiv (c : C) :
    (Block label R (some c) → ℕ) ≃ᵐ (Fin R → IntDir label c → ℕ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Block label R (some c) => ℕ)
    (blockCoords label R c)).symm.trans (MeasurableEquiv.curry (Fin R) (IntDir label c) ℕ)

omit [Fintype D] [DecidableEq D] [Fintype C] [DecidableEq C] in
@[simp] lemma unblockEquiv_apply (c : C) (x : Block label R (some c) → ℕ) :
    unblockEquiv label R c x = unblock label R c x := rfl

end SharpRamseyFive.TupleComponents
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ComponentLabelWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.TupleComponents
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore
open Classical
variable {D V C : Type} [Fintype D] [DecidableEq D]
  [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

variable (label : D → Option C) (R : ℕ) (color : V → C)
  (s : V → Finset D) (own : V → Fin R → Bool)

def hitBatches {R : ℕ} (mask : Fin R → Bool) : Finset (Fin R) :=
  Finset.univ.filter (fun r => mask r = true)

def BAD {R : ℕ} (mask : Fin R → Bool) : Prop := R / 2 ≤ (hitBatches mask).card

end SharpRamseyFive.TupleComponents

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_TruncatedTupleIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SharpRamseyFive.Designations
open MeasureTheory
open scoped BigOperators
open Classical
variable {C Ω : Type*} [Fintype C] [DecidableEq C]

noncomputable def badIndicator (bad : C → Ω → Prop) (c : C) (z : Ω) : ℝ :=
  if bad c z then 1 else 0

variable [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def badMass (T : Ω → ℝ) (bad : C → Ω → Prop) (U : Finset C) : ℝ :=
  ∫ z, T z * ∏ c ∈ U, badIndicator bad c z ∂μ

end SharpRamseyFive.Designations

namespace SharpRamseyFive.AmbientDesignations
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations
open Classical
variable {D V : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)

abbrev Components := (strongGraph weight s t).ConnectedComponent
noncomputable def vertex (c : Components weight s t) : V := c.out

noncomputable def simpleSet : Finset (Components weight s t) :=
  Finset.univ.filter (fun c => ∀ v, (strongGraph weight s t).connectedComponentMk v = c →
    v = vertex weight s t c)

noncomputable def alpha (v : V) : ℝ := mass weight (externalPart weight s t v)
noncomputable def delta (base : ℝ) (v : V) : ℝ := mass weight (s v) - base

variable (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (own : V → Fin R → Bool)

noncomputable def extraWeight (c : Components weight s t) : ℝ :=
  |delta weight s base (vertex weight s t c)| ^ (R / 2) +
    alpha weight s t (vertex weight s t c) ^ K +
    (if R < J then 0 else
      ∑ d ∈ inside (componentLabel weight s t) c (s (vertex weight s t c)),
        ((R : ℝ) * ((L * weight d : ℝ≥0) : ℝ)) ^ J)

noncomputable def isBad (c : Components weight s t)
    (z : Block (componentLabel weight s t) R none → ℕ) : Prop :=
  BAD (touched (componentLabel weight s t) R c (s (vertex weight s t c)) z)

noncomputable def componentAbs (c : Components weight s t)
    (z : Block (componentLabel weight s t) R none → ℕ) : ℝ :=
  |∫ x, componentFactor (componentLabel weight s t) R
      (strongGraph weight s t).connectedComponentMk s (Real.exp (-(L : ℝ) * base)) own J c z x
    ∂batchMeasure (fun i : Block (componentLabel weight s t) R (some c) => L * weight i.1.2)|

noncomputable def designatedBound : ℝ :=
  let S := simpleSet weight s t
  (Real.exp (-(17 / 25 : ℝ) * ((L : ℝ) * R)) ^ S.card *
    Real.exp (-(7 / 10 : ℝ) * ((L : ℝ) * R)) ^
      (Fintype.card (Components weight s t) - S.card)) *
    ∑ U ∈ S.powerset, (∏ c ∈ S \ U, extraWeight weight s t R J K L base c) *
      badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => L * weight i.1.2))
        (blockTrunc (componentLabel weight s t) R J none) (isBad weight s t R) U

end SharpRamseyFive.AmbientDesignations

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_CompleteProgramWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)

def selectedBadEvent (K J : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (f : V → H) : Set ((B × D) → ℕ) := by
  classical
  exact {ω | Function.Injective f ∧ ∃ hit : B → D → Prop,
    (∀ r d, hit r d → ω (r, d) ≠ 0) ∧ Coherent lines f hit K E s ∧
    (∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches (fun v => lines (f v)) hit v).card) ∧
    (low = false → ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J)}

end SharpRamseyFive.CertificateCover

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H C : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]

noncomputable def vertexBadMass (weight rate : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    (R J : ℕ) (A : Finset V) : ℝ :=
  badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => rate i.1.2))
    (blockTrunc (componentLabel weight s t) R J none)
    (fun v z => BAD (touched (componentLabel weight s t) R
      ((strongGraph weight s t).connectedComponentMk v) (s v) z)) A

end SharpRamseyFive.SelectionBridge

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_PatchNotMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

noncomputable def badExpansion (a : V → (V → H) → ℝ)
    (B : Finset V → (V → H) → ℝ) (E : Finset V) (f : V → H) : ℝ :=
  ∑ U ∈ E.powerset, (∏ u ∈ E \ U, a u f) * B U f

end SharpRamseyFive.ResidualElimination

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def independentWeight (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (R J : ℕ) (base : ℝ) (h : H) : ℝ :=
  |mass weight (lines h) - base| ^ (R / 2) +
    (if R < J then 0 else ∑ d ∈ lines h, ((R : ℝ) * (rate d : ℝ)) ^ J)

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

noncomputable def fiber (r : V → C) (c : C) : Finset V :=
  Finset.univ.filter (fun v => r v = c)
noncomputable def singles (r : V → C) : Finset V :=
  Finset.univ.filter (fun v => (fiber r (r v)).card = 1)
noncomputable def largeLabels (r : V → C) : Finset C :=
  Finset.univ.filter (fun c => 2 ≤ (fiber r c).card)

omit [DecidableEq V] [Fintype C] in
@[simp] lemma mem_fiber (r : V → C) (c : C) (v : V) : v ∈ fiber r c ↔ r v = c := by
  simp [fiber]
omit [DecidableEq V] [Fintype C] in
@[simp] lemma mem_singles (r : V → C) (v : V) :
    v ∈ singles r ↔ (fiber r (r v)).card = 1 := by simp [singles]
omit [DecidableEq V] in
@[simp] lemma mem_largeLabels (r : V → C) (c : C) :
    c ∈ largeLabels r ↔ 2 ≤ (fiber r c).card := by simp [largeLabels]
end SharpRamseyFive.ComponentPartition
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_SinglesUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
variable {V C : Type} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

variable (G : SimpleGraph V)
noncomputable def componentMap : V → V := fun v => (G.connectedComponentMk v).out

end SharpRamseyFive.ComponentPartition
namespace SharpRamseyFive.ComponentEnumeration
open Classical
open scoped BigOperators
open CertificateEnumeration
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H]

variable (R : H → H → Prop)
noncomputable def relationGraph (hsym : Std.Symm R) (f : V → H) : SimpleGraph V where
  Adj u v := u ≠ v ∧ R (f u) (f v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, hsym.symm _ _ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

abbrev Extension (s : V → H) := (u : V) × V × {h : H // R (s u) h}
noncomputable def extend (s : V → H) (a : Extension R s) : V → H :=
  Function.update s a.2.1 a.2.2.1

abbrev RelatedPair := (h : H) × {h' : H // R h h'}
abbrev Seed := V × V × RelatedPair R
noncomputable def seedStart (z : Seed (V := V) R) : V → H :=
  Function.update (fun _ => z.2.2.1) z.2.1 z.2.2.2.1

end SharpRamseyFive.ComponentEnumeration

namespace SharpRamseyFive.ComponentPartition
open scoped BigOperators
open Classical
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
variable {V H C : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype C] [DecidableEq C]

noncomputable def connectedWeight (R : H → H → Prop) (hsym : Std.Symm R)
    (r : V → C) (c : C) (x : fiber r c → H) : ℝ :=
  if (relationGraph R hsym x).Connected then 1 else 0

end SharpRamseyFive.ComponentPartition

namespace SharpRamseyFive.AmbientEnumeration
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def overlapRelation (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ)
    (h k : H) : Prop := t < mass weight (lines h ∩ lines k)

omit [Fintype D] [Fintype H] [DecidableEq H] in
lemma overlapRelation_symm (weight : D → ℝ≥0) (lines : H → Finset D) (t : ℝ) :
    Std.Symm (overlapRelation weight lines t) := by
  constructor
  intro h k hh
  simpa only [overlapRelation, Finset.inter_comm] using hh

end SharpRamseyFive.AmbientEnumeration
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

noncomputable def vertexExpansion (weight : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R J K : ℕ) (L : ℝ≥0) (base : ℝ) (E : Finset V) (f : V → H) : ℝ :=
  badExpansion
    (fun u f => independentWeight weight (fun d => L * weight d) lines R J base (f u) +
      alpha weight (lines ∘ f) t u ^ K)
    (fun A f => vertexBadMass weight (fun d => L * weight d) (lines ∘ f) t R J A) E f

end SharpRamseyFive.AmbientEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ProjectiveEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

noncomputable def projectiveEquiv (e : V ≃ₗ[K] W) : ℙ K V ≃ ℙ K W :=
  Equiv.ofBijective (Projectivization.map e.toLinearMap e.injective) ⟨
    Projectivization.map_injective e.toLinearMap e.injective, by
      intro p
      refine ⟨Projectivization.mk K (e.symm p.rep) (fun h => p.rep_nonzero ?_), ?_⟩
      · have he := congrArg e h
        simpa only [e.apply_symm_apply,map_zero] using he
      · rw [Projectivization.map_mk]
        simp only [LinearEquiv.coe_coe,e.apply_symm_apply,Projectivization.mk_rep]⟩

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_CellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.CellVariance
open Module SharpRamseyFive.ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

noncomputable def cellMass (C : Finset (ℙ K V)) (δ : ℝ) (b : ℙ K (Module.Dual K V)) : ℝ :=
  δ*(C.filter fun a => Incident a b).card

end SharpRamseyFive.CellVariance

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A]

noncomputable def uniformCutoff (q : ℝ) (C W : Finset A) (n : ℕ) : ℕ :=
  ⌈q/((9:ℝ)/10*((C.card:ℝ)/W.card)^n)⌉₊

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FreshPublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*}
lemma exists_accepted_index {n : ℕ} (E : Finset A) (t : Fin n→A) :
    ∃i : Option (Fin n),Option.map t i=firstAccepted E t := by
  cases he : firstAccepted E t with
  | none => exact ⟨none,rfl⟩
  | some a =>
    obtain ⟨i,hi,_⟩ := firstAccepted_index E t he
    exact ⟨some i,by simpa only [Option.map_some] using congrArg some hi⟩

noncomputable def acceptedIndex {n : ℕ} (E : Finset A) (t : Fin n→A) : Option (Fin n) :=
  Classical.choose (exists_accepted_index E t)
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OptionComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def optionCompose (p : Law (Option α)) (next : Option α→Law (Option β)) :
    Law (Option β) :=
  map (adaptiveLaw p next) (fun ab=>ab.1.bind (fun _=>ab.2))

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SplitEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.AffineChart
open Module
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def splitEquiv (φ : V →ₗ[K] K) (o : V) (ho : φ o = 1) :
    V ≃ₗ[K] K × LinearMap.ker φ where
  toFun v := (φ v, ⟨v - φ v • o, by simp [LinearMap.mem_ker, ho]⟩)
  invFun v := v.1 • o + v.2
  left_inv v := by simp
  right_inv v := by
    rcases v with ⟨a, w⟩
    ext
    · simp [ho]
    · simp [ho]
  map_add' u v := by
    ext
    · simp
    · simp [add_smul]; abel
  map_smul' a v := by
    ext
    · simp
    · simp [smul_sub, smul_smul]

variable {U : Type*} [AddCommGroup U] [Module K U]

def normalize (v : K × U) : U := v.1⁻¹ • v.2

end SharpRamseyFive.AffineChart

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_RichLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

namespace SharpLogRamsey.ImplicitBranch
open Polynomial
open scoped Ring

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

The following Hensel lifting theorem is adapted from Mathlib.RingTheory.Henselian.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Henselian.lean

This code has been modified.
-/

variable {σ K R S : Type*} [Fintype σ] [DecidableEq σ] [Field K]
  [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

noncomputable def liftZ (F : MvPolynomial (Option σ) K) :
    Polynomial (MvPowerSeries σ K) :=
  MvPolynomial.aeval (fun o => o.elim Polynomial.X
    (fun i => Polynomial.C (MvPowerSeries.X i))) F

end SharpLogRamsey.ImplicitBranch

open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]

noncomputable def jetIdeal (n : ℕ) : Ideal (MvPowerSeries σ K) where
  carrier := {f | (n : ℕ∞) ≤ f.order}
  zero_mem' := by simp
  add_mem' := fun ha hb => (le_min ha hb).trans MvPowerSeries.min_order_le_add
  smul_mem' := by
    intro a f hf
    change (n : ℕ∞) ≤ (a*f).order
    exact hf.trans ((le_add_left le_rfl).trans MvPowerSeries.le_order_mul)

variable {τ R : Type*} [CommRing R] [Algebra K R]

variable [Fintype τ] [DecidableEq τ]

noncomputable def branchPoint (h : MvPowerSeries σ K) : Option σ → MvPowerSeries σ K :=
  fun o => o.elim h MvPowerSeries.X

noncomputable def branchTangent (h : MvPowerSeries σ K) (a : σ) :
    Option σ → MvPowerSeries σ K := fun o => MvPowerSeries.pderiv _ a (branchPoint h o)

end SharpLogRamsey.FlatnessCore
end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_HessianTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]
variable {τ R : Type*} [CommRing R] [Algebra K R]
variable [Fintype τ] [DecidableEq τ]

def scaledTangent (g : Option σ → R) (a : σ) : Option σ → R :=
  fun o => o.elim (-g (some a)) (fun i => if i = a then g none else 0)

noncomputable def flatnessPolynomial (F : MvPolynomial (Option σ) K) (a b : σ) :
    MvPolynomial (Option σ) K :=
  ∑ j, ∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv j F) *
    scaledTangent (fun o => MvPolynomial.pderiv o F) a i *
    scaledTangent (fun o => MvPolynomial.pderiv o F) b j

end SharpLogRamsey.FlatnessCore

open scoped BigOperators
open MvPolynomial Finsupp

open scoped BigOperators
open MvPolynomial
namespace SharpLogRamsey.Translation
variable {σ K : Type*} [Field K]

noncomputable def translate (x : σ → K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval fun i => X i+C (x i)

@[simp] lemma translate_X (x : σ → K) (i : σ) : translate x (X i) = X i+C (x i) := by
  simp [translate]
@[simp] lemma translate_C (x : σ → K) (c : K) : translate x (C c) = C c := by
  simp [translate]

@[simp] lemma translate_neg_translate (x : σ → K) (F : MvPolynomial σ K) :
    translate (-x) (translate x F) = F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf => simp [hf]

@[simp] lemma translate_translate_neg (x : σ → K) (F : MvPolynomial σ K) :
    translate x (translate (-x) F) = F := by
  simpa using translate_neg_translate (-x) F

end SharpLogRamsey.Translation

open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid
namespace SharpLogRamsey.CoprimeCombination
variable {σ ι K : Type*} [Fintype ι] [Field K] [Infinite K]

noncomputable def combinationMap (Q : ι → MvPolynomial σ K) :
    (ι → K) →ₗ[K] MvPolynomial σ K :=
  ∑ i, (LinearMap.proj i).smulRight (Q i)
omit [Infinite K] in

@[simp] lemma combinationMap_apply (Q : ι → MvPolynomial σ K) (c : ι → K) :
    combinationMap Q c = ∑ i, c i • Q i := by simp [combinationMap]

end SharpLogRamsey.CoprimeCombination
end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_TotalDegreeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
open Finset Finsupp
open scoped BigOperators
open MvPolynomial Finsupp
open scoped BigOperators
open MvPolynomial
open scoped BigOperators
open Finset MvPolynomial UniqueFactorizationMonoid

namespace SharpLogRamsey.NonplaneCertificate
open MvPolynomial FlatnessCore
variable {K : Type*} [Field K]
noncomputable section

abbrev Index := (Option (Fin 2) ≃ Fin 3) × Fin 2 × Fin 2

noncomputable def flatFamily (G : MvPolynomial (Fin 3) K) (i : Index) :
    MvPolynomial (Fin 3) K :=
  renameEquiv K i.1 (flatnessPolynomial ((renameEquiv K i.1).symm G) i.2.1 i.2.2)

end
end SharpLogRamsey.NonplaneCertificate

open scoped BigOperators
open Finset MvPolynomial
namespace SharpLogRamsey.LineFlatness
variable {K σ R : Type*} [Field K] [Fintype σ] [DecidableEq σ]
  [CommRing R] [Algebra K R]

noncomputable def restrictLine (x v : σ → K) (F : MvPolynomial σ K) : Polynomial K :=
  aeval (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) F

noncomputable def hessian (x : σ → K) (F : MvPolynomial σ K) (u v : σ → K) : K :=
  ∑ j, ∑ i, eval x (pderiv i (pderiv j F))*u i*v j

def scaledTangent (g : Option (Fin 2) → K) (a : Fin 2) : Option (Fin 2) → K :=
  fun o => o.elim (-g (some a)) (fun i => if i = a then g none else 0)

end SharpLogRamsey.LineFlatness

end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_ScaledTangentDot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

section

namespace SharpLogRamsey.GenericCoordinates
open MvPolynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K] [Infinite K]
noncomputable section

def shear (a b c : K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 0+a*x 1+b*x 2, x 1+c*x 2, x 2]
  invFun x := ![x 0-a*x 1+(a*c-b)*x 2, x 1-c*x 2, x 2]
  left_inv x := by ext i; fin_cases i <;> simp ; ring
  right_inv x := by ext i; fin_cases i <;> simp ; ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r x := by ext i; fin_cases i <;> simp <;> ring

abbrev first (a b : K) : (Fin 3 → K) →ₗ[K] K :=
  LinearMap.proj 0+a • LinearMap.proj 1+b • LinearMap.proj 2

def line (x v : Fin 3 → K) : Set (Fin 3 → K) := Set.range (fun r : K => x+r • v)
def direction (t : (Fin 3 → K) →ₗ[K] K) (v : Fin 3 → K) : Fin 3 → K := (t v)⁻¹ • v
def base (t : (Fin 3 → K) →ₗ[K] K) (x v : Fin 3 → K) : Fin 3 → K :=
  x-t x • direction t v

end
end SharpLogRamsey.GenericCoordinates

end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_Triple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
namespace SharpLogRamsey.PolynomialCoordinates
open MvPolynomial
variable {K : Type*} [Field K]
noncomputable section
abbrev Triple := Polynomial (Polynomial (Polynomial K))

def encode : MvPolynomial (Fin 3) K ≃ₐ[K] Triple (K := K) :=
  (renameEquiv K (Equiv.swap 0 2)).trans ((finSuccEquiv K 2).trans
    (Polynomial.mapAlgEquiv ((finSuccEquiv K 1).trans
      (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1))))))

@[simp] lemma encode_C (a : K) : encode (C a) = Polynomial.C (Polynomial.C (Polynomial.C a)) := by
  simp [encode,finSuccEquiv_apply,uniqueAlgEquiv_apply]

@[simp] lemma encode_X (i : Fin 3) : encode (X i : MvPolynomial (Fin 3) K) =
    ![Polynomial.C (Polynomial.C Polynomial.X), Polynomial.C Polynomial.X, Polynomial.X] i := by
  have h2 : finSuccEquiv K 2 (X 2) = Polynomial.C (X 1) :=
    finSuccEquiv_X_succ (j := 1)
  have h1 : finSuccEquiv K 2 (X 1) = Polynomial.C (X 0) :=
    finSuccEquiv_X_succ (j := 0)
  have h11 : finSuccEquiv K 1 (X 1) = Polynomial.C (X 0) :=
    finSuccEquiv_X_succ (j := 0)
  fin_cases i <;> simp [encode,h2,h1,h11,finSuccEquiv_X_zero,
    uniqueAlgEquiv_apply,Equiv.swap_apply_def]

def changeHom (a b c : K) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0-C a*X 1+C (a*c-b)*X 2, X 1-C c*X 2, X 2]
def unchangeHom (a b c : K) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval ![X 0+C a*X 1+C b*X 2, X 1+C c*X 2, X 2]

lemma unchange_change (a b c : K) (F : MvPolynomial (Fin 3) K) :
    unchangeHom a b c (changeHom a b c F) = F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom,unchangeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom,unchangeHom] ; ring
lemma change_unchange (a b c : K) (F : MvPolynomial (Fin 3) K) :
    changeHom a b c (unchangeHom a b c F) = F := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [changeHom,unchangeHom]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,hf]
    congr 1
    fin_cases i <;> simp [changeHom,unchangeHom] ; ring

def change (a b c : K) : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (changeHom a b c) (unchangeHom a b c)
    (AlgHom.ext (change_unchange a b c))
    (AlgHom.ext (unchange_change a b c))

end
end SharpLogRamsey.PolynomialCoordinates

end

end

section

namespace SharpLogRamsey.AffineIncidence
open Finset
open scoped BigOperators
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
noncomputable section

def carrier (x v : Fin 3 → K) : Set (Fin 3 → K) := Set.range (fun r : K => x+r • v)

variable (x v : ι → Fin 3 → K)
def pencil (y : Fin 3 → K) : Finset ι := by
  classical
  exact univ.filter (fun i => y ∈ carrier (x i) (v i))
def onLine (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact S.filter (fun y => y ∈ carrier (x i) (v i))
def richPoints (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact (onLine x v S i).filter (fun y => 2 < (pencil x v y).card)
def poorPoints (S : Finset (Fin 3 → K)) (i : ι) : Finset (Fin 3 → K) := by
  classical
  exact (onLine x v S i).filter (fun y => (pencil x v y).card ≤ 2)

end
end SharpLogRamsey.AffineIncidence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Geometry_Weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section
section
section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def weight (p : ℝ) (f : V → Bool) : ℝ :=
  ∏ v, if f v then p else 1-p

def selected (f : V → Bool) : Finset V := univ.filter (fun v => f v = true)

noncomputable def count (F : Finset (Finset V)) (S : Finset V) : ℕ :=
  (F.filter (· ⊆ S)).card

end SharpLogRamsey.Sampling

end

section

namespace SharpLogRamsey.Interpolation
open Finset MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]
noncomputable section

abbrev Box (n h : ℕ) := Fin n → Fin (h+1)
def exponent {n h : ℕ} (d : Box n h) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (d i).val)

end
end SharpLogRamsey.Interpolation

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseSmallLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

noncomputable def bidualPoint : (ℙ K V) ≃ (ℙ K (Dual K (Dual K V))) :=
  projectiveEquiv (Module.evalEquiv K V)

end SharpRamseyFive.ProjectiveIncidence

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeometricRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveRestriction

section
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def Domain (f : V→ₗ[K]W) := {p : ℙ K V // f p.rep≠0}

end

open Module ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.ProjectiveRestriction

namespace SharpRamseyFive.DyadicLifts
open scoped Classical BigOperators
variable {A B : Type*}

noncomputable def multiplicity (f : A→B) (T : Finset A) (b : B) : ℕ :=
  (T.filter fun a=> f a=b).card

noncomputable def bin (f : A→B) (T : Finset A) (k : ℕ) : Finset A :=
  T.filter fun a=> Nat.log 2 (multiplicity f T (f a))=k

noncomputable def restrictions (f : A→B) (T : Finset A) (k : ℕ) : Finset B :=
  (bin f T k).image f

noncomputable def enclosure (f : A→B) (U : Finset A) (l : ℕ) : Finset B :=
  (U.image f).filter fun b=> l ≤ multiplicity f U b

end SharpRamseyFive.DyadicLifts

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LocalNodeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

def pairOptions (p : Option α×Option β) : Option (α×β) :=
  p.1.bind fun a=>p.2.map fun b=>(a,b)

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GenericFreshCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open MeasureTheory
open scoped Classical BigOperators
variable {Ω α β : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α] [DecidableEq α] [Fintype β]

noncomputable def publicTableLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (decode : Ω→α→β) : Law (α→β) := finiteImageLaw μ decode

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ScoreFiniteCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
  {Ω : ι→Type*} [∀i,Fintype (Ω i)] {M : ∀i,Ω i→Type*}

abbrev BranchMessage (t : ∀i,Ω i) := (i : ι)×M i (t i)
noncomputable def branchDecoded (decode : ∀i t,M i t→α) (t : ∀i,Ω i)
    (m : BranchMessage (M:=M) t) : α := decode m.1 (t m.1) m.2
noncomputable def branchEncoded (i : ι) (encode : ∀t : Ω i,Option (M i t))
    (t : ∀i,Ω i) : Option (BranchMessage (M:=M) t) :=
  (encode (t i)).map (Sigma.mk i)

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_GeneralReversedCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal

structure FinitePredictor (A B : Type) [Fintype A] [Fintype B] where
  Tape : Type
  tapeFintype : Fintype Tape
  Message : Tape→Type
  messageFintype : ∀t,Fintype (Message t)
  tapeLaw : @Law Tape tapeFintype
  decoded : ∀t,Message t→Finset A
  encoded : Finset A→Finset B→∀t,Option (Message t)
  cost : ∀t,Message t→ℝ
attribute [instance] FinitePredictor.tapeFintype FinitePredictor.messageFintype

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GuardedNodeOriginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α Ω J : Type*} [Fintype Ω] [Fintype J]

noncomputable def evictionFraction (X C : Finset α) : ℝ := (X\C).card/(X.card:ℝ)

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalLevelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α : Type*} [Fintype α]

noncomputable def positiveLaw (p : Law α) : Law {a // 0 < p a} where
  mass a := p a
  nonneg a := p.nonneg a
  sum_one := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a => 0 < p a)) (by simp), Finset.sum_filter]
    calc
      _ = ∑ a, p a := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : 0 < p a
        · simp [h]
        · have hz : p a = 0 := le_antisymm (le_of_not_gt h) (p.nonneg a)
          simp [hz]
      _ = 1 := p.sum_one

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]

noncomputable def originalLevelLaw (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j)) :
    Law ((∀ i, A i) × (∀ j, B j)) :=
  adaptiveLaw (piLaw μ) (fun _ => piLaw ν)

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_TargetLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) targetLossPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {Ω A B : Type*} [Fintype Ω]

def TargetCovered (ctx : Option (Finset A × Finset B))
    (caps : Option (Finset B × Finset A)) (a : A) (b : B) : Prop :=
  ∃ C D, ctx=some C ∧ caps=some D ∧ a∈C.1 ∧ b∈C.2 ∧ a∈D.2 ∧ b∈D.1

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndependentTargetLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
local instance (priority := high) independentTargetPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end
end

open scoped Classical BigOperators
noncomputable section
local instance (priority := high) targetProductPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
end

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IndependentSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators

noncomputable section
variable {α : Type*} [Fintype α]
lemma mean_congr_pos (p : Law α) {f g : α→ℝ} (h : ∀a,0<p a→f a=g a) : mean p f=mean p g :=
  le_antisymm (mean_mono_pos p (fun a ha=>(h a ha).le))
    (mean_mono_pos p (fun a ha=>(h a ha).ge))
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance uniformHistoryIndexDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

local instance uniformHistorySubtypeDecEq_rc9f2bd_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
def preRoundLaw (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) : Law ((κ×BlockHistory B A T β n)×(B→A)) :=
  adaptiveLaw (adaptiveLaw μ (fun c=>historyLaw (p c) (S c) n))
    (fun z=>freshBlockLaw (historyUnused (S z.1) z.2))

end

open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance historyProducerIndexDecEq : DecidableEq ((B × A) ⊕ T) := Classical.decEq _

local instance historyProducerSubtypeDecEq_rc9f2bd_1 (E : Finset ((B × A) ⊕ T)) : DecidableEq E := Classical.decEq _
def preRoundTupleLaw (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    Law (((κ×BlockHistory B A T β n)×(B→A))×(((B×A)⊕T)→β)) :=
  adaptiveLaw (preRoundLaw μ p S n) (fun z=>historyPosterior (p z.1.1) z.1.2)

variable {Ω : Type} [Fintype Ω]

def historyObservationLaw (μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (S : κ→B→Finset A) (n : ℕ) :
    Law ((κ×(((B×A)⊕T)→β))×(BlockHistory B A T β n×(B→A))) :=
  map (preRoundTupleLaw μ p S n) (fun z=>((z.1.1.1,z.2),(z.1.1.2,z.1.2)))

def originalHistoryLaw (P : Law Ω) (context : Ω→κ) (tuple : Ω→((B×A)⊕T)→β)
    (S : κ→B→Finset A) (n : ℕ) : Law (Ω×(BlockHistory B A T β n×(B→A))) :=
  liftObserved P (fun ω=>(context ω,tuple ω))
    (historyObservationLaw (first (pair P context tuple)) (fiber (pair P context tuple)) S n)

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Trees_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section

abbrev Slots (w r : ℕ) := (((Fin w×Bool)×Fin r)⊕(Fin w×Fin (2*r)))

end
end SharpRamseyFive.Windows

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PreRoundDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance preRoundDeletionIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _

def preRoundBad (_μ : Law κ) (p : κ→Law (((B×A)⊕T)→β))
    (_S : κ→B→Finset A) (n : ℕ) (J d e : ℝ)
    (c : κ→BlockHistory B A T β n→((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (z : (κ×BlockHistory B A T β n)×(B→A)) (i : ((B×A)⊕T)) : ℝ :=
  indexBad J d e (historyPosterior (p z.1.1) z.1.2) (c z.1.1 z.1.2) z.2 i

end

open scoped Classical BigOperators
variable {Ω W T : Type*} [Fintype Ω] [Fintype W] [Fintype T]

variable {κ β : Type} [Fintype κ] [Fintype β] {w r n rem : ℕ}
  [Nonempty (Fin r)]
local instance goodWindowIndexDecEq : DecidableEq (SharpRamseyFive.Windows.Slots w r) := Classical.decEq _

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowReadiness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {κ β : Type} [Fintype κ] [Fintype β] {w r n rem : ℕ} [Nonempty (Fin r)]
local instance readinessIndexDE : DecidableEq (Slots w r) := Classical.decEq _

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ConditionalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
variable {α β κ τ : Type*} [Fintype α] [Fintype β] [Fintype κ] [Fintype τ]

def coveredPositions {n : ℕ} (x : Fin n→β) (D : Finset β) : Finset (Fin n) :=
  Finset.univ.filter fun i=>x i∈D

end
end

open SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section
variable {κ β τ : Type} [Fintype κ] [Fintype β] [Fintype τ] {r n rem : ℕ} [Nonempty (Fin r)]
local instance readyExtractBlockDE_rc9f2bd_1 : DecidableEq (Fin 1×Bool) := Classical.decEq _
local instance readyExtractIndexDE : DecidableEq (Slots 1 r) := Classical.decEq _

end

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

def sourceSequence {n : ℕ} (reverse : Bool) (view : β→α) (x : Fin n→β) : Fin n→α :=
  fun i=>view (x (if reverse then i.rev else i))

structure SelectedStream (N n : ℕ) (admissible : (Fin N→α)→Prop) where
  law : Law Ω
  stream : Ω→Fin N→α
  tuple : Ω→Fin n→β
  reverse : Bool
  view : β→α
  selected : ∀ a,0<law a→stream a∈occurrences (sourceSequence reverse view (tuple a))
  good : ∀ a,0<law a→admissible (stream a)
  density : ℝ
  density_nonneg : 0≤density
  density_bound : ∀ s,map law stream s≤density/(Fintype.card α:ℝ)^N

end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_CountedExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
noncomputable section
local instance countedFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def RunAssignment (l w : ℕ) := {a : Fin l→Fin w // Monotone a}
instance instFintypeRunAssignment (l w : ℕ) : Fintype (RunAssignment l w) := inferInstanceAs (Fintype {a : Fin l→Fin w // Monotone a})

def runCutoff {l w : ℕ} (a : RunAssignment l w) (j : Fin w) : Fin (l+1) :=
  ⟨(Finset.univ.filter fun i=>a.val i≤j).card,by
    have h:=Finset.card_le_univ (Finset.univ.filter fun i=>a.val i≤j)
    simp only [Fintype.card_fin] at h
    omega⟩

lemma le_iff_lt_runCutoff {l w : ℕ} (a : RunAssignment l w) (i : Fin l) (j : Fin w) :
    a.val i≤j ↔ i.val<(runCutoff a j).val := by
  constructor
  · intro ha
    have hsub : Finset.Iic i⊆Finset.univ.filter (fun k=>a.val k≤j) := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(a.property (Finset.mem_Iic.mp hk)).trans ha⟩
    have h:=Finset.card_le_card hsub
    simp only [Fin.card_Iic] at h
    exact Nat.lt_of_succ_le h
  · intro hi
    by_contra! ha
    have hsub : Finset.univ.filter (fun k=>a.val k≤j)⊆Finset.Iio i := by
      intro k hk
      apply Finset.mem_Iio.mpr
      by_contra! hik
      exact (not_le_of_gt ha) ((a.property hik).trans (Finset.mem_filter.mp hk).2)
    have h:=Finset.card_le_card hsub
    simp only [Fin.card_Iio] at h
    exact (not_lt_of_ge h) hi

lemma runCutoff_injective {l w : ℕ} : Function.Injective (@runCutoff l w) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply le_antisymm
  · apply (le_iff_lt_runCutoff a i (b.val i)).mpr
    rw [h]
    exact (le_iff_lt_runCutoff b i (b.val i)).mp le_rfl
  · apply (le_iff_lt_runCutoff b i (a.val i)).mpr
    rw [←h]
    exact (le_iff_lt_runCutoff a i (a.val i)).mp le_rfl

lemma runAssignment_card (l w : ℕ) : Fintype.card (RunAssignment l w)≤(l+1)^w := by
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    Fintype.card_le_of_injective (@runCutoff l w) runCutoff_injective

variable {α β κ : Type*} [Fintype α] [Fintype β] [Fintype κ]

lemma runAssignment_entropy {l w : ℕ} (p : Law (RunAssignment l w)) :
    entropy p≤w*Real.log (l+1) := by
  have hc:=entropy_le_log_card p
  have hpos : 0<Fintype.card (RunAssignment l w) := by
    obtain ⟨a,ha⟩:=mean_exists_ge p (fun _=>(0:ℝ))
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  have hlog:=Real.log_le_log (by exact_mod_cast hpos : (0:ℝ)<Fintype.card (RunAssignment l w))
    (show (Fintype.card (RunAssignment l w):ℝ)≤((l+1)^w:ℕ) by exact_mod_cast runAssignment_card l w)
  have he : Real.log (((l+1)^w:ℕ):ℝ)=(w:ℝ)*Real.log (l+1) := by
    rw [Nat.cast_pow,Real.log_pow]
    simp only [Nat.cast_add,Nat.cast_one]
  exact hc.trans (he ▸ hlog)

def retainedAssignment {n l w : ℕ} (hl : l≤n) (S : Finset (Fin n))
    (slot : Fin n→Fin w) (hslot : Monotone slot) : RunAssignment l w :=
  ⟨slot ∘ retainedIndices hl S,hslot.comp (retainedIndices hl S).monotone⟩

end
end

open scoped Classical BigOperators
open SelectedTuple

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ContextDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
open SelectedTuple
noncomputable section
variable {Ω β κ Θ α : Type*} [Fintype Ω] [Fintype β] [Fintype κ] [Fintype Θ] [Fintype α]

local instance descriptionFinDecEq_rc9f2bd_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
structure ContextDescription {n : ℕ} (p : Law Ω) (x : Ω→Fin n→β) (L J : ℝ) where
  context : Ω→κ
  domain : κ→Fin n→Finset β
  entropy_bound : entropy (map p context)≤L
  contains : ∀ a,0<p a→∀ i,x a i∈domain (context a) i
  cap : ∀ a,0<p a→∀ i,Real.log (domain (context a) i).card≤J

def countedDescription {n l w : ℕ} (hl : l≤n) (p : Law Ω)
    (x : Ω→Fin n→β) (S : Ω→Finset (Fin n)) (ctx : Ω→κ) (D : κ→Fin w→Finset β)
    (slot : Ω→Fin n→Fin w) (hslot : ∀ a,Monotone (slot a))
    (hdom : ∀ a,0<p a→∀ i∈S a,x a i∈D (ctx a) (slot a i))
    (hE : 0<eventMass p (Finset.univ.filter fun a=>l≤(S a).card))
    (L M : ℝ) (hctx : entropy (map (conditionOn p _ hE) ctx)≤L)
    (hc : ∀ a,0<p a→∀ j,Real.log (D (ctx a) j).card≤M) :
    ContextDescription (κ:=κ×RunAssignment l w) (conditionOn p _ hE)
      (fun a=>retainedTuple hl (x a) (S a)) (L+w*Real.log (l+1)) M where
  context a:=(ctx a,retainedAssignment hl (S a) (slot a) (hslot a))
  domain c i:=D c.1 (c.2.val i)
  entropy_bound:=by
    have hh:=entropy_subadditive (pair (conditionOn p _ hE) ctx
      (fun a=>retainedAssignment hl (S a) (slot a) (hslot a)))
    simp only [first_pair,second_pair] at hh
    exact hh.trans (add_le_add hctx (runAssignment_entropy _))
  contains:=by
    intro a ha i
    obtain ⟨he,hp⟩:=conditionOn_positive p _ hE a ha
    exact hdom a hp _ (retainedIndices_mem hl _ (Finset.mem_filter.mp he).2 i)
  cap:=by
    intro a ha i
    exact hc a (conditionOn_positive p _ hE a ha).2 _

end

noncomputable section
local instance dependentTableFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_DependentPrivateStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A] {B : A→Type*} [∀a,Fintype (B a)]
lemma sigmaLaw_positive (p : Law A) (q : ∀a,Law (B a)) (z : Sigma B)
    (hz : 0 < sigmaLaw p q z) : 0<p z.1 ∧ 0<q z.1 z.2 := by
  change 0<p z.1*q z.1 z.2 at hz
  exact (mul_pos_iff.mp hz).resolve_right (fun h=>(p.nonneg _).not_gt h.1)
lemma map_sigma_first (p : Law A) (q : ∀a,Law (B a)) :
    map (sigmaLaw p q) Sigma.fst=p := by
  apply Law.ext_mean
  intro f
  rw [mean_map,mean_sigma]
  simp only [mean_const]
lemma sigma_stream {Γ : Type*} [Fintype Γ] (p : Law A) (q : ∀a,Law (B a)) (s : A→Γ) :
    map (sigmaLaw p q) (fun z=>s z.1)=map p s := by
  change map (sigmaLaw p q) (s ∘ Sigma.fst)=map p s
  rw [←map_comp,map_sigma_first]
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GoodEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

theorem scaled_heavy_atom_mass (p : Law α) (N M K : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hcap : ((support p).card:ℝ) ≤ M) :
    eventProbability p (Finset.univ.filter fun a => N*p a > Real.exp K) ≤
      (Real.log N-entropy p+M/N)/K := by
  let E := Finset.univ.filter fun a => N*p a > Real.exp K
  have hpoint (a : α) :
      (if a ∈ E then K*p a else 0)-(if a ∈ support p then 1/N else 0) ≤
        p a*Real.log (N*p a) := by
    by_cases hp : p a=0
    · have hE : a ∉ E := by simp only [E,Finset.mem_filter,Finset.mem_univ,true_and,hp,mul_zero]; exact (Real.exp_pos K).not_gt
      have hs : a ∉ support p := by simp [mem_support,hp]
      simp only [hp,hE,hs,ite_false,sub_zero,zero_mul,le_refl]
    · have hp' := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      have hs := (mem_support p a).mpr hp'
      by_cases he : a ∈ E
      · have hh : Real.exp K < N*p a := (Finset.mem_filter.mp he).2
        have hl : K ≤ Real.log (N*p a) := (Real.le_log_iff_exp_le (by positivity)).mpr hh.le
        simp only [he,hs,ite_true]
        nlinarith [mul_le_mul_of_nonneg_right hl (p.nonneg a),div_pos zero_lt_one hN]
      · have hh := point_log_ratio (p a) (1/N) (p.nonneg a) (by positivity) (fun _ => by positivity)
        have heq : p a/(1/N)=N*p a := by field_simp
        rw [heq] at hh
        simp only [he,hs,ite_false,ite_true,zero_sub]
        nlinarith [p.nonneg a]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  have hlog : (∑ a,p a*Real.log (N*p a))=Real.log N-entropy p := by
    calc
      _ = ∑ a,(p a*Real.log N+p a*Real.log (p a)) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hp : p a=0
        · simp [hp]
        · rw [Real.log_mul (ne_of_gt hN) hp]
          ring
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,p.sum_one,one_mul]; simp only [entropy,sub_neg_eq_add]
  rw [Finset.sum_sub_distrib,hlog] at h
  have he : (∑ a,if a ∈ E then K*p a else 0)=K*eventProbability p E := by
    rw [Finset.sum_ite_mem,Finset.univ_inter]
    simp only [eventProbability,Finset.mul_sum]
  have hs : (∑ a,if a ∈ support p then 1/N else 0)=((support p).card:ℝ)/N := by
    rw [Finset.sum_ite_mem]
    simp [div_eq_mul_inv]
  rw [he,hs] at h
  have hfrac : ((support p).card:ℝ)/N ≤ M/N := div_le_div_of_nonneg_right hcap hN.le
  apply (le_div_iff₀ hK).mpr
  dsimp [E] at h
  nlinarith

lemma small_atom_mass (p : Law α) (N K : ℝ) (hN : 0<N)
    (hcap : ((support p).card : ℝ) ≤ N) :
    eventMass p (Finset.univ.filter fun a => p a < Real.exp (-K)/N) ≤ Real.exp (-K) := by
  let E := Finset.univ.filter fun a => p a < Real.exp (-K)/N
  have hp (a : α) : (if a ∈ E then p a else 0) ≤
      if a ∈ support p then Real.exp (-K)/N else 0 := by
    by_cases hs : a ∈ support p
    · simp only [hs,ite_true]
      split_ifs with he
      · exact (Finset.mem_filter.mp he).2.le
      · positivity
    · have hz := outside_support p hs
      simp [hs,hz]
  have hh := Finset.sum_le_sum fun a (_ : a∈Finset.univ) => hp a
  calc
    _ = ∑ a, if a∈E then p a else 0 := by simp [eventMass, E, Finset.sum_filter]
    _ ≤ ∑ a, if a ∈ support p then Real.exp (-K)/N else 0 := hh
    _ = (support p).card * (Real.exp (-K)/N) := by simp [Finset.sum_ite_mem]
    _ ≤ N * (Real.exp (-K)/N) := mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = Real.exp (-K) := by field_simp

def heavyRow (p : Law (α × β)) (N K : ℝ) (a : α) : Finset β :=
  Finset.univ.filter fun b => Real.exp K < N*p (a,b)

def goodFirstEndpoints (p : Law (α × β)) (NA N K : ℝ) : Finset α :=
  Finset.univ.filter fun a => Real.exp (-K)/NA ≤ first p a ∧
    eventMass (fiber p a) (heavyRow p N K a) ≤ (1:ℝ)/50

lemma weighted_heavy_rows (p : Law (α × β)) (N K : ℝ) :
    (∑ a,first p a * eventMass (fiber p a) (heavyRow p N K a)) =
      eventProbability p (Finset.univ.filter fun z => Real.exp K < N*p z) := by
  simp only [eventMass,heavyRow,eventProbability,Finset.sum_filter,Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp only [mul_zero, mass_eq_first_mul_fiber]

lemma bad_conditional_row_mass (p : Law (α × β)) (N K : ℝ) :
    eventMass (first p) (Finset.univ.filter fun a =>
      (1:ℝ)/50 < eventMass (fiber p a) (heavyRow p N K a)) ≤
      50 * eventProbability p (Finset.univ.filter fun z => Real.exp K < N*p z) := by
  rw [←weighted_heavy_rows, Finset.mul_sum]
  unfold eventMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with ha
  · have hn := (first p).nonneg a
    nlinarith
  · exact mul_nonneg (by norm_num) (mul_nonneg ((first p).nonneg a)
      (Finset.sum_nonneg fun b _ => (fiber p a).nonneg b))

theorem bad_first_endpoint_mass (p : Law (α × β)) (NA N M K : ℝ)
    (hNA : 0<NA) (hN : 0<N) (hK : 0<K)
    (hA : ((support (first p)).card : ℝ) ≤ NA)
    (hflag : ((support p).card : ℝ) ≤ M) :
    eventMass (first p) (goodFirstEndpoints p NA N K)ᶜ ≤
      Real.exp (-K) + 50*(Real.log N-entropy p+M/N)/K := by
  let A := Finset.univ.filter fun a => first p a < Real.exp (-K)/NA
  let B := Finset.univ.filter fun a => (1:ℝ)/50 < eventMass (fiber p a) (heavyRow p N K a)
  have hsub : (goodFirstEndpoints p NA N K)ᶜ ⊆ A ∪ B := by
    intro a ha
    simp only [goodFirstEndpoints,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    simp only [A,B,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases h : first p a < Real.exp (-K)/NA
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge (fun hb => ha ⟨le_of_not_gt h,hb⟩))
  have hmass : eventMass (first p) (goodFirstEndpoints p NA N K)ᶜ ≤
      eventMass (first p) A + eventMass (first p) B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => (first p).nonneg a))
    have hle (a : α) : (if a ∈ A ∪ B then first p a else 0) ≤
        (if a ∈ A then first p a else 0)+(if a ∈ B then first p a else 0) := by
      by_cases ha : a ∈ A <;> by_cases hb : a ∈ B <;>
        simp [ha,hb,(first p).nonneg a]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hle a)
    simpa only [eventMass,Finset.sum_add_distrib, Finset.sum_ite_mem,Finset.univ_inter] using hh
  have ha := small_atom_mass (first p) NA K hNA hA
  have hb := bad_conditional_row_mass p N K
  have hc := scaled_heavy_atom_mass p N M K hN hK hflag
  dsimp only [A,B] at hmass
  have hh := add_le_add ha (hb.trans (mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤50)))
  apply hmass.trans
  convert hh using 1 <;> first | rfl | ring

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_CoreGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry

section
open Module SharpRamseyFive.FiniteEntropy
open scoped LinearAlgebra.Projectivization BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma rep_mem_iff (a : ℙ K V) (W : Submodule K V) :
    a.rep∈W ↔ a.submodule≤W := by
  rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]

end

section
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def InRectangle (U : Submodule K (Module.Dual K V)) (a : V)
    (b : Module.Dual K V) : Prop := a∈U.dualCoannihilator ∧ b∈U

end

open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}

def RectangleCharge (U W : Fin n → Submodule K (Module.Dual K V))
    (x : Fin n → V × Module.Dual K V) (i j : Fin n) : Prop :=
  i<j ∧ ((InRectangle (U i) (x i).1 (x i).2 ∧ InRectangle (U i) (x j).1 (x j).2) ∨
    (InRectangle (W j) (x i).1 (x i).2 ∧ InRectangle (W j) (x j).1 (x j).2))

end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_Cores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
noncomputable section
variable {K V α β : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype α] [Fintype β]

def firstCore (p : Law (α × β)) (w : β → Module.Dual K V) (a : α) :
    Submodule K (Module.Dual K V) := core (fiber p a) w (1/200)

def secondCore (p : Law (α × β)) (v : α → V) (b : β) : Submodule K V :=
  core (fiber (swap p) b) v (1/200)

end
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def state (a : ι → ℙ K V) (b : ι → ℙ K (Dual K V))
    (E : Finset ι) (y : ℙ K (Dual K V)) : Submodule K (Dual K V) :=
  ⨆ i∈E, if Incident (a i) y then (b i).submodule else ⊥

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ChooseLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (ℙ K (Dual K V))]

lemma card_upper (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    (upperSet W r).card=∑ l∈Finset.range (r+1),(levelSet W l).card := by
  have hh:=Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (ℙ K (Dual K V)))
    (Finset.range (r+1)) (fun y => finrank K (W y))
  simpa only [levelSet,upperSet,Finset.mem_range,Nat.lt_succ_iff] using hh.symm

lemma exists_level (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) :
    ∃ l,l ≤ r ∧ (∀ j,j ≤ r → (levelSet W j).card≤(levelSet W l).card) ∧
      (upperSet W r).card≤(r+1)*(levelSet W l).card := by
  obtain ⟨l,hl,hh⟩:=Finset.exists_max_image (Finset.range (r+1))
    (fun l => (levelSet W l).card) (by simp)
  refine ⟨l,Nat.le_of_lt_succ (Finset.mem_range.mp hl),?_,?_⟩
  · intro j hj
    exact hh j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  · rw [card_upper]
    calc
      _ ≤∑ j∈Finset.range (r+1),(levelSet W l).card := Finset.sum_le_sum hh
      _ = _ := by simp

noncomputable def chooseLevel (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : ℕ) : ℕ :=
  (exists_level W r).choose

end

open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))]

def Expensive (W : ℙ K (Dual K V) → Submodule K (Dual K V))
    (a : ℙ K V) (b : ℙ K (Dual K V)) (q : ℝ) : Prop :=
  let Z:=levelSet W (chooseLevel W (finrank K (W b)))
  ((Z.filter fun y => b.submodule≤W y).card:ℝ)<(Z.card:ℝ)/(16*q) ∧
  (Z.card:ℝ)/(8*q)<((Z.filter fun y => Incident a y).card:ℝ)

noncomputable def scanSet (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V)) (q : ℝ) : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => if Expensive (state a b (scanSet a b q n)) (a n) (b n) q
      then insert n (scanSet a b q n) else scanSet a b q n

noncomputable def scanState (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : ℙ K (Dual K V) → Submodule K (Dual K V) := state a b (scanSet a b q n)

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def scanRecord (a : ℕ → ℙ K V) (b : ℕ → ℙ K (Dual K V))
    (q : ℝ) (n : ℕ) : Option (ℙ K V × ℙ K (Dual K V)) :=
  if Expensive (scanState a b q n) (a n) (b n) q then some (a n,b n) else none

end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ScanRecordPresent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

variable {β : Type*} [Nonempty β] {N : ℕ}
local instance finiteMarkingDecEq_rc9f2bd_1 (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
def extendTuple (f : Fin N → β) (n : ℕ) : β :=
  if h:n<N then f ⟨n,h⟩ else Classical.choice ‹Nonempty β›

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]

abbrev FlagPair (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  ℙ K V × ℙ K (Dual K V)

def tupleFirst (f : Fin N → FlagPair K V) (n : ℕ) := (extendTuple f n).1
def tupleSecond (f : Fin N → FlagPair K V) (n : ℕ) := (extendTuple f n).2

def TupleConsistent (f : Fin N → FlagPair K V) : Prop :=
  ∀ i j,i<j → Incident (f i).1 (f j).2 → Incident (f j).1 (f i).2

def TupleIncident (f : Fin N → FlagPair K V) : Prop := ∀ i,Incident (f i).1 (f i).2

def finiteRecord (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :=
  scanRecord (tupleFirst f) (tupleSecond f) q i.val

def expensiveSet (f : Fin N → FlagPair K V) (q : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i => (finiteRecord f q i).isSome

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
local instance twoScanDecEq (N : ℕ) : DecidableEq (Fin N) := Classical.decEq _
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def swapFlag : FlagPair K V ≃ FlagPair K (Dual K V) :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) bidualPoint)

@[simp] lemma swapFlag_apply (f : FlagPair K V) : swapFlag f=(f.2,bidualPoint f.1) := rfl

def reverseTuple (f : Fin N → FlagPair K V) (i : Fin N) := swapFlag (f i.rev)

variable [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))]

def reverseExpensive (f : Fin N → FlagPair K V) (q : ℝ) : Finset (Fin N) :=
  (expensiveSet (reverseTuple f) q).image Fin.rev

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Nonempty (ℙ K V)] in
@[simp] lemma mem_reverseExpensive (f : Fin N → FlagPair K V) (q : ℝ) (i : Fin N) :
    i∈reverseExpensive f q ↔ i.rev∈expensiveSet (reverseTuple f) q := by
  simp only [reverseExpensive,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    simpa using hj
  · intro hi
    exact ⟨i.rev,hi,Fin.rev_rev i⟩

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkedActualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω κ α β I : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β] [Fintype I]

lemma fiber_pair_source (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (c : κ) (y : α)
    (hc : 0<first (pair p ctx x) c) (hy : 0<fiber (pair p ctx x) c y) :
    ∃z,0<p z ∧ ctx z=c ∧ x z=y := by
  have hp : 0<pair p ctx x (c,y) := by
    rw [mass_eq_first_mul_fiber]
    exact mul_pos hc hy
  obtain ⟨z,hz,he⟩:=map_positive p (fun z=>(ctx z,x z)) (c,y) hp
  exact ⟨z,hz,congrArg Prod.fst he,congrArg Prod.snd he⟩

lemma pair_fiber_domains (p : Law Ω) (ctx : Ω→κ) (x : Ω→I→β)
    (D : κ→I→Finset β) (hD : ∀z,0<p z→∀i,x z i∈D (ctx z) i)
    (c : κ) (hc : 0<first (pair p ctx x) c) :
    InDomains (fiber (pair p ctx x) c) (D c) := by
  intro y hy i
  obtain ⟨z,hz,he,rfl⟩:=fiber_pair_source p ctx x c y hc hy
  rw [←he]
  exact hD z hz i

lemma pair_map_tuple (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (f : α→β) :
    pair p ctx (fun z=>f (x z))=map (pair p ctx x) (fun z=>(z.1,f z.2)) := by
  rw [pair,pair,map_comp]
  rfl

lemma fiber_pair_map (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (f : α→β)
    (c : κ) (hc : 0 < map p ctx c) :
    fiber (pair p ctx (fun z=>f (x z))) c=map (fiber (pair p ctx x) c) f := by
  have he : pair p ctx (fun z=>f (x z))=
      adaptiveLaw (map p ctx) (fun c=>map (fiber (pair p ctx x) c) f) := by
    rw [pair_map_tuple,←first_pair p ctx x]
    apply Law.ext_mean
    intro g
    rw [mean_map,mean_adaptive]
    simp_rw [mean_map]
    have hh:=congrArg (fun p=>mean p (fun z=>g (z.1,f z.2))) (adaptive_reconstruct (pair p ctx x))
    rw [mean_adaptive] at hh
    exact hh.symm
  rw [he]
  exact fiber_adaptive _ _ _ hc

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_RectangleTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.CoreGeometry
open Module ProjectiveIncidence Marking
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma bidual_rep_mem (x : ℙ K V) (W : Submodule K (Dual K (Dual K V))) :
    (bidualPoint x).rep∈W ↔ (Dual.eval K V x.rep)∈W := by
  change (bidualPoint x).rep∈W ↔ x.rep∈W.comap (Dual.eval K V)
  rw [rep_mem_iff,rep_mem_iff]
  induction x using Projectivization.ind with | h v hv =>
  change (Projectivization.map (Module.evalEquiv K V).toLinearMap
    (Module.evalEquiv K V).injective (Projectivization.mk K v hv)).submodule≤W ↔ _
  rw [Projectivization.map_mk,Projectivization.submodule_mk,
    Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem,
    Submodule.span_singleton_le_iff_mem]
  rfl

lemma inRectangle_swap (W : Submodule K (Dual K (Dual K V))) (f : FlagPair K V) :
    InRectangle W (swapFlag f).1.rep (swapFlag f).2.rep ↔
      InRectangle W.dualCoannihilator f.1.rep f.2.rep := by
  simp only [InRectangle,swapFlag_apply]
  rw [bidual_rep_mem]
  have he : (Dual.eval K V f.1.rep)∈W ↔ f.1.rep∈W.dualCoannihilator.dualCoannihilator := by
    conv_lhs => rw [←Subspace.dualCoannihilator_dualAnnihilator_eq (W:=W)]
    rfl
  rw [he,and_comm]

omit [FiniteDimensional K V] in
lemma occupancy_reindex {I J : Type} [Fintype I] [Fintype J]
    (x : I→FlagPair K V) (e : J→I) (he : Function.Injective e) (M : ℝ)
    (h : ∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∀W : Submodule K (Dual K V),
      (∑j,if InRectangle W (x (e j)).1.rep (x (e j)).2.rep then (1:ℝ) else 0)≤M := by
  intro W
  apply le_trans _ (h W)
  calc
    _ = ∑i∈Finset.univ.image e,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0 := by
      rw [Finset.sum_image (by intro a ha b hb hab;exact he hab)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro i hi hni
      split <;> norm_num)

lemma occupancy_reverse {n : ℕ} (x : Fin n→FlagPair K V) (M : ℝ)
    (h : ∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∀W : Submodule K (Dual K (Dual K V)),
      (∑i,if InRectangle W (reverseTuple x i).1.rep (reverseTuple x i).2.rep then (1:ℝ) else 0)≤M := by
  intro W
  simp only [reverseTuple,inRectangle_swap]
  exact occupancy_reindex x Fin.rev Fin.rev_injective M h W.dualCoannihilator
end
end SharpRamseyFive.CoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OriginalHistoryPrivate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A T β κ Ω Θ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Fintype Ω] [Fintype Θ] [Nonempty A]
local instance historyPrivateIDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GoodPairScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
lemma pair_entropy_swap (p : Law X) (f : X→Y) (g : X→Z) :
    entropy (pair p f g)=entropy (pair p g f) := by
  have h:=entropy_map_injective (pair p f g) Prod.swap (by
    intro x y he
    exact Prod.swap_injective he)
  simp only [pair,map_comp,Function.comp_def,Prod.swap_prod_mk] at h
  exact h.symm

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β] [Nonempty A]

local instance goodPairIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _

attribute [local irreducible] indexInformation indexCollision indexBad coordinateInformation

def OtherBlock : ((B×A)⊕T)→B→Prop :=
  Sum.elim (fun z b=>b≠z.1) (fun _ _=>True)

omit [Nonempty A] in
lemma index_information_pair (p : Law (((B×A)⊕T)→β)) (s : B→A)
    (i : ((B×A)⊕T)) (b : B) (hi : OtherBlock i b) :
    entropy (map p (fun x=>x i))+entropy (map p (fun x=>x (Sum.inl (b,s b))))-
      entropy (pair p (fun x=>x i) (fun x=>x (Sum.inl (b,s b))))≤ indexInformation p s i := by
  have he : (coordinateInformation p i (Sum.inl (b,s b)):ℝ)=
      entropy (map p (fun x=>x i))+entropy (map p (fun x=>x (Sum.inl (b,s b))))-
        entropy (pair p (fun x=>x i) (fun x=>x (Sum.inl (b,s b)))) := by
    unfold coordinateInformation
    change information (pair p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i))=_
    simp only [information,first_pair,second_pair]
    rw [pair_entropy_swap p (fun x=>x (Sum.inl (b,s b))) (fun x=>x i),add_comm]
  rw [←he]
  cases i with
  | inl z =>
    unfold indexInformation
    change (coordinateInformation p (Sum.inl z) (Sum.inl (b,s b)):ℝ)≤(blockInformation p s z.1 z.2:ℝ)
    apply NNReal.coe_le_coe.mpr
    exact Finset.le_sup (f:=fun c=>coordinateInformation p (Sum.inl z) (Sum.inl (c,s c)))
      (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)
  | inr t =>
    unfold indexInformation
    change (coordinateInformation p (Sum.inr t) (Sum.inl (b,s b)):ℝ)≤(middleInformation p s t:ℝ)
    apply NNReal.coe_le_coe.mpr
    exact Finset.le_sup (f:=fun c=>coordinateInformation p (Sum.inr t) (Sum.inl (c,s c)))
      (Finset.mem_univ b)

omit [Fintype A] [Fintype T] [Nonempty A] in
lemma index_collision_pair (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (hc : ∀ i j,0 ≤ c i j) (s : B→A) (i : ((B×A)⊕T)) (b : B) (hi : OtherBlock i b) :
    c i (Sum.inl (b,s b))≤ indexCollision c s i := by
  cases i with
  | inl z =>
    unfold indexCollision otherCollision
    exact Finset.single_le_sum (f:=fun j=>c (Sum.inl z) (Sum.inl (j,s j))) (fun j _=>hc _ _) (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩)
  | inr t =>
    unfold indexCollision middleCollision
    exact Finset.single_le_sum (f:=fun j=>c (Sum.inr t) (Sum.inl (j,s j))) (fun j _=>hc _ _) (Finset.mem_univ b)

omit [Nonempty A] in
theorem good_index_scores (J d e : ℝ) (p : Law (((B×A)⊕T)→β))
    (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ) (hc : ∀ i j,0 ≤ c i j)
    (s : B→A) (i : ((B×A)⊕T)) (hg : indexBad J d e p c s i=0) :
    J-entropy (map p (fun x=>x i))≤d ∧ ∀ b,OtherBlock i b→
      entropy (map p (fun x=>x i))+entropy (map p (fun x=>x (Sum.inl (b,s b))))-
        entropy (pair p (fun x=>x i) (fun x=>x (Sum.inl (b,s b))))+c i (Sum.inl (b,s b))≤e := by
  unfold indexBad at hg
  obtain ⟨hd,he⟩:=badIndexIndicator_eq_zero hg
  refine ⟨hd,fun b hi=>?_⟩
  exact (add_le_add (index_information_pair p s i b hi) (index_collision_pair c hc s i b hi)).trans he

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_LevelCellSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]
lemma levelCell_subset_support (p : Law α) (n : Level p) : levelCell p n⊆support p := by
  intro a ha
  exact (mem_support p a).mpr ((mem_levelCell p n a).mp ha).1
lemma levelCell_cap (p : Law α) (N : ℝ) (hN : ((support p).card:ℝ) ≤ N) (n : Level p) :
    ((levelCell p n).card:ℝ) ≤ N :=
  (show ((levelCell p n).card:ℝ) ≤ (support p).card by
    exact_mod_cast Finset.card_le_card (levelCell_subset_support p n)).trans hN
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PermissibleLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α : Type*} [Fintype α]

noncomputable def levelLoss (p : Law α) (N : ℝ) (n : Level p) : ℝ :=
  Real.log (N/(levelCell p n).card)
noncomputable def levelBadMass (p : Law α) (Good : Finset α) (n : Level p) : ℝ :=
  ∑a∈levelCell p n\Good,p a
noncomputable def permissibleLevels (p : Law α) (Good : Finset α) (N K : ℝ) : Finset (Level p) :=
  Finset.univ.filter (fun n=>0<(levelCell p n).card ∧ levelLoss p N n≤K ∧
    (levelCell p n).card≤2*(levelCell p n∩Good).card)

lemma levelBadMass_nonneg (p : Law α) (Good : Finset α) (n : Level p) :
    0≤levelBadMass p Good n := Finset.sum_nonneg (fun a _=>p.nonneg a)

lemma sum_levelBadMass (p : Law α) (Good : Finset α) :
    (∑n : Level p,levelBadMass p Good n)=eventMass p Goodᶜ := by
  have hs (n : Level p) : levelCell p n\Good=
      Finset.univ.filter (fun a=>0<p a ∧ atomLevel p a=n.val ∧ a∉Good) := by
    ext a
    simp [levelCell,and_assoc]
  simp only [levelBadMass,hs,Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold eventMass
  rw [show Goodᶜ=Finset.univ.filter (fun a=>a∉Good) by ext a;simp,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p a=0
  · simp [hp]
  · have hp0 : 0<p a := lt_of_le_of_ne (p.nonneg _) (Ne.symm hp)
    have he (n : Level p) : atomLevel p a=n.val ↔ levelIndex p a=n := by
      change (levelIndex p a).val=n.val ↔ _
      exact Subtype.ext_iff.symm
    by_cases ha : a∈Good <;> simp [hp0,he,ha]

lemma levelLoss_nonneg (p : Law α) (N : ℝ) (hN : 0<N)
    (hcap : ∀n : Level p,((levelCell p n).card:ℝ)≤N) (n : Level p) :
    0≤levelLoss p N n := by
  by_cases hz : (levelCell p n).card=0
  · simp [levelLoss,hz]
  · have hn : (0:ℝ)<(levelCell p n).card := by exact_mod_cast Nat.pos_of_ne_zero hz
    exact (Real.log_nonneg_iff (div_pos hN hn)).mpr
      ((le_div_iff₀ hn).mpr (by simpa using hcap n))

lemma thin_level_mass (p : Law α) (Good : Finset α) (n : Level p)
    (hthin : 2*(levelCell p n∩Good).card<(levelCell p n).card) :
    levelLaw p n≤2*Real.exp 1*levelBadMass p Good n := by
  have hsplit := Finset.card_sdiff_add_card_inter (levelCell p n) Good
  have hbad : 0<(levelCell p n\Good).card := by omega
  have hbn : (0:ℝ)<(levelCell p n\Good).card := by exact_mod_cast hbad
  have hc : ((levelCell p n).card:ℝ)≤2*(levelCell p n\Good).card := by exact_mod_cast (show (levelCell p n).card≤2*(levelCell p n\Good).card by omega)
  have hs := Finset.sum_le_sum (s:=levelCell p n\Good) (fun a ha=>
    level_mass_bound p n (Finset.mem_sdiff.mp ha).1)
  have he : (∑a∈levelCell p n\Good,(levelCell p n).card*Real.exp 1*p a)=
      (levelCell p n).card*Real.exp 1*levelBadMass p Good n := by rw [levelBadMass,Finset.mul_sum]
  rw [he] at hs
  simp only [Finset.sum_const,Finset.card_sdiff, nsmul_eq_mul] at hs
  have hu := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (Real.exp_pos 1).le (levelBadMass_nonneg p Good n))
  have hs' : ((levelCell p n\Good).card:ℝ)*levelLaw p n≤
      (levelCell p n).card*Real.exp 1*levelBadMass p Good n := by simpa [Finset.card_sdiff] using hs
  apply (mul_le_mul_iff_right₀ hbn).mp
  nlinarith

theorem permissible_mass (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0<N) (hK : 0<K) (hcap : ∀n : Level p,((levelCell p n).card:ℝ)≤N) :
    1-(∑n : Level p,levelLaw p n*levelLoss p N n)/K-
      2*Real.exp 1*eventMass p Goodᶜ ≤
      eventMass (levelLaw p) (permissibleLevels p Good N K) := by
  have hpoint (n : Level p) :
      levelLaw p n≤(if n∈permissibleLevels p Good N K then levelLaw p n else 0)+
        levelLaw p n*levelLoss p N n/K+2*Real.exp 1*levelBadMass p Good n := by
    have hm := (levelLaw p).nonneg n
    have hl := levelLoss_nonneg p N hN hcap n
    have hb := levelBadMass_nonneg p Good n
    by_cases hn : n∈permissibleLevels p Good N K
    · rw [ite_eq_left hn]
      have h₁ : 0≤levelLaw p n*levelLoss p N n/K := div_nonneg (mul_nonneg hm hl) hK.le
      have h₂ : 0≤2*Real.exp 1*levelBadMass p Good n := by positivity
      linarith
    · rw [ite_eq_right hn,zero_add]
      simp only [permissibleLevels,Finset.mem_filter,Finset.mem_univ,true_and,not_and] at hn
      by_cases hz : (levelCell p n).card=0
      · have he : levelLaw p n=0 := by rw [level_mass];simp [Finset.card_eq_zero.mp hz]
        rw [he];positivity
      · have hn0 := Nat.pos_of_ne_zero hz
        by_cases hk : levelLoss p N n≤K
        · have hthin : 2*(levelCell p n∩Good).card<(levelCell p n).card := by
            exact Nat.lt_of_not_ge (hn hn0 hk)
          have hh := thin_level_mass p Good n hthin
          have : 0≤levelLaw p n*levelLoss p N n/K := div_nonneg (mul_nonneg hm hl) hK.le
          linarith
        · have hk' : K≤levelLoss p N n := (lt_of_not_ge hk).le
          have hlarge : levelLaw p n≤levelLaw p n*levelLoss p N n/K := by
            apply (le_div_iff₀ hK).mpr
            exact mul_le_mul_of_nonneg_left hk' hm
          have : 0≤2*Real.exp 1*levelBadMass p Good n := by positivity
          linarith
  have hh := Finset.sum_le_sum (fun n (_ : n∈Finset.univ)=>hpoint n)
  rw [(levelLaw p).sum_one,Finset.sum_add_distrib,Finset.sum_add_distrib,
    Finset.sum_ite_mem,Finset.univ_inter,←Finset.sum_div,←Finset.mul_sum,
    sum_levelBadMass] at hh
  change 1≤eventMass (levelLaw p) (permissibleLevels p Good N K)+_+_ at hh
  linarith

end

open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

lemma positive_map_exists (p : Law α) (f : α→β) {b : β} (hb : 0 < map p f b) :
    ∃a,0 < p a ∧ f a=b := by
  have hnon : ∀a∈Finset.univ,(0:ℝ) ≤ if f a=b then p a else 0 := by
    intro a _;split
    · exact p.nonneg a
    · exact le_rfl
  obtain ⟨a,_,ha⟩ := (Finset.sum_pos_iff_of_nonneg hnon).mp hb
  split_ifs at ha with he
  · exact ⟨a,ha,he⟩
  · linarith

lemma permissible_support_size (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0 < N) (hcap : ∀n : Level p,((levelCell p n).card:ℝ) ≤ N)
    {n : Level p} (hn : n∈permissibleLevels p Good N K) :
    N*Real.exp (-K)/2 ≤ ((levelCell p n∩Good).card:ℝ) ∧
      ((levelCell p n∩Good).card:ℝ) ≤ N := by
  obtain ⟨hn0,hl,hh⟩ := (Finset.mem_filter.mp hn).2
  have hc : (0:ℝ) < (levelCell p n).card := by exact_mod_cast hn0
  have he := Real.exp_le_exp.mpr hl
  rw [levelLoss,Real.exp_log (div_pos hN hc)] at he
  have hc₁ : N*Real.exp (-K) ≤ ((levelCell p n).card:ℝ) := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos K)).mpr
    have := (div_le_iff₀ hc).mp he
    nlinarith
  have hc₂ : ((levelCell p n).card:ℝ) ≤ 2*(levelCell p n∩Good).card := by exact_mod_cast hh
  constructor
  · linarith
  · exact (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_left) :
      ((levelCell p n∩Good).card:ℝ) ≤ (levelCell p n).card).trans (hcap n)

noncomputable def goodSupportLaw (p : Law α) (Good : Finset α) (N K : ℝ)
    (hE : (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K)) : Law (Finset α) :=
  map (conditionOn (levelLaw p) (permissibleLevels p Good N K) (by linarith))
    (fun n=>levelCell p n∩Good)

theorem goodSupportLaw_bounds (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0 < N) (hcap : ∀n : Level p,((levelCell p n).card:ℝ) ≤ N)
    (hE : (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K))
    (S : Finset α) (hS : 0 < goodSupportLaw p Good N K hE S) :
    S⊆Good ∧ N*Real.exp (-K)/2 ≤ (S.card:ℝ) ∧ (S.card:ℝ) ≤ N := by
  obtain ⟨n,hn,he⟩ := positive_map_exists _ _ hS
  have hm : n∈permissibleLevels p Good N K := by
    by_contra hh
    rw [conditionOn_apply,ite_eq_right hh] at hn
    exact lt_irrefl 0 hn
  subst S
  exact ⟨Finset.inter_subset_right,permissible_support_size p Good N K hN hcap hm⟩

theorem goodSupportLaw_domination (p : Law α) (Good : Finset α) (N K : ℝ)
    (hE : (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K)) (a : α) :
    (∑S,goodSupportLaw p Good N K hE S*(if a∈S then 1/(S.card:ℝ) else 0)) ≤
      4*Real.exp 1*p a := by
  unfold goodSupportLaw
  rw [sum_map]
  exact good_level_domination p Good _ hE
    (fun n hn=>(Finset.mem_filter.mp hn).2.2.2) a

lemma permissible_half_mass (p : Law α) (Good : Finset α) (N K : ℝ)
    (hN : 0 < N) (hK : 0 < K) (hcap : ∀n : Level p,((levelCell p n).card:ℝ) ≤ N)
    (hsmall : (∑n : Level p,levelLaw p n*levelLoss p N n)/K+
      2*Real.exp 1*eventMass p Goodᶜ ≤ (1:ℝ)/2) :
    (1:ℝ)/2 ≤ eventMass (levelLaw p) (permissibleLevels p Good N K) := by
  have := permissible_mass p Good N K hN hK hcap
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MapFst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped BigOperators Classical
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma map_fst (p : Law (α×β)) : map p Prod.fst=first p := by
  apply Law.ext
  funext a
  simp [map,first,Fintype.sum_prod_type,Finset.sum_comm]

lemma map_snd (p : Law (α×β)) : map p Prod.snd=second p := by
  apply Law.ext
  funext b
  simp [map,second,Fintype.sum_prod_type]

lemma pair_self_apply (p : Law α) (f : α→β) (b : β) (a : α) :
    pair p f id (b,a)=if f a=b then p a else 0 := by
  simp only [pair,map]
  rw [Finset.sum_eq_single a]
  · simp [Prod.mk.injEq]
  · intro c hc hca
    have hne : (f c,id c)≠(b,a) := fun h=>hca (congrArg Prod.snd h)
    simp [hca]
  · simp

lemma partition_first (p : Law α) (f : α→β) : first (pair p f id)=map p f :=
  first_pair p f id

lemma partition_entropy (p : Law α) (f : α→β) :
    entropy p=entropy (map p f)+∑b,map p f b*entropy (fiber (pair p f id) b) := by
  have he : entropy (pair p f id)=entropy p :=
    entropy_map_injective p _ (fun _ _ h=>congrArg Prod.snd h)
  rw [←he,entropy_chain,partition_first]

lemma partition_support_subset (p : Law α) (f : α→β) (b : β)
    (hb : 0 < map p f b) :
    support (fiber (pair p f id) b)⊆(support p).filter (fun a=>f a=b) := by
  intro a ha
  have hfa := (mem_support _ _).mp ha
  have hfst : 0 < first (pair p f id) b := by simpa only [partition_first] using hb
  have hp : 0 < pair p f id (b,a) := by
    rw [mass_eq_first_mul_fiber]
    exact mul_pos hfst hfa
  rw [pair_self_apply] at hp
  split_ifs at hp with hh
  · exact Finset.mem_filter.mpr ⟨(mem_support _ _).mpr hp,hh⟩
  · exact (lt_irrefl 0 hp).elim

theorem entropy_partition_bound (p : Law α) (f : α→β) (C : β→ℝ)
    (hC : ∀b,0 < map p f b →
      Real.log (((support p).filter (fun a=>f a=b)).card:ℝ)≤C b) :
    entropy p≤entropy (map p f)+∑b,map p f b*C b := by
  rw [partition_entropy p f]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro b _
  by_cases hz : map p f b=0
  · simp [hz]
  · have hp : 0 < map p f b := lt_of_le_of_ne ((map p f).nonneg _) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    have hh : ((support (fiber (pair p f id) b)).card:ℝ)≤
        ((support p).filter (fun a=>f a=b)).card := by
      exact_mod_cast Finset.card_le_card (partition_support_subset p f b hp)
    exact (entropy_support_cap _ _ hh).trans (hC b hp)

end

open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def endpointLevels (p : Law (α×β)) (z : α×β) :
    Level (first p)×Level (second p) := (levelIndex (first p) z.1,levelIndex (second p) z.2)
noncomputable def levelPairLaw (p : Law (α×β)) := map p (endpointLevels p)

lemma first_levelPairLaw (p : Law (α×β)) : first (levelPairLaw p)=levelLaw (first p) := by
  calc
    _ = map (levelPairLaw p) Prod.fst := (map_fst _).symm
    _ = map p (fun z=>levelIndex (first p) z.1) := map_comp p _ _
    _ = map (map p Prod.fst) (levelIndex (first p)) := (map_comp p Prod.fst (levelIndex (first p))).symm
    _ = _ := congrArg (fun μ : Law α=>map μ (levelIndex (first p))) (map_fst p)

lemma second_levelPairLaw (p : Law (α×β)) : second (levelPairLaw p)=levelLaw (second p) := by
  calc
    _ = map (levelPairLaw p) Prod.snd := (map_snd _).symm
    _ = map p (fun z=>levelIndex (second p) z.2) := map_comp p _ _
    _ = map (map p Prod.snd) (levelIndex (second p)) := (map_comp p Prod.snd (levelIndex (second p))).symm
    _ = _ := congrArg (fun μ : Law β=>map μ (levelIndex (second p))) (map_snd p)

lemma sum_levelPair_fst (p : Law (α×β)) (w : Level (first p)→ℝ) :
    (∑n,levelPairLaw p n*w n.1)=∑n,levelLaw (first p) n*w n := by
  simpa only [map_fst,first_levelPairLaw] using (sum_map (levelPairLaw p) Prod.fst w).symm

lemma sum_levelPair_snd (p : Law (α×β)) (w : Level (second p)→ℝ) :
    (∑n,levelPairLaw p n*w n.2)=∑n,levelLaw (second p) n*w n := by
  simpa only [map_snd,second_levelPairLaw] using (sum_map (levelPairLaw p) Prod.snd w).symm

lemma levelPair_entropy (p : Law (α×β)) :
    entropy (levelPairLaw p) ≤ entropy (levelLaw (first p))+entropy (levelLaw (second p)) := by
  simpa only [first_levelPairLaw,second_levelPairLaw] using entropy_subadditive (levelPairLaw p)

lemma positive_marginals (p : Law (α×β)) {z : α×β} (hz : 0 < p z) :
    0 < first p z.1 ∧ 0 < second p z.2 := by
  constructor
  · exact lt_of_lt_of_le hz (Finset.single_le_sum (fun b _=>p.nonneg (z.1,b)) (Finset.mem_univ z.2))
  · exact lt_of_lt_of_le hz (Finset.single_le_sum (fun a _=>p.nonneg (a,z.2)) (Finset.mem_univ z.1))

lemma level_pair_support_subset (p : Law (α×β)) (R : α→β→Prop)
    (hR : ∀z,0 < p z→R z.1 z.2) (n : Level (first p)×Level (second p)) :
    (support p).filter (fun z=>endpointLevels p z=n) ⊆
      ((levelCell (first p) n.1)×ˢ(levelCell (second p) n.2)).filter (fun z=>R z.1 z.2) := by
  intro z hz
  obtain ⟨hs,he⟩ := Finset.mem_filter.mp hz
  have hp := (mem_support p z).mp hs
  have hm := positive_marginals p hp
  have h₁ : atomLevel (first p) z.1=n.1.val := congrArg (fun x=>x.1.val) he
  have h₂ : atomLevel (second p) z.2=n.2.val := congrArg (fun x=>x.2.val) he
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨(mem_levelCell _ _ _).mpr ⟨hm.1,h₁⟩,(mem_levelCell _ _ _).mpr ⟨hm.2,h₂⟩⟩,hR z hp⟩

lemma positive_level_pair_support (p : Law (α×β)) (n : Level (first p)×Level (second p))
    (hn : 0 < levelPairLaw p n) :
    ((support p).filter (fun z=>endpointLevels p z=n)).Nonempty := by
  by_contra he
  have hz : levelPairLaw p n=0 := by
    unfold levelPairLaw map
    apply Finset.sum_eq_zero
    intro z _
    by_cases hh : endpointLevels p z=n
    · rw [ite_eq_left hh]
      have hnot : z∉support p := by
        intro hm
        exact he ⟨z,Finset.mem_filter.mpr ⟨hm,hh⟩⟩
      exact outside_support p hnot
    · simp [hh]
  linarith

theorem expected_total_level_loss (p : Law (α×β)) (NA NB D : ℝ)
    (hrect : ∀n : Level (first p)×Level (second p),0 < levelPairLaw p n→
      Real.log (((support p).filter (fun z=>endpointLevels p z=n)).card:ℝ) ≤
        D-(levelLoss (first p) NA n.1+levelLoss (second p) NB n.2)/2) :
    (∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n) ≤
      2*(D-entropy p+entropy (levelLaw (first p))+entropy (levelLaw (second p))) := by
  have he := entropy_partition_bound p (endpointLevels p)
    (fun n=>D-(levelLoss (first p) NA n.1+levelLoss (second p) NB n.2)/2) (by
      intro n hn
      convert hrect n hn using 1
      all_goals try with_reducible_and_instances rfl
      congr 3
      ext point
      simp)
  change entropy p ≤ entropy (levelPairLaw p)+
    ∑n,levelPairLaw p n*(D-(levelLoss (first p) NA n.1+levelLoss (second p) NB n.2)/2) at he
  have hs : (∑n,levelPairLaw p n*(D-(levelLoss (first p) NA n.1+
      levelLoss (second p) NB n.2)/2)) = D-
      ((∑n,levelLaw (first p) n*levelLoss (first p) NA n)+
      (∑n,levelLaw (second p) n*levelLoss (second p) NB n))/2 := by
    simp only [mul_sub,←mul_div_assoc,mul_add,Finset.sum_sub_distrib,←Finset.sum_div,
      Finset.sum_add_distrib,←Finset.sum_mul,(levelPairLaw p).sum_one,one_mul,
      sum_levelPair_fst,sum_levelPair_snd]
  rw [hs] at he
  have hh := levelPair_entropy p
  linarith

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GoodRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def goodRepresentative (p : Law (α×β)) (A : Finset α) (B : Finset β)
    (h : 0<eventMass p (A×ˢB)) : Law (α×β) := conditionOn p (A×ˢB) h

end

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_OrderedReciprocalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {I β : Type} [Fintype I] [Fintype β] {n : ℕ}

def orderedLaw (p : Law (I→β)) (e : I≃Fin n) : Law (Fin n→β) :=
  map p (fun x i=>x (e.symm i))
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalLevelProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
lemma eventMass_complement (p : Law α) (E : Finset α) :
    eventMass p Eᶜ+eventMass p E=1 := by
  change (∑ a∈Eᶜ,p a)+(∑ a∈E,p a)=1
  rw [Finset.sum_compl_add_sum]
  exact p.sum_one
lemma entropy_swap (p : Law (α×β)) : entropy (swap p)=entropy p := by
  simp only [entropy,Fintype.sum_prod_type,swap_mass]
  rw [Finset.sum_comm]
lemma support_swap_card (p : Law (α×β)) : (support (swap p)).card=(support p).card := by
  simp only [support,Finset.card_filter, Fintype.sum_prod_type]
  change (∑ b : β,∑ a : α,if 0<p (a,b) then (1:ℕ) else 0)=
    ∑ a : α,∑ b : β,if 0<p (a,b) then (1:ℕ) else 0
  exact Finset.sum_comm
end
end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Repair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

lemma Law.exists_positive (p : Law α) : ∃ a,0<p a := by
  by_contra h
  push Not at h
  have hz : ∑ a,p a=0 := Finset.sum_eq_zero (fun a _=>le_antisymm (h a) (p.nonneg a))
  rw [p.sum_one] at hz
  norm_num at hz

def Law.repair (p : Law α) (a : α) : α :=
  if 0<p a then a else Classical.choose p.exists_positive

lemma Law.repair_positive (p : Law α) (a : α) : 0<p (p.repair a) := by
  unfold Law.repair
  split_ifs with h
  · exact h
  · exact Classical.choose_spec p.exists_positive

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_WindowPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω κ α β I B A T : Type} [Fintype Ω] [Fintype κ] [Fintype α] [Fintype β]
  [Fintype I] [Fintype B] [Fintype A] [Fintype T] [Nonempty A]
local instance wpIDE_rc9f2bd_1 : DecidableEq ((B×A)⊕T) := Classical.decEq _
omit [Nonempty A] in
@[simp] lemma blockActive_univ : blockActive (T:=T) (fun _ : B=>(Finset.univ : Finset A))=Finset.univ := by
  ext i
  cases i <;> simp [blockActive]
lemma fixedOutside_univ (p : Law (I→β)) : FixedOutside p Finset.univ := by
  intro i hi
  exact False.elim (hi (Finset.mem_univ i))
lemma mean_fiber_entropy_injective (p : Law Ω) (ctx : Ω→κ) (x : Ω→α) (f : α→β)
    (hf : Function.Injective f) (F : ℝ→ℝ) :
    mean (first (pair p ctx (fun z=>f (x z)))) (fun c=>F (entropy (fiber (pair p ctx (fun z=>f (x z))) c)))=
    mean (first (pair p ctx x)) (fun c=>F (entropy (fiber (pair p ctx x) c))) := by
  simp only [first_pair]
  apply mean_congr_pos
  intro c hc
  rw [fiber_pair_map p ctx x f c hc,entropy_map_injective _ _ hf]
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_DomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

local instance dtPDE_rc9f2bd_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance dtDDE_rc9f2bd_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance dtDDDE_rc9f2bd_1 : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _
def swapDomain (D : Finset (FlagPair K V)) := D.map swapFlag.toEmbedding

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
@[simp] lemma mem_swapDomain_iff (D : Finset (FlagPair K V)) (z : FlagPair K V) :
    swapFlag z∈swapDomain D ↔ z∈D := by
  simp only [swapDomain,Finset.mem_map,Equiv.toEmbedding_apply,EmbeddingLike.apply_eq_iff_eq]
  simp

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_StreamGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}
structure Geometric (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible) (M : ℝ) : Prop where
  incident : ∀z,0<S.law z→TupleIncident (S.tuple z)
  consistent : ∀z,0<S.law z→TupleConsistent (S.tuple z)
  occupancy : ∀z,0<S.law z→∀W : Submodule K (Dual K V),
    (∑i,if InRectangle W (S.tuple z i).1.rep (S.tuple z i).2.rep then (1:ℝ) else 0)≤M

structure CodedStream (N n : ℕ) (admissible : (Fin N→α)→Prop) (density Λ J M : ℝ) where
  sample : Type
  [finiteSample : Fintype sample]
  stream : SelectedStream (Ω:=sample) (β:=FlagPair K V) N n admissible
  code : Type
  [finiteCode : Fintype code]
  description : ContextDescription (κ:=code) stream.law stream.tuple Λ J
  density_bound : stream.density≤density
  geometric : Geometric stream M
attribute [instance] CodedStream.finiteSample CodedStream.finiteCode
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {B A T β κ : Type} [Fintype B] [Fintype A] [Fintype T] [Fintype β]
  [Fintype κ] [Nonempty A]
local instance historySupportIndexDecEq : DecidableEq ((B×A)⊕T) := Classical.decEq _
omit [Nonempty A] in
lemma history_support (p : Law (((B×A)⊕T)→β)) (n : ℕ)
    (h : BlockHistory B A T β n) (x : ((B×A)⊕T)→β)
    (hx : 0<historyPosterior p h x) : 0<p x := by
  induction n generalizing p with
  | zero => exact hx
  | succ n ih =>
    exact fiber_reveal_support p (representativeSet h.1) h.2.1 x
      (ih _ h.2.2 hx)
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_HighEndpointCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

def highGoodFirst (p : Law (α×β)) (NA N U K : ℝ) : Finset α :=
  (goodFirstEndpoints p NA N K).filter fun a=>U*first p a≤Real.exp K

def highBadMass (s d C0 : ℝ) : ℝ :=
  Real.exp (-s)+50*(d+C0)/s+(d+Real.log 2+32)/s

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FiniteGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {S A : Type*}

def runSamples (step : S→A→S) : S→{n : ℕ}→(Fin n→A)→S
  | s,0,_=>s
  | s,_+1,x=>runSamples step (step s (x 0)) (fun i=>x i.succ)

def failedGrowth (step : S→A→S) (rank : S→ℕ) (d : ℕ) (s : S) (a : A) : Prop :=
  rank s<d ∧ rank (step s a) ≤ rank s

def growthFailures (step : S→A→S) (rank : S→ℕ) (d : ℕ) : S→{n : ℕ}→(Fin n→A)→ℕ
  | _,0,_=>0
  | s,_+1,x=>(if failedGrowth step rank d s (x 0) then 1 else 0)+
      growthFailures step rank d (step s (x 0)) (fun i=>x i.succ)

end

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReciprocalLossBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype β] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {Λ J Λ' J' : ℝ}
def ContextDescription.mono (C : ContextDescription (κ:=κ) p x Λ J)
    (hΛ : Λ≤Λ') (hJ : J≤J') : ContextDescription (κ:=κ) p x Λ' J' where
  context:=C.context
  domain:=C.domain
  entropy_bound:=C.entropy_bound.trans hΛ
  contains:=C.contains
  cap z hz i:=(C.cap z hz i).trans hJ
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DescriptionClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {L J : ℝ}
def ContextDescription.cleanDomain (C : ContextDescription (κ:=κ) p x L J) (c : κ) (i : Fin n) :=
  if 0 < map p C.context c then C.domain c i else ∅
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_GoodIndexThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
noncomputable section
lemma badIndexIndicator_mono {δ δ' g d e : ℝ} (hδ : δ≤δ') :
    badIndexIndicator δ g d e≤badIndexIndicator δ' g d e := by
  unfold badIndexIndicator
  split_ifs with h h' h'
  · exact le_rfl
  · exact False.elim (h' (h.imp (fun h=>lt_of_lt_of_le h hδ) id))
  · norm_num
  · exact le_rfl

variable {B A T β : Type} [Fintype B] [Fintype A] [Fintype T]
    [Fintype β]
local instance goodThresholdDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

lemma indexBad_cap_mono {J J' d e : ℝ} (hJ : J≤J')
    (p : Law (((B×A)⊕T)→β)) (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (s : B→A) (i : ((B×A)⊕T)) :
    indexBad J d e p c s i ≤ indexBad J' d e p c s i :=
  badIndexIndicator_mono (sub_le_sub_right hJ _)

lemma indexBad_of_larger_cap {J J' d e : ℝ} (hJ : J≤J')
    (p : Law (((B×A)⊕T)→β)) (c : ((B×A)⊕T)→((B×A)⊕T)→ℝ)
    (s : B→A) (i : ((B×A)⊕T)) (hi : indexBad J' d e p c s i=0) :
    indexBad J d e p c s i=0 := by
  apply le_antisymm
  · exact (indexBad_cap_mono hJ p c s i).trans hi.le
  · exact badIndexIndicator_nonneg _ _ _ _
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_PreparedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {κ B A T β : Type} [Fintype κ] [Fintype B] [Fintype A] [Fintype T]
  [Fintype β] [Nonempty A]
local instance chosenRoundDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Rectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators
variable {α : Type*} [Fintype α]

noncomputable def uniform (h : 0<Fintype.card α) : Law α where
  mass _ := 1/(Fintype.card α:ℝ)
  nonneg _ := by positivity
  sum_one := by
    have hh : (Fintype.card α:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt h
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_one_div_cancel hh

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-graph Ramsey number and its asymptotic bounds. -/

namespace SharpLogRamsey

def RamseyProperty (s t N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N),
    (∃ A : Finset (Fin N), G.IsNClique s A) ∨
    (∃ B : Finset (Fin N), Gᶜ.IsNClique t B)

noncomputable def ramsey (s t : ℕ) : ℕ := sInf {N | RamseyProperty s t N}

end SharpLogRamsey

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Bounds_Upper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def independentSets : Finset (Finset V) :=
  univ.filter (fun S => G.IsIndepSet (S : Set V))

@[simp] theorem mem_independentSets (S : Finset V) :
    S ∈ independentSets G ↔ G.IsIndepSet (S : Set V) := by
  simp [independentSets]

noncomputable def closed (x : V) : Finset V := insert x (G.neighborFinset x)
noncomputable def outside (x : V) (S : Finset V) : Finset V := S \ closed G x
noncomputable def available (x : V) (J : Finset V) : Finset V :=
  (G.neighborFinset x).filter (fun u => ∀ v ∈ J, ¬G.Adj u v)
noncomputable def fiber (x : V) (J : Finset V) : Finset (Finset V) :=
  (independentSets G).filter (fun S => outside G x S = J)

def Admissible (x : V) (J : Finset V) : Prop :=
  G.IsIndepSet (J : Set V) ∧ Disjoint J (closed G x)

@[simp] theorem mem_closed (x u : V) : u ∈ closed G x ↔ u = x ∨ G.Adj x u := by
  simp [closed]
@[simp] theorem mem_outside (x u : V) (S : Finset V) :
    u ∈ outside G x S ↔ u ∈ S ∧ u ≠ x ∧ ¬G.Adj x u := by
  simp [outside]
@[simp] theorem mem_available (x u : V) (J : Finset V) :
    u ∈ available G x J ↔ G.Adj x u ∧ ∀ v ∈ J, ¬G.Adj u v := by
  simp [available]

@[simp] theorem center_not_available (x : V) (J : Finset V) : x ∉ available G x J := by
  simp

end SharpLogRamsey.TriangleFree
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Bounds_SumFiberCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The off-diagonal Ramsey upper bound. -/

section
open scoped BigOperators Classical
open Finset
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.TriangleFree
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def Z (x : V) (S : Finset V) : ℕ :=
  (available G x (outside G x S)).card

end SharpLogRamsey.TriangleFree

open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.Sampling
variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V)

noncomputable def internalDegree (S : Finset V) (x : V) : ℕ :=
  (S.filter (G.Adj x)).card

noncomputable def degreeMass (S : Finset V) : ℕ := ∑ x ∈ S, internalDegree G S x

end SharpLogRamsey.Sampling

open scoped BigOperators
end

end OAI
end


