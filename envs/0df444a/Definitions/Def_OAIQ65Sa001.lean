-- Prove2me | Definitions.Def_OAIQ65Sa001
-- name    : OAIQ65Sa001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:24:08.106073+00:00
-- url     : https://prove2.me/theorems/62a7320d-2795-4a32-9370-cced435498ef
-- title:
--   Definitions bundle OAIQ65Sa001 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 639 declarations of OpenAI's Lean: 294 definitions, 5 inductive types or structures, 49 instances and 291 theorems. The definitions and types are `OAI.BarHomology.D`, `OAI.BoundedHomologyEdge.Hmap`, `OAI.BoundedHomologyEdge.lift₂`, `OAI.BoundedHomologyEdge.lift₃`, `OAI.BoundedHomologyEdge.lift₄`, `OAI.CanonicalShapiro.barComparison`, `OAI.CanonicalShapiro.barLift`, `OAI.CanonicalShapiro.barMap`, `OAI.CanonicalShapiro.chainsEquivalence`, `OAI.CanonicalShapiro.indUnit`, `OAI.CanonicalShapiro.resTensorIso`, `OAI.CanonicalShapiro.tensorBarMap`, `OAI.ChainComplex.positiveDesc`, `OAI.ChainComplex.positiveIsCokernel`, `OAI.ChainComplex.positiveπ`, `OAI.ChainComplex.zeroDesc`, `OAI.ChainComplex.zeroπ`, `OAI.CoefficientNerve.Coeff`, `OAI.CoefficientNerve.Obj`, `OAI.CoefficientNerve.Simplex`, `OAI.CoefficientNerve.augmentation`, `OAI.CoefficientNerve.augmented`, `OAI.CoefficientNerve.chainSimplicial`, `OAI.CoefficientNerve.chainSimplicialHomology`, `OAI.CoefficientNerve.complex`, `OAI.CoefficientNerve.contraction`, `OAI.CoefficientNerve.degree`, `OAI.CoefficientNerve.degreeIso`, `OAI.CoefficientNerve.desc`, `OAI.CoefficientNerve.double`, `OAI.CoefficientNerve.edge`, `OAI.CoefficientNerve.extra`, `OAI.CoefficientNerve.functor`, `OAI.CoefficientNerve.levelMap`, `OAI.CoefficientNerve.map`, `OAI.CoefficientNerve.mapNat`, `OAI.CoefficientNerve.overCocone`, `OAI.CoefficientNerve.overDiagram`, `OAI.CoefficientNerve.overIsColimit`, `OAI.CoefficientNerve.overLift` and 259 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Arithmetic_LatticeRange`, `SimpleAmenable_Arithmetic_PolygonArithmetic`, `SimpleAmenable_CentralCovers_BooleanCoordinateGeneration`, `SimpleAmenable_CentralCovers_BoundedRelationCover`, `SimpleAmenable_CentralCovers_ConditionalFamilyLaws`, `SimpleAmenable_CentralCovers_FinitelyManyTranslationRelations`, `SimpleAmenable_CentralCovers_PerfectCalculus`, `SimpleAmenable_CentralCovers_PerfectGeneratingFamilies`, `SimpleAmenable_Configurations_CofinalPowers`, `SimpleAmenable_Configurations_PointwisePolygonTables`, `SimpleAmenable_Configurations_StageBinary`, `SimpleAmenable_Configurations_TrackPoint`, `SimpleAmenable_Configurations_TrackTranslationChart`, `SimpleAmenable_Configurations_TransitiveInduction`, `SimpleAmenable_Homology_BoundedHomologyEdge`, `SimpleAmenable_Homology_ChainPositiveCokernel`, `SimpleAmenable_Homology_Coefficient`, `SimpleAmenable_Homology_CoefficientContraction`, `SimpleAmenable_Homology_DoubleCoordinates`, `SimpleAmenable_Homology_ExactShapeHomology`, `SimpleAmenable_Homology_FilteredHomology`, `SimpleAmenable_Homology_GroupoidComponentHomology`, `SimpleAmenable_Homology_HomologyAdditive`, `SimpleAmenable_Homology_MarkedLowHomology`, `SimpleAmenable_Homology_MarkedSigns`, `SimpleAmenable_Homology_PiBinary`, `SimpleAmenable_Homology_PiH1Coproduct`, `SimpleAmenable_Homology_PiSSet`, `SimpleAmenable_Homology_PowerEquivalence`, `SimpleAmenable_Homology_QuotientRegular`, `SimpleAmenable_Homology_ReducedTensorTwo`, `SimpleAmenable_Homology_RegularAugmentation`, `SimpleAmenable_Homology_RegularBlock`, `SimpleAmenable_Homology_RegularCoefficientDouble`, `SimpleAmenable_Homology_RegularLiftFaces`, `SimpleAmenable_Homology_RegularTotalDifferential`, `SimpleAmenable_Homology_TransitiveCanonical`, `SimpleAmenable_Homology_TranslationCoefficientAction`, `SimpleAmenable_PolygonGeometry_AlignedGroups`, `SimpleAmenable_PolygonGeometry_CanonicalSectors`, `SimpleAmenable_PolygonGeometry_InitialPointwiseTable`, `SimpleAmenable_PolygonGeometry_PolygonAction`, `SimpleAmenable_PolygonGeometry_Sectors`, `SimpleAmenable_PolygonGeometry_Supported`, `SimpleAmenable_PolygonGeometry_TranslationLifts`, `SimpleAmenable_PolygonGeometry_TupleChartDomain`, `SimpleAmenable_Simplicial_BarComponents`, `SimpleAmenable_Simplicial_BarContractible`, `SimpleAmenable_Simplicial_BarRowFiniteness`, `SimpleAmenable_Simplicial_CanonicalShapiro`, `SimpleAmenable_Simplicial_CoefficientFiltered`, `SimpleAmenable_Simplicial_CoefficientNaturality`, `SimpleAmenable_Simplicial_CoefficientNerve`, `SimpleAmenable_Simplicial_ConjugationNatural`, `SimpleAmenable_Simplicial_FinitePowerGeneral`, `SimpleAmenable_Simplicial_FirstBarDegreeTwoFinite`, `SimpleAmenable_Simplicial_GroupNerveCoordinates`, `SimpleAmenable_Simplicial_InducedMonoidal`, `SimpleAmenable_Simplicial_IntervalBinary`, `SimpleAmenable_Simplicial_IntervalEdge`, `SimpleAmenable_Simplicial_IntervalEquivalence`, `SimpleAmenable_Simplicial_LowerBarComposition`, `SimpleAmenable_Simplicial_MonoidFaceLabels`, `SimpleAmenable_Simplicial_MonoidNerveCoordinates`, `SimpleAmenable_Simplicial_MonoidalCongruence`, `SimpleAmenable_Simplicial_NerveProduct`, `SimpleAmenable_Simplicial_PiFiber`, `SimpleAmenable_Simplicial_ResolutionAugmentation`, `SimpleAmenable_Simplicial_RestrictedFunctorial`, `SimpleAmenable_Simplicial_RestrictedMonoidal`, `SimpleAmenable_Simplicial_RestrictedMonoidalTranspose`, `SimpleAmenable_Simplicial_RestrictedNerve`, `SimpleAmenable_Simplicial_SimplicialH0`, `SimpleAmenable_Simplicial_StageRefinementMonoidal`, `SimpleAmenable_Simplicial_StageTripleHomology`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa004`, `OAIQ65Sa005`, `OAIQ65Sa006`, `OAIQ65Sa013` and `OAIQ65Sa014`; the statements `OAI.SimpleAmenable.polygon_full_low_homology_finite` and `OAI.SimpleAmenable.polygon_infinite_simple_folner`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ065_SA.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_PolygonArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open scoped symmDiff

namespace SimpleAmenable

section PolygonArithmetic

abbrev CutRing := QuadraticAlgebra ℤ 1 1

noncomputable def ordinary : CutRing →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.goldenRatio, by
    simp only [one_smul, ← sq]
    linarith [Real.goldenRatio_sq]⟩

noncomputable def conjugate : CutRing →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.goldenConj, by
    simp only [one_smul, ← sq]
    linarith [Real.goldenConj_sq]⟩

theorem ordinary_apply (z : CutRing) :
    ordinary z = (z.re : ℝ) + (z.im : ℝ) * Real.goldenRatio := by
  simp [ordinary, QuadraticAlgebra.lift]

theorem conjugate_apply (z : CutRing) :
    conjugate z = (z.re : ℝ) + (z.im : ℝ) * Real.goldenConj := by
  simp [conjugate, QuadraticAlgebra.lift]

def endpointLabel (z : CutRing) : ℤ := z.im

noncomputable abbrev cutTau : CutRing := QuadraticAlgebra.omega

@[simp] theorem ordinary_cutTau : ordinary cutTau = Real.goldenRatio := by simp [cutTau, ordinary_apply]
@[simp] theorem conjugate_cutTau : conjugate cutTau = Real.goldenConj := by simp [cutTau, conjugate_apply]

noncomputable def cutForm (a : ℕ) (j : Fin 4) (p : ℝ × ℝ) : ℝ :=
  ![p.1, p.2, p.2 - Real.goldenRatio ^ a * p.1,
    p.1 - Real.goldenRatio ^ a * p.2] j

noncomputable def integralCutForm (a : ℕ) (j : Fin 4) (p : CutRing × CutRing) : CutRing :=
  ![p.1, p.2, p.2 - cutTau ^ a * p.1, p.1 - cutTau ^ a * p.2] j

theorem cutForm_ordinary (a : ℕ) (j : Fin 4) (p : CutRing × CutRing) :
    cutForm a j (ordinary p.1, ordinary p.2) = ordinary (integralCutForm a j p) := by
  fin_cases j <;> simp [cutForm, integralCutForm]

theorem cutForm_add (a : ℕ) (j : Fin 4) (p q : ℝ × ℝ) :
    cutForm a j (p + q) = cutForm a j p + cutForm a j q := by
  fin_cases j <;> simp [cutForm] <;> ring

def AvoidsCuts (a : ℕ) (p : ℝ × ℝ) : Prop :=
  ∀ (j : Fin 4) (z : CutRing), cutForm a j p ≠ ordinary z

theorem avoidsCuts_translate {a : ℕ} {p : ℝ × ℝ} (hp : AvoidsCuts a p)
    (u : CutRing × CutRing) : AvoidsCuts a (p + (ordinary u.1, ordinary u.2)) := by
  intro j z hz
  apply hp j (z - integralCutForm a j u)
  rw [cutForm_add, cutForm_ordinary] at hz
  simpa only [map_sub] using eq_sub_of_add_eq hz

def GenericSquare (a : ℕ) :=
  {p : ℝ × ℝ // p.1 ∈ Set.Ico 0 1 ∧ p.2 ∈ Set.Ico 0 1 ∧ AvoidsCuts a p}

def halfPlane (a : ℕ) (j : Fin 4) (z : CutRing) : Set (GenericSquare a) :=
  {p | cutForm a j p.val < ordinary z}

def polygonAlgebra (a : ℕ) : BooleanSubalgebra (Set (GenericSquare a)) :=
  BooleanSubalgebra.closure {U | ∃ j z, U = halfPlane a j z}

theorem polygon_induction {a : ℕ} {P : Set (GenericSquare a) → Prop}
    (hcut : ∀ j z, P (halfPlane a j z)) (hbot : P ∅)
    (hsup : ∀ U V, P U → P V → P (U ∪ V))
    (hcompl : ∀ U, P U → P Uᶜ) {U : Set (GenericSquare a)}
    (hU : U ∈ polygonAlgebra a) : P U := by
  induction hU using BooleanSubalgebra.closure_bot_sup_induction with
  | mem U h => obtain ⟨j, z, rfl⟩ := h; exact hcut j z
  | bot => exact hbot
  | sup U hU V hV ihU ihV => exact hsup U V ihU ihV
  | compl U hU ih => exact hcompl U ih

end PolygonArithmetic

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonAction

theorem fract_fract_add (x y : ℝ) : Int.fract (Int.fract x + y) = Int.fract (x + y) := by
  change Int.fract (x - (⌊x⌋ : ℝ) + y) = _
  rw [sub_add_eq_add_sub, Int.fract_sub_intCast]

noncomputable def translate (a : ℕ) (u : CutRing × CutRing) (p : GenericSquare a) :
    GenericSquare a := by
  let k : CutRing × CutRing :=
    ((⌊p.val.1 + ordinary u.1⌋ : ℤ), (⌊p.val.2 + ordinary u.2⌋ : ℤ))
  refine ⟨(Int.fract (p.val.1 + ordinary u.1), Int.fract (p.val.2 + ordinary u.2)),
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_⟩
  have h := avoidsCuts_translate p.property.2.2 (u - k)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [k, Int.fract, Prod.fst_sub, Prod.snd_sub, map_sub, map_intCast]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

@[simp] theorem translate_val (a : ℕ) (u : CutRing × CutRing) (p : GenericSquare a) :
    (translate a u p).val =
      (Int.fract (p.val.1 + ordinary u.1), Int.fract (p.val.2 + ordinary u.2)) := rfl

@[simp] theorem translate_zero (a : ℕ) (p : GenericSquare a) : translate a 0 p = p := by
  apply Subtype.ext
  simp only [translate_val, Prod.fst_zero, Prod.snd_zero, map_zero, add_zero]
  exact Prod.ext (Int.fract_eq_self.mpr p.property.1) (Int.fract_eq_self.mpr p.property.2.1)

theorem translate_add (a : ℕ) (u v : CutRing × CutRing) (p : GenericSquare a) :
    translate a (u + v) p = translate a u (translate a v p) := by
  apply Subtype.ext
  simp only [translate_val, Prod.fst_add, Prod.snd_add, map_add]
  rw [fract_fract_add, fract_fract_add]
  congr 1 <;> congr 1 <;> ring

noncomputable def translation (a : ℕ) (u : CutRing × CutRing) : Equiv.Perm (GenericSquare a) where
  toFun := translate a u
  invFun := translate a (-u)
  left_inv p := by rw [← translate_add, neg_add_cancel, translate_zero]
  right_inv p := by rw [← translate_add, add_neg_cancel, translate_zero]

@[simp] theorem translation_apply (a : ℕ) (u : CutRing × CutRing) (p : GenericSquare a) :
    translation a u p = translate a u p := rfl

@[simp] theorem translation_mul (a : ℕ) (u v : CutRing × CutRing) :
    translation a (u + v) = translation a u * translation a v := by
  ext p
  exact translate_add a u v p

theorem halfPlane_mem (a : ℕ) (j : Fin 4) (z : CutRing) :
    halfPlane a j z ∈ polygonAlgebra a :=
  BooleanSubalgebra.subset_closure ⟨j, z, rfl⟩

noncomputable def wrapIndices (u : CutRing × CutRing) : Finset (ℤ × ℤ) :=
  (Finset.Icc ⌊ordinary u.1⌋ (⌊ordinary u.1⌋ + 1)) ×ˢ
    (Finset.Icc ⌊ordinary u.2⌋ (⌊ordinary u.2⌋ + 1))

def wrapCell (a : ℕ) (u : CutRing × CutRing) (k : ℤ × ℤ) : Set (GenericSquare a) :=
  (halfPlane a 0 ((k.1 : CutRing) + 1 - u.1) ∩
    (halfPlane a 0 ((k.1 : CutRing) - u.1))ᶜ) ∩
  (halfPlane a 1 ((k.2 : CutRing) + 1 - u.2) ∩
    (halfPlane a 1 ((k.2 : CutRing) - u.2))ᶜ)

theorem wrapCell_mem (a : ℕ) (u : CutRing × CutRing) (k : ℤ × ℤ) :
    wrapCell a u k ∈ polygonAlgebra a :=
  BooleanSubalgebra.inf_mem
    (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))
    (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))

theorem mem_wrapCell {a : ℕ} (u : CutRing × CutRing) (k : ℤ × ℤ) (p : GenericSquare a) :
    p ∈ wrapCell a u k ↔
      ⌊p.val.1 + ordinary u.1⌋ = k.1 ∧ ⌊p.val.2 + ordinary u.2⌋ = k.2 := by
  simp only [wrapCell, Set.mem_inter_iff, halfPlane, Set.mem_ofPred_eq,
    Set.mem_compl_iff, cutForm, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_sub, map_add, map_one, map_intCast, not_lt, Int.floor_eq_iff]
  constructor
  · rintro ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨hx, hx'⟩, ⟨hy, hy'⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem floor_wrap_mem {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (t : ℝ) :
    ⌊x + t⌋ ∈ Finset.Icc ⌊t⌋ (⌊t⌋ + 1) := by
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (by linarith [hx.1]),
    (Int.floor_mono (show x + t ≤ t + 1 by linarith [hx.2])).trans_eq (Int.floor_add_one t)⟩

theorem point_wrap_mem {a : ℕ} (u : CutRing × CutRing) (p : GenericSquare a) :
    (⌊p.val.1 + ordinary u.1⌋, ⌊p.val.2 + ordinary u.2⌋) ∈ wrapIndices u := by
  exact Finset.mem_product.mpr
    ⟨floor_wrap_mem p.property.1 _, floor_wrap_mem p.property.2.1 _⟩

theorem translate_on_wrap {a : ℕ} (u : CutRing × CutRing) (k : ℤ × ℤ)
    {p : GenericSquare a} (hp : p ∈ wrapCell a u k) :
    (translate a u p).val = p.val +
      (ordinary (u.1 - (k.1 : CutRing)), ordinary (u.2 - (k.2 : CutRing))) := by
  obtain ⟨h1, h2⟩ := (mem_wrapCell u k p).mp hp
  simp only [translate_val, Int.fract, h1, h2, map_sub, map_intCast]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem preimage_halfPlane (a : ℕ) (u : CutRing × CutRing) (j : Fin 4) (z : CutRing) :
    translate a u ⁻¹' halfPlane a j z =
      ⋃ k ∈ wrapIndices u, wrapCell a u k ∩
        halfPlane a j (z - integralCutForm a j
          (u.1 - (k.1 : CutRing), u.2 - (k.2 : CutRing))) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hp
    let k := (⌊p.val.1 + ordinary u.1⌋, ⌊p.val.2 + ordinary u.2⌋)
    have hk : p ∈ wrapCell a u k := (mem_wrapCell u k p).mpr ⟨rfl, rfl⟩
    refine ⟨k, point_wrap_mem u p, hk, ?_⟩
    change cutForm a j (translate a u p).val < ordinary z at hp
    rw [translate_on_wrap u k hk, cutForm_add, cutForm_ordinary a j (u.1 - (k.1 : CutRing), u.2 - (k.2 : CutRing))] at hp
    change cutForm a j p.val < ordinary (z - _)
    rw [map_sub]
    linarith
  · rintro ⟨k, _, hk, hp⟩
    change cutForm a j p.val < ordinary (z - _) at hp
    rw [map_sub] at hp
    change cutForm a j (translate a u p).val < ordinary z
    rw [translate_on_wrap u k hk, cutForm_add,
      cutForm_ordinary a j (u.1 - (k.1 : CutRing), u.2 - (k.2 : CutRing))]
    linarith

theorem polygon_preimage_translate {a : ℕ} (u : CutRing × CutRing)
    {U : Set (GenericSquare a)} (hU : U ∈ polygonAlgebra a) :
    translate a u ⁻¹' U ∈ polygonAlgebra a := by
  apply polygon_induction (P := fun V => translate a u ⁻¹' V ∈ polygonAlgebra a) ?_ ?_ ?_ ?_ hU
  · intro j z
    rw [preimage_halfPlane]
    exact BooleanSubalgebra.biSup_mem (wrapIndices u).finite_toSet
      (fun k _ => BooleanSubalgebra.inf_mem (wrapCell_mem a u k) (halfPlane_mem _ _ _))
  · simpa using (BooleanSubalgebra.bot_mem : (∅ : Set (GenericSquare a)) ∈ polygonAlgebra a)
  · intro U V hU hV; exact BooleanSubalgebra.sup_mem hU hV
  · intro U hU; exact BooleanSubalgebra.compl_mem hU

theorem polygon_image_translation {a : ℕ} (u : CutRing × CutRing)
    {U : Set (GenericSquare a)} (hU : U ∈ polygonAlgebra a) :
    translation a u '' U ∈ polygonAlgebra a := by
  rw [(translation a u).image_eq_preimage_symm]
  exact polygon_preimage_translate (-u) hU

end PolygonAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrackPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup

attribute [local instance] Classical.propDecidable

abbrev TrackPoint (a m : ℕ) := Fin m × GenericSquare a

structure TableChart (a m : ℕ) where
  source : Fin m
  target : Fin m
  shift : CutRing × CutRing
  domain : polygonAlgebra a

def TableChart.Holds {a m : ℕ} (c : TableChart a m) (f : TrackPoint a m → TrackPoint a m) : Prop :=
  ∀ x ∈ c.domain.val, f (c.source, x) = (c.target, translate a c.shift x)

def TableChart.Contains {a m : ℕ} (c : TableChart a m) (p : TrackPoint a m) : Prop :=
  p.1 = c.source ∧ p.2 ∈ c.domain.val

def HasTranslationTable {a m : ℕ} (f : TrackPoint a m → TrackPoint a m) : Prop :=
  ∃ s : Finset (TableChart a m),
    (∀ c ∈ s, c.Holds f) ∧ (∀ p, ∃ c ∈ s, c.Contains p)

def identityChart (a m : ℕ) (i : Fin m) : TableChart a m :=
  ⟨i, i, 0, ⟨Set.univ, BooleanSubalgebra.top_mem⟩⟩

theorem identity_hasTable (a m : ℕ) : HasTranslationTable (id : TrackPoint a m → TrackPoint a m) := by
  classical
  refine ⟨Finset.univ.image (identityChart a m), ?_, ?_⟩
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    intro x _
    simp [identityChart]
  · intro p
    exact ⟨identityChart a m p.1, Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩,
      rfl, Set.mem_univ _⟩

noncomputable def TableChart.comp {a m : ℕ} (c d : TableChart a m) : TableChart a m :=
  ⟨d.source, c.target, c.shift + d.shift,
    ⟨d.domain.val ∩ translate a d.shift ⁻¹' c.domain.val,
      BooleanSubalgebra.inf_mem d.domain.property (polygon_preimage_translate _ c.domain.property)⟩⟩

theorem TableChart.comp_holds {a m : ℕ} {c d : TableChart a m}
    {f g : TrackPoint a m → TrackPoint a m}
    (hc : c.Holds f) (hd : d.Holds g) (hcd : c.source = d.target) :
    (c.comp d).Holds (f ∘ g) := by
  intro x hx
  change f (g (d.source, x)) = (c.target, translate a (c.shift + d.shift) x)
  rw [hd x hx.1, ← hcd, hc _ hx.2, translate_add]

theorem comp_hasTable {a m : ℕ} {f g : TrackPoint a m → TrackPoint a m}
    (hf : HasTranslationTable f) (hg : HasTranslationTable g) : HasTranslationTable (f ∘ g) := by
  classical
  obtain ⟨s, hs, hscover⟩ := hf
  obtain ⟨t, ht, htcover⟩ := hg
  let pairs := (s ×ˢ t).filter (fun cd => cd.1.source = cd.2.target)
  refine ⟨pairs.image (fun cd => cd.1.comp cd.2), ?_, ?_⟩
  · intro e he
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hmem, hmatch⟩ := Finset.mem_filter.mp hcd
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hmem
    exact TableChart.comp_holds (hs c hc) (ht d hd) hmatch
  · intro p
    obtain ⟨d, hd, hp⟩ := htcover p
    obtain ⟨c, hc, hgp⟩ := hscover (g p)
    have hdvalue : g p = (d.target, translate a d.shift p.2) := by
      convert ht d hd p.2 hp.2 using 1
      all_goals try with_reducible_and_instances rfl
      exact congrArg g (Prod.ext hp.1 rfl : p = (d.source, p.2))
    have hmatch : c.source = d.target := by
      rw [hdvalue] at hgp
      exact hgp.1.symm
    refine ⟨c.comp d, Finset.mem_image.mpr ⟨(c,d), ?_, rfl⟩, hp.1, hp.2, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,hd⟩, hmatch⟩
    · change translate a d.shift p.2 ∈ c.domain.val
      simpa only [hdvalue] using hgp.2

noncomputable def TableChart.inverse {a m : ℕ} (c : TableChart a m) : TableChart a m :=
  ⟨c.target, c.source, -c.shift,
    ⟨translation a c.shift '' c.domain.val, polygon_image_translation _ c.domain.property⟩⟩

theorem inverse_hasTable {a m : ℕ} (f : Equiv.Perm (TrackPoint a m))
    (hf : HasTranslationTable f) : HasTranslationTable f.symm := by
  classical
  obtain ⟨s, hs, hcover⟩ := hf
  refine ⟨s.image TableChart.inverse, ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change f.symm (d.target, translate a d.shift x) =
      (d.source, translate a (-d.shift) (translate a d.shift x))
    rw [← hs d hd x hx, f.symm_apply_apply, ← translate_add, neg_add_cancel, translate_zero]
  · intro p
    obtain ⟨c, hc, hp⟩ := hcover (f.symm p)
    have hvalue : f (c.source, (f.symm p).2) =
        (c.target, translate a c.shift (f.symm p).2) := hs c hc _ hp.2
    have hpair : (c.source, (f.symm p).2) = f.symm p := Prod.ext hp.1.symm rfl
    rw [hpair, f.apply_symm_apply] at hvalue
    refine ⟨c.inverse, Finset.mem_image.mpr ⟨c,hc,rfl⟩, ?_, ?_⟩
    · exact congrArg Prod.fst hvalue
    · exact ⟨(f.symm p).2, hp.2, (congrArg Prod.snd hvalue).symm⟩

noncomputable def polygonFullGroup (a m : ℕ) : Subgroup (Equiv.Perm (TrackPoint a m)) where
  carrier := {f | HasTranslationTable f}
  one_mem' := identity_hasTable a m
  mul_mem' := comp_hasTable
  inv_mem' := fun {f} h => inverse_hasTable f h

noncomputable def SlotMap (a m : ℕ) (U : polygonAlgebra a) {n : ℕ}
    (slots : Fin n → Fin m × (CutRing × CutRing)) :
    Fin n × U.val → TrackPoint a m :=
  fun ix => ((slots ix.1).1, translate a (slots ix.1).2 ix.2.val)

def IsThreeSlotCycle {a m : ℕ} (g : polygonFullGroup a m) : Prop :=
  ∃ (U : polygonAlgebra a) (slots : Fin 3 → Fin m × (CutRing × CutRing)),
    U.val.Nonempty ∧ Function.Injective (SlotMap a m U slots) ∧
    (∀ (i : Fin 3) (x : U.val),
      g.val (SlotMap a m U slots (i,x)) = SlotMap a m U slots (i+1,x)) ∧
    (∀ p ∉ Set.range (SlotMap a m U slots), g.val p = p)

noncomputable def polygonAlternatingGroup (a m : ℕ) : Subgroup (polygonFullGroup a m) :=
  Subgroup.closure {g | IsThreeSlotCycle g}

noncomputable def conditionalPerm {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) : Equiv.Perm (TrackPoint a m) := by
  classical
  exact {
    toFun := fun p => (if p.2 ∈ U.val then σ p.1 else p.1, p.2)
    invFun := fun p => (if p.2 ∈ U.val then σ.symm p.1 else p.1, p.2)
    left_inv := by intro p; by_cases h : p.2 ∈ U.val <;> simp [h]
    right_inv := by intro p; by_cases h : p.2 ∈ U.val <;> simp [h] }

@[simp] theorem conditionalPerm_apply {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (p : TrackPoint a m) :
    conditionalPerm U σ p = (if p.2 ∈ U.val then σ p.1 else p.1, p.2) := by
  classical
  rfl

noncomputable def conditionalChart {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) (b : Bool) (i : Fin m) : TableChart a m :=
  ⟨i, if b then σ i else i, 0,
    if b then U else ⟨U.valᶜ, BooleanSubalgebra.compl_mem U.property⟩⟩

theorem conditional_hasTable {a m : ℕ} (U : polygonAlgebra a)
    (σ : Equiv.Perm (Fin m)) : HasTranslationTable (conditionalPerm U σ) := by
  classical
  refine ⟨Finset.univ.image (fun bi : Bool × Fin m => conditionalChart U σ bi.1 bi.2), ?_, ?_⟩
  · intro c hc
    obtain ⟨⟨b,i⟩, _, rfl⟩ := Finset.mem_image.mp hc
    cases b <;> intro x hx
    · change x ∉ U.val at hx
      simp [conditionalChart, hx]
    · change x ∈ U.val at hx
      simp [conditionalChart, hx]
  · intro p
    by_cases hp : p.2 ∈ U.val
    · refine ⟨conditionalChart U σ true p.1, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(true,p.1), Finset.mem_univ _,rfl⟩
      · exact ⟨rfl,hp⟩
    · refine ⟨conditionalChart U σ false p.1, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨(false,p.1), Finset.mem_univ _,rfl⟩
      · exact ⟨rfl,hp⟩

noncomputable def conditionalHom {a m : ℕ} (U : polygonAlgebra a) :
    Equiv.Perm (Fin m) →* polygonFullGroup a m where
  toFun σ := ⟨conditionalPerm U σ, conditional_hasTable U σ⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change conditionalPerm U 1 p = p
    simp
  map_mul' σ ρ := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change conditionalPerm U (σ * ρ) p = conditionalPerm U σ (conditionalPerm U ρ p)
    by_cases hp : p.2 ∈ U.val <;> simp [hp]

noncomputable def slotPerm {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots))
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (TrackPoint a m) :=
  Equiv.Perm.viaEmbedding (Equiv.prodCongr σ (Equiv.refl U.val)) ⟨SlotMap a m U slots, hinj⟩

theorem slotPerm_apply {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (x : U.val) :
    slotPerm U slots hinj σ (SlotMap a m U slots (i,x)) =
      SlotMap a m U slots (σ i,x) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem slotPerm_apply_of_notMem {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    {p : TrackPoint a m} (hp : p ∉ Set.range (SlotMap a m U slots)) :
    slotPerm U slots hinj σ p = p :=
  Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hp

noncomputable def slotChart {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : TableChart a m :=
  ⟨(slots i).1, (slots (σ i)).1, (slots (σ i)).2 - (slots i).2,
    ⟨translate a (slots i).2 '' U.val, polygon_image_translation _ U.property⟩⟩

def slotVoid {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (i : Fin m) :
    Set (GenericSquare a) :=
  (⋃ j : Fin n, ⋃ (_ : (slots j).1 = i), translate a (slots j).2 '' U.val)ᶜ

theorem slotVoid_mem {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (i : Fin m) :
    slotVoid U slots i ∈ polygonAlgebra a := by
  apply BooleanSubalgebra.compl_mem
  apply BooleanSubalgebra.iSup_mem
  intro j
  apply BooleanSubalgebra.iSup_mem
  intro _
  exact polygon_image_translation _ U.property

theorem mem_slotVoid {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (p : TrackPoint a m) :
    p.2 ∈ slotVoid U slots p.1 ↔ p ∉ Set.range (SlotMap a m U slots) := by
  simp only [slotVoid, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image, Set.mem_range]
  constructor
  · rintro h ⟨⟨i,x⟩, he⟩
    apply h
    exact ⟨i, congrArg Prod.fst he, x.val, x.property, congrArg Prod.snd he⟩
  · rintro h ⟨i, hi, x, hx, he⟩
    apply h
    exact ⟨(i,⟨x,hx⟩), Prod.ext hi he⟩

noncomputable def slotVoidChart {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing)) (i : Fin m) : TableChart a m :=
  ⟨i,i,0,⟨slotVoid U slots i, slotVoid_mem U slots i⟩⟩

theorem slotPerm_hasTable {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n)) :
    HasTranslationTable (slotPerm U slots hinj σ) := by
  classical
  refine ⟨(Finset.univ.image (slotChart U slots σ)) ∪
    (Finset.univ.image (slotVoidChart U slots)), ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      change slotPerm U slots hinj σ (SlotMap a m U slots (i,⟨y,hy⟩)) = _
      rw [slotPerm_apply]
      change ((slots (σ i)).1, translate a (slots (σ i)).2 y) =
        ((slots (σ i)).1, translate a ((slots (σ i)).2 - (slots i).2)
          (translate a (slots i).2 y))
      rw [← translate_add]
      simp
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      change slotPerm U slots hinj σ (i,x) = (i,translate a 0 x)
      rw [translate_zero]
      exact slotPerm_apply_of_notMem U slots hinj σ ((mem_slotVoid U slots (i,x)).mp hx)
  · intro p
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩, rfl⟩ := hp
      refine ⟨slotChart U slots σ i, Finset.mem_union_left _ ?_, rfl, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · exact ⟨x.val, x.property, rfl⟩
    · refine ⟨slotVoidChart U slots p.1, Finset.mem_union_right _ ?_, rfl, ?_⟩
      · exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, rfl⟩
      · exact (mem_slotVoid U slots p).mpr hp

noncomputable def slotHom {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) :
    Equiv.Perm (Fin n) →* polygonFullGroup a m where
  toFun σ := ⟨slotPerm U slots hinj σ, slotPerm_hasTable U slots hinj σ⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩, rfl⟩ := hp
      exact slotPerm_apply U slots hinj 1 i x
    · exact slotPerm_apply_of_notMem U slots hinj 1 hp
  map_mul' σ ρ := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change slotPerm U slots hinj (σ * ρ) p =
      slotPerm U slots hinj σ (slotPerm U slots hinj ρ p)
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩, rfl⟩ := hp
      simp only [slotPerm_apply, Equiv.Perm.mul_apply]
    · simp only [slotPerm_apply_of_notMem U slots hinj _ hp]

theorem SlotMap_injective_mono {a m n : ℕ} {U V : polygonAlgebra a}
    (slots : Fin n → Fin m × (CutRing × CutRing)) (hVU : V.val ⊆ U.val)
    (hU : Function.Injective (SlotMap a m U slots)) :
    Function.Injective (SlotMap a m V slots) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have ht := hU (show SlotMap a m U slots (i,⟨x.val,hVU x.property⟩) =
    SlotMap a m U slots (j,⟨y.val,hVU y.property⟩) from he)
  exact Prod.ext (congrArg (fun p : Fin n × U.val => p.1) ht)
    (Subtype.ext (congrArg (fun p => p.2.val) ht))

noncomputable def polygonInter {a : ℕ} (U V : polygonAlgebra a) : polygonAlgebra a :=
  ⟨U.val ∩ V.val, BooleanSubalgebra.inf_mem U.property V.property⟩

noncomputable def polygonDiff {a : ℕ} (U V : polygonAlgebra a) : polygonAlgebra a :=
  ⟨U.val \ V.val, BooleanSubalgebra.inf_mem U.property (BooleanSubalgebra.compl_mem V.property)⟩

theorem slotPerm_restrict_apply {a m n : ℕ} {U V : polygonAlgebra a}
    (slots : Fin n → Fin m × (CutRing × CutRing)) (hVU : V.val ⊆ U.val)
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (x : U.val) :
    slotPerm V slots (SlotMap_injective_mono slots hVU hU) σ (SlotMap a m U slots (i,x)) =
      if x.val ∈ V.val then SlotMap a m U slots (σ i,x) else SlotMap a m U slots (i,x) := by
  classical
  split_ifs with hx
  · exact slotPerm_apply V slots _ σ i ⟨x.val,hx⟩
  · apply slotPerm_apply_of_notMem
    rintro ⟨⟨j,y⟩,he⟩
    have ht := hU (show SlotMap a m U slots (j,⟨y.val,hVU y.property⟩) =
      SlotMap a m U slots (i,x) from he)
    have hyx : y.val = x.val := congrArg (fun p => p.2.val) ht
    exact hx (hyx ▸ y.property)

theorem slotHom_split {a m n : ℕ} (U V : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n)) :
    slotHom U slots hU σ =
      slotHom (polygonInter U V) slots (SlotMap_injective_mono slots (fun _ h => h.1) hU) σ *
      slotHom (polygonDiff U V) slots (SlotMap_injective_mono slots (fun _ h => h.1) hU) σ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change slotPerm U slots hU σ p =
    slotPerm (polygonInter U V) slots _ σ (slotPerm (polygonDiff U V) slots _ σ p)
  by_cases hp : p ∈ Set.range (SlotMap a m U slots)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    rw [slotPerm_apply, slotPerm_restrict_apply slots (V := polygonDiff U V) (fun _ h => h.1) hU σ]
    by_cases hx : x.val ∈ V.val
    · simp only [polygonDiff, Set.mem_sdiff, x.property, hx, not_true_eq_false, and_false,
        ↓reduceIte]
      rw [slotPerm_restrict_apply slots (V := polygonInter U V) (fun _ h => h.1) hU σ]
      simp [polygonInter, x.property, hx]
    · simp only [polygonDiff, Set.mem_sdiff, x.property, hx, not_false_eq_true, and_self,
        ↓reduceIte]
      rw [slotPerm_restrict_apply slots (V := polygonInter U V) (fun _ h => h.1) hU σ]
      simp [polygonInter, x.property, hx]
  · have hout (W : polygonAlgebra a) (hW : W.val ⊆ U.val) : p ∉ Set.range (SlotMap a m W slots) := by
      rintro ⟨⟨i,x⟩,he⟩
      exact hp ⟨(i,⟨x.val,hW x.property⟩),he⟩
    rw [slotPerm_apply_of_notMem _ _ _ _ hp,
      slotPerm_apply_of_notMem _ _ _ _ (hout (polygonDiff U V) (fun _ h => h.1)),
      slotPerm_apply_of_notMem _ _ _ _ (hout (polygonInter U V) (fun _ h => h.1))]

theorem slotHom_empty {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (h_empty : U.val = ∅) : slotHom U slots hU σ = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  apply slotPerm_apply_of_notMem
  rintro ⟨⟨i,x⟩,_⟩
  simpa [h_empty] using x.property

theorem slotHom_of_finite_cover {a m n : ℕ} {β : Type*}
    (s : Finset β) (cover : β → polygonAlgebra a) (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots)) (σ : Equiv.Perm (Fin n))
    (N : Subgroup (polygonFullGroup a m))
    (hcover : ∀ x ∈ U.val, ∃ b ∈ s, x ∈ (cover b).val)
    (hlocal : ∀ b ∈ s, ∀ V : polygonAlgebra a, ∀ hV : V.val ⊆ U.val,
      V.val ⊆ (cover b).val →
      slotHom V slots (SlotMap_injective_mono slots hV hU) σ ∈ N) :
    slotHom U slots hU σ ∈ N := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
      have hu : U.val = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        obtain ⟨b,hb,_⟩ := hcover x hx
        simp at hb)
      rw [slotHom_empty U slots hU σ hu]
      exact N.one_mem
  | @insert b s hb ih =>
      rw [slotHom_split U (cover b) slots hU σ]
      apply N.mul_mem
      · exact hlocal b (Finset.mem_insert_self ..) (polygonInter U (cover b)) (fun _ h => h.1) (fun _ h => h.2)
      · apply ih
        · intro x hx
          obtain ⟨c,hc,hxc⟩ := hcover x hx.1
          rcases Finset.mem_insert.mp hc with rfl | hc
          · exact (hx.2 hxc).elim
          · exact ⟨c,hc,hxc⟩
        · intro c hc V hV hVc
          exact hlocal c (Finset.mem_insert_of_mem hc) V (fun x hx => (hV hx).1) hVc

theorem slotHom_conjugate {a m n : ℕ} (U : polygonAlgebra a)
    (slots targets : Fin n → Fin m × (CutRing × CutRing))
    (hU : Function.Injective (SlotMap a m U slots))
    (hT : Function.Injective (SlotMap a m U targets))
    (g : polygonFullGroup a m)
    (htransport : ∀ (i : Fin n) (x : U.val),
      g.val (SlotMap a m U slots (i,x)) = SlotMap a m U targets (i,x))
    (σ : Equiv.Perm (Fin n)) :
    g * slotHom U slots hU σ * g⁻¹ = slotHom U targets hT σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨p,rfl⟩ := g.val.surjective y
  change g.val (slotPerm U slots hU σ (g.val.symm (g.val p))) =
    slotPerm U targets hT σ (g.val p)
  rw [g.val.symm_apply_apply]
  by_cases hp : p ∈ Set.range (SlotMap a m U slots)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    rw [slotPerm_apply, htransport, htransport, slotPerm_apply]
  · have hout : g.val p ∉ Set.range (SlotMap a m U targets) := by
      rintro ⟨⟨i,x⟩,he⟩
      rw [← htransport] at he
      exact hp ⟨(i,x),g.val.injective he⟩
    rw [slotPerm_apply_of_notMem U slots hU σ hp,
      slotPerm_apply_of_notMem U targets hT σ hout]

end PolygonFullGroup
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TupleChartDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

noncomputable def tupleChartDomain {a m n : ℕ}
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (cs : Fin n → TableChart a m) : polygonAlgebra a := by
  classical
  refine ⟨⋂ i, if (slots i).1 = (cs i).source then
    translate a (slots i).2 ⁻¹' (cs i).domain.val else ∅, ?_⟩
  apply BooleanSubalgebra.iInf_mem
  intro i
  split_ifs
  · exact polygon_preimage_translate _ (cs i).domain.property
  · exact BooleanSubalgebra.bot_mem

theorem mem_tupleChartDomain {a m n : ℕ}
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (cs : Fin n → TableChart a m) (x : GenericSquare a) :
    x ∈ (tupleChartDomain slots cs).val ↔
      ∀ i, (cs i).Contains ((slots i).1, translate a (slots i).2 x) := by
  classical
  simp only [tupleChartDomain, Set.mem_iInter, TableChart.Contains]
  apply forall_congr'
  intro i
  by_cases h : (slots i).1 = (cs i).source <;> simp [h]

def trackCycle {m : ℕ} (ι : Fin 3 ↪ Fin m) : Equiv.Perm (Fin m) :=
  Equiv.swap (ι 0) (ι 1) * Equiv.swap (ι 1) (ι 2)

theorem trackCycle_apply {m : ℕ} (ι : Fin 3 ↪ Fin m) (i : Fin 3) :
    trackCycle ι (ι i) = ι (i+1) := by
  fin_cases i <;> simp [trackCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    ι.injective.eq_iff]

theorem trackCycle_apply_of_notMem {m : ℕ} (ι : Fin 3 ↪ Fin m)
    {j : Fin m} (hj : j ∉ Set.range ι) : trackCycle ι j = j := by
  have hne (i : Fin 3) : j ≠ ι i := by
    intro h
    exact hj ⟨i,h.symm⟩
  simp [trackCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hne]

theorem slotHom_cycle_isThreeSlotCycle {a m n : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (ι : Fin 3 ↪ Fin n) :
    IsThreeSlotCycle (slotHom U slots hinj (trackCycle ι)) := by
  let subslots : Fin 3 → Fin m × (CutRing × CutRing) := slots ∘ ι
  have he (i : Fin 3) (x : U.val) :
      SlotMap a m U subslots (i,x) = SlotMap a m U slots (ι i,x) := rfl
  refine ⟨U,subslots,hU,?_,?_,?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    rw [he, he] at h
    have hi := hinj h
    exact Prod.ext (ι.injective (congrArg Prod.fst hi)) (congrArg (fun z : Fin n × U.val => z.2) hi)
  · intro i x
    rw [he,he]
    change slotPerm U slots hinj (trackCycle ι) (SlotMap a m U slots (ι i,x)) = _
    rw [slotPerm_apply,trackCycle_apply]
  · intro p hp
    change slotPerm U slots hinj (trackCycle ι) p = p
    by_cases h : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨j,x⟩, rfl⟩ := h
      rw [slotPerm_apply]
      have hj : j ∉ Set.range ι := by
        rintro ⟨i,rfl⟩
        exact hp ⟨(i,x),rfl⟩
      rw [trackCycle_apply_of_notMem ι hj]
    · exact slotPerm_apply_of_notMem U slots hinj _ h

theorem conditional_isThreeSlotCycle {a m : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) (ι : Fin 3 ↪ Fin m) :
    IsThreeSlotCycle (conditionalHom U (trackCycle ι)) := by
  classical
  let slots : Fin 3 → Fin m × (CutRing × CutRing) := fun i => (ι i, 0)
  have hslot (i : Fin 3) (x : U.val) :
      SlotMap a m U slots (i,x) = (ι i,x.val) := by
    simp [SlotMap, slots]
  refine ⟨U, slots, hU, ?_, ?_, ?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    simp only [hslot, Prod.mk.injEq] at h
    exact Prod.ext (ι.injective h.1) (Subtype.ext h.2)
  · intro i x
    rw [hslot, hslot]
    change conditionalPerm U (trackCycle ι) (ι i, x.val) = _
    simp [x.property, trackCycle_apply]
  · intro p hp
    have hn (i : Fin 3) (hx : p.2 ∈ U.val) : p.1 ≠ ι i := by
      intro h
      apply hp
      exact ⟨(i,⟨p.2,hx⟩), by rw [hslot]; exact Prod.ext h.symm rfl⟩
    change conditionalPerm U (trackCycle ι) p = p
    by_cases hx : p.2 ∈ U.val
    · simp [hx, trackCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hn _ hx]
    · simp [hx]

theorem conditional_cycle_mem {a m : ℕ} (U : polygonAlgebra a)
    (ι : Fin 3 ↪ Fin m) : conditionalHom U (trackCycle ι) ∈ polygonAlternatingGroup a m := by
  classical
  by_cases hU : U.val.Nonempty
  · exact Subgroup.subset_closure (conditional_isThreeSlotCycle U hU ι)
  · have hz : conditionalHom U (trackCycle ι) = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro p
      have hp : p.2 ∉ U.val := fun h => hU ⟨p.2,h⟩
      change conditionalPerm U (trackCycle ι) p = p
      simp [hp]
    rw [hz]
    exact (polygonAlternatingGroup a m).one_mem

noncomputable def shrinkingLevel (n : ℕ) : CutRing := (cutTau - 1) ^ (n+1)

@[simp] theorem ordinary_shrinkingLevel (n : ℕ) :
    ordinary (shrinkingLevel n) = (Real.goldenRatio - 1) ^ (n+1) := by
  simp [shrinkingLevel]

theorem conjugate_threeSlot_mem {a m : ℕ} (g h : polygonFullGroup a m)
    (hh : IsThreeSlotCycle h) : g * h * g⁻¹ ∈ polygonAlternatingGroup a m := by
  classical
  obtain ⟨U,slots,hne,hinj,hcycle,hfix⟩ := hh
  let σ := trackCycle (Function.Embedding.refl (Fin 3))
  have heq : h = slotHom U slots hinj σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩,rfl⟩ := hp
      change h.val (SlotMap a m U slots (i,x)) = slotPerm U slots hinj σ _
      rw [hcycle, slotPerm_apply]
      exact (congrArg (fun j => SlotMap a m U slots (j,x))
        (trackCycle_apply (Function.Embedding.refl (Fin 3)) i)).symm
    · exact (hfix p hp).trans (slotPerm_apply_of_notMem U slots hinj σ hp).symm
  rw [heq]
  let N := (polygonAlternatingGroup a m).comap (MulAut.conj g).toMonoidHom
  change slotHom U slots hinj σ ∈ N
  obtain ⟨s,hs,hcover⟩ := g.property
  let β := Fin 3 → {c // c ∈ s}
  let cover : β → polygonAlgebra a := fun cs => tupleChartDomain slots (fun i => (cs i).val)
  apply slotHom_of_finite_cover (Finset.univ : Finset β) cover U slots hinj σ N
  · intro x hx
    have hc (i : Fin 3) : ∃ c : {c // c ∈ s}, c.val.Contains ((slots i).1,translate a (slots i).2 x) := by
      obtain ⟨c,hc,hcp⟩ := hcover ((slots i).1,translate a (slots i).2 x)
      exact ⟨⟨c,hc⟩,hcp⟩
    choose cs hcs using hc
    exact ⟨cs,Finset.mem_univ _,(mem_tupleChartDomain slots _ x).mpr hcs⟩
  · intro cs _ V hVU hVC
    let targets : Fin 3 → Fin m × (CutRing × CutRing) :=
      fun i => ((cs i).val.target, (cs i).val.shift + (slots i).2)
    have htrans (i : Fin 3) (x : V.val) :
        g.val (SlotMap a m V slots (i,x)) = SlotMap a m V targets (i,x) := by
      have hx := (mem_tupleChartDomain slots _ x.val).mp (hVC x.property) i
      change g.val ((slots i).1,translate a (slots i).2 x.val) =
        ((cs i).val.target,translate a ((cs i).val.shift + (slots i).2) x.val)
      rw [hx.1, hs (cs i).val (cs i).property _ hx.2, translate_add]
    have hinjV := SlotMap_injective_mono slots hVU hinj
    have hinjT : Function.Injective (SlotMap a m V targets) := by
      rintro ⟨i,x⟩ ⟨j,y⟩ he
      rw [← htrans, ← htrans] at he
      exact hinjV (g.val.injective he)
    change g * slotHom V slots hinjV σ * g⁻¹ ∈ polygonAlternatingGroup a m
    rw [slotHom_conjugate V slots targets hinjV hinjT g htrans σ]
    by_cases hV : V.val.Nonempty
    · apply Subgroup.subset_closure
      exact slotHom_cycle_isThreeSlotCycle V hV targets hinjT (Function.Embedding.refl (Fin 3))
    · rw [slotHom_empty V targets hinjT σ (Set.not_nonempty_iff_eq_empty.mp hV)]
      exact Subgroup.one_mem _

theorem polygonAlternatingGroup_normal (a m : ℕ) : (polygonAlternatingGroup a m).Normal := by
  constructor
  intro h hh g
  change h ∈ Subgroup.closure {h | IsThreeSlotCycle h} at hh
  have hc : Subgroup.closure {h : polygonFullGroup a m | IsThreeSlotCycle h} ≤
      (polygonAlternatingGroup a m).comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    exact conjugate_threeSlot_mem g h hh
  exact hc hh

theorem isThreeCycle_eq_trackCycle {m : ℕ} {σ : Equiv.Perm (Fin m)}
    (hσ : σ.IsThreeCycle) : ∃ ι : Fin 3 ↪ Fin m, σ = trackCycle ι := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < σ.support.card by rw [hσ.card_support]; decide)
  have hn := hσ.nodup_iff_mem_support.mpr hi
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hn
  have h01 : i ≠ σ i := hn.1.1
  have h02 : i ≠ σ (σ i) := hn.1.2
  have h12 : σ i ≠ σ (σ i) := hn.2
  let ι : Fin 3 ↪ Fin m := ⟨![i,σ i,σ (σ i)], by
    intro j k h
    fin_cases j <;> fin_cases k <;> simp_all⟩
  exact ⟨ι,hσ.eq_swap_mul_swap_iff_mem_support.mpr hi⟩

theorem conditionalHom_alternating_mem {a m : ℕ} (U : polygonAlgebra a)
    {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ alternatingGroup (Fin m)) :
    conditionalHom U σ ∈ polygonAlternatingGroup a m := by
  have hle : alternatingGroup (Fin m) ≤
      (polygonAlternatingGroup a m).comap (conditionalHom U) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    intro ρ hρ
    obtain ⟨ι,rfl⟩ := isThreeCycle_eq_trackCycle hρ
    exact conditional_cycle_mem U ι
  exact hle hσ

noncomputable def trackTranslationPerm {a m : ℕ}
    (d : Fin m → CutRing × CutRing) : Equiv.Perm (TrackPoint a m) where
  toFun p := (p.1, translate a (d p.1) p.2)
  invFun p := (p.1, translate a (-d p.1) p.2)
  left_inv p := by simp only [← translate_add, neg_add_cancel, translate_zero]
  right_inv p := by simp only [← translate_add, add_neg_cancel, translate_zero]

end PolygonFullGroup
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrackTranslationChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

noncomputable def trackTranslationChart {a m : ℕ}
    (d : Fin m → CutRing × CutRing) (i : Fin m) : TableChart a m :=
  ⟨i,i,d i,⟨Set.univ,BooleanSubalgebra.top_mem⟩⟩

theorem trackTranslation_hasTable {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    HasTranslationTable (trackTranslationPerm (a := a) d) := by
  classical
  refine ⟨Finset.univ.image (trackTranslationChart d), ?_, ?_⟩
  · intro c hc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
    intro x _
    rfl
  · intro p
    exact ⟨trackTranslationChart d p.1,
      Finset.mem_image.mpr ⟨p.1,Finset.mem_univ _,rfl⟩,rfl,Set.mem_univ _⟩

noncomputable def trackTranslation {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    polygonFullGroup a m := ⟨trackTranslationPerm d,trackTranslation_hasTable d⟩

@[simp] theorem trackTranslation_apply {a m : ℕ} (d : Fin m → CutRing × CutRing)
    (p : TrackPoint a m) :
    (trackTranslation d).val p = (p.1,translate a (d p.1) p.2) := rfl

@[simp] theorem trackTranslation_zero {a m : ℕ} :
    trackTranslation (a := a) (m := m) 0 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  simp

@[simp] theorem trackTranslation_add {a m : ℕ} (d e : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (d+e) = trackTranslation d * trackTranslation e := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change (p.1,translate a (d p.1 + e p.1) p.2) =
    (p.1,translate a (d p.1) (translate a (e p.1) p.2))
  rw [translate_add]

@[simp] theorem trackTranslation_neg {a m : ℕ} (d : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (-d) = (trackTranslation d)⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rfl

@[simp] theorem trackTranslation_sub {a m : ℕ} (d e : Fin m → CutRing × CutRing) :
    trackTranslation (a := a) (d-e) = trackTranslation d * (trackTranslation e)⁻¹ := by
  rw [sub_eq_add_neg,trackTranslation_add,trackTranslation_neg]

noncomputable def wholePolygon (a : ℕ) : polygonAlgebra a :=
  ⟨Set.univ,BooleanSubalgebra.top_mem⟩

theorem constant_conjugate_translation {a m : ℕ} (ρ : Equiv.Perm (Fin m))
    (d : Fin m → CutRing × CutRing) :
    conditionalHom (wholePolygon a) ρ * trackTranslation d *
        (conditionalHom (wholePolygon a) ρ)⁻¹ =
      trackTranslation (fun i => d (ρ.symm i)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm (wholePolygon a) ρ
    (trackTranslationPerm d ((conditionalPerm (wholePolygon a) ρ).symm p)) = _
  simp [conditionalPerm,wholePolygon,trackTranslationPerm,trackTranslation]

theorem constant_conjugate_point_translation {a m : ℕ} (ρ : Equiv.Perm (Fin m))
    (i : Fin m) (v : CutRing × CutRing) :
    conditionalHom (wholePolygon a) ρ * trackTranslation (Pi.single i v) *
        (conditionalHom (wholePolygon a) ρ)⁻¹ =
      trackTranslation (Pi.single (ρ i) v) := by
  rw [constant_conjugate_translation]
  congr 1
  funext j
  simp only [Pi.single_apply]
  congr 1
  exact propext (Equiv.symm_apply_eq ρ)

theorem trackTranslation_difference_mem {a m : ℕ} (hm : 3 ≤ m)
    (i j : Fin m) (v : CutRing × CutRing) :
    trackTranslation (a := a) (Pi.single j v - Pi.single i v) ∈ polygonAlternatingGroup a m := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  let ι : Fin 3 ↪ Fin m := ⟨![i,j,k], by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all⟩
  let c := conditionalHom (wholePolygon a) (trackCycle ι)
  let t := trackTranslation (a := a) (Pi.single i v)
  have hc : c ∈ polygonAlternatingGroup a m := conditional_cycle_mem _ _
  have hnormal := polygonAlternatingGroup_normal a m
  have ht : c * t * c⁻¹ * t⁻¹ ∈ polygonAlternatingGroup a m := by
    have hconj := hnormal.conj_mem c⁻¹ ((polygonAlternatingGroup a m).inv_mem hc) t
    simpa only [mul_assoc] using (polygonAlternatingGroup a m).mul_mem hc hconj
  have he : (trackCycle ι) i = j := trackCycle_apply ι 0
  have heq : c * t * c⁻¹ = trackTranslation (a := a) (Pi.single j v) := by
    change conditionalHom (wholePolygon a) (trackCycle ι) * trackTranslation (Pi.single i v) *
      (conditionalHom (wholePolygon a) (trackCycle ι))⁻¹ = _
    rw [constant_conjugate_point_translation,he]
  rw [heq] at ht
  simpa only [trackTranslation_sub,t] using ht

noncomputable def coordinatePrimitive (a : ℕ) (j : Fin 2) : polygonAlgebra a :=
  ⟨halfPlane a (Fin.castLE (by omega) j) (cutTau-1) ∩
      (halfPlane a (Fin.castLE (by omega) j) 0)ᶜ,
    BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem
      (halfPlane_mem _ _ _))⟩

noncomputable def circularBoxPiece (a : ℕ) (r : CutRing) (k : Fin 2 × Fin 2) :
    polygonAlgebra a :=
  ⟨(halfPlane a 0 (r + (k.1.val : CutRing)) ∩
      (halfPlane a 0 (-r + (k.1.val : CutRing)))ᶜ) ∩
    (halfPlane a 1 (r + (k.2.val : CutRing)) ∩
      (halfPlane a 1 (-r + (k.2.val : CutRing)))ᶜ), by
    apply BooleanSubalgebra.inf_mem <;> apply BooleanSubalgebra.inf_mem
    · exact halfPlane_mem _ _ _
    · exact BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)
    · exact halfPlane_mem _ _ _
    · exact BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)⟩

noncomputable def clippedSlopePrimitive (a : ℕ) (r : CutRing) (j : Fin 4) :
    polygonAlgebra a :=
  ⟨⋃ k : Fin 2 × Fin 2, (circularBoxPiece a r k).val ∩
      (halfPlane a j (integralCutForm a j (k.1.val,k.2.val)))ᶜ, by
    apply BooleanSubalgebra.iSup_mem
    intro k
    exact BooleanSubalgebra.inf_mem (circularBoxPiece a r k).property
      (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _))⟩

noncomputable def initialTest (a : ℕ) (r : CutRing) : Fin 5 → polygonAlgebra a :=
  ![wholePolygon a,coordinatePrimitive a 0,coordinatePrimitive a 1,
    clippedSlopePrimitive a r 2,clippedSlopePrimitive a r 3]

def SourceGeneratorLabel (m : ℕ) :=
  (Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
    σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}) ⊕ (Fin m × Fin 2)

noncomputable def sourceGenerator (a : ℕ) (r : CutRing) (m : ℕ) :
    SourceGeneratorLabel m → polygonFullGroup a (m+1)
  | Sum.inl (j,σ) => conditionalHom (initialTest a r j) σ.val
  | Sum.inr (i,j) => trackTranslation
      (Pi.single i.castSucc (if j = 0 then (cutTau,0) else (0,cutTau)) -
       Pi.single (Fin.last m) (if j = 0 then (cutTau,0) else (0,cutTau)))

theorem sourceGenerator_mem (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (s : SourceGeneratorLabel m) : sourceGenerator a r m s ∈ polygonAlternatingGroup a (m+1) := by
  cases s with
  | inl s => exact conditionalHom_alternating_mem _ s.2.property.1
  | inr s => exact trackTranslation_difference_mem (by omega) _ _ _

noncomputable def alternatingGenerator (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) :
    SourceGeneratorLabel m → polygonAlternatingGroup a (m+1) :=
  fun s => ⟨sourceGenerator a r m s,sourceGenerator_mem a r m hm s⟩

end PolygonFullGroup

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PerfectCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PerfectCalculus

open scoped commutatorElement

variable {P H Q : Type*} [Group P] [Group H] [Group Q]

theorem perfect_hom_to_commGroup {A : Type*} [Group A] [IsMulCommutative A] [Group.IsPerfect P]
    (f : P →* A) (x : P) : f x = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨f x, x, rfl⟩ : f.range) 1)

theorem perfect_lift_unique [Group.IsPerfect P] (q : H →* Q)
    (hq : q.ker ≤ Subgroup.center H) (f g : P →* H)
    (hfg : q.comp f = q.comp g) : f = g := by
  have hpoint (x : P) : q (f x) = q (g x) := DFunLike.congr_fun hfg x
  have hc (x : P) : f x * (g x)⁻¹ ∈ Subgroup.center H := by
    apply hq
    change q (f x * (g x)⁻¹) = 1
    simp [hpoint]
  let d : P →* Subgroup.center H :=
    { toFun := fun x => ⟨f x * (g x)⁻¹, hc x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change f (x * y) * (g (x * y))⁻¹ =
          (f x * (g x)⁻¹) * (f y * (g y)⁻¹)
        rw [map_mul, map_mul, mul_inv_rev]
        have hcomm := Subgroup.mem_center_iff.mp (hc y) ((g x)⁻¹)
        calc
          f x * f y * ((g y)⁻¹ * (g x)⁻¹) =
              f x * ((f y * (g y)⁻¹) * (g x)⁻¹) := by simp only [mul_assoc]
          _ = f x * ((g x)⁻¹ * (f y * (g y)⁻¹)) := by rw [hcomm]
          _ = (f x * (g x)⁻¹) * (f y * (g y)⁻¹) := by simp only [mul_assoc] }
  ext x
  have heq := congrArg Subtype.val (perfect_hom_to_commGroup d x)
  exact mul_inv_eq_one.mp heq

theorem perfect_commutator_central_trivial (A B : Subgroup H) [Group.IsPerfect A]
    (h : ⁅A, B⁆ ≤ Subgroup.center H) : ⁅A, B⁆ = ⊥ := by
  have hz : ⁅⁅A, B⁆, (⊤ : Subgroup H)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr h
  have ha : ⁅⁅A, B⁆, A⁆ = ⊥ :=
    bot_unique ((Subgroup.commutator_mono le_rfl le_top).trans hz.le)
  have hb : ⁅⁅B, A⁆, A⁆ = ⊥ := by simpa only [Subgroup.commutator_comm B A] using ha
  have hc : ⁅⁅A, A⁆, B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate ha hb
  simpa only [Subgroup.commutator_eq_self] using hc

theorem central_extension_decomposition [Group.IsPerfect Q] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (x : H) :
    ∃ d ∈ commutator H, ∃ z ∈ Subgroup.center H, x = d * z := by
  have hmap : (commutator H).map q = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (hmap.symm ▸ Subgroup.mem_top (q x))
  refine ⟨d, hd, d⁻¹ * x, hcentral ?_, by simp⟩
  change q (d⁻¹ * x) = 1
  simp [hdx]

theorem central_extension_commutator_perfect [Group.IsPerfect Q] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) :
    Group.IsPerfect (commutator H) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  obtain ⟨d, hd, z, hz, rfl⟩ := central_extension_decomposition q hq hcentral x
  obtain ⟨e, he, w, hw, rfl⟩ := central_extension_decomposition q hq hcentral y
  have hzcomm : ⁅z, e * w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp hz (e * w)).symm)
  have hwcomm : ⁅d, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw d)
  rw [commutatorElement_mul_left_eq_conj_mul, hzcomm]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj, hwcomm]
  simpa only [mul_one, mul_inv_cancel_right, commutator_def] using Subgroup.commutator_mem_commutator hd he

theorem central_extension_commutator_surjective [Group.IsPerfect Q] (q : H →* Q)
    (hq : Function.Surjective q) :
    Function.Surjective (q.comp (commutator H).subtype) := by
  intro x
  have hmap : (commutator H).map q = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp (hmap.symm ▸ Subgroup.mem_top x)
  exact ⟨⟨d, hd⟩, hdx⟩

end PerfectCalculus

open scoped commutatorElement

section UniversalCentralExtension

open scoped commutatorElement

variable (E : Type*) [Group E]

def freeEvaluation : FreeGroup E →* E := FreeGroup.lift id

@[simp] theorem freeEvaluation_of (x : E) : freeEvaluation E (FreeGroup.of x) = x :=
  FreeGroup.lift_apply_of

def centralizingRelations : Subgroup (FreeGroup E) :=
  ⁅(⊤ : Subgroup (FreeGroup E)), (freeEvaluation E).ker⁆

instance instNormalFreeGroupCentralizingRelations : (centralizingRelations E).Normal := by
  unfold centralizingRelations
  infer_instance

abbrev CentralizedFree := FreeGroup E ⧸ centralizingRelations E

def centralFreeMap : CentralizedFree E →* E :=
  QuotientGroup.lift (centralizingRelations E) (freeEvaluation E)
    (fun _ h => Subgroup.commutator_le_right (⊤ : Subgroup (FreeGroup E))
      (freeEvaluation E).ker h)

@[simp] theorem centralFreeMap_mk (x : FreeGroup E) :
    centralFreeMap E (QuotientGroup.mk' (centralizingRelations E) x) =
      freeEvaluation E x := rfl

theorem centralFreeMap_surjective : Function.Surjective (centralFreeMap E) := by
  intro x
  exact ⟨QuotientGroup.mk' (centralizingRelations E) (FreeGroup.of x), freeEvaluation_of E x⟩

theorem centralFreeMap_central : (centralFreeMap E).ker ≤ Subgroup.center (CentralizedFree E) := by
  intro x
  refine QuotientGroup.induction_on x ?_
  intro w hw
  apply Subgroup.mem_center_iff.mpr
  intro y
  refine QuotientGroup.induction_on y ?_
  intro v
  apply commutatorElement_eq_one_iff_mul_comm.mp
  change ⁅QuotientGroup.mk' (centralizingRelations E) v,
    QuotientGroup.mk' (centralizingRelations E) w⁆ = 1
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hw

abbrev UniversalExtension := commutator (CentralizedFree E)

def universalProjection : UniversalExtension E →* E :=
  (centralFreeMap E).comp (commutator (CentralizedFree E)).subtype

instance instIsPerfectSubtypeCentralizedFreeMemSubgroupUniversalExtension [Group.IsPerfect E] : Group.IsPerfect (UniversalExtension E) :=
  central_extension_commutator_perfect (centralFreeMap E)
    (centralFreeMap_surjective E) (centralFreeMap_central E)

theorem universalProjection_surjective [Group.IsPerfect E] :
    Function.Surjective (universalProjection E) :=
  central_extension_commutator_surjective (centralFreeMap E) (centralFreeMap_surjective E)

theorem universalProjection_central :
    (universalProjection E).ker ≤ Subgroup.center (UniversalExtension E) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (centralFreeMap_central E hx) y.val

variable {E} {H Q : Type*} [Group H] [Group Q]

theorem universal_lift_exists (q : H →* Q) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    ∃ l : UniversalExtension E →* H, q.comp l = f.comp (universalProjection E) := by
  classical
  let a : E → H := fun x => (hq (f x)).choose
  have ha (x : E) : q (a x) = f x := (hq (f x)).choose_spec
  let F : FreeGroup E →* H := FreeGroup.lift a
  have hF : q.comp F = f.comp (freeEvaluation E) := by
    ext x
    simpa [F, freeEvaluation] using ha x
  have hrel : centralizingRelations E ≤ F.ker := by
    apply Subgroup.commutator_le.mpr
    intro x _ r hr
    change F ⁅x, r⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    apply Subgroup.mem_center_iff.mp
    apply hcentral
    change q (F r) = 1
    have hpoint := DFunLike.congr_fun hF r
    simpa only [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hr, map_one] using hpoint
  let Fbar : CentralizedFree E →* H :=
    QuotientGroup.lift (centralizingRelations E) F (fun _ hr => hrel hr)
  refine ⟨Fbar.comp (commutator (CentralizedFree E)).subtype, ?_⟩
  ext x
  change q (Fbar x.val) = f (centralFreeMap E x.val)
  have hpoint (y : CentralizedFree E) : q (Fbar y) = f (centralFreeMap E y) := by
    refine QuotientGroup.induction_on y ?_
    intro w
    exact DFunLike.congr_fun hF w
  exact hpoint x.val

theorem universal_lift_exists_unique [Group.IsPerfect E] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    ∃! l : UniversalExtension E →* H, q.comp l = f.comp (universalProjection E) := by
  obtain ⟨l, hl⟩ := universal_lift_exists q hq hcentral f
  refine ⟨l, hl, ?_⟩
  intro l' hl'
  exact perfect_lift_unique q hcentral l' l (hl'.trans hl.symm)

noncomputable def universalLift [Group.IsPerfect E] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    UniversalExtension E →* H :=
  (universal_lift_exists_unique q hq hcentral f).choose

theorem universalLift_spec [Group.IsPerfect E] (q : H →* Q)
    (hq : Function.Surjective q) (hcentral : q.ker ≤ Subgroup.center H) (f : E →* Q) :
    q.comp (universalLift q hq hcentral f) = f.comp (universalProjection E) :=
  (universal_lift_exists_unique q hq hcentral f).choose_spec.1

variable [Group.IsPerfect E] [Group.IsPerfect H] [Group.IsPerfect Q]

noncomputable def universalMap (f : E →* H) : UniversalExtension E →* UniversalExtension H :=
  universalLift (universalProjection H) (universalProjection_surjective H)
    (universalProjection_central H) f

theorem universalMap_spec (f : E →* H) :
    (universalProjection H).comp (universalMap f) = f.comp (universalProjection E) :=
  universalLift_spec _ _ _ _

@[simp] theorem universalMap_id : universalMap (MonoidHom.id E) =
    MonoidHom.id (UniversalExtension E) := by
  apply perfect_lift_unique (universalProjection E) (universalProjection_central E)
  simpa using universalMap_spec (MonoidHom.id E)

@[simp] theorem universalMap_comp (g : H →* Q) (f : E →* H) :
    universalMap (g.comp f) = (universalMap g).comp (universalMap f) := by
  apply perfect_lift_unique (universalProjection Q) (universalProjection_central Q)
  rw [universalMap_spec, ← MonoidHom.comp_assoc, universalMap_spec]
  simp only [MonoidHom.comp_assoc, universalMap_spec]

end UniversalCentralExtension

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_BoundedRelationCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section BoundedRelationCover

variable (α : Type*) (L : ℕ)

def ShortWord := Σ n : Fin (L + 1), Fin n.val → α × Bool

def ShortWord.value (w : ShortWord α L) : FreeGroup α :=
  FreeGroup.mk (List.ofFn w.2)

variable {α} {G : Type*} [Group G] (f : α → G)

def shortRelations : Set (FreeGroup α) :=
  Set.range (ShortWord.value α L) ∩ (FreeGroup.lift f).ker

abbrev BoundedRelationCover := PresentedGroup (shortRelations L f)

def coverMap : BoundedRelationCover L f →* G :=
  PresentedGroup.toGroup (fun _ h => h.2)

@[simp] theorem coverMap_mk (w : FreeGroup α) :
    coverMap L f (PresentedGroup.mk (shortRelations L f) w) = FreeGroup.lift f w := rfl

@[simp] theorem coverMap_of (a : α) :
    coverMap L f (PresentedGroup.of a) = f a := by
  exact FreeGroup.lift_apply_of

end BoundedRelationCover

section CoherentBoundedCovers
variable {α G : Type*} [Group G] (f : α → G)

theorem shortRelations_mono {L M : ℕ} (hLM : L ≤ M) :
    shortRelations L f ⊆ shortRelations M f := by
  rintro w ⟨⟨⟨n,v⟩,rfl⟩,he⟩
  exact ⟨⟨⟨⟨n.val,by omega⟩,v⟩,rfl⟩,he⟩

def coverTransition {L M : ℕ} (hLM : L ≤ M) :
    BoundedRelationCover L f →* BoundedRelationCover M f :=
  PresentedGroup.map (MonoidHom.id _) (fun _ h => shortRelations_mono f hLM h)

@[simp] theorem coverTransition_mk {L M : ℕ} (hLM : L ≤ M) (w : FreeGroup α) :
    coverTransition f hLM (PresentedGroup.mk (shortRelations L f) w) =
      PresentedGroup.mk (shortRelations M f) w := rfl

end CoherentBoundedCovers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FinitelyManyTranslationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section FinitelyManyTranslationRelations

open scoped IsMulCommutative

variable {β H : Type*} [Group H]

noncomputable def commutingFamilyHom (t : β → H) (ht : ∀ i j, Commute (t i) (t j)) :
    Multiplicative (FreeAbelianGroup β) →* H := by
  let C := Subgroup.closure (Set.range t)
  haveI : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    exact ht i j)
  letI : CommGroup C := by infer_instance
  exact C.subtype.comp (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift (fun i => Additive.ofMul (⟨t i,Subgroup.subset_closure ⟨i,rfl⟩⟩ : C))))

@[simp] theorem commutingFamilyHom_of (t : β → H) (ht : ∀ i j, Commute (t i) (t j))
    (i : β) : commutingFamilyHom t ht (Multiplicative.ofAdd (FreeAbelianGroup.of i)) = t i := by
  simp [commutingFamilyHom]

end FinitelyManyTranslationRelations

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TranslationLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualTranslationLifts

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

theorem source_translation_commute (i j : Fin m × Fin 2) :
    Commute (alternatingGenerator a r m hm (Sum.inr i))
      (alternatingGenerator a r m hm (Sum.inr j)) := by
  change _ * _ = _ * _
  apply Subtype.ext
  change trackTranslation _ * trackTranslation _ = trackTranslation _ * trackTranslation _
  rw [← trackTranslation_add, ← trackTranslation_add]
  congr 1
  exact add_comm _ _

end ActualTranslationLifts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PerfectGeneratingFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section SourceCentralizingTranslations

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

noncomputable def sourceLatticeMap :
    Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      polygonAlternatingGroup a (m+1) :=
  commutingFamilyHom (fun i => alternatingGenerator a r m hm (Sum.inr i))
    (source_translation_commute a r m hm)

end SourceCentralizingTranslations

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_LatticeRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceLatticeRange

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

noncomputable def sourceLatticeFullMap :
    Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      polygonFullGroup a (m+1) :=
  (polygonAlternatingGroup a (m+1)).subtype.comp (sourceLatticeMap a r m hm)

end SourceLatticeRange

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_BooleanCoordinateGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BooleanCoordinateGeneration

noncomputable def coordinateShift (j : Fin 2) (z : CutRing) : CutRing × CutRing :=
  if j = 0 then (z,0) else (0,z)

end BooleanCoordinateGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

def bankIndex : Fin 3 × Fin 3 ≃ Fin 9 := finProdFinEquiv

def bankPermutation : Equiv.Perm (Fin 9) :=
  bankIndex.permCongr (Equiv.prodCongr (Equiv.addRight (1 : Fin 3)) (Equiv.refl (Fin 3)))

@[simp] theorem bankPermutation_apply (i j : Fin 3) :
    bankPermutation (bankIndex (i,j)) = bankIndex (i+1,j) := by
  simp [bankPermutation,Equiv.permCongr_apply]

noncomputable def bankSlots {m : ℕ}
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing)) (i : Fin 9) :
    Fin m × (CutRing × CutRing) := b (bankIndex.symm i).1 (bankIndex.symm i).2

@[simp] theorem bankSlots_apply {m : ℕ}
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing)) (i j : Fin 3) :
    bankSlots b (bankIndex (i,j)) = b i j := by
  simp [bankSlots]

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AlignedGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AlignedGroups

variable {A H : Type*} [Group A] [Group H] {B : Type*}

noncomputable def alignedGroup (t : A →* H) (x : B → H) (P : B → Prop) : Subgroup H :=
  Subgroup.closure {y | ∃ b, P b ∧ ∃ u, y = t u*x b*(t u)⁻¹}

end AlignedGroups

section SourceAlignedGroups

def SmallConditional (m : ℕ) := Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
  σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}

end SourceAlignedGroups

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CanonicalSectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CanonicalSectors
open scoped commutatorElement

variable {E H Q : Type*} [Group E] [Group H] [Group Q]

theorem perfect_maps_commute_of_central [Group.IsPerfect E]
    {P : Type*} [Group P] (q : H →* Q) (hc : q.ker ≤ Subgroup.center H)
    (f : E →* H) (g : P →* H)
    (hfg : ∀ x y, Commute (q (f x)) (q (g y))) :
    ∀ x y, Commute (f x) (g y) := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hh : ⁅f.range,g.range⁆ ≤ Subgroup.center H := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    apply hc
    change q ⁅f x,g y⁆ = 1
    rw [map_commutatorElement]
    exact (hfg x y).commutator_eq
  have hzero := perfect_commutator_central_trivial f.range g.range hh
  intro x y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  have hh' := Subgroup.commutator_mem_commutator
    (show f x ∈ f.range from ⟨x,rfl⟩) (show g y ∈ g.range from ⟨y,rfl⟩)
  simpa [hzero] using hh'

variable {Ω : Type*}

noncomputable def sectorMask (U : Set Ω) : E →* (Ω → E) := by
  classical
  exact { toFun := fun s ω => if ω ∈ U then s else 1
          map_one' := by funext ω; simp
          map_mul' := by intro s t; funext ω; by_cases h : ω ∈ U <;> simp [h] }

@[simp] theorem sectorMask_of_mem (U : Set Ω) (s : E) (ω : Ω) (h : ω ∈ U) :
    sectorMask U s ω = s := by
  classical
  simp [sectorMask, h]

@[simp] theorem sectorMask_of_not_mem (U : Set Ω) (s : E) (ω : Ω) (h : ω ∉ U) :
    sectorMask U s ω = 1 := by
  classical
  simp [sectorMask, h]

theorem sectorMask_commute {U V : Set Ω} (huv : Disjoint U V) (s t : E) :
    Commute (sectorMask U s) (sectorMask V t) := by
  classical
  funext ω
  change sectorMask U s ω * sectorMask V t ω = sectorMask V t ω * sectorMask U s ω
  have hd := Set.disjoint_left.mp huv
  by_cases hu : ω ∈ U <;> by_cases hv : ω ∈ V <;> simp_all [sectorMask]

theorem sectorMask_disjoint_union {U V : Set Ω} (huv : Disjoint U V) (s : E) :
    sectorMask (U ∪ V) s = sectorMask U s * sectorMask V s := by
  classical
  funext ω
  have hd := Set.disjoint_left.mp huv
  by_cases hu : ω ∈ U <;> by_cases hv : ω ∈ V <;> simp_all [sectorMask, Pi.mul_apply]

variable [Group.IsPerfect E]

def commutingProduct (f g : E →* H) (hc : ∀ s t, Commute (f s) (g t)) : E →* H :=
  (f.noncommCoprod g hc).comp ((MonoidHom.id E).prod (MonoidHom.id E))

omit [Group.IsPerfect E] in
@[simp] theorem commutingProduct_apply (f g : E →* H)
    (hc : ∀ s t, Commute (f s) (g t)) (s : E) :
    commutingProduct f g hc s = f s * g s := rfl

end CanonicalSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConditionalFamilyLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section ActualFamilyLaws

variable {ι E H Q : Type*} [Group E] [Group H] [Group Q]

def CentralOn (q : H →* Q) (S : Subgroup H) : Prop :=
  (q.comp S.subtype).ker ≤ Subgroup.center S

end ActualFamilyLaws

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_CofinalPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits
namespace CofinalPowers

variable {P:Type} [CommMonoid P]
noncomputable def sequence (x:P) : ℕ ⥤ ActionCategory P P where
  obj n := (x^n:P)
  map {n m} f := ⟨x^(m-n),by
    change x^(m-n)*x^n=x^m
    rw [←pow_add,Nat.sub_add_cancel (leOfHom f)]⟩
  map_id n := by
    apply Subtype.ext
    change x^(n-n)=1
    simp
  map_comp {n m k} f g := by
    apply Subtype.ext
    change x^(k-n)=x^(k-m)*x^(m-n)
    rw [←pow_add]
    congr 1
    have h:=leOfHom f; have h':=leOfHom g; omega
lemma final (x:P) (hx:∀p:P,∃q n,p*q=x^n) : (sequence x).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro p
    obtain ⟨q,n,h⟩:=hx p.back
    exact ⟨n,⟨⟨q,by change q*p.back=x^n; simpa only [mul_comm] using h⟩⟩⟩
  · intro p n f g
    obtain ⟨q,k,h⟩:=hx p.back
    refine ⟨n+k,homOfLE (Nat.le_add_right n k),?_⟩
    apply Subtype.ext
    change x^(n+k-n)*f.val=x^(n+k-n)*g.val
    rw [Nat.add_sub_cancel_left]
    have eh : f.val*p.back=g.val*p.back:=f.property.trans g.property.symm
    rw [←h]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using congrArg (fun p:P=>p*q) eh
noncomputable def colimitIso {A:Type*} [Category A] (x:P) (hx:∀p:P,∃q n,p*q=x^n)
    (F:ActionCategory P P ⥤ A) [HasColimit F] [HasColimit (sequence x ⋙ F)] :
    colimit (sequence x ⋙ F) ≅ colimit F := by
  haveI := final x hx
  exact Functor.Final.colimitIso (sequence x) F
end CofinalPowers

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PointwisePolygonTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PointwisePolygonTables

variable {a m : ℕ}

noncomputable def conditionalAlternatingHom (U : polygonAlgebra a) :
    alternatingGroup (Fin m) →* polygonAlternatingGroup a m :=
  ((conditionalHom U).comp (alternatingGroup (Fin m)).subtype).codRestrict
    (polygonAlternatingGroup a m) (fun s => conditionalHom_alternating_mem U s.property)

theorem conditionalHom_disjoint_commute (U V : polygonAlgebra a)
    (hUV : Disjoint U.val V.val) (σ ρ : Equiv.Perm (Fin m)) :
    Commute (conditionalHom U σ) (conditionalHom V ρ) := by
  change _ * _ = _ * _
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm U σ (conditionalPerm V ρ p) =
    conditionalPerm V ρ (conditionalPerm U σ p)
  by_cases hu : p.2 ∈ U.val <;> by_cases hv : p.2 ∈ V.val
  · exact False.elim (Set.disjoint_left.mp hUV hu hv)
  all_goals simp [conditionalPerm, hu, hv]

structure PolygonLabelling (a : ℕ) (Ω : Type*) where
  label : GenericSquare a → Ω
  fiber_mem : ∀ ω, {p | label p = ω} ∈ polygonAlgebra a

noncomputable def PolygonLabelling.fiber {Ω : Type*} (v : PolygonLabelling a Ω)
    (ω : Ω) : polygonAlgebra a := ⟨{p | v.label p = ω},v.fiber_mem ω⟩

theorem PolygonLabelling.fiber_disjoint {Ω : Type*} (v : PolygonLabelling a Ω)
    {ω ν : Ω} (h : ω ≠ ν) : Disjoint (v.fiber ω).val (v.fiber ν).val := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact h (hp.symm.trans hq)

noncomputable def PolygonLabelling.permutationHom {Ω : Type*} (v : PolygonLabelling a Ω) :
    (Ω → alternatingGroup (Fin m)) →* Equiv.Perm (TrackPoint a m) where
  toFun σ := {
    toFun := fun p => ((σ (v.label p.2)).val p.1,p.2)
    invFun := fun p => ((σ (v.label p.2)).val.symm p.1,p.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }
  map_one' := by apply Equiv.ext; intro p; rfl
  map_mul' := by intro σ ρ; apply Equiv.ext; intro p; rfl

@[simp] theorem PolygonLabelling.permutationHom_apply {Ω : Type*}
    (v : PolygonLabelling a Ω) (σ : Ω → alternatingGroup (Fin m)) (p : TrackPoint a m) :
    v.permutationHom σ p = ((σ (v.label p.2)).val p.1,p.2) := rfl

noncomputable def PolygonLabelling.tableHom {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) :
    (Ω → alternatingGroup (Fin m)) →* polygonAlternatingGroup a m :=
  MonoidHom.noncommPiCoprod (fun ω => conditionalAlternatingHom (v.fiber ω)) (by
    intro ω ν h s t
    change _ * _ = _ * _
    apply Subtype.ext
    exact (conditionalHom_disjoint_commute (v.fiber ω) (v.fiber ν)
      (v.fiber_disjoint h) s.val t.val).eq)

@[simp] theorem PolygonLabelling.tableHom_single {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (v : PolygonLabelling a Ω) (ω : Ω) (s : alternatingGroup (Fin m)) :
    v.tableHom (Pi.mulSingle ω s) = conditionalAlternatingHom (v.fiber ω) s :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem PolygonLabelling.tableHom_permutation {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) :
    (polygonFullGroup a m).subtype.comp
        ((polygonAlternatingGroup a m).subtype.comp v.tableHom) = v.permutationHom := by
  classical
  apply MonoidHom.pi_ext
  intro ω s
  simp only [MonoidHom.comp_apply, v.tableHom_single]
  apply Equiv.ext
  intro p
  change conditionalPerm (v.fiber ω) s.val p =
    (((Pi.mulSingle ω s : Ω → alternatingGroup (Fin m)) (v.label p.2)).val p.1,p.2)
  by_cases hp : v.label p.2 = ω
  · simp [conditionalPerm, PolygonLabelling.fiber, hp]
  · simp [conditionalPerm, PolygonLabelling.fiber, hp]

@[simp] theorem PolygonLabelling.tableHom_apply {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) (σ : Ω → alternatingGroup (Fin m)) (p : TrackPoint a m) :
    (v.tableHom σ).val.val p = ((σ (v.label p.2)).val p.1,p.2) := by
  have he := DFunLike.congr_fun v.tableHom_permutation σ
  exact DFunLike.congr_fun he p

noncomputable def polygonAssignment {ι : Type*} (U : ι → polygonAlgebra a)
    (p : GenericSquare a) : ι → Bool := by
  classical
  exact fun i => decide (p ∈ (U i).val)

theorem polygonAssignment_fiber_mem {ι : Type*} [Finite ι]
    (U : ι → polygonAlgebra a) (ω : ι → Bool) :
    {p | polygonAssignment U p = ω} ∈ polygonAlgebra a := by
  classical
  have he : {p | polygonAssignment U p = ω} =
      ⋂ i, if ω i then (U i).val else (U i).valᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff, polygonAssignment]
    apply forall_congr'
    intro i
    cases ω i <;> simp
  rw [he]
  apply BooleanSubalgebra.iInf_mem
  intro i
  cases ω i
  · exact BooleanSubalgebra.compl_mem (U i).property
  · exact (U i).property

noncomputable def actualPolygonLabelling {ι : Type*} [Finite ι]
    (U : ι → polygonAlgebra a) : PolygonLabelling a (Set.range (polygonAssignment U)) where
  label p := ⟨polygonAssignment U p,⟨p,rfl⟩⟩
  fiber_mem ω := by
    have he : {p | (⟨polygonAssignment U p,⟨p,rfl⟩⟩ : Set.range (polygonAssignment U)) = ω} =
        {p | polygonAssignment U p = ω.val} := by
      ext p
      exact Subtype.ext_iff
    rw [he]
    exact polygonAssignment_fiber_mem U ω.val

end PointwisePolygonTables

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InitialPointwiseTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceInitialPointwiseTable

variable {a m : ℕ} {ι : Type*} [Finite ι]

noncomputable def actualPolygonTableHom (U : ι → polygonAlgebra a) :
    (Set.range (polygonAssignment U) → alternatingGroup (Fin m)) →*
      polygonAlternatingGroup a m := by
  classical
  let := Fintype.ofFinite (Set.range (polygonAssignment U))
  exact (actualPolygonLabelling U).tableHom

@[simp] theorem actualPolygonTableHom_apply (U : ι → polygonAlgebra a)
    (σ : Set.range (polygonAssignment U) → alternatingGroup (Fin m))
    (p : TrackPoint a m) :
    (actualPolygonTableHom U σ).val.val p =
      ((σ ⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩).val p.1,p.2) := by
  classical
  let := Fintype.ofFinite (Set.range (polygonAssignment U))
  exact (actualPolygonLabelling U).tableHom_apply σ p

noncomputable def polygonTableInput (U : ι → polygonAlgebra a) (i : ι) :
    alternatingGroup (Fin m) →* (Set.range (polygonAssignment U) → alternatingGroup (Fin m)) :=
  sectorMask {ω | ω.val i = true}

@[simp] theorem actualPolygonTableHom_input (U : ι → polygonAlgebra a) (i : ι)
    (σ : alternatingGroup (Fin m)) :
    actualPolygonTableHom U (polygonTableInput U i σ) = conditionalAlternatingHom (U i) σ := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [actualPolygonTableHom_apply]
  change ((polygonTableInput U i σ ⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩).val p.1,p.2) =
    conditionalPerm (U i) σ.val p
  rw [conditionalPerm_apply]
  by_cases hp : p.2 ∈ (U i).val
  · have hω : (⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩ :
        Set.range (polygonAssignment U)) ∈ {ω | ω.val i = true} := by
      change decide (p.2 ∈ (U i).val) = true
      exact decide_eq_true hp
    rw [polygonTableInput, sectorMask_of_mem _ _ _ hω, ite_eq_left hp]
  · have hω : (⟨polygonAssignment U p.2,⟨p.2,rfl⟩⟩ :
        Set.range (polygonAssignment U)) ∉ {ω | ω.val i = true} := by
      change ¬decide (p.2 ∈ (U i).val) = true
      simpa only [decide_eq_true_eq] using hp
    rw [polygonTableInput, sectorMask_of_not_mem _ _ _ hω, ite_eq_right hp]
    rfl

def sourceConditionalLabel (m : ℕ)
    (b : Fin 5 × {σ : Equiv.Perm (Fin (m+1)) //
      σ ∈ alternatingGroup (Fin (m+1)) ∧ σ.support.card ≤ 5}) :
    SourceGeneratorLabel m := Sum.inl b

end SourceInitialPointwiseTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Sectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualSectors

variable {P E H Q Ω : Type*} [Group P] [Group E] [Group H] [Group Q]

theorem CentralOn.lift_unique [Group.IsPerfect P] (q : H →* Q) (S : Subgroup H)
    (h : CentralOn q S) (f g : P →* H) (hf : f.range ≤ S) (hg : g.range ≤ S)
    (he : q.comp f = q.comp g) : f = g := by
  let f' : P →* S := f.codRestrict S (fun x => hf ⟨x,rfl⟩)
  let g' : P →* S := g.codRestrict S (fun x => hg ⟨x,rfl⟩)
  have hh : f' = g' := perfect_lift_unique (q.comp S.subtype) h f' g' he
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun hh x)

structure ActualLawfulTable (q : H →* Q) (v : (Ω → E) →* Q) where
  carrier : Subgroup H
  law : CentralOn q carrier
  model : carrier →* (Ω → E)
  onto : Function.Surjective model
  projection : q.comp carrier.subtype = v.comp model

namespace ActualLawfulTable

variable {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem kernel_central : T.model.ker ≤ Subgroup.center T.carrier := by
  intro x hx
  apply T.law
  change q x.val = 1
  have he := DFunLike.congr_fun T.projection x
  change q x.val = v (T.model x) at he
  rw [he,show T.model x = 1 from hx,map_one]

variable [Group.IsPerfect E]

noncomputable def sector (U : Set Ω) : UniversalExtension E →* H :=
  T.carrier.subtype.comp (universalLift T.model T.onto T.kernel_central (sectorMask U))

theorem sector_mem (U : Set Ω) (s : UniversalExtension E) : T.sector U s ∈ T.carrier :=
  (universalLift T.model T.onto T.kernel_central (sectorMask U) s).property

theorem sector_projection (U : Set Ω) :
    q.comp (T.sector U) = (v.comp (sectorMask U)).comp (universalProjection E) := by
  unfold sector
  rw [← MonoidHom.comp_assoc,T.projection,MonoidHom.comp_assoc,
    universalLift_spec,← MonoidHom.comp_assoc]

@[simp] theorem sector_projection_apply (U : Set Ω) (s : UniversalExtension E) :
    q (T.sector U s) = v (sectorMask U (universalProjection E s)) :=
  DFunLike.congr_fun (T.sector_projection U) s

theorem sector_commute {U V : Set Ω} (h : Disjoint U V)
    (s t : UniversalExtension E) : Commute (T.sector U s) (T.sector V t) := by
  have hc := perfect_maps_commute_of_central T.model T.kernel_central
    (universalLift T.model T.onto T.kernel_central (sectorMask U))
    (universalLift T.model T.onto T.kernel_central (sectorMask V))
    (fun s t => by
      have hU := DFunLike.congr_fun (universalLift_spec T.model T.onto T.kernel_central (sectorMask U)) s
      have hV := DFunLike.congr_fun (universalLift_spec T.model T.onto T.kernel_central (sectorMask V)) t
      simp only [MonoidHom.comp_apply] at hU hV
      rw [hU,hV]
      exact sectorMask_commute h _ _) s t
  exact congrArg Subtype.val hc.eq

theorem sector_union {U V : Set Ω} (h : Disjoint U V) :
    T.sector (U ∪ V) = commutingProduct (T.sector U) (T.sector V)
      (T.sector_commute h) := by
  apply T.law.lift_unique q T.carrier
  · rintro x ⟨s,rfl⟩
    exact T.sector_mem _ s
  · rintro x ⟨s,rfl⟩
    exact T.carrier.mul_mem (T.sector_mem _ s) (T.sector_mem _ s)
  · ext s
    simp only [MonoidHom.comp_apply, commutingProduct_apply, map_mul]
    rw [T.sector_projection_apply,T.sector_projection_apply,T.sector_projection_apply]
    simp only [sectorMask_disjoint_union h,map_mul]

@[simp] theorem sector_empty : T.sector ∅ = 1 := by
  apply T.law.lift_unique q T.carrier
  · rintro x ⟨s,rfl⟩
    exact T.sector_mem _ s
  · intro x hx
    rw [MonoidHom.range_one] at hx
    have hx' : x = 1 := hx
    rw [hx']
    exact T.carrier.one_mem
  · rw [T.sector_projection]
    ext s
    simp only [MonoidHom.comp_apply,MonoidHom.one_apply,map_one]
    have he : sectorMask (∅ : Set Ω) (universalProjection E s) = 1 := by ext ω; simp [sectorMask]
    rw [he,map_one]

end ActualLawfulTable

end ActualSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TransitiveInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TransitiveInduction

open Classical _root_.CategoryTheory Representation Finsupp
namespace TransitiveInduction
variable {G X : Type} [Group G] [MulAction G X] (x : X)

noncomputable def permutationRep : Representation ℤ G (X →₀ ℤ) where
  toFun g := Finsupp.lmapDomain ℤ ℤ (g • ·)
  map_one' := by ext y z; simp
  map_mul' g h := by ext y z; simp [mul_smul]

@[simp] lemma permutationRep_single (g : G) (y : X) (z : ℤ) :
    permutationRep (G:=G) (X:=X) g (Finsupp.single y z)=Finsupp.single (g • y) z := by
  simp [permutationRep]

noncomputable def pointMap : Rep.trivial ℤ (MulAction.stabilizer G x) ℤ ⟶
    Rep.res (MulAction.stabilizer G x).subtype (Rep.of (permutationRep (G:=G) (X:=X))) :=
  Rep.ofHom ⟨Finsupp.lsingle x,by
    intro g
    apply LinearMap.ext
    intro z
    change Finsupp.single x z=permutationRep (G:=G) (X:=X) g.val (Finsupp.single x z)
    rw [permutationRep_single]
    exact congrArg (fun y => Finsupp.single y z) g.property.symm⟩

noncomputable def toPermutation :
    Rep.ind (MulAction.stabilizer G x).subtype (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ⟶
      Rep.of (permutationRep (G:=G) (X:=X)) :=
  (Rep.indResHomEquiv _ _ _).symm (pointMap (G:=G) x)

@[simp] theorem toPermutation_mk (g : G) (z : ℤ) :
    toPermutation (G:=G) x (IndV.mk (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) g z)=Finsupp.single (g⁻¹ • x) z := by
  simp [toPermutation,Rep.indResHomEquiv,pointMap]

end TransitiveInduction
end TransitiveInduction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BoundedHomologyEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory CategoryTheory.Limits

namespace BoundedHomologyEdge

universe u
variable {k G : Type u} [CommRing k] [Group G]

noncomputable abbrev Hmap {A B : Rep k G} (n : ℕ) (f : A ⟶ B) :
    groupHomology A n ⟶ groupHomology B n :=
  (groupHomology.functor k G n).map f

lemma Hmap_comp {A B C : Rep k G} (n : ℕ) (f : A ⟶ B) (g : B ⟶ C) :
    Hmap n (f ≫ g) = Hmap n f ≫ Hmap n g :=
  (groupHomology.functor k G n).map_comp f g

lemma epi_Hmap_zero {A B : Rep k G} (f : A ⟶ B) [Epi f] : Epi (Hmap 0 f) :=
  groupHomology.epi_map_0_of_epi f

lemma exact₂ {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
    (ShortComplex.mk (Hmap n X.f) (Hmap n X.g)
      (by rw [← Hmap_comp, X.zero]; exact (groupHomology.functor k G n).map_zero _ _)).Exact :=
  groupHomology.mapShortComplex₂_exact hX n

lemma exact₁ {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
    (ShortComplex.mk (groupHomology.δ hX (n+1) n rfl) (Hmap n X.f)
      (groupHomology.mapShortComplex₁ hX rfl).zero).Exact :=
  groupHomology.mapShortComplex₁_exact hX rfl

lemma exact₃ {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
    (ShortComplex.mk (Hmap (n+1) X.g) (groupHomology.δ hX (n+1) n rfl)
      (groupHomology.mapShortComplex₃ hX rfl).zero).Exact :=
  groupHomology.mapShortComplex₃_exact hX rfl

lemma epi_Hmap_succ_of_mono {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    [Mono (Hmap n X.f)] : Epi (Hmap (n+1) X.g) := by
  exact (exact₃ hX n).epi_f ((exact₁ hX n).mono_g_iff.mp (show Mono (Hmap n X.f) from inferInstance))

lemma epi_Hmap_succ_of_isZero {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    (h : IsZero (groupHomology X.X₁ n)) : Epi (Hmap (n+1) X.g) := by
  exact (exact₃ hX n).epi_f (h.eq_zero_of_tgt _)

lemma mono_Hmap_of_zero {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    (h : Hmap n X.f = 0) : Mono (Hmap n X.g) :=
  (exact₂ hX n).mono_g_iff.mpr h

lemma isZero_H0_quotient {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Epi (Hmap 0 X.f)] : IsZero (groupHomology X.X₃ 0) := by
  let : Epi X.g := hX.epi_g
  let : Epi (Hmap 0 X.g) := epi_Hmap_zero X.g
  exact IsZero.of_epi_eq_zero (Hmap 0 X.g) ((exact₂ hX 0).epi_f_iff.mp (show Epi (Hmap 0 X.f) from inferInstance))

lemma isIso_right_of_epi_left {A B C : ModuleCat k} (f : A ⟶ B) (g : B ⟶ C)
    [Epi f] [IsIso (f ≫ g)] : IsIso g := by
  let : Mono f := mono_of_mono f g
  let : IsIso f := isIso_of_mono_of_epi f
  exact IsIso.of_isIso_comp_left f g

section TwoKernels
variable {Z₁ Z₂ C₀ C₁ C₂ C₃ : Rep k G}
  {i₁ : Z₁ ⟶ C₁} {p₁ : C₁ ⟶ C₀} {i₂ : Z₂ ⟶ C₂} {p₂ : C₂ ⟶ Z₁}
  {w₁ : i₁ ≫ p₁ = 0} {w₂ : i₂ ≫ p₂ = 0}
  (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
  (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
  (e : C₃ ⟶ Z₂) [Epi e]

lemma isIso_H0_i₂ [IsIso (Hmap 0 (e ≫ i₂))] : IsIso (Hmap 0 i₂) := by
  let : Epi (Hmap 0 e) := epi_Hmap_zero e
  let : IsIso (Hmap 0 e ≫ Hmap 0 i₂) := by rw [← Hmap_comp]; infer_instance
  exact isIso_right_of_epi_left (Hmap 0 e) (Hmap 0 i₂)

include h₂

lemma isZero_H0_kernel [IsIso (Hmap 0 (e ≫ i₂))] :
    IsZero (groupHomology Z₁ 0) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  exact isZero_H0_quotient h₂

include h₁

lemma H1_isIso [IsIso (Hmap 0 (e ≫ i₂))]
    (hodd : Hmap 1 (p₂ ≫ i₁) = 0) : IsIso (Hmap 1 p₁) := by
  let : IsIso (Hmap 0 i₂) := isIso_H0_i₂ e
  let : Epi (Hmap 1 p₂) := epi_Hmap_succ_of_mono h₂ 0
  have hi : Hmap 1 i₁ = 0 := zero_of_epi_comp (Hmap 1 p₂) (by
    rw [← Hmap_comp]; exact hodd)
  let : Mono (Hmap 1 p₁) := mono_Hmap_of_zero h₁ 1 hi
  let : Epi (Hmap 1 p₁) := epi_Hmap_succ_of_isZero h₁ 0 (isZero_H0_kernel h₂ e)
  exact isIso_of_mono_of_epi (Hmap 1 p₁)

end TwoKernels

section KernelWindow

lemma exact_of_comp_mono {𝒞 : Type*} [Category 𝒞] [HasZeroMorphisms 𝒞]
    {A B C D : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (i : C ⟶ D) [Mono i]
    (w : f ≫ g = 0) (w' : f ≫ (g ≫ i) = 0)
    (h : (ShortComplex.mk f (g ≫ i) w').Exact) :
    (ShortComplex.mk f g w).Exact := by
  let φ : ShortComplex.mk f g w ⟶ ShortComplex.mk f (g ≫ i) w' :=
    { τ₁ := 𝟙 A, τ₂ := 𝟙 B, τ₃ := i, comm₁₂ := by simp, comm₂₃ := by simp }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr h

lemma kernel_shortExact {A B : Rep k G} (f : A ⟶ B) [Epi f] :
    (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).ShortExact :=
  { exact := ShortComplex.exact_kernel f, mono_f := inferInstance, epi_g := inferInstance }

variable {C₀ C₁ C₂ C₃ C₄ C₅ : Rep k G}
  (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃) (d₅ : C₅ ⟶ C₄)
  (w₂ : d₂ ≫ d₁ = 0) (w₃ : d₃ ≫ d₂ = 0) (w₄ : d₄ ≫ d₃ = 0) (w₅ : d₅ ≫ d₄ = 0)

noncomputable def lift₂ := kernel.lift d₁ d₂ w₂

@[simp] lemma lift₂_ι : lift₂ d₁ d₂ w₂ ≫ kernel.ι d₁ = d₂ := kernel.lift_ι _ _ _

include w₃ in
lemma comp_lift₂_zero : d₃ ≫ lift₂ d₁ d₂ w₂ = 0 := by
  apply zero_of_comp_mono (kernel.ι d₁)
  simpa only [Category.assoc, lift₂_ι] using w₃

noncomputable def lift₃ :=
  kernel.lift (lift₂ d₁ d₂ w₂) d₃ (comp_lift₂_zero d₁ d₂ d₃ w₂ w₃)

@[simp] lemma lift₃_ι : lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂) = d₃ :=
  kernel.lift_ι _ _ _

include w₄ in
lemma comp_lift₃_zero : d₄ ≫ lift₃ d₁ d₂ d₃ w₂ w₃ = 0 := by
  apply zero_of_comp_mono (kernel.ι (lift₂ d₁ d₂ w₂))
  simpa only [Category.assoc, lift₃_ι] using w₄

noncomputable def lift₄ :=
  kernel.lift (lift₃ d₁ d₂ d₃ w₂ w₃) d₄ (comp_lift₃_zero d₁ d₂ d₃ d₄ w₂ w₃ w₄)

@[simp] lemma lift₄_ι : lift₄ d₁ d₂ d₃ d₄ w₂ w₃ w₄ ≫
    kernel.ι (lift₃ d₁ d₂ d₃ w₂ w₃) = d₄ := kernel.lift_ι _ _ _

lemma epi_lift₂ (h : (ShortComplex.mk d₂ d₁ w₂).Exact) : Epi (lift₂ d₁ d₂ w₂) :=
  h.epi_kernelLift

lemma epi_lift₃ (h : (ShortComplex.mk d₃ d₂ w₃).Exact) : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := by
  have hh : (ShortComplex.mk d₃ (lift₂ d₁ d₂ w₂)
      (comp_lift₂_zero d₁ d₂ d₃ w₂ w₃)).Exact := by
    apply exact_of_comp_mono d₃ (lift₂ d₁ d₂ w₂) (kernel.ι d₁)
      (comp_lift₂_zero d₁ d₂ d₃ w₂ w₃) (by simpa using w₃)
    simpa using h
  exact hh.epi_kernelLift

lemma chain_H1_isIso [Epi d₁]
    (h₁ : (ShortComplex.mk d₂ d₁ w₂).Exact)
    (h₂ : (ShortComplex.mk d₃ d₂ w₃).Exact)
    [IsIso (Hmap 0 d₃)] (hodd : Hmap 1 d₂ = 0) : IsIso (Hmap 1 d₁) := by
  let : Epi (lift₂ d₁ d₂ w₂) := epi_lift₂ d₁ d₂ w₂ h₁
  let : Epi (lift₃ d₁ d₂ d₃ w₂ w₃) := epi_lift₃ d₁ d₂ d₃ w₂ w₃ h₂
  let : IsIso (Hmap 0 (lift₃ d₁ d₂ d₃ w₂ w₃ ≫ kernel.ι (lift₂ d₁ d₂ w₂))) := by
    simpa only [lift₃_ι] using (inferInstance : IsIso (Hmap 0 d₃))
  apply H1_isIso (kernel_shortExact d₁) (kernel_shortExact (lift₂ d₁ d₂ w₂))
    (lift₃ d₁ d₂ d₃ w₂ w₃)
  simpa only [lift₂_ι] using hodd

end KernelWindow

end BoundedHomologyEdge

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_CanonicalShapiro
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits Finsupp Representation Rep TensorProduct

universe u
namespace CanonicalShapiro
variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def barLift (f : G →* H) (n : ℕ) :
    Rep.free k G (Fin n → G) ⟶ Rep.res f (Rep.free k H (Fin n → H)) :=
  Rep.freeLift k G _ (fun x => Finsupp.single (f ∘ x) (MonoidAlgebra.single 1 1))

@[simp] lemma barLift_single (f : G →* H) (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (barLift (k:=k) f n).hom (single x (MonoidAlgebra.single g r)) =
      single (f ∘ x) (MonoidAlgebra.single (f g) r) := by
  simp [barLift, Representation.freeLift_single_single]

lemma barLift_d (f : G →* H) (n : ℕ) :
    Rep.barComplex.d k G n ≫ barLift f n =
      barLift f (n+1) ≫ (Rep.resFunctor.{u,u,u,u} f).map (Rep.barComplex.d k H n) := by
  apply Rep.free_ext
  intro x
  change (barLift (k:=k) f n).hom
      ((Rep.barComplex.d k G n).hom (single x (MonoidAlgebra.single 1 1))) =
    (Rep.barComplex.d k H n).hom
      ((barLift (k:=k) f (n+1)).hom (single x (MonoidAlgebra.single 1 1)))
  rw [Rep.barComplex.d_single, barLift_single, map_one, Rep.barComplex.d_single]
  simp only [map_add, map_sum]
  congr 1
  · rw [barLift_single]
    rfl
  · apply Finset.sum_congr rfl
    intro j hj
    rw [barLift_single, map_one]
    congr 1
    simp [Fin.comp_contractNth]

noncomputable def barMap (f : G →* H) : Rep.barComplex k G ⟶
    ((Rep.resFunctor.{u,u,u,u} f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex k H) where
  f n := barLift f n
  comm' i j h := by
    subst h
    show barLift (k:=k) f (j+1) ≫ (Rep.resFunctor.{u,u,u,u} f).map ((Rep.barComplex k H).d (j+1) j) = (Rep.barComplex k G).d (j+1) j ≫ barLift (k:=k) f j
    simp only [Rep.barComplex, ChainComplex.of_d]
    exact (barLift_d (k:=k) f j).symm

lemma diagonal_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom (single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial,
    Iso.trans_inv, Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single x (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single g 1 ⊗ₜ[k] MonoidAlgebra.single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Action.tensorObj_V, Rep.tensor_V, Rep.tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      simp only [one_mul]
      congr 1
      exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x)

@[simp] lemma bar_π_zero_single (x : Fin 0 → G) (g : G) (r : k) :
    ((Rep.barResolution k G).π.f 0).hom (single x (MonoidAlgebra.single g r)) = r := by
  change (Rep.standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom (single x (MonoidAlgebra.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

lemma barMap_π (S : Subgroup G) :
    barMap (k:=k) S.subtype ≫
      ((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution (Rep.barResolution k G)).π =
        (Rep.barResolution k S).π := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  apply Rep.free_ext
  intro x
  change (((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution
    (Rep.barResolution k G)).π.f 0).hom
      ((barLift S.subtype 0).hom (single x (MonoidAlgebra.single 1 1))) = _
  rw [barLift_single]
  change ((Rep.barResolution k G).π.f 0).hom
    (single (S.subtype ∘ x) (MonoidAlgebra.single (S.subtype 1) 1)) = _
  change ((Rep.barResolution k G).π.f 0).hom
    (single (S.subtype ∘ x) (MonoidAlgebra.single (S.subtype 1) 1)) =
      ((Rep.barResolution k S).π.f 0).hom (single x (MonoidAlgebra.single 1 1))
  rw [bar_π_zero_single, bar_π_zero_single]
noncomputable def barComparison (S : Subgroup G) :
    HomotopyEquiv (Rep.barComplex k S)
      (((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution (Rep.barResolution k G)).complex) :=
  (ProjectiveResolution.homotopyEquiv (Rep.barResolution k S)
    ((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution (Rep.barResolution k G))).copy
    (ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial k S k)) _ (barMap S.subtype)
      (by
        change _ = (Rep.barResolution k S).π ≫
          (ChainComplex.single₀ (Rep k S)).map (𝟙 (Rep.trivial k S k))
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
        exact ProjectiveResolution.homotopyEquiv_hom_π _ _)
      (by
        change _ = (Rep.barResolution k S).π ≫
          (ChainComplex.single₀ (Rep k S)).map (𝟙 (Rep.trivial k S k))
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
        exact barMap_π (k:=k) S))

@[simp] lemma barComparison_hom (S : Subgroup G) :
    (barComparison (k:=k) S).hom = barMap S.subtype := rfl

noncomputable def indUnit (f : G →* H) (A : Rep.{u} k G) : A ⟶ Rep.res f (Rep.ind.{u,u,u,u} f A) :=
  Rep.indResHomEquiv f A (Rep.ind.{u,u,u,u} f A) (𝟙 _)

@[simp] lemma indUnit_apply (f : G →* H) (A : Rep.{u} k G) (a : A) :
    (indUnit f A).hom a = Representation.IndV.mk f A.ρ 1 a := by
  simp [indUnit, Rep.indResHomEquiv]

@[simp] lemma coinvariantsTensor_map_mk {A B C : Rep.{u} k G} (f : B ⟶ C) (a : A) (b : B) :
    (((Rep.coinvariantsTensor k G).obj A).map f) (Rep.coinvariantsTensorMk A B a b) =
      Rep.coinvariantsTensorMk A C a (f.hom b) := by
  simp [Rep.coinvariantsTensor, Rep.coinvariantsTensorMk]

noncomputable def tensorBarMap (S : Subgroup G) (A : Rep.{u} k S) :
    (Rep.barComplex k S).coinvariantsTensorObj A ⟶
      (((Rep.resFunctor.{u,u,u,u} S.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).complex).coinvariantsTensorObj A :=
  (((Rep.coinvariantsTensor k S).obj A).mapHomologicalComplex _).map (barMap S.subtype)

lemma chainsIso_hom_single (A : Rep.{u} k G) [DecidableEq G]
    (n : ℕ) (x : Fin n → G) (a : A) :
    (groupHomology.inhomogeneousChainsIso A).hom.f n (single x a) =
      Rep.coinvariantsTensorMk A (Rep.free k G (Fin n → G)) a
        (single x (MonoidAlgebra.single 1 1)) := by
  change (Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)).symm (single x a) = _
  exact Rep.finsuppToCoinvariantsTensorFree_single x a

lemma chainsIso_inv_mk_single (A : Rep.{u} k G) [DecidableEq G]
    (n : ℕ) (x : Fin n → G) (a : A) :
    (groupHomology.inhomogeneousChainsIso A).inv.f n
      (Rep.coinvariantsTensorMk A (Rep.free k G (Fin n → G)) a
        (single x (MonoidAlgebra.single 1 1))) = single x a := by
  rw [← chainsIso_hom_single]
  exact congrArg (fun f : groupHomology.inhomogeneousChains A ⟶
      groupHomology.inhomogeneousChains A => f.f n (single x a))
    (Iso.hom_inv_id (groupHomology.inhomogeneousChainsIso A))

lemma tensorBarMap_f_mk (S : Subgroup G) (A : Rep.{u} k S)
    (n : ℕ) (x : Fin n → S) (a : A) :
    (tensorBarMap S A).f n
      (Rep.coinvariantsTensorMk A (Rep.free k S (Fin n → S)) a
        (single x (MonoidAlgebra.single 1 1))) =
      Rep.coinvariantsTensorMk A (Rep.res S.subtype (Rep.free k G (Fin n → G))) a
        (single (S.subtype ∘ x) (MonoidAlgebra.single 1 1)) := by
  change (((Rep.coinvariantsTensor k S).obj A).map (barLift S.subtype n)) _ = _
  rw [coinvariantsTensor_map_mk, barLift_single, map_one]

noncomputable def resTensorIso (S : Subgroup G) (A : Rep.{u} k S) :
    ((((Rep.resFunctor.{u,u,u,u} S.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Rep.barComplex k G)).coinvariantsTensorObj A) ≅
      (Rep.barComplex k G).coinvariantsTensorObj (Rep.ind.{u,u,u,u} S.subtype A) :=
  groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution k G)

lemma resTensorIso_hom_f (S : Subgroup G) (A : Rep.{u} k S) (n : ℕ) :
    (resTensorIso S A).hom.f n =
      Rep.coinvariantsTensorIndInv S.subtype A (Rep.free k G (Fin n → G)) := rfl

lemma resIso_hom_f_mk (S : Subgroup G) (A : Rep.{u} k S)
    (n : ℕ) (b : Rep.free k G (Fin n → G)) (a : A) :
    (resTensorIso S A).hom.f n
      (Rep.coinvariantsTensorMk A (Rep.res S.subtype (Rep.free k G (Fin n → G))) a b) =
      Rep.coinvariantsTensorMk (Rep.ind.{u,u,u,u} S.subtype A) (Rep.free k G (Fin n → G))
        (Representation.IndV.mk S.subtype A.ρ 1 a) b := by
  rw [resTensorIso_hom_f]
  exact Rep.coinvariantsTensorIndInv_mk_tmul_indMk S.subtype a b

lemma chainsMap_factorization (S : Subgroup G) (A : Rep.{u} k S) [DecidableEq G] :
    groupHomology.chainsMap S.subtype (indUnit S.subtype A) =
      (groupHomology.inhomogeneousChainsIso A).hom ≫ tensorBarMap S A ≫
      (resTensorIso S A).hom ≫
      (groupHomology.inhomogeneousChainsIso (Rep.ind.{u,u,u,u} S.subtype A)).inv := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  change (groupHomology.chainsMap S.subtype (indUnit S.subtype A)).f n (single x a) = _
  rw [groupHomology.chainsMap_f_single]
  change _ = (groupHomology.inhomogeneousChainsIso (Rep.ind.{u,u,u,u} S.subtype A)).inv.f n
    ((resTensorIso S A).hom.f n
      ((tensorBarMap S A).f n ((groupHomology.inhomogeneousChainsIso A).hom.f n (single x a))))
  rw [chainsIso_hom_single, tensorBarMap_f_mk, resIso_hom_f_mk, chainsIso_inv_mk_single,
    indUnit_apply]

noncomputable def chainsEquivalence (S : Subgroup G) (A : Rep.{u} k S) [DecidableEq G] :
    HomotopyEquiv (groupHomology.inhomogeneousChains A)
      (groupHomology.inhomogeneousChains (Rep.ind.{u,u,u,u} S.subtype A)) :=
  (HomotopyEquiv.ofIso (groupHomology.inhomogeneousChainsIso A)).trans
    ((((Rep.coinvariantsTensor k S).obj A).mapHomotopyEquiv (barComparison S)).trans
      ((HomotopyEquiv.ofIso (resTensorIso S A)).trans
        (HomotopyEquiv.ofIso (groupHomology.inhomogeneousChainsIso
          (Rep.ind.{u,u,u,u} S.subtype A)).symm)))

lemma chainsEquivalence_hom (S : Subgroup G) (A : Rep.{u} k S) [DecidableEq G] :
    (chainsEquivalence S A).hom =
      groupHomology.chainsMap S.subtype (indUnit S.subtype A) :=
  (chainsMap_factorization S A).symm

lemma isIso_map_indUnit (S : Subgroup G) (A : Rep.{u} k S) (n : ℕ) :
    IsIso (groupHomology.map S.subtype (indUnit S.subtype A) n) := by
  classical
  change IsIso (HomologicalComplex.homologyMap
    (groupHomology.chainsMap S.subtype (indUnit S.subtype A)) n)
  rw [← chainsEquivalence_hom]
  exact (chainsEquivalence S A).toHomologyIso n |>.isIso_hom

end CanonicalShapiro

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ConjugationNatural
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory CategoryTheory.Limits Finsupp Representation Rep
universe u
namespace HomologyConjugation
variable {k G : Type u} [CommRing k] [Group G]

noncomputable def rightBarLift (c : G) (n : ℕ) :
    Rep.free k G (Fin n → G) ⟶ Rep.free k G (Fin n → G) :=
  Rep.freeLift k G _ (fun x => Finsupp.single ((MulAut.conj c) ∘ x)
    (MonoidAlgebra.single c⁻¹ 1))

@[simp] lemma rightBarLift_single (c : G) (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (rightBarLift (k:=k) c n).hom (single x (MonoidAlgebra.single g r)) =
      single ((MulAut.conj c) ∘ x) (MonoidAlgebra.single (g*c⁻¹) r) := by
  simp [rightBarLift, Representation.freeLift_single_single]

lemma bar_d_weighted (n : ℕ) (x : Fin (n+1) → G) (g : G) (r : k) :
    (Rep.barComplex.d k G n).hom (single x (MonoidAlgebra.single g r)) =
      single (fun i => x i.succ) (MonoidAlgebra.single (g*x 0) r) +
        ∑j : Fin (n+1), single (Fin.contractNth j (·*·) x)
          (MonoidAlgebra.single g (r*((-1:k)^(j.val+1)))) := by
  simp [Rep.barComplex.d, ← Representation.IntertwiningMap.toLinearMap_apply,
    smul_add, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul]

lemma rightBarLift_d (c : G) (n : ℕ) :
    Rep.barComplex.d k G n ≫ rightBarLift c n =
      rightBarLift c (n+1) ≫ Rep.barComplex.d k G n := by
  apply Rep.free_ext
  intro x
  change (rightBarLift (k:=k) c n).hom
      ((Rep.barComplex.d k G n).hom (single x (MonoidAlgebra.single 1 1))) =
    (Rep.barComplex.d k G n).hom
      ((rightBarLift (k:=k) c (n+1)).hom (single x (MonoidAlgebra.single 1 1)))
  rw [Rep.barComplex.d_single, rightBarLift_single, bar_d_weighted]
  simp only [map_add, map_sum]
  apply congrArg₂ (·+·)
  · rw [rightBarLift_single]
    congr 1
    simp [MulAut.conj_apply, mul_assoc]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [rightBarLift_single]
    congr 1
    · exact Fin.comp_contractNth (·*·) (·*·) (map_mul (MulAut.conj c)) j x
    · simp

noncomputable def rightBarMap (c : G) : Rep.barComplex k G ⟶ Rep.barComplex k G where
  f n := rightBarLift c n
  comm' i j h := by subst h; simpa [ChainComplex.of.d] using (rightBarLift_d (k:=k) c j).symm

lemma rightBarMap_π (c : G) :
    rightBarMap (k:=k) c ≫ (Rep.barResolution k G).π = (Rep.barResolution k G).π := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution k G).π.f 0).hom
      ((rightBarLift c 0).hom (single x (MonoidAlgebra.single 1 1))) =
    ((Rep.barResolution k G).π.f 0).hom (single x (MonoidAlgebra.single 1 1))
  rw [rightBarLift_single, CanonicalShapiro.bar_π_zero_single, CanonicalShapiro.bar_π_zero_single]

noncomputable def rightBarHomotopy (c : G) :
    Homotopy (rightBarMap (k:=k) c) (𝟙 (Rep.barComplex k G)) :=
  ProjectiveResolution.liftHomotopy (𝟙 (Rep.trivial k G k))
    (P:=Rep.barResolution k G) (Q:=Rep.barResolution k G) _ _
    (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact rightBarMap_π (k:=k) c) (by dsimp only [Rep.barResolution]; simp)

noncomputable def conjugationCoeff (c : G) (A : Rep.{u} k G) :
    A ⟶ Rep.res (MulAut.conj c).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ c, by
    intro g
    ext a
    simp [MulAut.conj_apply, ← Module.End.mul_apply, ← map_mul, mul_assoc]⟩

@[simp] lemma conjugationCoeff_apply (c : G) (A : Rep.{u} k G) (a : A) :
    (conjugationCoeff c A).hom a = A.ρ c a := rfl

lemma chainsIso_inv_weighted (A : Rep.{u} k G) [DecidableEq G]
    (n : ℕ) (x : Fin n → G) (a : A) (g : G) (r : k) :
    (groupHomology.inhomogeneousChainsIso A).inv.f n
      (Rep.coinvariantsTensorMk A (Rep.free k G (Fin n → G)) a
        (single x (MonoidAlgebra.single g r))) = single x (r • A.ρ g⁻¹ a) := by
  change Rep.coinvariantsTensorFreeToFinsupp A _ _ = _
  exact Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single A a x g r

lemma conjugation_factorization (c : G) (A : Rep.{u} k G) [DecidableEq G] :
    groupHomology.chainsMap (MulAut.conj c).toMonoidHom (conjugationCoeff c A) =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map (rightBarMap c) ≫
      (groupHomology.inhomogeneousChainsIso A).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change (groupHomology.chainsMap (MulAut.conj c).toMonoidHom (conjugationCoeff c A)).f n (single x a) = _
  rw [groupHomology.chainsMap_f_single]
  change single ((MulAut.conj c) ∘ x) (A.ρ c a) =
    (groupHomology.inhomogeneousChainsIso A).inv.f n
      ((((Rep.coinvariantsTensor k G).obj A).map (rightBarLift c n))
        ((groupHomology.inhomogeneousChainsIso A).hom.f n (single x a)))
  rw [CanonicalShapiro.chainsIso_hom_single, CanonicalShapiro.coinvariantsTensor_map_mk,
    rightBarLift_single, chainsIso_inv_weighted]
  simp

lemma map_conjugation (c : G) (A : Rep.{u} k G) (n : ℕ) :
    groupHomology.map (MulAut.conj c).toMonoidHom (conjugationCoeff c A) n =
      𝟙 (groupHomology A n) := by
  classical
  let F := (Rep.coinvariantsTensor k G).obj A
  have hh := ((F.mapHomotopy (rightBarHomotopy (k:=k) c)).compLeft
    (groupHomology.inhomogeneousChainsIso A).hom).compRight
    (groupHomology.inhomogeneousChainsIso A).inv
  have hm : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (𝟙 (Rep.barComplex k G)) = 𝟙 _ :=
    (F.mapHomologicalComplex _).map_id _
  rw [hm] at hh
  have he : Homotopy (groupHomology.chainsMap (MulAut.conj c).toMonoidHom
      (conjugationCoeff c A)) (𝟙 _) := by
    rw [conjugation_factorization]
    simpa only [Category.id_comp, Iso.hom_inv_id, Category.assoc] using hh
  exact he.homologyMap_eq n |>.trans (HomologicalComplex.homologyMap_id _ _)

variable {H : Type u} [Group H]

lemma map_after_conjugation (f : H →* G) {B : Rep.{u} k H} {A : Rep.{u} k G}
    (φ : B ⟶ Rep.res f A) (c : G) (n : ℕ) :
    groupHomology.map ((MulAut.conj c).toMonoidHom.comp f)
      (φ ≫ (Rep.resFunctor.{u,u,u,u} f).map (conjugationCoeff c A)) n =
      groupHomology.map f φ n := by
  rw [groupHomology.map_comp, map_conjugation, Category.comp_id]

lemma map_eq_of_centralizer (f : H →* G) {B : Rep.{u} k H} {A : Rep.{u} k G}
    (φ ψ : B ⟶ Rep.res f A) (c : G) (hc : ∀h,c*f h=f h*c)
    (hψ : ∀b,ψ.hom b=A.ρ c (φ.hom b)) (n : ℕ) :
    groupHomology.map f ψ n = groupHomology.map f φ n := by
  have he : (MulAut.conj c).toMonoidHom.comp f=f := by
    ext h
    change c * f h * c⁻¹=f h
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have ht := groupHomology.map_congr (A:=B) (B:=A) (n:=n)
    (f:=(MulAut.conj c).toMonoidHom.comp f) (g:=f)
    (φ:=φ ≫ (Rep.resFunctor.{u,u,u,u} f).map (conjugationCoeff c A)) (ψ:=ψ) he
    (by apply LinearMap.ext; intro b; exact (hψ b).symm)
  exact ht.symm.trans (map_after_conjugation f φ c n)

end HomologyConjugation

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TransitiveCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

noncomputable def equivariantMap (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) :
    Rep.of (permutationRep (G:=G) (X:=X)) ⟶
      Rep.of (permutationRep (G:=G) (X:=Y)) :=
  Rep.ofHom ⟨Finsupp.lmapDomain ℤ ℤ f, by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    simp [permutationRep, hf]⟩

@[simp] lemma equivariantMap_single (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x)
    (x : X) (z : ℤ) : (equivariantMap f hf).hom (Finsupp.single x z) =
      Finsupp.single (f x) z := by
  simp [equivariantMap]

end SimpleAmenable.TransitiveInduction

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_HomologyAdditive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open _root_.CategoryTheory Representation Rep Finsupp
universe u
namespace HomologyAdditive
variable {k G H : Type u} [CommRing k] [Group G] [Group H]

lemma chainsMap_add (f : G →* H) {A : Rep.{u} k G} {B : Rep.{u} k H}
    (φ ψ : A ⟶ Rep.res f B) :
    groupHomology.chainsMap f (φ+ψ) = groupHomology.chainsMap f φ + groupHomology.chainsMap f ψ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change (groupHomology.chainsMap f (φ+ψ)).f n (single x a) =
    (groupHomology.chainsMap f φ).f n (single x a) +
    (groupHomology.chainsMap f ψ).f n (single x a)
  rw [groupHomology.chainsMap_f_single, groupHomology.chainsMap_f_single,
    groupHomology.chainsMap_f_single]
  change single _ (φ.hom a + ψ.hom a)=_
  exact Finsupp.single_add _ _ _

instance additive (n : ℕ) : (groupHomology.functor k G n).Additive where
  map_add {A B φ ψ} := by
    change HomologicalComplex.homologyMap (groupHomology.chainsMap (MonoidHom.id G) (φ+ψ)) n = _
    rw [chainsMap_add, HomologicalComplex.homologyMap_add]
    rfl

end HomologyAdditive

end

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEquivalence
attribute [-instance] _root_.OAI.HomologyAdditive.additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory SimplicialObject Simplicial Opposite MonoidalCategory
namespace CategoryTheory.nerve
open scoped _root_.CategoryTheory _root_.CategoryTheory.nerve
lemma connected_of_hom {C : Type} [_root_.CategoryTheory.Category C] [Nonempty C]
    (h : ∀ x y : C,Nonempty (x ⟶ y)) : (_root_.CategoryTheory.nerve C).IsConnected where
  allEq u v := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective v
    exact SSet.π₀.sound (_root_.CategoryTheory.nerve.homEquiv.symm (Classical.choice (h (_root_.CategoryTheory.nerveEquiv x) (_root_.CategoryTheory.nerveEquiv y))))
  nonempty := ⟨nerveEquiv.symm (Classical.arbitrary C)⟩
end CategoryTheory.nerve

end

open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SimplicialH0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace BarHomology

abbrev D := SimplexCategory × SimplexCategory
end BarHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits SimplicialObject Simplicial Opposite MonoidalCategory
namespace SimplicialDiagonal

lemma connected_of_iso {X Y : SSet} (e : X ≅ Y) [Y.IsConnected] : X.IsConnected where
  allEq u v := by
    have h := congrArg (SSet.mapπ₀ e.inv) (Subsingleton.elim (SSet.mapπ₀ e.hom u) (SSet.mapπ₀ e.hom v))
    simpa only [←SSet.mapπ₀_comp_apply,Iso.hom_inv_id,SSet.mapπ₀_id_apply] using h
  nonempty := ⟨e.inv.app _ (Classical.arbitrary _)⟩
end SimplicialDiagonal
namespace CategoryTheory.nerve
open scoped _root_.CategoryTheory _root_.CategoryTheory.nerve

lemma const_map {C : Type} [_root_.CategoryTheory.Category.{0} C] (c : C) :
    _root_.CategoryTheory.nerveMap ((_root_.CategoryTheory.Functor.const C).obj c) = SSet.const (nerveEquiv.symm c) := by
  ext n x
  rfl
end CategoryTheory.nerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FilteredHomology
attribute [-instance] _root_.OAI.HomologyAdditive.additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace FilteredHomology

variable {J : Type} [Category.{0} J] [IsFiltered J]
abbrev A := ModuleCat.{0} ℤ
abbrev c := ComplexShape.down ℕ
noncomputable def complex (F : J ⥤ ChainComplex A ℕ) : ChainComplex (J ⥤ A) ℕ where
  X i := F ⋙ HomologicalComplex.eval A c i
  d i j := { app t := (F.obj t).d i j
             naturality _ _ f := (F.map f).comm i j }
  shape i j h := by apply NatTrans.ext; funext t; exact (F.obj t).shape i j h
  d_comp_d' i j k _ _ := by apply NatTrans.ext; funext t; exact (F.obj t).d_comp_d i j k
noncomputable def injection (j : J) : (evaluation J A).obj j ⟶ colim where
  app F := colimit.ι F j
  naturality _ _ f := (colimit.ι_map f j).symm
noncomputable def cocone (F : J ⥤ ChainComplex A ℕ) : Cocone F where
  pt := (colim.mapHomologicalComplex c).obj (complex F)
  ι := {
    app j := {
      f i := colimit.ι ((complex F).X i) j
      comm' i k _ := colimit.ι_map ((complex F).d i k) j }
    naturality i j f := by
      apply HomologicalComplex.Hom.ext; funext n
      exact colimit.w (F ⋙ HomologicalComplex.eval A c n) f }
noncomputable def isColimit (F : J ⥤ ChainComplex A ℕ) : IsColimit (cocone F) :=
  HomologicalComplex.isColimitOfEval F (cocone F) (fun _ => colimit.isColimit _)
noncomputable def evaluationHomology (F : J ⥤ ChainComplex A ℕ) (n : ℕ) (j:J) :
    (F.obj j).homology n ≅ ((complex F).homology n).obj j :=
  ((complex F).sc n).mapHomologyIso ((evaluation J A).obj j)
noncomputable def colimitHomology (F : J ⥤ ChainComplex A ℕ) (n : ℕ) :
    (cocone F).pt.homology n ≅ colimit ((complex F).homology n) :=
  ((complex F).sc n).mapHomologyIso colim
lemma homology_injection (F : J ⥤ ChainComplex A ℕ) (n : ℕ) (j:J) :
    HomologicalComplex.homologyMap ((cocone F).ι.app j) n =
      (evaluationHomology F n j).hom ≫ colimit.ι ((complex F).homology n) j ≫
        (colimitHomology F n).inv :=
  ShortComplex.homologyMap_mapNatTrans ((complex F).sc n) (injection j)
omit [IsFiltered J] in
lemma evaluationHomology_naturality (F : J ⥤ ChainComplex A ℕ) (n : ℕ) {i j:J} (f:i⟶j) :
    HomologicalComplex.homologyMap (F.map f) n ≫ (evaluationHomology F n j).hom =
      (evaluationHomology F n i).hom ≫ ((complex F).homology n).map f := by
  have h := ShortComplex.homologyMap_mapNatTrans ((complex F).sc n) ((evaluation J A).map f)
  change HomologicalComplex.homologyMap (F.map f) n =
    (evaluationHomology F n i).hom ≫ ((complex F).homology n).map f ≫
      (evaluationHomology F n j).inv at h
  rw [h]
  simp [Category.assoc]
noncomputable def homologyCocone (F : J ⥤ ChainComplex A ℕ) (n : ℕ)
    (d : Cocone (F ⋙ HomologicalComplex.homologyFunctor A c n)) :
    Cocone ((complex F).homology n) where
  pt := d.pt
  ι := { app j := (evaluationHomology F n j).inv ≫ d.ι.app j
         naturality i j f := by
           have h := evaluationHomology_naturality F n f
           rw [←Iso.inv_comp_eq] at h
           erw [Category.assoc ((evaluationHomology F n i).inv), ←h]
           erw [Category.assoc ((evaluationHomology F n i).inv),
             Category.assoc (HomologicalComplex.homologyMap (F.map f) n),
             Iso.hom_inv_id_assoc (evaluationHomology F n j)]
           simp only [Functor.const_obj_map]
           exact congrArg (fun t => (evaluationHomology F n i).inv ≫ t) (d.w f) }
noncomputable def homologyIsColimit (F : J ⥤ ChainComplex A ℕ) (n : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor A c n).mapCocone (cocone F)) where
  desc d := (colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)
  fac d j := by
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫ _ = _
    rw [homology_injection]
    erw [Category.assoc (evaluationHomology F n j).hom,
      Category.assoc (colimit.ι ((complex F).homology n) j),
      Iso.inv_hom_id_assoc (colimitHomology F n), colimit.ι_desc]
    change (evaluationHomology F n j).hom ≫ ((evaluationHomology F n j).inv ≫ d.ι.app j) = _
    exact Iso.hom_inv_id_assoc _ _
  uniq d m hm := by
    apply (cancel_epi (colimitHomology F n).inv).mp
    erw [Iso.inv_hom_id_assoc]
    apply colimit.hom_ext
    intro j
    have h := hm j
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫ m = _ at h
    rw [homology_injection] at h
    have he := congrArg (fun t => (evaluationHomology F n j).inv ≫ t) h
    erw [Category.assoc (evaluationHomology F n j).hom,
      Iso.inv_hom_id_assoc (evaluationHomology F n j),
      Category.assoc (colimit.ι ((complex F).homology n) j)] at he
    erw [colimit.ι_desc]
    exact he
noncomputable instance homology_preserves (n : ℕ) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor A c n) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone (isColimit F) (homologyIsColimit F n)
end FilteredHomology

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace FilteredHomology

variable {J : Type} [Category.{0} J]
noncomputable instance chain_preserves (Z : A) :
    PreservesColimitsOfShape J ((SSet.chainComplexFunctor A).obj Z) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J ((evaluation SimplexCategoryᵒᵖ (Type)).obj (op ⦋n⦌) ⋙ sigmaConst.obj Z)
  infer_instance
noncomputable instance sset_homology_preserves [IsFiltered J] (Z : A) (n:ℕ) :
    PreservesColimitsOfShape J (SSet.homologyFunctor Z n) := by
  change PreservesColimitsOfShape J (((SSet.chainComplexFunctor A).obj Z) ⋙
    HomologicalComplex.homologyFunctor A c n)
  infer_instance
end FilteredHomology

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PowerEquivalence
attribute [-instance] _root_.OAI.HomologyAdditive.additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace ColimitTransfer

universe u v w z
variable {J : Type u} [Category.{v} J] {C : Type w} [Category.{z} C]
noncomputable def ofIsos {F G : J ⥤ C} (s : Cocone F) (t : Cocone G)
    (u : F ⟶ G) [IsIso u] (f : s.pt ⟶ t.pt) [IsIso f]
    (comm : ∀j,s.ι.app j ≫ f=u.app j ≫ t.ι.app j) (ht : IsColimit t) : IsColimit s := by
  let e := asIso u
  have hnat (j:J) : (((Cocone.precompose e.inv).obj s).ι.app j) ≫ f=t.ι.app j := by
    change ((inv u).app j ≫ s.ι.app j) ≫ f = _
    rw [Category.assoc,comm]
    simp
  exact (IsColimit.equivOfNatIsoOfIso e s t (Cocone.ext (asIso f) hnat)).symm ht
noncomputable abbrev H (q:ℕ) : Cat.{0,0} ⥤ ModuleCat ℤ :=
  nerveFunctor ⋙ SSet.homologyFunctor (ModuleCat.of ℤ ℤ) q
end ColimitTransfer

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageTripleHomology
attribute [-instance] _root_.OAI.HomologyAdditive.additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace ColimitTransfer

universe u v
variable {J : Type} {A : Type u} [Category.{0} J] [Category.{v} A]
noncomputable def transportDiagram (F : J ⥤ A) (X : J → A) (e : ∀j,X j≅F.obj j) : J ⥤ A where
  obj := X
  map {i j} f := (e i).hom ≫ F.map f ≫ (e j).inv
  map_id i := by simp
  map_comp f g := by simp [Category.assoc]
noncomputable def transportIso (F : J ⥤ A) (X : J → A) (e : ∀j,X j≅F.obj j) :
    transportDiagram F X e ≅ F := NatIso.ofComponents e (by intro i j f; simp [transportDiagram])
noncomputable def transportCocone {F : J ⥤ A} (s : Cocone F) (X : J → A)
    (e : ∀j,X j≅F.obj j) (Y : A) (d : Y≅s.pt) : Cocone (transportDiagram F X e) where
  pt := Y
  ι := { app j := (e j).hom ≫ s.ι.app j ≫ d.inv
         naturality i j f := by simp [transportDiagram,Category.assoc] }
noncomputable def transportIsColimit {F : J ⥤ A} (s : Cocone F) (X : J → A)
    (e : ∀j,X j≅F.obj j) (Y : A) (d : Y≅s.pt) (hs : IsColimit s) :
    IsColimit (transportCocone s X e Y d) := by
  let pointIso : (transportCocone s X e Y d).pt ≅ s.pt := d
  refine ofIsos (transportCocone s X e Y d) s (transportIso F X e).hom pointIso.hom ?_ hs
  intro j
  change ((e j).hom ≫ s.ι.app j ≫ d.inv) ≫ d.hom =
    (e j).hom ≫ s.ι.app j
  simp [Category.assoc]
end ColimitTransfer

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageRefinementMonoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
namespace IntervalBar.Diagram

universe u v u' v' w
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
    {F G : C ⥤ D} [F.Braided] [G.Braided]
    {I : Type w} [Preorder I]
lemma monoidalNatTrans_eta (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    α.app (𝟙_ C) ≫ η G=η F := by
  apply (cancel_epi (ε F)).mp
  rw [←Category.assoc,NatTrans.IsMonoidal.unit,Functor.Monoidal.ε_η,Functor.Monoidal.ε_η]

end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace NerveHomotopy
universe u v
variable {C D C' D' : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} C'] [Category.{v} D']
lemma functor_map_heq {H K : C ⥤ D} (h:H=K) {X Y:C} (f:X⟶Y) : HEq (H.map f) (K.map f) := by cases h; rfl
lemma comp_heq {X Y Z X' Y' Z' : D} (hX:X=X') (hY:Y=Y') (hZ:Z=Z')
    {f:X⟶Y} {g:Y⟶Z} {f':X'⟶Y'} {g':Y'⟶Z'} (hf:HEq f f') (hg:HEq g g') :
    HEq (f≫g) (f'≫g') := by subst X';subst Y';subst Z'; cases hf;cases hg;rfl
end NerveHomotopy

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PiSSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet

variable {ι:Type} (X:ι→SSet)
noncomputable def obj : SSet where
  obj p := ∀i,(X i).obj p
  map f := ↾fun s i=>(X i).map f (s i)
  map_id p := by apply ConcreteCategory.hom_ext; intro s; funext i; exact congrArg (fun f=>f (s i)) ((X i).map_id p)
  map_comp f g := by apply ConcreteCategory.hom_ext; intro s; funext i; exact congrArg (fun f=>f (s i)) ((X i).map_comp f g)
noncomputable def proj (i:ι) : obj X ⟶ X i where
  app _ := ↾fun s=>s i
  naturality _ _ _ := rfl
noncomputable def lift {Y:SSet} (f:∀i,Y⟶X i) : Y⟶obj X where
  app p := ↾fun s i=>(f i).app p s
  naturality p q g := by apply ConcreteCategory.hom_ext; intro s; funext i; exact congrArg (fun f=>f s) ((f i).naturality g)
@[simp] lemma lift_proj {Y:SSet} (f:∀i,Y⟶X i) (i:ι) : lift X f ≫ proj X i=f i := rfl
noncomputable def incl (x:∀i,(X i).obj (op ⦋0⦌)) (i:ι) : X i ⟶ obj X := by
  classical
  exact lift X (fun j=>if h:i=j then eqToHom (congrArg X h) else SSet.const (x j))
@[simp] lemma incl_self (x:∀i,(X i).obj (op ⦋0⦌)) (i:ι) : incl X x i ≫ proj X i=𝟙 _ := by
  classical
  simp [incl]
lemma incl_other (x:∀i,(X i).obj (op ⦋0⦌)) {i j:ι} (h:i≠j) :
    incl X x i ≫ proj X j=SSet.const (x j) := by
  classical
  simp [incl,h]
noncomputable def finSuccIso {n:ℕ} (X:Fin (n+1)→SSet) :
    obj X ≅ X 0 ⊗ obj (fun i:Fin n=>X i.succ) where
  hom := {app _ := ↾fun x=>(x 0,fun i=>x i.succ)
          naturality _ _ _ := rfl}
  inv := {app _ := ↾fun x=>Fin.cases x.1 x.2
          naturality _ _ _ := by
            apply ConcreteCategory.hom_ext; intro x; funext i
            cases i using Fin.cases <;> rfl}
  hom_inv_id := by
    apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i
    cases i using Fin.cases <;> rfl
  inv_hom_id := by ext p x <;> rfl
@[simp] lemma finSucc_fst {n:ℕ} (X:Fin (n+1)→SSet) :
    (finSuccIso X).hom ≫ CartesianMonoidalCategory.fst _ _=proj X 0 := rfl
@[simp] lemma finSucc_snd {n:ℕ} (X:Fin (n+1)→SSet) (i:Fin n) :
    (finSuccIso X).hom ≫ CartesianMonoidalCategory.snd _ _ ≫ proj (fun j:Fin n=>X j.succ) i=proj X i.succ := rfl
end PiSSet

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
abbrev P (C:Type) [Category.{0} C] := Skeleton C
noncomputable def repr (p:P C) : C := (fromSkeleton C).obj p
omit [MonoidalCategory C] [SymmetricCategory C] in
@[simp] lemma repr_component (p:P C) : toSkeleton (repr p)=p := toSkeleton_fromSkeleton_obj p
abbrev property (p:P C) : ObjectProperty C := fun U=>toSkeleton U=p
abbrev Fiber (p:P C) := (property p).FullSubcategory
noncomputable def reprMul (r s:P C) : repr r ⊗ repr s ≅ repr (r*s) :=
  Skeleton.isoOfEq (by simp [Skeleton.toSkeleton_tensorObj])
noncomputable def reprOne : repr (1:P C) ≅ 𝟙_ C :=
  Skeleton.isoOfEq (by simp [Skeleton.one_eq])
noncomputable def translate (r p q:P C) (h:r*p=q) : Fiber p ⥤ Fiber q :=
  (property q).lift ((property p).ι ⋙ tensorLeft (repr r)) (fun U=>by
    change toSkeleton (repr r ⊗ U.obj)=q
    rw [Skeleton.toSkeleton_tensorObj,repr_component,U.property,h])
noncomputable def translateOne (p:P C) (h:(1:P C)*p=p) : translate 1 p p h ⟶ 𝟭 (Fiber p) := by
  let α : tensorLeft (repr (1:P C)) ⟶ 𝟭 C :=
    (tensoringLeft C).map (reprOne (C:=C)).hom ≫ (leftUnitorNatIso C).hom
  exact { app U := ObjectProperty.homMk (α.app U.obj)
          naturality U V f := by apply ObjectProperty.hom_ext; exact α.naturality f.hom }
noncomputable def translateComp {p q t:P C} (r s:P C) (h:r*p=q) (k:s*q=t)
    (l:(s*r)*p=t) : translate (s*r) p t l ⟶ translate r p q h ⋙ translate s q t k := by
  let α : tensorLeft (repr (s*r)) ⟶ tensorLeft (repr r) ⋙ tensorLeft (repr s) :=
    (tensoringLeft C).map (reprMul s r).inv ≫ (tensorLeftTensor (repr s) (repr r)).hom
  exact { app U := ObjectProperty.homMk (α.app U.obj)
          naturality U V f := by apply ObjectProperty.hom_ext; exact α.naturality f.hom }
end ComponentTranslation

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ExactShapeHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace ExactShapeHomology

section

variable {J : Type} [Category.{0} J]
abbrev A := ModuleCat.{0} ℤ
abbrev c := ComplexShape.down ℕ
variable [HasExactColimitsOfShape J A]
noncomputable def complex (F : J ⥤ ChainComplex A ℕ) : ChainComplex (J ⥤ A) ℕ where
  X i := F ⋙ HomologicalComplex.eval A c i
  d i j := { app t := (F.obj t).d i j
             naturality _ _ f := (F.map f).comm i j }
  shape i j h := by apply NatTrans.ext; funext t; exact (F.obj t).shape i j h
  d_comp_d' i j k _ _ := by apply NatTrans.ext; funext t; exact (F.obj t).d_comp_d i j k
noncomputable def injection (j : J) : (evaluation J A).obj j ⟶ colim where
  app F := colimit.ι F j
  naturality _ _ f := (colimit.ι_map f j).symm
noncomputable def cocone (F : J ⥤ ChainComplex A ℕ) : Cocone F where
  pt := (colim.mapHomologicalComplex c).obj (complex F)
  ι := {
    app j := {
      f i := colimit.ι ((complex F).X i) j
      comm' i k _ := colimit.ι_map ((complex F).d i k) j }
    naturality _ _ f := by
      apply HomologicalComplex.Hom.ext; funext n
      exact colimit.w (F ⋙ HomologicalComplex.eval A c n) f }
noncomputable def isColimit (F : J ⥤ ChainComplex A ℕ) : IsColimit (cocone F) :=
  HomologicalComplex.isColimitOfEval F (cocone F) (fun _ => colimit.isColimit _)
noncomputable def evaluationHomology (F : J ⥤ ChainComplex A ℕ) (n : ℕ) (j:J) :
    (F.obj j).homology n ≅ ((complex F).homology n).obj j :=
  ((complex F).sc n).mapHomologyIso ((evaluation J A).obj j)
noncomputable def colimitHomology (F : J ⥤ ChainComplex A ℕ) (n : ℕ) :
    (cocone F).pt.homology n ≅ colimit ((complex F).homology n) :=
  ((complex F).sc n).mapHomologyIso colim
lemma homology_injection (F : J ⥤ ChainComplex A ℕ) (n : ℕ) (j:J) :
    HomologicalComplex.homologyMap ((cocone F).ι.app j) n =
      (evaluationHomology F n j).hom ≫ colimit.ι ((complex F).homology n) j ≫
        (colimitHomology F n).inv :=
  ShortComplex.homologyMap_mapNatTrans ((complex F).sc n) (injection j)
omit [HasExactColimitsOfShape J A] in
lemma evaluationHomology_naturality (F : J ⥤ ChainComplex A ℕ) (n : ℕ) {i j:J} (f:i⟶j) :
    HomologicalComplex.homologyMap (F.map f) n ≫ (evaluationHomology F n j).hom =
      (evaluationHomology F n i).hom ≫ ((complex F).homology n).map f := by
  have h := ShortComplex.homologyMap_mapNatTrans ((complex F).sc n) ((evaluation J A).map f)
  change HomologicalComplex.homologyMap (F.map f) n =
    (evaluationHomology F n i).hom ≫ ((complex F).homology n).map f ≫
      (evaluationHomology F n j).inv at h
  rw [h]
  simp [Category.assoc]
noncomputable def homologyCocone (F : J ⥤ ChainComplex A ℕ) (n : ℕ)
    (d : Cocone (F ⋙ HomologicalComplex.homologyFunctor A c n)) :
    Cocone ((complex F).homology n) where
  pt := d.pt
  ι := { app j := (evaluationHomology F n j).inv ≫ d.ι.app j
         naturality i _ f := by
           have h := evaluationHomology_naturality F n f
           rw [←Iso.inv_comp_eq] at h
           rw [←h]
           simp only [Category.assoc,Functor.const_obj_map]
           erw [Iso.hom_inv_id_assoc,Category.comp_id]
           exact congrArg (fun t => (evaluationHomology F n i).inv ≫ t) (d.w f) }
noncomputable def homologyIsColimit (F : J ⥤ ChainComplex A ℕ) (n : ℕ) :
    IsColimit ((HomologicalComplex.homologyFunctor A c n).mapCocone (cocone F)) where
  desc d := (colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)
  fac d j := by
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫
      ((colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)) = d.ι.app j
    rw [homology_injection]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc,colimit.ι_desc]
    exact Iso.hom_inv_id_assoc _ _
  uniq d m hm := by
    change m = (colimitHomology F n).hom ≫ colimit.desc _ (homologyCocone F n d)
    apply (Iso.inv_comp_eq (colimitHomology F n)).mp
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc]
    change colimit.ι ((complex F).homology n) j ≫ ((colimitHomology F n).inv ≫ m) =
      (evaluationHomology F n j).inv ≫ d.ι.app j
    apply (Iso.eq_inv_comp (evaluationHomology F n j)).mpr
    have h := hm j
    change HomologicalComplex.homologyMap ((cocone F).ι.app j) n ≫ m = _ at h
    rw [homology_injection] at h
    erw [Category.assoc,Category.assoc] at h
    exact h
noncomputable instance homology_preserves (n : ℕ) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor A c n) where
  preservesColimit {F} := preservesColimit_of_preserves_colimit_cocone (isColimit F) (homologyIsColimit F n)
end
variable {J : Type} [Category.{0} J] [HasExactColimitsOfShape J A]
noncomputable instance sset_homology_preserves (Z:A) (n:ℕ) :
    PreservesColimitsOfShape J (SSet.homologyFunctor Z n) := by
  change PreservesColimitsOfShape J (((SSet.chainComplexFunctor A).obj Z) ⋙
    HomologicalComplex.homologyFunctor A c n)
  infer_instance
end ExactShapeHomology

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace ComponentCoproduct
open ComponentTranslation

variable (C:Type) [Groupoid.{0} C]
noncomputable def diagram : Discrete (Skeleton C) ⥤ SSet :=
  Discrete.functor (fun p=>nerve (Fiber p))
noncomputable def cocone : Cocone (diagram C) :=
  Cofan.mk (nerve C) (fun p=>nerveMap (property p).ι)
noncomputable def lift {n:ℕ} (s:ComposableArrows C n) :
    ComposableArrows (Fiber (toSkeleton s.left)) n :=
  (property (toSkeleton s.left)).lift s (fun i=>
    (congr_toSkeleton_of_iso (asIso (s.map (homOfLE (Fin.zero_le i))))).symm)
lemma inclusion_injective (p:Skeleton C) {n:ℕ} :
    Function.Injective (fun s:ComposableArrows (Fiber p) n=>s ⋙ (property p).ι) := by
  intro s t h
  have object_eq : ∀ index, s.obj index = t.obj index := by
    intro index
    apply ObjectProperty.FullSubcategory.ext
    exact CategoryTheory.Functor.congr_obj h index
  refine CategoryTheory.Functor.ext object_eq ?_
  intro source target arrow
  apply ObjectProperty.hom_ext
  simpa using CategoryTheory.Functor.congr_hom h arrow
noncomputable def pointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C)) := by
  let cf : Cofan (fun p:Skeleton C=>ComposableArrows (Fiber p) n) :=
    Cofan.mk (ComposableArrows C n) (fun p=>↾fun s=>s ⋙ (property p).ι)
  let s := (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C))
  let e : diagram C ⋙ (evaluation _ (Type)).obj (op ⦋n⦌) ≅ Discrete.functor (fun p:Skeleton C=>ComposableArrows (Fiber p) n) := Discrete.natIso (fun _=>Iso.refl _)
  let pointIso : s.pt ≅ cf.pt := Iso.refl _
  apply ColimitTransfer.ofIsos s cf e.hom pointIso.hom (fun _=>by simp [s,e,cf,cocone,pointIso]; rfl)
  apply Classical.choice
  rw [←cf.isColimit_cofanTypes_iff]
  apply CofanTypes.isColimit_mk
  · intro s
    exact ⟨toSkeleton s.left,lift C s,rfl⟩
  · intro p; exact inclusion_injective C p
  · intro p q s t h
    have he := CategoryTheory.Functor.congr_obj h (0:Fin (n+1))
    exact s.left.property.symm.trans ((congrArg toSkeleton he).trans t.left.property)
noncomputable def isColimit : IsColimit (cocone C) :=
  evaluationJointlyReflectsColimits _ (fun n=>pointwiseIsColimit C n.unop.len)
end ComponentCoproduct

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_GroupNerveCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite
namespace GroupNerveCoordinates

variable {G : Type} [Group G] {n : ℕ}
def labels (F:ComposableArrows (SingleObj G) n) : Fin n → G :=
  fun i => (F.map (homOfLE (show i.castSucc ≤ i.succ by exact Fin.castSucc_le_succ i)))⁻¹
noncomputable def ofLabels (g:Fin n → G) : ComposableArrows (SingleObj G) n where
  obj _ := SingleObj.star G
  map {i j} _ := (Fin.partialProd g j)⁻¹ * Fin.partialProd g i
  map_id i := inv_mul_cancel _
  map_comp := by intros; change _ = (_ * _) * (_ * _); group
@[simp] lemma labels_ofLabels (g:Fin n → G) : labels (ofLabels g)=g := by
  funext i
  change ((Fin.partialProd g i.succ)⁻¹ * Fin.partialProd g i.castSucc)⁻¹=g i
  rw [mul_inv_rev,inv_inv,Fin.partialProd_right_inv]
lemma eqToHom_one {x y:SingleObj G} (h:x=y) : eqToHom h=(1:G) := by subst y; rfl
@[simp] lemma ofLabels_labels (F:ComposableArrows (SingleObj G) n) : ofLabels (labels F)=F := by
  apply ComposableArrows.ext (fun _=>Subsingleton.elim _ _)
  intro i hi
  simp only [eqToHom_one,SingleObj.comp_as_mul,one_mul,mul_one]
  change (Fin.partialProd (labels F) (Fin.succ ⟨i,hi⟩))⁻¹ *
    Fin.partialProd (labels F) (Fin.castSucc ⟨i,hi⟩)=_
  rw [Fin.partialProd_succ,mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  simp only [labels,inv_inv]
noncomputable def equiv (G:Type) [Group G] (n:ℕ) :
    ComposableArrows (SingleObj G) n ≃ (Fin n → G) where
  toFun := labels
  invFun := ofLabels
  left_inv := ofLabels_labels
  right_inv := labels_ofLabels
lemma labels_zero_face (F:ComposableArrows (SingleObj G) (n+1)) :
    labels ((nerve _).δ (0:Fin (n+2)) F) = Fin.tail (labels F) := by
  funext i
  rfl
lemma labels_succ_face (F:ComposableArrows (SingleObj G) (n+1)) (i:Fin (n+1)) :
    labels ((nerve _).δ i.succ F) = Fin.contractNth i (· * ·) (labels F) := by
  obtain ⟨g,rfl⟩ := (equiv G (n+1)).symm.surjective F
  change labels ((nerve _).δ i.succ (ofLabels g)) = _
  change labels ((nerve (SingleObj G)).δ i.succ (ofLabels g)) =
    Fin.contractNth i (· * ·) (labels (ofLabels g))
  rw [labels_ofLabels]
  funext k
  change ((Fin.partialProd g (i.succ.succAbove k.succ))⁻¹ *
    Fin.partialProd g (i.succ.succAbove k.castSucc))⁻¹ = _
  rw [mul_inv_rev,inv_inv,Fin.succ_succAbove_succ]
  exact Fin.inv_partialProd_mul_eq_contractNth g i k
end GroupNerveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PiFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet

variable {ι:Type} (C:ι→Type) [∀i,Category.{0} (C i)]
noncomputable def nervePiIso : nerve (∀i,C i) ≅ obj (fun i=>nerve (C i)) where
  hom := lift _ (fun i=>nerveMap (Pi.eval C i))
  inv := {app _ := ↾fun X=>Functor.pi' X
          naturality _ _ _ := by ext X; rfl}
  hom_inv_id := by ext p X; rfl
  inv_hom_id := by ext p X; rfl
end PiSSet
namespace ComponentTranslation

variable {C:Type} [Groupoid.{0} C]
noncomputable def base (p:Skeleton C) : Fiber p := ⟨(fromSkeleton C).obj p,toSkeleton_fromSkeleton_obj p⟩
noncomputable def fiberIso (p:Skeleton C) (U V:Fiber p) : U≅V :=
  (property p).ι.preimageIso (Skeleton.isoOfEq (U.property.trans V.property.symm))
noncomputable instance fiber_nonempty (p:Skeleton C) : Nonempty (Fiber p) := ⟨base p⟩
instance fiber_nerve_connected (p:Skeleton C) : (nerve (Fiber p)).IsConnected where
  nonempty := ⟨nerveEquiv.symm (base p)⟩
  allEq x y := by
    obtain ⟨x,rfl⟩:=SSet.π₀.mk_surjective x
    obtain ⟨y,rfl⟩:=SSet.π₀.mk_surjective y
    have h:=SSet.π₀.sound (nerve.edgeMk (fiberIso p (nerveEquiv x) (nerveEquiv y)).hom)
    exact (congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply x)).symm.trans
      (h.trans (congrArg SSet.π₀.mk (nerveEquiv.symm_apply_apply y)))
end ComponentTranslation
namespace PiFiber
open ComponentTranslation

variable (C:Type) [Groupoid.{0} C] (ι:Type)
noncomputable def prod : SSet := PiSSet.obj (fun _:ι=>nerve C)
noncomputable def piece (p:ι→Skeleton C) : SSet := PiSSet.obj (fun i=>nerve (Fiber (p i)))
noncomputable def diagram : Discrete (ι→Skeleton C) ⥤ SSet := Discrete.functor (piece C ι)
noncomputable def inclusion (p:ι→Skeleton C) : piece C ι p ⟶ prod C ι :=
  PiSSet.lift _ (fun i=>PiSSet.proj _ i ≫ nerveMap (property (p i)).ι)
noncomputable def cocone : Cocone (diagram C ι) := Cofan.mk (prod C ι) (inclusion C ι)
noncomputable def pointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C ι)) := by
  let cf : Cofan (fun p:ι→Skeleton C=>∀i,ComposableArrows (Fiber (p i)) n) :=
    Cofan.mk (∀_:ι,ComposableArrows C n) (fun p=>↾fun s i=>s i ⋙ (property (p i)).ι)
  let s := (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C ι))
  let e : diagram C ι ⋙ (evaluation _ (Type)).obj (op ⦋n⦌) ≅
      Discrete.functor (fun p:ι→Skeleton C=>∀i,ComposableArrows (Fiber (p i)) n) :=
    Discrete.natIso (fun _=>Iso.refl _)
  let pointIso : s.pt ≅ cf.pt := Iso.refl _
  apply ColimitTransfer.ofIsos s cf e.hom pointIso.hom
    (fun _=>by simp [s,e,cf,cocone,pointIso]; rfl)
  apply Classical.choice
  rw [←cf.isColimit_cofanTypes_iff]
  apply CofanTypes.isColimit_mk
  · intro s
    exact ⟨fun i=>toSkeleton (s i).left,fun i=>ComponentCoproduct.lift C (s i),rfl⟩
  · intro p s t h
    funext i
    exact ComponentCoproduct.inclusion_injective C (p i) (congrFun h i)
  · intro p q s t h
    funext i
    have he:=CategoryTheory.Functor.congr_obj (congrFun h i) (0:Fin (n+1))
    exact (s i).left.property.symm.trans ((congrArg toSkeleton he).trans (t i).left.property)
noncomputable def isColimit : IsColimit (cocone C ι) :=
  evaluationJointlyReflectsColimits _ (fun n=>pointwiseIsColimit C ι n.unop.len)
end PiFiber

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_GroupoidComponentHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace GroupoidComponentHomology
open ComponentTranslation SimpleAmenable

variable {C:Type} [Groupoid.{0} C]
noncomputable def inclusion (U:C) : SingleObj (Aut U) ⥤ C :=
  SingleObj.functor (Aut.toEnd U)
@[simp] lemma inclusion_obj (U:C) (x:SingleObj (Aut U)) : (inclusion U).obj x=U := rfl
@[simp] lemma inclusion_map (U:C) {x y:SingleObj (Aut U)} (f:x⟶y) :
    (inclusion U).map f=f.hom := rfl
instance inclusion_faithful (U:C) : (inclusion U).Faithful where
  map_injective h := Iso.ext h
noncomputable instance inclusion_full (U:C) : (inclusion U).Full where
  map_surjective f := ⟨(Groupoid.isoEquivHom U U).symm f,rfl⟩
noncomputable def fiberInclusion {p:Skeleton C} (U:Fiber p) : SingleObj (Aut U.obj) ⥤ Fiber p :=
  (property p).lift (inclusion U.obj) (fun _=>U.property)
instance fiberInclusion_faithful {p:Skeleton C} (U:Fiber p) : (fiberInclusion U).Faithful where
  map_injective h := Iso.ext (congrArg (fun f : (fiberInclusion U).obj _ ⟶ (fiberInclusion U).obj _ => f.hom) h)
noncomputable instance fiberInclusion_full {p:Skeleton C} (U:Fiber p) : (fiberInclusion U).Full where
  map_surjective f := ⟨(Groupoid.isoEquivHom U.obj U.obj).symm f.hom,rfl⟩
instance fiberInclusion_essSurj {p:Skeleton C} (U:Fiber p) : (fiberInclusion U).EssSurj where
  mem_essImage V := ⟨SingleObj.star _,⟨fiberIso p U V⟩⟩
noncomputable instance fiberInclusion_isEquivalence {p:Skeleton C} (U:Fiber p) :
    (fiberInclusion U).IsEquivalence := ⟨inferInstance,inferInstance,inferInstance⟩
end GroupoidComponentHomology

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_QuotientRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q] (f : G →* Q)

noncomputable abbrev regular : Rep ℤ G :=
  Rep.res f (Rep.of (Representation.leftRegular ℤ Q))

noncomputable def point : Rep.trivial ℤ f.ker ℤ ⟶ Rep.res f.ker.subtype (regular f) :=
  Rep.ofHom ⟨(MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp (Finsupp.lsingle (1:Q)),by
    intro g
    apply LinearMap.ext
    intro z
    change MonoidAlgebra.single (1:Q) z=Representation.leftRegular ℤ Q (f g.val) (MonoidAlgebra.single (1:Q) z)
    rw [g.property]
    simp⟩

noncomputable def kernelEquivStabilizer :
    letI : MulAction G Q := MulAction.compHom Q f
    f.ker ≃* MulAction.stabilizer G (1:Q) := by
  letI : MulAction G Q := MulAction.compHom Q f
  exact MulEquiv.subgroupCongr (by
    ext g
    change f g=1 ↔ f g*1=1
    simp)

noncomputable def permutationIso :
    letI : MulAction G Q := MulAction.compHom Q f
    regular f ≅ Rep.of (TransitiveInduction.permutationRep (G:=G) (X:=Q)) := by
  letI : MulAction G Q := MulAction.compHom Q f
  refine Rep.mkIso (.mk (MonoidAlgebra.coeffLinearEquiv ℤ) ?_)
  intro g
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext
  intro z
  simp [TransitiveInduction.permutationRep]
  rfl

noncomputable def right (q : Q) : regular f ⟶ regular f :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap ℤ ℤ (·*q),by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro z
    simp [Representation.leftRegular, mul_assoc]⟩

@[simp] lemma right_single (q x : Q) (z : ℤ) :
    (right f q).hom (MonoidAlgebra.single x z)=MonoidAlgebra.single (x*q) z := by
  simp [right]

noncomputable def conjugate (g : G) : f.ker ≃* f.ker :=
  (MulAut.conjNormal g : f.ker ≃* f.ker)

end QuotientRegular

end

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Finsupp
namespace FiniteFreeRep

attribute [local instance 1200] Rep.hV2
variable {k Q : Type} [CommRing k] [Group Q]

noncomputable def incl (A : Rep.{0} k Q) {n : ℕ} (i : Fin n) : A ⟶ Rep.finsupp (Fin n) A :=
  Rep.ofHom ⟨Finsupp.lsingle i,by
    intro g
    apply LinearMap.ext
    intro x
    simp⟩

noncomputable def proj (A : Rep.{0} k Q) {n : ℕ} (i : Fin n) : Rep.finsupp (Fin n) A ⟶ A :=
  Rep.ofHom ⟨Finsupp.lapply i,by
    intro g
    apply Finsupp.lhom_ext
    intro j x
    by_cases h : i=j
    · subst j; simp
    · simp [h]⟩

instance finite_free (n : ℕ) :
    Module.Finite (MonoidAlgebra k Q) (Rep.free k Q (Fin n)).ρ.asModule :=
  Module.Finite.of_basis (Representation.freeAsModuleBasis k Q (Fin n))

end FiniteFreeRep

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q]

noncomputable def augment : Rep.leftRegular ℤ Q ⟶ Rep.trivial ℤ Q ℤ :=
  Rep.ofHom ⟨(MonoidAlgebra.lift ℤ ℤ Q (1:Q →* ℤ)).toLinearMap,by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro z
    simp⟩

@[simp] lemma augment_single (q:Q) (z:ℤ) :
    (augment (Q:=Q)).hom (MonoidAlgebra.single q z)=z := by
  simp [augment,MonoidAlgebra.lift_single]

instance augment_epi : Epi (augment (Q:=Q)) := by
  apply ConcreteCategory.epi_of_surjective
  intro z
  exact ⟨MonoidAlgebra.single 1 z,augment_single 1 z⟩

end QuotientRegular

end

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open SimpleAmenable
namespace QuotientRegular

attribute [local instance 1200] Rep.hV2
variable {G Q : Type} [Group G] [Group Q]

instance finite_regular_module :
    Module.Finite (MonoidAlgebra ℤ Q) (Rep.leftRegular ℤ Q).ρ.asModule := by
  let p : Rep.free ℤ Q (Fin 1) ⟶ Rep.leftRegular ℤ Q := FiniteFreeRep.proj (Rep.leftRegular ℤ Q) (n:=1) 0
  have : Epi p := ConcreteCategory.epi_of_surjective p (by
    intro x
    exact ⟨Finsupp.single 0 x,by simp [p,FiniteFreeRep.proj]⟩)
  let q := Rep.toModuleMonoidAlgebra.map p
  have : Epi q := inferInstanceAs (Epi (Rep.toModuleMonoidAlgebra.map p))
  have : Module.Finite (MonoidAlgebra ℤ Q)
      (Rep.toModuleMonoidAlgebra.obj (Rep.free ℤ Q (Fin 1))) :=
    inferInstanceAs (Module.Finite (MonoidAlgebra ℤ Q) (Rep.free ℤ Q (Fin 1)).ρ.asModule)
  exact Module.Finite.of_surjective q.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end QuotientRegular

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ChainPositiveCokernel
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits HomologicalComplex
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
variable (n:ℕ) (hn:K.d (n+1) n=0)
noncomputable def positiveπ : K.X (n+1) ⟶ K.homology (n+1) :=
  K.pOpcycles (n+1) ≫ (K.isoHomologyι (n+1) n (by simp) hn).inv
instance instEpiModuleCatPositiveπ : Epi (positiveπ K n hn) := by dsimp only [positiveπ]; infer_instance
@[reassoc (attr:=simp)] lemma d_positiveπ : K.d (n+2) (n+1) ≫ positiveπ K n hn=0 := by
  simp [positiveπ]
noncomputable def positiveDesc {V:ModuleCat.{0} R} (f:K.X (n+1) ⟶ V)
    (hf:K.d (n+2) (n+1) ≫ f=0) : K.homology (n+1) ⟶ V :=
  (K.isoHomologyι (n+1) n (by simp) hn).hom ≫
    K.descOpcycles f (n+2) (by simp) hf
@[reassoc (attr:=simp)] lemma positiveπ_desc {V:ModuleCat.{0} R} (f:K.X (n+1) ⟶ V)
    (hf:K.d (n+2) (n+1) ≫ f=0) : positiveπ K n hn ≫ positiveDesc K n hn f hf=f := by
  simp [positiveπ,positiveDesc]
end ChainComplex

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerGeneral
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
def outerOrder (i:Fin 2) : Fin 2 →o Fin 3 :=
  if i=0 then (SimplexCategory.δ (0:Fin 3)).toOrderHom else (SimplexCategory.δ (2:Fin 3)).toOrderHom
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_LowerBarComposition
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialFirstFinite

attribute [local instance 1200] Submodule.module
universe u
variable {R:Type u} [CommRing R]
variable (T:SimplicialObject (ModuleCat.{u} R))
abbrev K := AlternatingFaceMapComplex.obj T
variable (h0:IsZero (T.obj (op ⦋0⦌)))
include h0
omit h0 in
lemma d21 : (K T).d 2 1=T.δ (0:Fin 3)-T.δ (1:Fin 3)+T.δ (2:Fin 3) := by
  simp [K,AlternatingFaceMapComplex.obj_d_eq,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc]
end SimplicialFirstFinite

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedNerve
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C) [W.IsMultiplicative]
instance instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions (n : ℕ) : (W.functorCategory (Fin (n+1))).IsMultiplicative where
  id_mem object index := W.id_mem (object.obj index)
  comp_mem first second hfirst hsecond index :=
    W.comp_mem (first.app index) (second.app index) (hfirst index) (hsecond index)
abbrev Strings (n : ℕ) := WideSubcategory (W.functorCategory (Fin (n+1)))
def allowed (n : ℕ) : ObjectProperty (Fin (n+1) ⥤ C) :=
  fun F => ∀ i j (f : i ⟶ j), W (F.map f)
abbrev Vertical (n : ℕ) := (allowed W n).FullSubcategory

def reindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) : Strings W m ⥤ Strings W n where
  obj F := ⟨u ⋙ F.obj⟩
  map f := ⟨Functor.whiskerLeft u f.hom,fun i => f.property (u.obj i)⟩
  map_id _ := by apply WideSubcategory.hom_ext; rfl
  map_comp _ _ := by apply WideSubcategory.hom_ext; rfl
lemma reindex_id (n : ℕ) : reindex W (𝟭 (Fin (n+1)))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun object => by cases object; rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl
lemma reindex_comp {n m k : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1)) :
    reindex W (u⋙v)=reindex W v ⋙ reindex W u := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

def vreindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) : Vertical W m ⥤ Vertical W n where
  obj F := ⟨u ⋙ F.obj,fun i j f => F.property (u.obj i) (u.obj j) (u.map f)⟩
  map f := ObjectProperty.homMk (Functor.whiskerLeft u f.hom)
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; rfl
omit [W.IsMultiplicative] in
lemma vreindex_id (n : ℕ) : vreindex W (𝟭 (Fin (n+1)))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun object => by cases object; rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl
omit [W.IsMultiplicative] in
lemma vreindex_comp {n m k : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1)) :
    vreindex W (u⋙v)=vreindex W v ⋙ vreindex W u := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

def constant (n : ℕ) : C ⥤ Vertical W n where
  obj U := ⟨(Functor.const (Fin (n+1))).obj U,fun _ _ _ => W.id_mem U⟩
  map f := ObjectProperty.homMk ((Functor.const (Fin (n+1))).map f)
def evaluation (n : ℕ) : Vertical W n ⥤ C where
  obj F := F.obj.obj 0
  map f := f.hom.app 0
noncomputable def constantComparison (n : ℕ) : evaluation W n ⋙ constant W n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun F => {
    hom := ObjectProperty.homMk {
      app i := F.obj.map (homOfLE (Fin.zero_le i))
      naturality i j f := by
        change 𝟙 _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [Category.id_comp,←F.obj.map_comp]
        congr 1 }
    inv := ObjectProperty.homMk {
      app i := by
        change F.obj.obj i ⟶ F.obj.obj 0
        exact inv (F.obj.map (homOfLE (Fin.zero_le i)))
      naturality i j f := by
        change F.obj.map f ≫ inv (F.obj.map _) = inv (F.obj.map _) ≫ 𝟙 _
        rw [Category.comp_id]
        apply (cancel_mono (F.obj.map (homOfLE (Fin.zero_le j)))).mp
        simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]
        have he : F.obj.map (homOfLE (Fin.zero_le j)) =
            F.obj.map (homOfLE (Fin.zero_le i)) ≫ F.obj.map f := by
          rw [←F.obj.map_comp]; congr 1
        rw [he,←Category.assoc,IsIso.inv_hom_id,Category.id_comp] }
    hom_inv_id := by apply ObjectProperty.hom_ext; ext i; exact IsIso.hom_inv_id _
    inv_hom_id := by
      apply ObjectProperty.hom_ext
      ext i
      exact IsIso.inv_hom_id (F.obj.map (homOfLE (Fin.zero_le i))) })
    (by
      intro F G f
      apply ObjectProperty.hom_ext; ext i
      exact (f.hom.naturality _).symm)
noncomputable def equivalence (n : ℕ) : C ≌ Vertical W n where
  functor := constant W n
  inverse := evaluation W n
  unitIso := Iso.refl _
  counitIso := constantComparison W n
  functor_unitIso_comp U := by
    apply ObjectProperty.hom_ext; ext i
    change 𝟙 U ≫ 𝟙 U = 𝟙 U
    exact Category.id_comp _
noncomputable instance instIsEquivalenceVerticalConstant (n : ℕ) : (constant W n).IsEquivalence :=
  (equivalence W n).isEquivalence_functor

def horizontal : SimplicialObject Cat.{0,0} where
  obj p := Cat.of (Strings W p.unop.len)
  map f := (reindex W f.unop.toOrderHom.toFunctor).toCatHom
  map_id p := by apply Cat.ext; exact reindex_id W p.unop.len
  map_comp f g := by apply Cat.ext; exact reindex_comp W g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor
def vertical : SimplicialObject Cat.{0,0} where
  obj p := Cat.of (Vertical W p.unop.len)
  map f := (vreindex W f.unop.toOrderHom.toFunctor).toCatHom
  map_id p := by apply Cat.ext; exact vreindex_id W p.unop.len
  map_comp f g := by apply Cat.ext; exact vreindex_comp W g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor
def constantMap : (Functor.const SimplexCategoryᵒᵖ).obj (Cat.of C) ⟶ vertical W where
  app p := (constant W p.unop.len).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro source target arrow
    erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (Category.id_comp _).symm

def transpose {p q : ℕ} (F : Fin (q+1) ⥤ Strings W p) : Fin (p+1) ⥤ Vertical W q where
  obj i := ⟨{
    obj j := (F.obj j).obj.obj i
    map f := (F.map f).hom.app i
    map_id j := by have h := F.map_id j; exact congrArg (fun x => x.hom.app i) h
    map_comp f g := by have h := F.map_comp f g; exact congrArg (fun x => x.hom.app i) h },
    fun j k f => (F.map f).property i⟩
  map f := ObjectProperty.homMk {
    app j := (F.obj j).obj.map f
    naturality j k g := ((F.map g).hom.naturality f).symm }
  map_id i := by apply ObjectProperty.hom_ext; ext j; exact (F.obj j).obj.map_id i
  map_comp f g := by apply ObjectProperty.hom_ext; ext j; exact (F.obj j).obj.map_comp f g

def untranspose {p q : ℕ} (F : Fin (p+1) ⥤ Vertical W q) : Fin (q+1) ⥤ Strings W p where
  obj i := ⟨{
    obj j := (F.obj j).obj.obj i
    map f := (F.map f).hom.app i
    map_id j := by have h := F.map_id j; exact congrArg (fun x => x.hom.app i) h
    map_comp f g := by have h := F.map_comp f g; exact congrArg (fun x => x.hom.app i) h }⟩
  map f := ⟨{
    app j := (F.obj j).obj.map f
    naturality j k g := ((F.map g).hom.naturality f).symm },
    fun i => (F.obj i).property _ _ f⟩
  map_id i := by apply WideSubcategory.hom_ext; ext j; exact (F.obj j).obj.map_id i
  map_comp f g := by apply WideSubcategory.hom_ext; ext j; exact (F.obj j).obj.map_comp f g
lemma untranspose_transpose {p q : ℕ} (F : Fin (q+1) ⥤ Strings W p) :
    untranspose W (transpose W F)=F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply WideSubcategory.hom_ext
  ext index
  rfl
lemma transpose_untranspose {p q : ℕ} (F : Fin (p+1) ⥤ Vertical W q) :
    transpose W (untranspose W F)=F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply ObjectProperty.hom_ext
  ext index
  rfl
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidal
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory
namespace RestrictedNerve

section

section

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C) [W.IsMultiplicative]
  [Fact W.StableUnderInverse]
noncomputable instance restricted_isIso {U V : WideSubcategory W} (f : U ⟶ V) : IsIso f := by
  refine ⟨⟨⟨inv f.hom,?_⟩,?_,?_⟩⟩
  · exact (Fact.out : W.StableUnderInverse) (asIso f.hom) f.property
  · apply WideSubcategory.hom_ext; exact IsIso.hom_inv_id f.hom
  · apply WideSubcategory.hom_ext; exact IsIso.inv_hom_id f.hom
noncomputable instance restricted_groupoid : Groupoid (WideSubcategory W) :=
  Groupoid.ofIsIso (fun _ => inferInstance)
instance strings_inverse (n : ℕ) : Fact (W.functorCategory (Fin (n+1))).StableUnderInverse where
  out _ _ e h i := by
    have hi := (Fact.out : W.StableUnderInverse) (e.app i) (h i)
    exact hi
noncomputable instance strings_isIso {n : ℕ} {U V : Strings W n} (f : U ⟶ V) : IsIso f := by
  let : IsIso f.hom := NatIso.isIso_of_isIso_app f.hom
  refine ⟨⟨⟨inv f.hom,?_⟩,?_,?_⟩⟩
  · intro i
    rw [NatIso.isIso_inv_app]
    exact (Fact.out : W.StableUnderInverse) (asIso (f.hom.app i)) (f.property i)
  · apply WideSubcategory.hom_ext; exact IsIso.hom_inv_id f.hom
  · apply WideSubcategory.hom_ext; exact IsIso.inv_hom_id f.hom
noncomputable instance strings_groupoid (n : ℕ) : Groupoid (Strings W n) :=
  Groupoid.ofIsIso (fun _ => inferInstance)
omit [Fact W.StableUnderInverse] in
@[simp] lemma wide_hom_inv {source target : WideSubcategory W} (iso : source ≅ target) :
    iso.hom.hom ≫ iso.inv.hom = 𝟙 _ := congrArg (fun arrow => arrow.hom) iso.hom_inv_id
omit [Fact W.StableUnderInverse] in
@[simp] lemma wide_inv_hom {source target : WideSubcategory W} (iso : source ≅ target) :
    iso.inv.hom ≫ iso.hom.hom = 𝟙 _ := congrArg (fun arrow => arrow.hom) iso.inv_hom_id
end

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
instance strings_monoidal (n : ℕ) : (W.functorCategory (Fin (n+1))).IsMonoidalStable where
  whiskerLeft object _ _ arrow member index :=
    W.whiskerLeft_mem (object.obj index) (arrow.app index) (member index)
  whiskerRight arrow member object index :=
    W.whiskerRight_mem (arrow.app index) (member index) (object.obj index)
  associator_hom_mem first second third index :=
    W.associator_hom_mem (first.obj index) (second.obj index) (third.obj index)
  associator_inv_mem first second third index :=
    W.associator_inv_mem (first.obj index) (second.obj index) (third.obj index)
  leftUnitor_hom_mem object index := W.leftUnitor_hom_mem (object.obj index)
  leftUnitor_inv_mem object index := W.leftUnitor_inv_mem (object.obj index)
  rightUnitor_hom_mem object index := W.rightUnitor_hom_mem (object.obj index)
  rightUnitor_inv_mem object index := W.rightUnitor_inv_mem (object.obj index)
instance strings_braided (n : ℕ) : (W.functorCategory (Fin (n+1))).IsStableUnderBraiding where
  braiding_hom_mem first second index := W.braiding_hom_mem (first.obj index) (second.obj index)
  braiding_inv_mem first second index := W.braiding_inv_mem (first.obj index) (second.obj index)
noncomputable instance reindexMonoidal {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (reindex W u).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by
    intro X Y f X'
    apply WideSubcategory.hom_ext
    ext i
    change (f.hom.app (u.obj i) ▷ X'.obj.obj (u.obj i)) ≫ 𝟙 _ =
      𝟙 _ ≫ (f.hom.app (u.obj i) ▷ X'.obj.obj (u.obj i))
    simp
  μIso_hom_natural_right := by
    intro X Y X' f
    apply WideSubcategory.hom_ext
    ext i
    change (X'.obj.obj (u.obj i) ◁ f.hom.app (u.obj i)) ≫ 𝟙 _ =
      𝟙 _ ≫ (X'.obj.obj (u.obj i) ◁ f.hom.app (u.obj i))
    simp
  associativity := by
    intro X Y Z
    apply WideSubcategory.hom_ext
    ext i
    let x := X.obj.obj (u.obj i)
    let y := Y.obj.obj (u.obj i)
    let z := Z.obj.obj (u.obj i)
    change (𝟙 (x ⊗ y) ▷ z) ≫ 𝟙 _ ≫ (α_ x y z).hom =
      (α_ x y z).hom ≫ (x ◁ 𝟙 (y ⊗ z)) ≫ 𝟙 _
    simp
  left_unitality := by
    intro X
    apply WideSubcategory.hom_ext
    ext i
    let x := X.obj.obj (u.obj i)
    change (λ_ x).hom = (𝟙 (𝟙_ C) ▷ x) ≫ 𝟙 _ ≫ (λ_ x).hom
    simp
  right_unitality := by
    intro X
    apply WideSubcategory.hom_ext
    ext i
    let x := X.obj.obj (u.obj i)
    change (ρ_ x).hom = (x ◁ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ x).hom
    simp }

noncomputable instance reindexBraided {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (reindex W u).Braided where
  braided _ _ := by
    apply WideSubcategory.hom_ext; ext i
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
end

open IntervalBar IntervalBar.Diagram

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_InducedMonoidal
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
namespace InducedMonoidal

variable {C D : Type} [cC : Category.{0} C] [cD : Category.{0} D] [mC : MonoidalCategory C] [mD : MonoidalCategory D]
variable (F : C ⥤ D)
section
variable [F.Monoidal]
abbrev Cat := InducedCategory D F.obj
abbrev inclusion : Cat F ⥤ D := inducedFunctor F.obj
noncomputable instance monoidalStruct : MonoidalCategoryStruct (Cat F) where
  tensorObj X Y := @MonoidalCategoryStruct.tensorObj C cC mC.toMonoidalCategoryStruct X Y
  tensorUnit := 𝟙_ C
  tensorHom {X Y X' Y'} f g := InducedCategory.homMk (δ F X X' ≫ (f.hom ⊗ₘ g.hom) ≫ μ F Y Y')
  whiskerLeft X _ _ f := InducedCategory.homMk (δ F X _ ≫ (F.obj X ◁ f.hom) ≫ μ F X _)
  whiskerRight f Y := InducedCategory.homMk (δ F _ Y ≫ (f.hom ▷ F.obj Y) ≫ μ F _ Y)
  associator X Y Z := InducedCategory.isoMk (F.mapIso (@MonoidalCategoryStruct.associator C cC mC.toMonoidalCategoryStruct X Y Z))
  leftUnitor X := InducedCategory.isoMk (F.mapIso (@MonoidalCategoryStruct.leftUnitor C cC mC.toMonoidalCategoryStruct X))
  rightUnitor X := InducedCategory.isoMk (F.mapIso (@MonoidalCategoryStruct.rightUnitor C cC mC.toMonoidalCategoryStruct X))
noncomputable def data : Monoidal.InducingFunctorData (inclusion F) where
  μIso X Y := Functor.Monoidal.μIso F X Y
  εIso := Functor.Monoidal.εIso F
  whiskerLeft_eq := by intros; rfl
  whiskerRight_eq _ _ := rfl
  tensorHom_eq _ _ := rfl
  associator_eq X Y Z := by
    change F.map (@MonoidalCategoryStruct.associator C cC mC.toMonoidalCategoryStruct X Y Z).hom = _
    simpa only [inclusion,inducedFunctor, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit, monoidalStruct, Iso.trans_hom,Iso.symm_hom,tensorIso_hom,Iso.refl_hom,tensorHom_id,id_tensorHom,
      Functor.Monoidal.μIso_hom,Functor.Monoidal.μIso_inv,Category.assoc] using
      Functor.Monoidal.map_associator F X Y Z
  leftUnitor_eq X := by
    change F.map (@MonoidalCategoryStruct.leftUnitor C cC mC.toMonoidalCategoryStruct X).hom = _
    simpa only [inclusion,inducedFunctor, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit, monoidalStruct, Iso.trans_hom,Iso.symm_hom,tensorIso_hom,Iso.refl_hom,tensorHom_id,id_tensorHom,
      Functor.Monoidal.μIso_hom,Functor.Monoidal.μIso_inv,Functor.Monoidal.εIso_inv,Category.assoc] using
      Functor.Monoidal.map_leftUnitor F X
  rightUnitor_eq X := by
    change F.map (@MonoidalCategoryStruct.rightUnitor C cC mC.toMonoidalCategoryStruct X).hom = _
    simpa only [inclusion,inducedFunctor, MonoidalCategoryStruct.tensorObj, MonoidalCategoryStruct.tensorUnit, monoidalStruct, Iso.trans_hom,Iso.symm_hom,tensorIso_hom,Iso.refl_hom,tensorHom_id,id_tensorHom,
      Functor.Monoidal.μIso_hom,Functor.Monoidal.μIso_inv,Functor.Monoidal.εIso_inv,Category.assoc] using
      Functor.Monoidal.map_rightUnitor F X
noncomputable instance monoidal : MonoidalCategory (Cat F) := Monoidal.induced (inclusion F) (data F)
noncomputable instance inclusionMonoidal : (inclusion F).Monoidal := Monoidal.fromInducedMonoidal (inclusion F) (data F)
end
section
variable [BraidedCategory C] [BraidedCategory D] [F.Braided]
noncomputable instance braided : BraidedCategory (Cat F) :=
  BraidedCategory.ofFaithful (inclusion F)
    (fun X Y => InducedCategory.isoMk (F.mapIso (@BraidedCategory.braiding C cC mC _ X Y))) (by
      intro X Y
      change μ F X Y ≫ F.map (@BraidedCategory.braiding C cC mC _ X Y).hom = (β_ _ _).hom ≫ μ F Y X
      exact Functor.LaxBraided.braided X Y)
noncomputable instance inclusionBraided : (inclusion F).Braided where
  braided X Y := by
    change μ F X Y ≫ F.map (@BraidedCategory.braiding C cC mC _ X Y).hom = (β_ _ _).hom ≫ μ F Y X
    exact Functor.LaxBraided.braided X Y
end
variable [BraidedCategory C] [SymmetricCategory D] [F.Braided]
noncomputable instance symmetric : SymmetricCategory (Cat F) :=
  SymmetricCategory.ofFaithful (inclusion F)
end InducedMonoidal

end

open _root_.CategoryTheory MonoidalCategory

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidalTranspose
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I : Type} [Preorder I]
omit [Fact W.StableUnderInverse] in
@[simp] lemma reindex_η {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    Functor.OplaxMonoidal.η (reindex W u)=𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma reindex_μ {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) (A B : Strings W m) :
    Functor.LaxMonoidal.μ (reindex W u) A B=𝟙 _ := rfl
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedFunctorial
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

section

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  (W:MorphismProperty C) (V:MorphismProperty D) [W.IsMultiplicative] [V.IsMultiplicative]
  (F:C⥤D) (hF:∀{X Y:C} (f:X⟶Y),W f→V (F.map f))
def verticalMap (n:ℕ) : Vertical W n ⥤ Vertical V n where
  obj A := ⟨A.obj⋙F,fun i j f=>hF _ (A.property i j f)⟩
  map f := ObjectProperty.homMk (Functor.whiskerRight f.hom F)
  map_id _ := by apply ObjectProperty.hom_ext; ext i; exact F.map_id _
  map_comp _ _ := by apply ObjectProperty.hom_ext; ext i; exact F.map_comp _ _
def verticalMapNat : vertical W ⟶ vertical V where
  app p := (verticalMap W V F hF p.unop.len).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro source target arrow
    erw [Category.id_comp, Category.comp_id]
    apply ObjectProperty.hom_ext; ext index; rfl
omit [W.IsMultiplicative] in
@[simp] lemma eqToHom_vertical_app {n:ℕ} {A B:Vertical W n} (e:A=B) (i:Fin (n+1)) :
    (eqToHom e).hom.app i=eqToHom (congrArg (fun A:Vertical W n=>A.obj.obj i) e) := by
  cases e; rfl
end

end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_MonoidalCongruence
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
lemma monoidal_congr {F G:C⥤D} [hF:F.Monoidal] [hG:G.Monoidal] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : HEq hF hG := by
  cases e
  apply heq_of_eq
  have hε : hF.ε=hG.ε := by
    have hh := h.unit
    simpa only [eqToHom_refl,NatTrans.id_app,Category.comp_id] using hh
  have hμ : hF.μ=hG.μ := by
    funext X Y
    have hh := h.tensor X Y
    simpa only [eqToHom_refl,NatTrans.id_app,Category.comp_id,id_tensorHom_id,Category.id_comp] using hh
  apply Functor.Monoidal.ext hε hμ
  · have he : @Functor.Monoidal.εIso _ _ _ _ _ _ F hF = @Functor.Monoidal.εIso _ _ _ _ _ _ F hG := Iso.ext hε
    exact congrArg Iso.inv he
  · funext X Y
    have he : @Functor.Monoidal.μIso _ _ _ _ _ _ F hF X Y = @Functor.Monoidal.μIso _ _ _ _ _ _ F hG X Y :=
      Iso.ext (congrFun (congrFun hμ X) Y)
    exact congrArg Iso.inv he
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
lemma braided_congr {F G:C⥤D} [hF:F.Braided] [hG:G.Braided] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : HEq hF hG := by
  have hm := monoidal_congr e h
  cases e
  apply heq_of_eq
  apply Functor.Braided.ext
  · exact congrArg (fun h:F.Monoidal=>h.ε) (eq_of_heq hm)
  · exact congrArg (fun h:F.Monoidal=>h.μ) (eq_of_heq hm)
  · exact congrArg (fun h:F.Monoidal=>h.η) (eq_of_heq hm)
  · exact congrArg (fun h:F.Monoidal=>h.δ) (eq_of_heq hm)
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PiH1Coproduct
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupoidComponentHomology.fiberInclusion_essSurj _root_.OAI.GroupoidComponentHomology.fiberInclusion_faithful _root_.OAI.GroupoidComponentHomology.fiberInclusion_full _root_.OAI.GroupoidComponentHomology.fiberInclusion_isEquivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def points {n:ℕ} (p:Fin n→Skeleton C) :
    ∀i,(nerve (Fiber (p i))).obj (op ⦋0⦌) := fun i=>nerveEquiv.symm (base (p i))
end MarkedH1

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_CoefficientNerve
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits Simplicial Opposite Classical
open scoped DirectSum
namespace CoefficientNerve

variable {R:Type} [CommRing R]
variable {C D E:Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable (F:C ⥤ ModuleCat.{0} R)
abbrev Simplex (C:Type) [Category.{0} C] (n:ℕ) := ComposableArrows Cᵒᵖ n
abbrev Coeff (n:ℕ) (s:Simplex C n) := F.obj s.right.unop
noncomputable abbrev Obj (n:ℕ) := ModuleCat.of R (⨁ (s:Simplex C n), Coeff F n s)
noncomputable def single {n:ℕ} (s:Simplex C n) : Coeff F n s ⟶ Obj F n :=
  ModuleCat.ofHom (DirectSum.lof R (Simplex C n) (fun t => (Coeff F n t : Type)) s)
noncomputable def desc {n:ℕ} {M:ModuleCat.{0} R} (f:∀s:Simplex C n, Coeff F n s ⟶ M) : Obj F n ⟶ M :=
  ModuleCat.ofHom (DirectSum.toModule R (Simplex C n) (M:=fun s => (Coeff F n s : Type)) M (fun s=>(f s).hom))
@[reassoc (attr:=simp)] lemma single_desc {n:ℕ} {M:ModuleCat.{0} R}
    (f:∀s:Simplex C n, Coeff F n s ⟶ M) (s:Simplex C n) :
    single F s ≫ desc F f=f s := by
  ext x
  exact DirectSum.toModule_lof R (φ:=fun s => (f s).hom) s x
lemma hom_ext {n:ℕ} {M:ModuleCat.{0} R} {f g:Obj F n ⟶ M}
    (h:∀s, single F s ≫ f=single F s ≫ g) : f=g := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext (R:=R) (M:=fun s:Simplex C n => (Coeff F n s : Type))
  intro s
  exact congrArg ModuleCat.Hom.hom (h s)
def trunc {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) : Simplex C m :=
  (SimplexCategory.toCat.map f).toFunctor ⋙ s
def tail {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    s.right.unop ⟶ (trunc f s).right.unop :=
  (s.map (homOfLE (Fin.le_last (f.toOrderHom (Fin.last m))))).unop
noncomputable def map {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) : Obj F n ⟶ Obj F m :=
  desc F (fun s=>F.map (tail f s) ≫ single F (trunc f s))
@[reassoc (attr:=simp)] lemma single_map {m n:ℕ} (f:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    single F s ≫ map F f=F.map (tail f s) ≫ single F (trunc f s) := single_desc _ _ _
@[simp] lemma trunc_id {n:ℕ} (s:Simplex C n) : trunc (𝟙 ⦋n⦌) s=s := rfl
@[simp] lemma tail_id {n:ℕ} (s:Simplex C n) : tail (𝟙 ⦋n⦌) s=𝟙 _ := by
  change (s.map (𝟙 _)).unop=𝟙 _
  rw [s.map_id]; rfl
lemma trunc_comp {l m n:ℕ} (f:⦋l⦌ ⟶ ⦋m⦌) (g:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    trunc (f ≫ g) s=trunc f (trunc g s) := rfl
lemma tail_comp {l m n:ℕ} (f:⦋l⦌ ⟶ ⦋m⦌) (g:⦋m⦌ ⟶ ⦋n⦌) (s:Simplex C n) :
    tail (f ≫ g) s=tail g s ≫ tail f (trunc g s) := by
  change (s.map (homOfLE (Fin.le_last (g.toOrderHom (f.toOrderHom (Fin.last l)))))).unop =
    (s.map (homOfLE (Fin.le_last (g.toOrderHom (Fin.last m))))).unop ≫
    (s.map (homOfLE (g.toOrderHom.monotone (Fin.le_last (f.toOrderHom (Fin.last l)))))).unop
  rw [←unop_comp,←s.map_comp]
  congr 2
lemma map_id (n:ℕ) : map F (𝟙 ⦋n⦌)=𝟙 _ := by
  apply hom_ext; intro s
  simp
lemma map_comp {l m n:ℕ} (f:⦋l⦌ ⟶ ⦋m⦌) (g:⦋m⦌ ⟶ ⦋n⦌) :
    map F (f ≫ g)=map F g ≫ map F f := by
  apply hom_ext; intro s
  simp only [single_map,tail_comp,F.map_comp,Category.assoc,single_map_assoc,trunc_comp]
noncomputable def simplicial : SimplicialObject (ModuleCat.{0} R) where
  obj n := Obj F n.unop.len
  map f := map F f.unop
  map_id n := map_id F n.unop.len
  map_comp f g := map_comp F g.unop f.unop
noncomputable def complex : ChainComplex (ModuleCat.{0} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{0} R)).obj (simplicial F)
noncomputable def post (u:C ⥤ D) (G:D ⥤ ModuleCat.{0} R) :
    simplicial (u ⋙ G) ⟶ simplicial G where
  app n := desc (u ⋙ G) (fun s=>single G (s ⋙ u.op))
  naturality n m f := by
    apply hom_ext; intro s
    simp only [simplicial,single_desc,single_map_assoc,single_map,single_desc_assoc]
    rfl
@[reassoc (attr:=simp)] lemma single_post (u:C ⥤ D) (G:D ⥤ ModuleCat.{0} R) (n:ℕ)
    (s:Simplex C n) : single (u ⋙ G) s ≫ (post u G).app (op ⦋n⦌)=single G (s ⋙ u.op) :=
  single_desc _ _ _
end CoefficientNerve

end

section
open _root_.CategoryTheory Limits Simplicial Opposite
namespace NervePrefix

variable {C:Type} [Category.{0} C] {d:C} (hd:IsInitial d)
def extra {n:ℕ} (s:ComposableArrows C n) : ComposableArrows C (n+1) :=
  s.precomp (hd.to s.left)
lemma precomp_delta {n:ℕ} (s:ComposableArrows C (n+1)) (i:Fin (n+2)) :
    (nerve C).δ i.succ (extra hd s)=extra hd ((nerve C).δ i s) := by
  have h₀ : ((nerve C).δ i.succ (extra hd s)).obj 0=d := by
    change (extra hd s).obj (i.succ.succAbove 0)=d
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp)]
    rfl
  have h : ((nerve C).δ i.succ (extra hd s)).δ₀=((nerve C).δ i s) := by
    have h:=congrArg (fun f => f (extra hd s)) ((nerve C).δ_comp_δ (Fin.zero_le i))
    exact h
  exact ComposableArrows.ext_succ h₀ h
    ((IsInitial.ofIso hd (eqToIso h₀.symm)).hom_ext _ _)

end NervePrefix

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_CoefficientContraction
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology
namespace SemiExtra
variable {C:Type*} [Category* C]
structure Data (X:Augmented C) where
  s' : X.right ⟶ X.left _⦋0⦌
  s : ∀n:ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n+1⦌
  s'_comp_ε : s' ≫ X.hom.app (op ⦋0⦌)=𝟙 X.right
  s₀_comp_δ₁ : s 0 ≫ X.left.δ 1=X.hom.app (op ⦋0⦌) ≫ s'
  s_comp_δ₀ : ∀n:ℕ, s n ≫ X.left.δ 0=𝟙 _
  s_comp_δ : ∀ (n:ℕ) (i:Fin (n+2)),s (n+1) ≫ X.left.δ i.succ=X.left.δ i ≫ s n
attribute [reassoc] Data.s₀_comp_δ₁ Data.s_comp_δ
attribute [reassoc (attr:=simp)] Data.s'_comp_ε Data.s_comp_δ₀

noncomputable def homotopyEquiv [Preadditive C] [HasZeroObject C]
    {X:Augmented C} (ed:Data X) :
    HomotopyEquiv (AlternatingFaceMapComplex.obj (Augmented.drop.obj X))
      ((ChainComplex.single₀ C).obj (Augmented.point.obj X)) where
  hom := AlternatingFaceMapComplex.ε.app X
  inv := (ChainComplex.fromSingle₀Equiv _ _).symm (by exact ed.s')
  homotopyInvHomId := Homotopy.ofEq (by
    ext
    simp [dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
      (C:=AlternatingFaceMapComplex.obj X.left)])
  homotopyHomInvId :=
    { hom i := Pi.single (i+1) (-ed.s i)
      zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
      comm i := by
        cases i with
        | zero =>
          rw [Homotopy.prevD_chainComplex,Homotopy.dNext_zero_chainComplex]
          simp [dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
            (C:=AlternatingFaceMapComplex.obj X.left),Data.s_comp_δ₀,Data.s₀_comp_δ₁]
        | succ i =>
          rw [Homotopy.prevD_chainComplex,Homotopy.dNext_succ_chainComplex]
          simp [Fin.sum_univ_succ (n:=i+2),Data.s_comp_δ₀,Preadditive.sum_comp,
            Preadditive.comp_sum,Data.s_comp_δ,pow_succ] }
end SemiExtra
namespace CoefficientNerve

variable {R:Type} [CommRing R] {C:Type} [Category.{0} C]
variable (F:C ⥤ ModuleCat.{0} R)
lemma weighted_eq {n:ℕ} {s t:Simplex C n} (h:s=t) {x:C}
    (f:x ⟶ s.right.unop) (g:x ⟶ t.right.unop)
    (w:f ≫ eqToHom (congrArg (fun s:Simplex C n => s.right.unop) h)=g) :
    F.map f ≫ single F s=F.map g ≫ single F t := by
  subst t
  simpa only [eqToHom_refl,Category.comp_id] using congrArg (fun v=>F.map v ≫ single F s) w
variable {d:C} (hd:IsTerminal d)
noncomputable def augmentation : simplicial F ⟶ (SimplicialObject.const _).obj (F.obj d) where
  app n := desc F (fun s=>F.map (hd.from s.right.unop))
  naturality n m f := by
    apply hom_ext; intro s
    change single F s ≫ map F f.unop ≫ desc F _ = single F s ≫ desc F _ ≫ 𝟙 _
    rw [single_map_assoc,single_desc,Category.comp_id,single_desc,←F.map_comp]
    congr 1
    exact hd.hom_ext _ _
noncomputable def augmented : Augmented (ModuleCat.{0} R) :=
  { left := simplicial F, right := F.obj d, hom := augmentation F hd }
noncomputable def extra (n:ℕ) : Obj F n ⟶ Obj F (n+1) :=
  desc F (fun s=>single F (NervePrefix.extra hd.op s))
@[reassoc (attr:=simp)] lemma single_extra {n:ℕ} (s:Simplex C n) :
    single F s ≫ extra F hd n=single F (NervePrefix.extra hd.op s) := single_desc _ _ _
lemma extra_zero (n:ℕ) : extra F hd n ≫ (simplicial F).δ 0=𝟙 _ := by
  apply hom_ext; intro s
  change single F s ≫ extra F hd n ≫ map F (SimplexCategory.δ 0)=single F s ≫ 𝟙 _
  erw [single_extra_assoc,single_map,Category.comp_id]
  change F.map ((s.map (𝟙 _)).unop) ≫ single F s=single F s
  simp
lemma extra_tail_map {n:ℕ} (s:Simplex C n) (i j:Fin (n+1)) (hij:i≤j)
    (k:Fin (n+2)) (hk:k=i.succ) (hkj:k≤j.succ)
    (he:((NervePrefix.extra hd.op s).obj k).unop=(s.obj i).unop) :
    ((NervePrefix.extra hd.op s).map (homOfLE hkj)).unop ≫ eqToHom he =
      (s.map (homOfLE hij)).unop := by
  subst k
  change (s.map (homOfLE hij)).unop ≫ eqToHom _ = (s.map (homOfLE hij)).unop
  simp
lemma extra_succ (n:ℕ) (i:Fin (n+2)) :
    extra F hd (n+1) ≫ (simplicial F).δ i.succ=(simplicial F).δ i ≫ extra F hd n := by
  apply hom_ext; intro s
  change single F s ≫ extra F hd (n+1) ≫ map F (SimplexCategory.δ i.succ) =
    single F s ≫ map F (SimplexCategory.δ i) ≫ extra F hd n
  erw [single_extra_assoc,single_map,single_map_assoc,single_extra]
  apply weighted_eq F (NervePrefix.precomp_delta hd.op s i)
  change ((NervePrefix.extra hd.op s).map (homOfLE
    (show i.succ.succAbove (Fin.last n).succ ≤ (Fin.last (n+1)).succ from Fin.le_last _))).unop ≫ eqToHom _ =
    (s.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))).unop
  exact extra_tail_map hd s (i.succAbove (Fin.last n)) (Fin.last (n+1)) _ _
    (Fin.succ_succAbove_succ i (Fin.last n)) _ _
noncomputable def contraction : SemiExtra.Data (augmented F hd) where
  s' := single F (ComposableArrows.mk₀ (op d))
  s := extra F hd
  s'_comp_ε := by
    change single F _ ≫ desc F _=𝟙 _
    erw [single_desc]
    change F.map (hd.from d)=𝟙 (F.obj d)
    rw [show hd.from d=𝟙 d from hd.hom_ext _ _,F.map_id]
  s₀_comp_δ₁ := by
    apply hom_ext; intro s
    change single F s ≫ extra F hd 0 ≫ map F (SimplexCategory.δ 1) =
      single F s ≫ desc F _ ≫ single F (ComposableArrows.mk₀ (op d))
    erw [single_extra_assoc,single_map,single_desc_assoc]
    have hs : trunc (SimplexCategory.δ 1) (NervePrefix.extra hd.op s) = ComposableArrows.mk₀ (op d) := ComposableArrows.ext₀ rfl
    apply weighted_eq F hs
    exact hd.hom_ext _ _
  s_comp_δ₀ := extra_zero F hd
  s_comp_δ := extra_succ F hd
noncomputable def terminalHomotopyEquiv : HomotopyEquiv (complex F)
    ((ChainComplex.single₀ (ModuleCat R)).obj (F.obj d)) :=
  SemiExtra.homotopyEquiv (contraction F hd)
end CoefficientNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_CoefficientFiltered
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CoefficientNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology

variable {R:Type} [CommRing R] {C:Type} [Category.{0} C]
variable (F:C ⥤ ModuleCat.{0} R)
lemma single_eq {n:ℕ} {s t:Simplex C n} (h:s=t)
    (e:Coeff F n s=Coeff F n t) : single F s=eqToHom e ≫ single F t := by
  subst t
  simp
def overLift {n:ℕ} (s:Simplex C n) : Simplex (Over s.left.unop) n where
  obj i := op (Over.mk ((s.map (homOfLE (Fin.zero_le i))).unop))
  map {i j} f := (Over.homMk (s.map f).unop (by
    change (s.map f).unop ≫ (s.map (homOfLE (Fin.zero_le i))).unop =
      (s.map (homOfLE (Fin.zero_le j))).unop
    rw [←unop_comp,←s.map_comp]
    congr 2)).op
  map_id i := by apply Quiver.Hom.unop_inj; apply Over.OverMorphism.ext; simp; rfl
  map_comp f g := by apply Quiver.Hom.unop_inj; apply Over.OverMorphism.ext; simp
lemma overLift_forget {n:ℕ} (s:Simplex C n) : overLift s ⋙ (Over.forget s.left.unop).op=s := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  simp [overLift]
  change s.map arrow = 𝟙 _ ≫ s.map arrow
  exact (Category.id_comp _).symm
lemma overLift_map {n:ℕ} {x:C} (s:Simplex (Over x) n) :
    overLift (s ⋙ (Over.forget x).op) ⋙ (Over.map s.left.unop.hom).op=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp
    change (s.map f).unop.left = 𝟙 _ ≫ (s.map f).unop.left ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · intro i
    apply unop_injective
    refine Comma.ext (x:=(overLift (s ⋙ (Over.forget x).op) ⋙ (Over.map s.left.unop.hom).op).obj i|>.unop)
      (y:=(s.obj i).unop) rfl (Subsingleton.elim _ _) ?_
    apply heq_of_eq
    exact (s.map (homOfLE (Fin.zero_le i))).unop.w
noncomputable def overDiagram : C ⥤ SimplicialObject (ModuleCat.{0} R) where
  obj x := simplicial (Over.forget x ⋙ F)
  map {x y} f := post (Over.map f) (Over.forget y ⋙ F)
  map_id x := by
    apply NatTrans.ext; funext n
    apply hom_ext; intro s
    change single (Over.forget x ⋙ F) s ≫ desc _ _ = single (Over.forget x ⋙ F) s ≫ 𝟙 _
    erw [single_desc,Category.comp_id]
    have he : s ⋙ (Over.map (𝟙 x)).op=s := by rw [Over.mapId_eq]; rfl
    simpa only [eqToHom_refl,Category.id_comp] using! single_eq (Over.forget x ⋙ F) he rfl
  map_comp {x y z} f g := by
    apply NatTrans.ext; funext n
    apply hom_ext; intro s
    change single (Over.forget x ⋙ F) s ≫ desc _ _ =
      single (Over.forget x ⋙ F) s ≫ desc _ _ ≫ desc _ _
    erw [single_desc,single_desc_assoc,single_desc]
    have he : s ⋙ (Over.map (f ≫ g)).op=(s ⋙ (Over.map f).op) ⋙ (Over.map g).op := by
      rw [Over.mapComp_eq]; rfl
    simpa only [eqToHom_refl,Category.id_comp] using! single_eq (Over.forget z ⋙ F) he rfl
noncomputable def overCocone : Cocone (overDiagram F) where
  pt := simplicial F
  ι := { app x := post (Over.forget x) F
         naturality x y f := by
           apply NatTrans.ext; funext n
           apply hom_ext; intro s
           change single (Over.forget x ⋙ F) s ≫ desc _ _ ≫ desc _ _ =
             single (Over.forget x ⋙ F) s ≫ desc _ _
           erw [single_desc_assoc,single_desc,single_desc]
           rfl }
noncomputable def overPointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (ModuleCat R)).obj (op ⦋n⦌)).mapCocone (overCocone F)) where
  desc d := desc F (fun s=>single (Over.forget s.left.unop ⋙ F) (overLift s) ≫ d.ι.app s.left.unop)
  fac d x := by
    apply hom_ext; intro s
    change single (Over.forget x ⋙ F) s ≫ desc _ _ ≫ desc _ _ = single (Over.forget x ⋙ F) s ≫ d.ι.app x
    erw [single_desc_assoc,single_desc]
    have h:=congrArg (fun k=>single (Over.forget s.left.unop.left ⋙ F) (overLift (s ⋙ (Over.forget x).op)) ≫ k) (d.w s.left.unop.hom)
    change _ = single _ _ ≫ d.ι.app s.left.unop.left at h
    change single (Over.forget s.left.unop.left ⋙ F) (overLift (s ⋙ (Over.forget x).op)) ≫
      d.ι.app s.left.unop.left=single (Over.forget x ⋙ F) s ≫ d.ι.app x
    rw [←h]
    change single (Over.forget s.left.unop.left ⋙ F) (overLift (s ⋙ (Over.forget x).op)) ≫
      desc _ _ ≫ d.ι.app x=single (Over.forget x ⋙ F) s ≫ d.ι.app x
    erw [single_desc_assoc]
    apply congrArg (fun z=>z ≫ d.ι.app x)
    simpa only [eqToHom_refl,Category.id_comp] using! single_eq (Over.forget x ⋙ F) (overLift_map s) rfl
  uniq d m hm := by
    apply hom_ext; intro s
    erw [single_desc]
    have h:=congrArg (fun k=>single (Over.forget s.left.unop ⋙ F) (overLift s) ≫ k) (hm s.left.unop)
    change single _ _ ≫ desc _ _ ≫ m=_ at h
    erw [single_desc_assoc] at h
    have he:=weighted_eq F (overLift_forget s) (𝟙 _) (𝟙 _) (by simp; rfl)
    simp only [CategoryTheory.Functor.map_id,Category.id_comp] at he
    change single F _ ≫ m = _ at h
    rw [he] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
noncomputable def overIsColimit : IsColimit (overCocone F) :=
  evaluationJointlyReflectsColimits _ (fun n=>overPointwiseIsColimit F n.unop.len)
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex

variable {J C:Type} [Category.{0} J] [Category.{0} C]
noncomputable instance alternating_preserves :
    PreservesColimitsOfShape J (alternatingFaceMapComplex (ModuleCat.{0} ℤ)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{0} ℤ)).obj (op ⦋n⦌))
  infer_instance
end

end CoefficientNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_Coefficient
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
noncomputable def zeroπ : K.X 0 ⟶ K.homology 0 := K.pOpcycles 0 ≫ K.isoHomologyι₀.inv
instance instEpiModuleCatZeroπ : Epi (zeroπ K) := by dsimp [zeroπ]; infer_instance
@[reassoc (attr:=simp)] lemma d_zeroπ : K.d 1 0 ≫ zeroπ K=0 := by simp [zeroπ]
noncomputable def zeroDesc {V:ModuleCat.{0} R} (f:K.X 0 ⟶ V) (hf:K.d 1 0 ≫ f=0) :
    K.homology 0 ⟶ V := K.isoHomologyι₀.hom ≫ K.descOpcycles f 1 ((ComplexShape.down ℕ).prev_eq' rfl) hf
@[reassoc (attr:=simp)] lemma zeroπ_desc {V:ModuleCat.{0} R} (f:K.X 0 ⟶ V) (hf:K.d 1 0 ≫ f=0) :
    zeroπ K ≫ zeroDesc K f hf=f := by simp [zeroπ,zeroDesc]
end ChainComplex
namespace CoefficientNerve

variable {C:Type} [Category.{0} C] (F:C ⥤ ModuleCat.{0} ℤ)
noncomputable def point (x:C) : F.obj x ⟶ Obj F 0 := single F (ComposableArrows.mk₀ (op x))
noncomputable def zeroι (x:C) : F.obj x ⟶ (complex F).homology 0 :=
  single F (ComposableArrows.mk₀ (op x)) ≫ (_root_.OAI.ChainComplex.zeroπ (complex F))
lemma d10 : (complex F).d 1 0=map F (SimplexCategory.δ 0)-map F (SimplexCategory.δ 1) := by
  change (∑ i:Fin 2, (-1:ℤ)^i.val • map F (SimplexCategory.δ i))=_
  simp [Fin.sum_univ_two]
  exact (sub_eq_add_neg _ _).symm
noncomputable def edge (s:Simplex C 1) : s.right.unop ⟶ s.left.unop :=
  (s.map (homOfLE (Fin.zero_le (Fin.last 1)))).unop
lemma single_d10 (s:Simplex C 1) :
    single F s ≫ (complex F).d 1 0 =
      point F s.right.unop-
        F.map (edge s) ≫
          point F s.left.unop := by
  dsimp only [point]
  erw [d10,Preadditive.comp_sub,single_map,single_map]
  have h0 : trunc (SimplexCategory.δ (0:Fin 2)) s=ComposableArrows.mk₀ s.right :=
    ComposableArrows.ext₀ rfl
  have h1 : trunc (SimplexCategory.δ (1:Fin 2)) s=ComposableArrows.mk₀ s.left :=
    ComposableArrows.ext₀ rfl
  have t0 : tail (SimplexCategory.δ (0:Fin 2)) s=𝟙 _ := by
    change (s.map (𝟙 _)).unop=𝟙 _
    rw [s.map_id]; rfl
  erw [t0,F.map_id,Category.id_comp]
  have e0:=single_eq F h0 rfl
  have e1:=single_eq F h1 rfl
  erw [eqToHom_refl,Category.id_comp] at e0 e1
  rw [e0,e1]
  rfl
lemma zeroι_naturality {x y:C} (f:x⟶y) : F.map f ≫ zeroι F y=zeroι F x := by
  have h:=congrArg (fun k=>single F (ComposableArrows.mk₁ f.op) ≫ k) (ChainComplex.d_zeroπ (complex F))
  erw [←Category.assoc,single_d10,Preadditive.sub_comp,comp_zero] at h
  change zeroι F x - F.map f ≫ zeroι F y=0 at h
  exact (sub_eq_zero.mp h).symm
noncomputable def zeroCocone : Cocone F where
  pt := (complex F).homology 0
  ι := { app := zeroι F
         naturality x y f := by simpa using zeroι_naturality F f }
lemma desc_d10 (d:Cocone F) : (complex F).d 1 0 ≫ desc F (fun s=>d.ι.app s.right.unop)=0 := by
  apply hom_ext; intro s
  erw [←Category.assoc,single_d10,Preadditive.sub_comp]
  dsimp only [point]
  erw [single_desc,Category.assoc,single_desc,comp_zero]
  exact sub_eq_zero.mpr (d.w (s.map (homOfLE (Fin.zero_le (Fin.last 1)))).unop).symm
noncomputable def zeroIsColimit : IsColimit (zeroCocone F) where
  desc d := _root_.OAI.ChainComplex.zeroDesc (complex F) (desc F (fun s=>d.ι.app s.right.unop)) (desc_d10 F d)
  fac d x := by
    dsimp only [zeroCocone,zeroι]
    erw [Category.assoc,ChainComplex.zeroπ_desc,single_desc]
    rfl
  uniq d m hm := by
    change (complex F).homology 0 ⟶ d.pt at m
    apply (cancel_epi (_root_.OAI.ChainComplex.zeroπ (complex F))).mp
    erw [ChainComplex.zeroπ_desc]
    apply hom_ext; intro s
    rw [single_desc]
    have he : single F s = single F (ComposableArrows.mk₀ s.right) := by
      have single_equality :=
        single_eq F (ComposableArrows.ext₀ (F:=s) (G:=ComposableArrows.mk₀ s.right) rfl) rfl
      erw [eqToHom_refl,Category.id_comp] at single_equality
      exact single_equality
    rw [he]
    exact hm s.right.unop
noncomputable def zeroIso : (complex F).homology 0 ≅ colimit F :=
  (zeroIsColimit F).coconePointUniqueUpToIso (colimit.isColimit F)
end CoefficientNerve

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_CoefficientNaturality
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CoefficientNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite

lemma comp_pair {V : Type*} [Category V] {A B C D E F : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {b : E ⟶ F} {k : F ⟶ D}
    (h₁ : i ≫ f = a ≫ j) (h₂ : j ≫ g = b ≫ k) :
    i ≫ f ≫ g = (a ≫ b) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

lemma square_of_components {V : Type*} [Category V] {A B C D E F : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {k : E ⟶ D} {h : B ⟶ F} {l : A ⟶ F} {q : F ⟶ D}
    (hf : i ≫ f = a ≫ j) (hg : j ≫ g = k)
    (hh : i ≫ h = l) (hq : a ≫ k = l ≫ q) :
    i ≫ f ≫ g = i ≫ h ≫ q := by
  rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc, hh, hq]

lemma iso_transport_cancel {V : Type*} [Category V] {A B C D : V}
    (a : A ≅ B) (b : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f = a.hom ≫ g ≫ b.inv) : f ≫ b.hom = a.hom ≫ g := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section

variable {R:Type} [CommRing R] {C:Type} [Category.{0} C]
variable {F G H:C ⥤ ModuleCat.{0} R}
noncomputable def mapNat (η:F⟶G) : simplicial F ⟶ simplicial G where
  app n := desc F (fun s=>η.app s.right.unop ≫ single G s)
  naturality n m f := by
    apply hom_ext; intro s
    dsimp only [simplicial]
    rw [single_map_assoc,single_desc,single_desc_assoc,Category.assoc,single_map,
      ←Category.assoc,η.naturality,Category.assoc]
@[reassoc (attr:=simp)] lemma single_mapNat (η:F⟶G) {n:ℕ} (s:Simplex C n) :
    single F s ≫ (mapNat η).app (op ⦋n⦌)=η.app s.right.unop ≫ single G s := single_desc _ _ _
lemma mapNat_id (F:C ⥤ ModuleCat.{0} R) : mapNat (𝟙 F)=𝟙 (simplicial F) := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  simp only [mapNat,single_desc,NatTrans.id_app]
  exact (Category.comp_id (single F s)).symm
lemma mapNat_comp (η:F⟶G) (θ:G⟶H) : mapNat (η≫θ)=mapNat η ≫ mapNat θ := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  simp only [mapNat,single_desc,NatTrans.comp_app]
  change (η.app s.right.unop ≫ θ.app s.right.unop) ≫ single H s =
    single F s ≫ (mapNat η).app n ≫ (mapNat θ).app n
  exact (comp_pair (single_desc F _ s) (single_desc G _ s)).symm
end

variable {C:Type} [Category.{0} C]
noncomputable def functor : (C ⥤ ModuleCat.{0} ℤ) ⥤ SimplicialObject (ModuleCat.{0} ℤ) where
  obj := simplicial
  map := mapNat
  map_id := mapNat_id
  map_comp := mapNat_comp
noncomputable instance instAdditiveFunctorModuleCatIntSimplicialObjectFunctor : (functor (C:=C)).Additive where
  map_add := by
    intro F G η θ
    apply NatTrans.ext; funext n
    apply hom_ext; intro s
    simp only [functor,mapNat,single_desc]
    erw [NatTrans.app_add, Preadditive.comp_add, single_desc, single_desc, Preadditive.add_comp]
noncomputable def vertices (n:ℕ) : Discrete (Simplex C n) ⥤ C :=
  Discrete.functor (fun s=>s.right.unop)
noncomputable def degree (n:ℕ) : (C ⥤ ModuleCat.{0} ℤ) ⥤ ModuleCat.{0} ℤ :=
  functor ⋙ (evaluation _ _).obj (op ⦋n⦌)
noncomputable def vertexCocone (F:C ⥤ ModuleCat.{0} ℤ) (n:ℕ) : Cocone (vertices n ⋙ F) where
  pt := Obj F n
  ι := Discrete.natTrans (fun s=>single F s.as)
noncomputable def vertexIsColimit (F:C ⥤ ModuleCat.{0} ℤ) (n:ℕ) : IsColimit (vertexCocone F n) where
  desc d := desc F (fun s=>d.ι.app ⟨s⟩)
  fac _ _ := single_desc _ _ _
  uniq d _ h := hom_ext F (fun s=> (h ⟨s⟩).trans (single_desc F (fun s=>d.ι.app ⟨s⟩) s).symm)
noncomputable def degreeIso (n:ℕ) : degree (C:=C) n ≅
    (Functor.whiskeringLeft (Discrete (Simplex C n)) C (ModuleCat.{0} ℤ)).obj (vertices n) ⋙ colim :=
  NatIso.ofComponents (fun F=>(vertexIsColimit F n).coconePointUniqueUpToIso (colimit.isColimit _)) (by
    intro F G η
    apply hom_ext; intro s
    change single F s ≫ (mapNat η).app (op ⦋n⦌) ≫ _ = _
    have hg := (vertexIsColimit G n).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨s⟩
    have hf := (vertexIsColimit F n).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨s⟩
    change single G s ≫ _ = colimit.ι (vertices n ⋙ G) ⟨s⟩ at hg
    change single F s ≫ _ = colimit.ι (vertices n ⋙ F) ⟨s⟩ at hf
    exact square_of_components (single_mapNat η s) hg hf
      (colimit.ι_map (Functor.whiskerLeft (vertices n) η) ⟨s⟩).symm)
noncomputable instance degree_preservesLimits (n:ℕ) : PreservesFiniteLimits (degree (C:=C) n) :=
  preservesFiniteLimits_of_natIso (degreeIso n).symm
noncomputable instance degree_preservesColimits (n:ℕ) : PreservesColimits (degree (C:=C) n) :=
  preservesColimits_of_natIso (degreeIso n).symm
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
open ExactShapeHomology

variable {C:Type} [Category.{0} C]
noncomputable def levelMap {m n:ℕ} (f:⦋m⦌⟶⦋n⦌) : degree (C:=C) n ⟶ degree m where
  app F := (simplicial F).map f.op
  naturality _ _ η := ((mapNat η).naturality f.op).symm
lemma levelMap_id (n:ℕ) : levelMap (C:=C) (𝟙 ⦋n⦌)=𝟙 _ := by
  apply NatTrans.ext; funext F
  exact (simplicial F).map_id _
lemma levelMap_comp {l m n:ℕ} (f:⦋l⦌⟶⦋m⦌) (g:⦋m⦌⟶⦋n⦌) :
    levelMap (C:=C) (f≫g)=levelMap g ≫ levelMap f := by
  apply NatTrans.ext; funext F
  exact (simplicial F).map_comp g.op f.op
noncomputable def chainSimplicial (L:ChainComplex (C ⥤ A) ℕ) :
    SimplicialObject (ChainComplex A ℕ) where
  obj p := ((degree p.unop.len).mapHomologicalComplex c).obj L
  map f := (NatTrans.mapHomologicalComplex (levelMap f.unop) c).app L
  map_id p := by
    apply HomologicalComplex.Hom.ext; funext q
    exact congrArg (fun η=>(η.app (L.X q))) (levelMap_id p.unop.len)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext; funext q
    exact congrArg (fun η=>(η.app (L.X q))) (levelMap_comp g.unop f.unop)
noncomputable def chainSimplicialHomology (L:ChainComplex (C ⥤ A) ℕ) (q:ℕ) :
    chainSimplicial L ⋙ homologyFunctor A c q ≅ simplicial (L.homology q) :=
  NatIso.ofComponents (fun p=>(L.sc q).mapHomologyIso (degree p.unop.len)) (by
    intro p r f
    have h:=ShortComplex.homologyMap_mapNatTrans (L.sc q) (levelMap (C:=C) f.unop)
    change homologyMap ((chainSimplicial L).map f) q =
      ((L.sc q).mapHomologyIso (degree p.unop.len)).hom ≫
        (simplicial (L.homology q)).map f ≫
          ((L.sc q).mapHomologyIso (degree r.unop.len)).inv at h
    change homologyMap ((chainSimplicial L).map f) q ≫ _ = _
    exact iso_transport_cancel _ _ _ _ h)
noncomputable def double (L:ChainComplex (C ⥤ A) ℕ) :
    HomologicalComplex₂ A c c := (alternatingFaceMapComplex _).obj (chainSimplicial L)
end

end CoefficientNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TranslationCoefficientAction
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace RegularTranslation

variable {P:Type} [CommMonoid P]
abbrev C := ActionCategory P P
lemma eqToHom_val {x y:C (P:=P)} (h:x=y) : (eqToHom h).val=(1:P) := by subst y; rfl
noncomputable def shift (p:P) : C (P:=P) ⥤ C (P:=P) where
  obj x := (p*x.back:P)
  map f := ⟨f.val,by change f.val*(p*_)=_; rw [mul_left_comm]; exact congrArg (p*·) f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl
lemma shift_one : shift (1:P)=𝟭 (C (P:=P)) := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Subtype.ext
    erw [CategoryOfElements.comp_val, CategoryOfElements.comp_val, eqToHom_val, eqToHom_val]; erw [SingleObj.comp_as_mul, SingleObj.comp_as_mul, one_mul, mul_one]; rfl
  · intro x; apply (ActionCategory.objEquiv P P).symm.injective; exact one_mul _
lemma shift_mul (p q:P) : shift (p*q)=shift p ⋙ shift q := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Subtype.ext
    erw [CategoryOfElements.comp_val, CategoryOfElements.comp_val, eqToHom_val, eqToHom_val]; erw [SingleObj.comp_as_mul, SingleObj.comp_as_mul, one_mul, mul_one]; rfl
  · intro x; apply (ActionCategory.objEquiv P P).symm.injective
    change (p*q)*x.back=q*(p*x.back)
    simp only [mul_assoc,mul_left_comm]
noncomputable def forward (p:P) : 𝟭 (C (P:=P)) ⟶ shift p where
  app x := ⟨p,rfl⟩
  naturality x y f := by apply Subtype.ext; exact mul_comm _ _
end RegularTranslation
namespace RegularCoefficient
open CoefficientNerve RegularTranslation

lemma comp_step {V : Type*} [Category V] {A B C D E : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {k : E ⟶ D}
    (hf : i ≫ f = a ≫ j) (hg : j ≫ g = k) : i ≫ f ≫ g = a ≫ k := by
  rw [← Category.assoc, hf, Category.assoc, hg]

lemma comp_pair {V : Type*} [Category V] {A B C D E F : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {b : E ⟶ F} {k : F ⟶ D}
    (h₁ : i ≫ f = a ≫ j) (h₂ : j ≫ g = b ≫ k) :
    i ≫ f ≫ g = (a ≫ b) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable {P:Type} [CommMonoid P] {R:Type} [CommRing R]
variable (F:ActionCategory P P ⥤ ModuleCat.{0} R)
noncomputable def action (p:P) : simplicial F ⟶ simplicial F :=
  mapNat (Functor.whiskerRight (forward p) F) ≫ post (shift p) F
@[reassoc] lemma single_action (p:P) {n:ℕ} (s:Simplex (ActionCategory P P) n) :
    single F s ≫ (action F p).app (op ⦋n⦌)=F.map ((forward p).app s.right.unop) ≫ single F (s ⋙ (shift p).op) := by
  simp only [action,NatTrans.comp_app]
  exact comp_step (single_mapNat (Functor.whiskerRight (forward p) F) s)
    (single_post (shift p) F n s)
lemma action_one : action F (1:P)=𝟙 _ := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  change single F s ≫ (action F 1).app (op ⦋n.unop.len⦌)=single F s ≫ 𝟙 _
  rw [single_action,Category.comp_id]
  conv_rhs => rw [←Category.id_comp (single F s),←F.map_id s.right.unop]
  apply weighted_eq F (by rw [shift_one]; rfl)
  apply Subtype.ext
  erw [CategoryOfElements.comp_val, eqToHom_val, Category.comp_id]
  rfl
lemma action_mul (p q:P) : action F (p*q)=action F p ≫ action F q := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  change single F s ≫ (action F (p*q)).app (op ⦋n.unop.len⦌)=
    single F s ≫ (action F p).app (op ⦋n.unop.len⦌) ≫ (action F q).app (op ⦋n.unop.len⦌)
  have hc := comp_pair (single_action F p s) (single_action F q (s ⋙ (shift p).op))
  refine (single_action F (p*q) s).trans (Eq.trans ?_ hc.symm)
  rw [← F.map_comp]
  apply weighted_eq F (by rw [shift_mul]; rfl)
  apply Subtype.ext
  erw [CategoryOfElements.comp_val, CategoryOfElements.comp_val, eqToHom_val, Category.comp_id, SingleObj.comp_as_mul]
  exact mul_comm p q
noncomputable def representation : SingleObj P ⥤ SimplicialObject (ModuleCat.{0} R) where
  obj _ := simplicial F
  map p := action F p
  map_id _ := action_one F
  map_comp p q := by change action F (q*p)=_; rw [mul_comm q p]; exact action_mul F p q
end RegularCoefficient

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] {K L:ChainComplex (ModuleCat.{0} R) ℕ}
@[reassoc] lemma zeroπ_natural (f:K⟶L) : f.f 0 ≫ zeroπ L=zeroπ K ≫ homologyMap f 0 := by
  simp only [zeroπ,Category.assoc,_root_.ChainComplex.isoHomologyι₀_inv_naturality,HomologicalComplex.p_opcyclesMap_assoc]
end ChainComplex
namespace RegularCoefficient
open CoefficientNerve RegularTranslation

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ ModuleCat.{0} ℤ)
lemma zeroι_action (p:P) (x:ActionCategory P P) :
    zeroι F x ≫ homologyMap ((alternatingFaceMapComplex _).map (action F p)) 0=zeroι F x := by
  dsimp only [zeroι]
  erw [Category.assoc,←ChainComplex.zeroπ_natural,←Category.assoc]
  change (single F (ComposableArrows.mk₀ (op x)) ≫ (action F p).app (op ⦋0⦌)) ≫ _ = _
  erw [single_action,Category.assoc]
  exact zeroι_naturality F ((forward p).app x)
lemma homology_action_zero (p:P) :
    homologyMap ((alternatingFaceMapComplex _).map (action F p)) 0=𝟙 _ := by
  apply (zeroIsColimit F).hom_ext
  intro x
  exact (zeroι_action F p x).trans (Category.comp_id _).symm
end RegularCoefficient

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularCoefficientDouble
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularCoefficient
open CoefficientNerve

lemma iso_transport_cancel {V : Type*} [Category V] {A B C D : V}
    (a : A ≅ B) (b : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f = a.hom ≫ g ≫ b.inv) : f ≫ b.hom = a.hom ≫ g := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma inverse_square_of_identity {V : Type*} [Category V] {X Y Z T : V}
    (a : X ≅ Y) (b : X ≅ Z) (f : Y ⟶ Z) (g : X ⟶ T)
    (h : 𝟙 X ≫ b.hom = a.hom ≫ f) : f ≫ b.inv ≫ g = a.inv ≫ g ≫ 𝟙 T := by
  simp only [Category.id_comp] at h
  apply (cancel_epi a.hom).mp
  simp only [← Category.assoc, ← h, Iso.hom_inv_id, Category.id_comp, Category.comp_id]

end RegularCoefficient

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite
namespace RegularCoordinates
open CoefficientNerve RegularTranslation

variable {P:Type} [CommMonoid P]
abbrev B (n:ℕ) := Simplex (SingleObj P) n
lemma opposite_eqToHom_val {x y:Opposite (C (P:=P))} (h:x=y) : (eqToHom h).unop.val=(1:P) := by subst y; rfl
lemma single_eqToHom_val {x y:Opposite (SingleObj P)} (h:x=y) : (eqToHom h).unop=(1:P) := by subst y; rfl
noncomputable def lift {n:ℕ} (p:P) (s:B (P:=P) n) : Simplex (C (P:=P)) n where
  obj i := op ((ActionCategory.objEquiv P P) ((s.map (homOfLE (Fin.le_last i))).unop * p))
  map {i j} f := (show ((ActionCategory.objEquiv P P) ((s.map (homOfLE (Fin.le_last j))).unop * p)) ⟶
      ((ActionCategory.objEquiv P P) ((s.map (homOfLE (Fin.le_last i))).unop * p)) from
    ⟨(s.map f).unop,by
      change (s.map f).unop * ((s.map (homOfLE (Fin.le_last j))).unop * p)=_
      rw [←mul_assoc]
      have h:=congrArg Quiver.Hom.unop (s.map_comp f (homOfLE (Fin.le_last j)))
      change (s.map (f ≫ homOfLE (Fin.le_last j))).unop=
        (s.map f).unop * (s.map (homOfLE (Fin.le_last j))).unop at h
      rw [←h]
      rfl⟩).op
  map_id i := by apply Quiver.Hom.unop_inj; apply Subtype.ext; exact congrArg Quiver.Hom.unop (s.map_id i)
  map_comp f g := by apply Quiver.Hom.unop_inj; apply Subtype.ext; exact congrArg Quiver.Hom.unop (s.map_comp f g)
lemma lift_right {n:ℕ} (p:P) (s:B (P:=P) n) : (lift p s).right.unop.back=p := by
  change (s.map (𝟙 _)).unop * p=p
  rw [s.map_id]
  exact one_mul _
lemma lift_project {n:ℕ} (p:P) (s:B (P:=P) n) : lift p s ⋙ (ActionCategory.π P P).op=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    simp only [unop_comp,single_eqToHom_val,SingleObj.comp_as_mul,one_mul,mul_one]
    rfl
  · intro i; exact Subsingleton.elim _ _
lemma lift_recover {n:ℕ} (s:Simplex (C (P:=P)) n) :
    lift s.right.unop.back (s ⋙ (ActionCategory.π P P).op)=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    simp only [unop_comp]; erw [CategoryOfElements.comp_val, CategoryOfElements.comp_val, opposite_eqToHom_val, opposite_eqToHom_val]; erw [SingleObj.comp_as_mul, SingleObj.comp_as_mul, one_mul, mul_one]
    rfl
  · intro i
    apply unop_injective
    apply (ActionCategory.objEquiv P P).symm.injective
    exact (s.map (homOfLE (Fin.le_last i))).unop.property
noncomputable def coordinates (n:ℕ) : Simplex (C (P:=P)) n ≃ P × B (P:=P) n where
  toFun s := (s.right.unop.back,s ⋙ (ActionCategory.π P P).op)
  invFun x := lift x.1 x.2
  left_inv := lift_recover
  right_inv x := Prod.ext (lift_right x.1 x.2) (lift_project x.1 x.2)
lemma shift_right {n:ℕ} (q:P) (s:Simplex (C (P:=P)) n) :
    (ComposableArrows.right (s ⋙ (shift q).op)).unop.back=q*s.right.unop.back := rfl
lemma shift_project {n:ℕ} (q:P) (s:Simplex (C (P:=P)) n) :
    (s ⋙ (shift q).op) ⋙ (ActionCategory.π P P).op = s ⋙ (ActionCategory.π P P).op := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    simp only [unop_comp,single_eqToHom_val,SingleObj.comp_as_mul,one_mul,mul_one]
    rfl
  · intro i; exact Subsingleton.elim _ _
lemma shift_lift {n:ℕ} (q p:P) (s:B (P:=P) n) :
    lift p s ⋙ (shift q).op=lift (q*p) s := by
  apply (coordinates n).injective
  apply Prod.ext
  · change (ComposableArrows.right (lift p s ⋙ (shift q).op)).unop.back=(lift (q*p) s).right.unop.back
    rw [shift_right,lift_right,lift_right]
  · change (lift p s ⋙ (shift q).op) ⋙ (ActionCategory.π P P).op=lift (q*p) s ⋙ (ActionCategory.π P P).op
    rw [shift_project,lift_project,lift_project]
end RegularCoordinates

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_MonoidNerveCoordinates
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite
namespace MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] {n:ℕ}
abbrev Simplex (P:Type) [CommMonoid P] (n:ℕ) := ComposableArrows (SingleObj P)ᵒᵖ n
def labels (s:Simplex P n) : Fin n→P := fun i=>(s.map (homOfLE (Fin.castSucc_le_succ i))).unop
noncomputable def ofLabels (x:Fin n→P) : Simplex P n :=
  ComposableArrows.mkOfObjOfMapSucc (fun _=>op (SingleObj.star P)) (fun i=>Quiver.Hom.op (x i:SingleObj.star P⟶SingleObj.star P))
lemma eqToHom_val {x y:(SingleObj P)ᵒᵖ} (h:x=y) : (eqToHom h).unop=(1:P) := by subst y; rfl
@[simp] lemma labels_ofLabels (x:Fin n→P) : labels (ofLabels x)=x := by
  funext i
  exact congrArg Quiver.Hom.unop (ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i.val i.isLt)
@[simp] lemma ofLabels_labels (s:Simplex P n) : ofLabels (labels s)=s := by
  apply ComposableArrows.ext (fun _=>Subsingleton.elim _ _)
  intro i hi
  apply Quiver.Hom.unop_inj
  simp only [unop_comp,eqToHom_val,SingleObj.comp_as_mul,one_mul,mul_one]
  exact congrArg Quiver.Hom.unop (ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi)
noncomputable def equiv (P:Type) [CommMonoid P] (n:ℕ) : Simplex P n ≃ (Fin n→P) where
  toFun := labels
  invFun := ofLabels
  left_inv := ofLabels_labels
  right_inv := labels_ofLabels
lemma map_congr (s:Simplex P n) {i j i' j':Fin (n+1)} (hi:i=i') (hj:j=j')
    (f:i⟶j) (g:i'⟶j') : (s.map f).unop=(s.map g).unop := by
  subst i'; subst j'
  congr 2
  exact Subsingleton.elim _ _
end MonoidNerveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularBlock
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology

namespace RegularLabels
open CoefficientNerve RegularCoordinates MonoidNerveCoordinates

variable {P:Type}
  [CommMonoid P]
abbrev W (h v:ℕ) := (Fin v→P) × P × (Fin h→P)
lemma rightEq {v:ℕ} (p:P) (y:Fin v→P) :
    (lift p (ofLabels y)).right.unop = ActionCategory.objEquiv P P p := by
  apply (ActionCategory.objEquiv P P).symm.injective
  exact lift_right p (ofLabels y)
end RegularLabels

end

namespace MarkedCoordinates
variable {P:Type} {n:ℕ}
abbrev Split (P:Type) (n:ℕ) := Σi:Fin (n+1),(Fin i.val→P) × P × (Fin (n-i.val)→P)
def word (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) : Fin (n+1)→P :=
  fun j=>if h:j.val < i.val then y ⟨j.val,h⟩ else
    if h':j.val = i.val then p else x ⟨n-j.val,by omega⟩
@[simp] lemma word_center (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) :
    word i y p x i=p := by simp [word]
lemma word_left (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) (j:Fin i.val) :
    word i y p x ⟨j.val,by omega⟩=y j := by simp [word,j.isLt]
def vertical (w:Fin (n+1)→P) (i:Fin (n+1)) : Fin i.val→P := fun j=>w ⟨j.val,by omega⟩
def horizontal (w:Fin (n+1)→P) (i:Fin (n+1)) : Fin (n-i.val)→P := fun j=>w ⟨n-j.val,by omega⟩
lemma word_recover (w:Fin (n+1)→P) (i:Fin (n+1)) : word i (vertical w i) (w i) (horizontal w i)=w := by
  funext j
  dsimp only [word]
  split_ifs with h h'
  · rfl
  · congr 1; exact Fin.ext h'.symm
  · dsimp only [horizontal]
    congr 1
    apply Fin.ext
    dsimp
    omega
lemma vertical_word (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) :
    vertical (word i y p x) i=y := by funext j; exact word_left i y p x j
end MarkedCoordinates

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalBinary
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def oneConst : C ⥤ (Fin 1→C) := Functor.pi' (fun _=>𝟭 C)
noncomputable def piOneEquiv : (Fin 1→C) ≌ C where
  functor := Pi.eval (fun _:Fin 1=>C) 0
  inverse := oneConst
  unitIso := NatIso.ofComponents (fun values =>
    Pi.isoMk (fun index => eqToIso (congrArg values (Subsingleton.elim index 0)))) (by
      intro source target morphism
      funext index
      have index_eq : index = 0 := Subsingleton.elim _ _
      subst index
      change morphism 0 ≫ eqToHom (rfl : target 0 = target 0) =
        eqToHom (rfl : source 0 = source 0) ≫ morphism 0
      simp)
  counitIso := Iso.refl _
  functor_unitIso_comp values := by
    change eqToHom (rfl : values 0 = values 0) ≫ 𝟙 (values 0) = 𝟙 (values 0)
    simp
noncomputable def tensorPair : (Fin 2→C) ⥤ C where
  obj X := X 0 ⊗ X 1
  map f := f 0 ⊗ₘ f 1
  map_id X := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_DoubleCoordinates
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DoubleCoordinates
variable {P:Type} {n:ℕ}
abbrev Index (P:Type) (n:ℕ) := Σhv:{hv:ℕ×ℕ // hv.1+hv.2=n},(Fin hv.val.2→P) × P × (Fin hv.val.1→P)
def toSplit (s:Index P n) : MarkedCoordinates.Split P n :=
  ⟨⟨s.1.val.2,by have:=s.1.property; omega⟩,s.2.1,s.2.2.1,
    fun j=>s.2.2.2 ⟨j.val,by have:=s.1.property; dsimp at *; omega⟩⟩
def ofSplit (s:MarkedCoordinates.Split P n) : Index P n :=
  ⟨⟨(n-s.1.val,s.1.val),by omega⟩,s.2.1,s.2.2.1,s.2.2.2⟩
lemma payload_heq {m n v:ℕ} (e:m=n) (y:Fin v→P) (p:P) (x:Fin n→P)
    (hp:∀j:Fin m,j.val<n) : HEq (y,p,fun j:Fin m=>x ⟨j.val,hp j⟩) (y,p,x) := by
  subst n
  rfl
lemma left_inv (s:Index P n) : ofSplit (toSplit s)=s := by
  rcases s with ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  subst n
  change Fin v→P at y
  change Fin h→P at x
  dsimp [toSplit,ofSplit]
  apply Sigma.ext
  · exact Subtype.ext (Prod.ext (Nat.add_sub_cancel h v) rfl)
  · exact payload_heq (Nat.add_sub_cancel h v) y p x _
lemma right_inv (s:MarkedCoordinates.Split P n) : toSplit (ofSplit s)=s := by
  rcases s with ⟨i,y,p,x⟩
  rfl
noncomputable def equiv (P:Type) (n:ℕ) : Index P n ≃ MarkedCoordinates.Split P n where
  toFun:=toSplit
  invFun:=ofSplit
  left_inv:=left_inv
  right_inv:=right_inv
end DoubleCoordinates

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_MonoidFaceLabels
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite
namespace MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] {n:ℕ}
def faceLabels (k:Fin (n+2)) (x:Fin (n+1)→P) : Fin n→P := fun j=>
  if j.val+1 < k.val then x j.castSucc else
  if j.val+1 = k.val then x j.castSucc * x j.succ else x j.succ
lemma labels_face (s:Simplex P (n+1)) (k:Fin (n+2)) :
    labels ((nerve _).δ k s)=faceLabels k (labels s) := by
  funext j
  dsimp only [faceLabels]
  change (s.map (homOfLE (show k.succAbove j.castSucc ≤ k.succAbove j.succ from
    (Fin.succAboveOrderEmb k).monotone (Fin.castSucc_le_succ j)))).unop = _
  split_ifs with h h'
  · apply map_congr s
    · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val < k.val; omega)
    · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val+1 < k.val; exact h)
  · have hh : k.succAbove j.castSucc=j.castSucc.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by change j.val < k.val; omega)
    have hh' : k.succAbove j.succ=j.succ.succ :=
      Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ j.val+1; omega)
    rw [map_congr s hh hh' _ (homOfLE (show j.castSucc.castSucc ≤ j.succ.succ from by
      change j.val ≤ j.val+2; omega))]
    have hc:=congrArg Quiver.Hom.unop (s.map_comp
      (homOfLE (Fin.castSucc_le_succ j.castSucc))
      (homOfLE (Fin.castSucc_le_succ j.succ)))
    exact hc
  · apply map_congr s
    · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ j.val; omega)
    · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ j.val+1; omega)
lemma tail_face_val (s:Simplex P (n+1)) (k:Fin (n+2)) (hk:k≠Fin.last (n+1)) :
    (s.map (homOfLE (Fin.le_last (k.succAbove (Fin.last n))))).unop=(1:P) := by
  have h:k.succAbove (Fin.last n)=Fin.last (n+1) := by
    apply Fin.ext
    rw [Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ n; have:=k.isLt; have hn:=Fin.val_ne_of_ne hk; dsimp at hn; omega)]
    rfl
  have he:=map_congr s h rfl (homOfLE (Fin.le_last (k.succAbove (Fin.last n)))) (𝟙 _)
  rw [he,s.map_id]
  rfl
lemma tail_face_last_val (s:Simplex P (n+1)) :
    (s.map (homOfLE (Fin.le_last ((Fin.last (n+1)).succAbove (Fin.last n))))).unop=labels s (Fin.last n) := by
  apply map_congr s
  · simp
  · rfl
end MonoidNerveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularLiftFaces
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite
namespace RegularCoordinates
open CoefficientNerve MonoidNerveCoordinates

variable {P:Type} [CommMonoid P]
noncomputable def arrow (a p:P) : ActionCategory.objEquiv P P p ⟶ ActionCategory.objEquiv P P (a*p) := ⟨a,rfl⟩
lemma arrow_one (p:P) : arrow (1:P) p=eqToHom (congrArg (ActionCategory.objEquiv P P) (one_mul p).symm) := by
  apply Subtype.ext
  exact (RegularTranslation.eqToHom_val _).symm
end RegularCoordinates
namespace RegularLabels
open CoefficientNerve RegularCoordinates MonoidNerveCoordinates

variable {P:Type}
  [CommMonoid P]
noncomputable def faceWeight {n:ℕ} (k:Fin (n+2)) (y:Fin (n+1)→P) : P :=
  if k=Fin.last (n+1) then y (Fin.last n) else 1
lemma tail_face {n:ℕ} (k:Fin (n+2)) (y:Fin (n+1)→P) :
    tail (SimplexCategory.δ k) (ofLabels y)=faceWeight k y := by
  dsimp only [faceWeight]
  split_ifs with h
  · subst k
    exact (tail_face_last_val (ofLabels y)).trans (congrFun (labels_ofLabels y) (Fin.last n))
  · exact tail_face_val (ofLabels y) k h
end RegularLabels

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularTotalDifferential
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace FilteredEdge

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
structure Data where
  s : D →ₗ[R] A
  d : A →ₗ[R] B
  e : B →ₗ[R] C
  ds : d.comp s = 0
  ed : e.comp d = 0
  FD : ℤ → Submodule R D
  FA : ℤ → Submodule R A
  FB : ℤ → Submodule R B
  FC : ℤ → Submodule R C
  monoA : Monotone FA
  monoB : Monotone FB
namespace Data
variable (K : Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
variable (p : ℤ)
def inputs (k : ℤ) : Submodule R A := K.FA k ⊓ (K.FB p).comap K.d
end Data
end FilteredEdge

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ResolutionAugmentation
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C) [W.IsMultiplicative]

def verticalDiagonalFunctor {n:ℕ} (F:Fin (n+1)⥤Vertical W n) : Fin (n+1)⥤C where
  obj i := (F.obj i).obj.obj i
  map {i j} f := (F.map f).hom.app i ≫ (F.obj j).obj.map f
  map_id _ := by simp
  map_comp {i j k} f g := by
    have hn := (F.map g).hom.naturality f
    simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [←Category.assoc ((F.map g).hom.app i),←hn]
    simp only [Category.assoc]
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarRowFiniteness
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace NerveComponents

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
noncomputable def toSkeletonπ : (nerve C).π₀ → Skeleton C :=
  SSet.π₀.lift (fun x=>toSkeleton (nerveEquiv x)) (fun {_ _} e=>congr_toSkeleton_of_iso (asIso (nerve.homEquiv e)))
noncomputable def fromSkeletonπ (p:Skeleton C) : (nerve C).π₀ :=
  SSet.π₀.mk (nerveEquiv.symm ((fromSkeleton C).obj p))
lemma roundtrip (x:(nerve C).π₀) : fromSkeletonπ (toSkeletonπ x)=x := by
  obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective x
  have e : (fromSkeleton C).obj (toSkeleton (nerveEquiv x)) ≅ nerveEquiv x :=
    Skeleton.isoOfEq (toSkeleton_fromSkeleton_obj _)
  exact (SSet.π₀.sound (nerve.edgeMk e.hom)).trans (by erw [Equiv.symm_apply_apply])
noncomputable def componentEquiv : (nerve C).π₀ ≃ Skeleton C where
  toFun := toSkeletonπ
  invFun := fromSkeletonπ
  left_inv := roundtrip
  right_inv p := toSkeleton_fromSkeleton_obj p
noncomputable def map (F:C⥤D) : Skeleton C → Skeleton D :=
  Quotient.lift (fun x=>toSkeleton (F.obj x)) (by rintro x y ⟨e⟩; exact congr_toSkeleton_of_iso (F.mapIso e))
@[simp] lemma map_mk (F:C⥤D) (x:C) : map F (toSkeleton x)=toSkeleton (F.obj x) := rfl
end NerveComponents

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarComponents
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

section
open NerveComponents

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma single_eqToHom {P:Type} [Monoid P] {x y:SingleObj P} (h:x=y) : eqToHom h=(1:P) := by subst y; rfl
end

open NerveComponents AlgebraicTopology

end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace FilteredNerve

variable (C:Type) [Category.{0} C]
def diagram : C ⥤ SSet := Over.mapFunctor C ⋙ nerveFunctor
def cocone : Cocone (diagram C) where
  pt := nerve C
  ι := { app x := nerveMap (Over.forget x)
         naturality x y f := by change nerveMap (Over.map f ⋙ Over.forget y)=_; rfl }
def lastCocone {n:ℕ} (s:ComposableArrows C n) : s ⟶ (Functor.const _).obj s.right where
  app i := s.map (homOfLE (Fin.le_last i))
  naturality i j f := by
    change s.map f ≫ s.map (homOfLE (Fin.le_last j)) = s.map (homOfLE (Fin.le_last i)) ≫ 𝟙 _
    rw [Category.comp_id,←s.map_comp]
    congr 1
def lift {n:ℕ} (s:ComposableArrows C n) : ComposableArrows (Over s.right) n :=
  Over.lift s (lastCocone C s)
lemma lift_map {n:ℕ} {x:C} (s:ComposableArrows (Over x) n) :
    lift C (s ⋙ Over.forget x) ⋙ Over.map s.right.hom=s := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    refine Comma.ext (x:=(lift C (s ⋙ Over.forget x) ⋙ Over.map s.right.hom).obj i)
      (y:=s.obj i) rfl (Subsingleton.elim _ _) ?_
    apply heq_of_eq
    change (s.map (homOfLE (Fin.le_last i))).left ≫ s.right.hom=(s.obj i).hom
    exact (s.map (homOfLE (Fin.le_last i))).w
  case h_map =>
    intro i j f
    apply Over.OverMorphism.ext
    simp only [Functor.comp_map,Over.comp_left]
    erw [Over.eqToHom_left,Over.eqToHom_left]
    simp [lift,Over.lift]
    erw [eqToHom_refl,Category.id_comp]
    rfl
noncomputable def pointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (Type)).obj (op ⦋n⦌)).mapCocone (cocone C)) where
  desc d := ↾fun s => d.ι.app s.right (lift C s)
  fac d x := by
    ext s
    have h:=congrArg (fun k => k (lift C (s ⋙ Over.forget x))) (d.w s.right.hom)
    change d.ι.app x (lift C (s ⋙ Over.forget x) ⋙ Over.map s.right.hom)=_ at h
    erw [lift_map] at h
    exact h.symm
  uniq d m hm := by
    ext s
    have h:=congrArg (fun k => k (lift C s)) (hm s.right)
    exact h
noncomputable def isColimit : IsColimit (cocone C) :=
  evaluationJointlyReflectsColimits _ (fun n => pointwiseIsColimit C n.unop.len)
instance connected [IsFiltered C] : (nerve C).IsConnected where
  allEq u v := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective v
    let a := nerveEquiv x
    let b := nerveEquiv y
    have h₁ := SSet.π₀.sound (nerve.edgeMk (IsFiltered.leftToMax a b))
    have h₂ := SSet.π₀.sound (nerve.edgeMk (IsFiltered.rightToMax a b))
    have component_eq := h₁.trans h₂.symm
    change SSet.π₀.mk (X:=nerve C) (nerveEquiv.symm (nerveEquiv x)) =
      SSet.π₀.mk (X:=nerve C) (nerveEquiv.symm (nerveEquiv y)) at component_eq
    erw [Equiv.symm_apply_apply,Equiv.symm_apply_apply] at component_eq
    exact component_eq
  nonempty := by
    let := IsFiltered.nonempty (C:=C)
    exact ⟨nerveEquiv.symm (Classical.arbitrary C)⟩
end FilteredNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_NerveProduct
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveProduct

variable (C D:Type) [Category.{0} C] [Category.{0} D]
noncomputable def iso : nerve (C×D) ≅ nerve C⊗nerve D where
  hom := {app _:=↾fun F=>(F⋙CategoryTheory.Prod.fst C D,F⋙CategoryTheory.Prod.snd C D)
          naturality _ _ _:=rfl}
  inv := {app _:=↾fun F=>F.1.prod' F.2
          naturality _ _ _:=rfl}
  hom_inv_id := by ext p F; rfl
  inv_hom_id := by ext p F <;> rfl
variable {C D} {C' D':Type} [Category.{0} C'] [Category.{0} D']
@[reassoc] lemma natural (f:C⥤C') (g:D⥤D') :
    nerveMap (f.prod g) ≫ (iso C' D').hom=(iso C D).hom ≫ (nerveMap f⊗ₘnerveMap g) := rfl
@[simp] lemma fst : (iso C D).hom ≫ CartesianMonoidalCategory.fst _ _=nerveMap (CategoryTheory.Prod.fst C D) := rfl
@[simp] lemma snd : (iso C D).hom ≫ CartesianMonoidalCategory.snd _ _=nerveMap (CategoryTheory.Prod.snd C D) := rfl
end NerveProduct
namespace ComponentStable
open ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def reprObjectIso (U:C) : repr (toSkeleton U) ≅ U := Skeleton.isoOfEq (repr_component _)
noncomputable def tensorFunctor : C×C ⥤ C where
  obj X:=X.1⊗X.2
  map f:=f.1⊗ₘf.2
  map_id _:=by simp
  map_comp _ _:=by simp [tensorHom_comp_tensorHom]
noncomputable def multiplication : nerve C⊗nerve C ⟶ nerve C :=
  (NerveProduct.iso C C).inv ≫ nerveMap tensorFunctor
noncomputable def leftTensorIso (U:C) :
    ((tensorLeft U).prod (𝟭 C)) ⋙ tensorFunctor ≅ tensorFunctor ⋙ tensorLeft U :=
  NatIso.ofComponents (fun X=>α_ U X.1 X.2) (by
    intro X Y f
    change ((U ◁ f.1)⊗ₘf.2) ≫ (α_ U Y.1 Y.2).hom = (α_ U X.1 X.2).hom ≫ (U ◁ (f.1⊗ₘf.2))
    simp [←id_tensorHom])
noncomputable def rightTensorIso (U:C) :
    ((𝟭 C).prod (tensorRight U)) ⋙ tensorFunctor ≅ tensorFunctor ⋙ tensorRight U :=
  NatIso.ofComponents (fun X=>(α_ X.1 X.2 U).symm) (by
    intro X Y f
    change (f.1⊗ₘ(f.2 ▷ U)) ≫ (α_ Y.1 Y.2 U).inv = (α_ X.1 X.2 U).inv ≫ ((f.1⊗ₘf.2) ▷ U)
    simp [←tensorHom_id])
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedTensorTwo
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
noncomputable def positiveIsCokernel (n:ℕ) (hn:K.d (n+1) n=0) :
    IsColimit (CokernelCofork.ofπ (positiveπ K n hn) (d_positiveπ K n hn)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun f hf=>⟨positiveDesc K n hn f hf,positiveπ_desc K n hn f hf⟩)
end ChainComplex

end

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] {K L:ChainComplex (ModuleCat.{0} R) ℕ}
@[reassoc] lemma positiveπ_natural (f:K⟶L) (n:ℕ) (hK:K.d (n+1) n=0) (hL:L.d (n+1) n=0) :
    positiveπ K n hK ≫ homologyMap f (n+1)=f.f (n+1) ≫ positiveπ L n hL := by
  apply (cancel_mono (L.homologyι (n+1))).mp
  simp only [positiveπ,Category.assoc,homologyι_naturality,isoHomologyι_inv_hom_id_assoc,
    isoHomologyι_inv_hom_id,Category.comp_id,p_opcyclesMap]
end ChainComplex

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace GroupNerveCoordinates
variable (G:Type) [Monoid G]
instance zero_subsingleton : Subsingleton ((nerve (SingleObj G)).obj (op ⦋0⦌)) :=
  ⟨fun _ _=>nerveEquiv.injective (Subsingleton.elim _ _)⟩
instance connected : (nerve (SingleObj G)).IsConnected where
  nonempty:=⟨nerveEquiv.symm (SingleObj.star G)⟩
  allEq x y:=by
    obtain ⟨x,rfl⟩:=SSet.π₀.mk_surjective x
    obtain ⟨y,rfl⟩:=SSet.π₀.mk_surjective y
    congr 1
    exact Subsingleton.elim _ _
end GroupNerveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedSigns
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MarkedSigns

def exponent (h v:ℕ) : ℕ := h*v+h*(h+3)/2
lemma square (n:ℕ) : (-1:ℤ)^n * (-1)^n=1 := by
  rw [←mul_pow]; norm_num
end MarkedSigns

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEdge
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def pairAt {n:ℕ} (i j:Fin n) : (Fin n→C) ⥤ C where
  obj X := X i ⊗ X j
  map f := f i ⊗ₘ f j
  map_id X := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]
noncomputable def faceEdge {n:ℕ} (k:Fin (n+2)) (j:Fin n) : (Fin (n+1)→C) ⥤ C :=
  if j.val+1<k.val then Pi.eval _ j.castSucc else
  if j.val+1=k.val then pairAt j.castSucc j.succ else Pi.eval _ j.succ
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedLowHomology
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Opposite
namespace CommMonoidOpposite

variable (P:Type) [CommMonoid P]
def functor : (SingleObj P)ᵒᵖ ⥤ SingleObj P where
  obj _ := SingleObj.star _
  map f := f.unop
  map_id _ := rfl
  map_comp _ _ := mul_comm _ _
instance instFaithfulOppositeSingleObjFunctor : (functor P).Faithful where
  map_injective h := Quiver.Hom.unop_inj h
instance instFullOppositeSingleObjFunctor : (functor P).Full where
  map_surjective morphism := ⟨morphism.op,rfl⟩
instance instEssSurjOppositeSingleObjFunctor : (functor P).EssSurj where
  mem_essImage _ := ⟨op (SingleObj.star _), ⟨eqToIso (Subsingleton.elim _ _)⟩⟩
instance instIsEquivalenceOppositeSingleObjFunctor : (functor P).IsEquivalence := ⟨inferInstance,inferInstance,inferInstance⟩
end CommMonoidOpposite

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PiBinary
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet

noncomputable def binaryIso (X:Fin 2→SSet) : obj X ≅ X 0⊗X 1 where
  hom := {app _:=↾fun z=>(z 0,z 1)
          naturality _ _ _:=rfl}
  inv := {app _:=↾fun z=>Fin.cases z.1 (Fin.cases z.2 (fun i=>i.elim0))
          naturality _ _ _:=by apply ConcreteCategory.hom_ext; intro z; funext i; fin_cases i <;> rfl}
  hom_inv_id:=by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro z; funext i; fin_cases i <;> rfl
  inv_hom_id:=by ext p z <;> rfl
@[simp] lemma binaryIso_fst (X:Fin 2→SSet) : (binaryIso X).hom ≫ CartesianMonoidalCategory.fst _ _=proj X 0 := rfl
@[simp] lemma binaryIso_snd (X:Fin 2→SSet) : (binaryIso X).hom ≫ CartesianMonoidalCategory.snd _ _=proj X 1 := rfl
end PiSSet

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarDegreeTwoFinite
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace StableBarOne
open ComponentTranslation IntervalBar.Diagram MarkedH1

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]

lemma eq_of_boundary {V : Type*} [AddGroup V] {x y z a b : V}
    (h : x - y + z = 0) (hx : x = a) (hy : y = b) (hz : z = 0) : b = a := by
  rw [hx,hy,hz,add_zero] at h
  exact (sub_eq_zero.mp h).symm

end StableBarOne

end OAI
end


