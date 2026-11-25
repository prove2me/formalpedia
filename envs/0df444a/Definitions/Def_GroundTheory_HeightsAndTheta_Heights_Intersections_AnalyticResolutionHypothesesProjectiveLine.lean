-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:26:39.294367+00:00
-- url     : https://prove2.me/theorems/9ada230b-4d5e-4f16-b2a1-dd1bbb03cb9e
-- title:
--   Analytic Resolution Hypotheses Projective Line
-- statement:
--   Definitions and structural lemmas for Analytic Resolution Hypotheses Projective Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AnalyticResolutionHypothesesProjectiveLine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjectiveLineHomogeneousLift
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_exists_atlas
import Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_bot_dim
import Theorems.Thm_ReciprocityTheory_AnForm_R_locRing_bot_regular
import Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdeal_fin_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)
abbrev HLine {K : Type} [Fintype K] (ι : K → Type) := ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
section Objects
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
abbrev MCone (ι : K → Type) := (Σ k, ι k) → ℂ
def tsmul (c : K → ℂ) (z : MCone ι) : MCone ι := fun q => c q.1 * z q
def zPts (P : Ideal (MRing ι ℂ)) : Set (MCone ι) :=
  ReciprocityTheory.AnForm.R.conePts P
def IsProjVar (P : Ideal (MRing ι ℂ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P ∧ ringKrullDim (MRing ι ℂ ⧸ P) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
def IsLocSmooth (P : Ideal (MRing ι ℂ)) (g : MCone ι → ℝ) : Prop :=
  ∀ z ∈ zPts P, ∃ U ∈ 𝓝 z, ∃ G : MCone ι → ℝ, ContDiffOn ℝ ∞ G U ∧ ∀ w ∈ U ∩ zPts P, g w = G w
def IsSmoothFn (P : Ideal (MRing ι ℂ)) (g : MCone ι → ℝ) : Prop :=
  (∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ zPts P, g (tsmul c z) = g z) ∧ IsLocSmooth P g
def logH (L : HLine ι) : MCone ι → ℝ := fun z => Real.log (L.h z)
def IsSmoothMetric (P : Ideal (MRing ι ℂ)) (L : HLine ι) : Prop :=
  IsLocSmooth P (logH L)
def IsSmoothPot (P : Ideal (MRing ι ℂ)) (φ : MCone ι → ℝ) : Prop :=
  (∃ a : K → ℤ, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ zPts P,
    φ (tsmul c z) = φ z + ∑ k, (a k : ℝ) * Real.log ‖c k‖) ∧ IsLocSmooth P φ
def secNorm (A : HLine ι) (s : MRing ι ℂ) : MCone ι → ℝ :=
  fun z => Real.log (‖eval z s‖ / A.h z)
def IsFormSec {R : Type} [CommRing R] (P : Ideal (MRing ι R)) (A : HLine ι) (s : MRing ι R) : Prop :=
  ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P
def comps {R : Type} [CommRing R] (P : Ideal (MRing ι R)) (s : MRing ι R) :
    Set (Ideal (MRing ι R)) :=
  {W | W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W}
variable (ι) in

structure Res (P : Ideal (MRing ι ℂ)) (e : ℕ) where

  D : Ideal (MRing ι ℂ)
  homog : IsMultiHomogIdeal D
  not_le : ¬ D ≤ P

  R : ReciprocityTheory.AnForm.R.AlgRes ι P D e
namespace Res
variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)
def idx (x : R.R.M) : Fin R.R.n := (R.R.cover x).choose
theorem mem_src_idx (x : R.R.M) : x ∈ R.R.src (R.idx x) := (R.R.cover x).choose_spec
def liftAt (x y : R.R.M) : MCone ι :=
  fun q => eval (R.R.coord (R.idx x) y) (R.R.lift (R.idx x) q)
def pt (x : R.R.M) : MCone ι := R.liftAt x x
def atlas : FinHolAtlas e R.R.M := R.R.exists_atlas.choose
def pot (φ : MCone ι → ℝ) : LocPot R.R.M where
  U x := R.R.src (R.idx x)
  isOpen_U _ := R.R.isOpen_alt_bis _
  mem_U x := R.mem_src_idx x
  φ x y := φ (R.liftAt x y)
def int (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) : ℝ :=
  mInt R.atlas (fun j => R.pot (φ j)) (fun x => g (R.pt x))
end Res
open Classical in

def zInt (P : Ideal (MRing ι ℂ)) (e : ℕ) (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) : ℝ :=
  if h : Nonempty (Res ι P e) then h.some.int φ g else 0
def extC (P0 : Ideal (MRing ι ℚ)) : Ideal (MRing ι ℂ) :=
  ReciprocityTheory.AnForm.R.extC P0
def sC (s : MRing ι ℚ) : MRing ι ℂ := MvPolynomial.map (algebraMap ℚ ℂ) s
def IsProjVarQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P0 ∧ ringKrullDim (MRing ι ℚ ⧸ P0) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
def zIntQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ) : ℝ :=
  ∑ᶠ Z ∈ (extC P0).minimalPrimes, zInt Z e φ g
end Objects
def projectiveLineZeroForm_holds.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) (W : Set X) (B : FinHolAtlas e W),
    IsPotential A L → IsSection A L s → IsSNC A L s ![1] ![W] → HoloMap B A Subtype.val →
    ∀ v : X → ℝ, A.Smooth v → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
        mInt B (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) -
          mInt A (Fin.cons L Φ) v
def ResIndep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (R R' : Res ι P e) (φ : Fin e → MCone ι → ℝ) (g : MCone ι → ℝ),
    IsProjVar P e → (∀ j, IsSmoothPot P (φ j)) →
    (IsSmoothFn P g ∨ ∃ (A : HLine ι) (s : MRing ι ℂ), IsSmoothMetric P A ∧ IsFormSec P A s ∧
      g = secNorm A s) →
    R.int φ g = R'.int φ g
def S3.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (v w : MCone ι → ℝ),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothFn P v → IsSmoothFn P w →
    zInt P (e + 1) (Fin.cons w fun j => logH (L j)) v =
      zInt P (e + 1) (Fin.cons v fun j => logH (L j)) w
def ThreeSphereMass.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L L' : Fin e → HLine ι),
    IsProjVar P e → Nonempty (Res ι P e) → (∀ j, IsSmoothMetric P (L j)) →
    (∀ j, IsSmoothMetric P (L' j)) → (∀ j, (L j).a = (L' j).a) →
    zInt P e (fun j => logH (L j)) (fun _ => 1) = zInt P e (fun j => logH (L' j)) (fun _ => 1)
def S4.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (R : Res ι P e) (φ : Fin e → MCone ι → ℝ) (A : HLine ι)
    (s : MRing ι ℂ),
    IsProjVar P e → (∀ j, IsSmoothPot P (φ j)) → IsSmoothMetric P A → IsFormSec P A s →
    MIntegrable R.atlas (fun j => R.pot (φ j)) (fun x => secNorm A s (R.pt x))
def PoincareLelongAlt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A : HLine ι) (s : MRing ι ℂ)
    (v : MCone ι → ℝ),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ W ∈ comps P s, Nonempty (Res ι W e)) →
    (∀ j, IsSmoothMetric P (L j)) → IsSmoothMetric P A → IsFormSec P A s → IsSmoothFn P v →
    zInt P (e + 1) (Fin.cons v fun j => logH (L j)) (secNorm A s) =
      (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) v) -
        zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) v
def Degrees.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι),
    IsProjVar P e → Nonempty (Res ι P e) → (∀ j, IsSmoothMetric P (L j)) →
    zInt P e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ P (fun j => (L j).a) : ℝ)
def ProjectiveLineTwo.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A A' : HLine ι) (s s' : MRing ι ℂ),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ W ∈ comps P s, Nonempty (Res ι W e)) →
    (∀ W ∈ comps P s', Nonempty (Res ι W e)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothMetric P A → IsSmoothMetric P A' → IsFormSec P A s → IsFormSec P A' s' →
    (∀ W ∈ comps P s, W ∉ comps P s') →
    (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) (secNorm A' s')) +
        zInt P (e + 1) (Fin.cons (logH A') fun j => logH (L j)) (secNorm A s) =
      (∑ᶠ W ∈ comps P s', (divCycle P s' W : ℝ) * zInt W e (fun j => logH (L j)) (secNorm A s)) +
        zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (secNorm A' s')
def BCMult.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (s : MRing ι ℚ) (a : K → ℕ) (W : Ideal (MRing ι ℚ))
    (Wa : Ideal (MRing ι ℂ)),
    IsProjVarQ P0 (e + 1) → IsMultiHomog s a → s ∉ P0 → W ∈ comps P0 s →
    Wa ∈ (extC W).minimalPrimes →
    divCycle P0 s W = ∑ᶠ Z ∈ (extC P0).minimalPrimes, divCycle Z (sC s) Wa
def BCCommon.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (s s' : MRing ι ℚ) (a a' : K → ℕ) (Z Wa : Ideal (MRing ι ℂ)),
    IsProjVarQ P0 (e + 1) → IsMultiHomog s a → s ∉ P0 → IsMultiHomog s' a' → s' ∉ P0 →
    Z ∈ (extC P0).minimalPrimes → Wa ∈ comps Z (sC s) → Wa ∈ comps Z (sC s') →
    Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) ∈ comps P0 s ∩ comps P0 s'
def BCDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (bs : Fin e → K → ℤ),
    IsProjVarQ P0 e →
    intNum ℚ P0 bs = ∑ᶠ Z ∈ (extC P0).minimalPrimes, intNum ℂ Z bs
def DegreesQ.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (L : Fin e → HLine ι),
    IsProjVarQ P0 e → (∀ Z ∈ (extC P0).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ j, IsSmoothMetric (extC P0) (L j)) →
    zIntQ P0 e (fun j => logH (L j)) (fun _ => 1) = (intNum ℚ P0 (fun j => (L j).a) : ℝ)
def ProjectiveLineOverRationals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (L : Fin e → HLine ι) (A : HLine ι) (s : MRing ι ℚ)
    (v : MCone ι → ℝ),
    IsProjVarQ P0 (e + 1) → (∀ Z ∈ (extC P0).minimalPrimes, Nonempty (Res ι Z (e + 1))) →
    (∀ W ∈ comps P0 s, ∀ Z ∈ (extC W).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ j, IsSmoothMetric (extC P0) (L j)) → IsSmoothMetric (extC P0) A → IsFormSec P0 A s →
    IsSmoothFn (extC P0) v →
    zIntQ P0 (e + 1) (Fin.cons v fun j => logH (L j)) (secNorm A (sC s)) =
      (∑ᶠ W ∈ comps P0 s, (divCycle P0 s W : ℝ) * zIntQ W e (fun j => logH (L j)) v) -
        zIntQ P0 (e + 1) (Fin.cons (logH A) fun j => logH (L j)) v
def ProjectivePlaneOverRationals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P0 : Ideal (MRing ι ℚ)) (e : ℕ) (L : Fin e → HLine ι) (A A' : HLine ι) (s s' : MRing ι ℚ),
    IsProjVarQ P0 (e + 1) → (∀ Z ∈ (extC P0).minimalPrimes, Nonempty (Res ι Z (e + 1))) →
    (∀ W ∈ comps P0 s, ∀ Z ∈ (extC W).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ W ∈ comps P0 s', ∀ Z ∈ (extC W).minimalPrimes, Nonempty (Res ι Z e)) →
    (∀ j, IsSmoothMetric (extC P0) (L j)) → IsSmoothMetric (extC P0) A →
    IsSmoothMetric (extC P0) A' → IsFormSec P0 A s → IsFormSec P0 A' s' →
    (∀ W ∈ comps P0 s, W ∉ comps P0 s') →
    (∑ᶠ W ∈ comps P0 s, (divCycle P0 s W : ℝ) *
        zIntQ W e (fun j => logH (L j)) (secNorm A' (sC s'))) +
        zIntQ P0 (e + 1) (Fin.cons (logH A') fun j => logH (L j)) (secNorm A (sC s)) =
      (∑ᶠ W ∈ comps P0 s', (divCycle P0 s' W : ℝ) *
        zIntQ W e (fun j => logH (L j)) (secNorm A (sC s))) +
        zIntQ P0 (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (secNorm A' (sC s'))
section Ring
variable {K : Type} {ι : K → Type}
theorem mem_span_X_iff {R : Type} [CommRing R] (q : Σ k, ι k) (f : MRing ι R) :
    f ∈ Ideal.span {(X q : MRing ι R)} ↔ ∀ m ∈ f.support, m q ≠ 0 := by
  rw [← Set.image_singleton, mem_ideal_span_X_image]
  simp
theorem isMultiHomogIdeal_span_X [Fintype K] [DecidableEq K] {R : Type} [CommRing R] (q : Σ k, ι k) :
    IsMultiHomogIdeal (Ideal.span {(X q : MRing ι R)}) := by
  intro f hf b
  rw [mem_span_X_iff] at hf ⊢
  intro m hm
  apply hf m
  rw [mem_support_iff] at hm ⊢
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact hm
  · exact absurd rfl hm
theorem isPrime_span_X {R : Type} [CommRing R] [IsDomain R] (q : Σ k, ι k) :
    (Ideal.span {(X q : MRing ι R)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero q)).mpr X_prime
theorem X_ne_bot {R : Type} [CommRing R] [Nontrivial R] (q : Σ k, ι k) :
    (X q : MRing ι R) ∉ (⊥ : Ideal (MRing ι R)) := by
  rw [Submodule.mem_bot]
  exact X_ne_zero q
end Ring
abbrev ι1 : Unit → Type := fun _ => Fin 2
abbrev Xj {R : Type} [CommRing R] (j : Fin 2) : MRing ι1 R := X ⟨(), j⟩
abbrev ptI {R : Type} [CommRing R] (j : Fin 2) : Ideal (MRing ι1 R) := Ideal.span {Xj j}
theorem fin_two_eq_or_eq_add_one (j i : Fin 2) : i = j ∨ i = j + 1 := by
  fin_cases j <;> fin_cases i <;> decide
def projLineResolution : Res ι1 (⊥ : Ideal (MRing ι1 ℂ)) 1 where
  D := ptI 0
  homog := isMultiHomogIdeal_span_X _
  not_le h := X_ne_bot (R := ℂ) (⟨(), 0⟩ : Σ _ : Unit, Fin 2) (h (Ideal.subset_span rfl))
  R := ReciprocityTheory.AnForm.R.projectiveLineAlgRes
def ptVec (j : Fin 2) : MCone ι1 := fun q => if q.2 = j then 0 else 1
def ptLift (j : Fin 2) : (Σ _ : Unit, Fin 2) → MvPolynomial (Fin 0) ℂ :=
  fun q => if q.2 = j then 0 else 1
theorem eval_ptLift (j : Fin 2) (y : Fin 0 → ℂ) (q : Σ _ : Unit, Fin 2) :
    eval y (ptLift j q) = ptVec j q := by
  unfold ptLift ptVec
  split_ifs <;> simp
theorem ptVec_mem (j : Fin 2) : ptVec j ∈ ReciprocityTheory.AnForm.R.conePts (ptI (R := ℂ) j) := by
  refine ⟨fun k => ⟨j + 1, ?_⟩, fun f hf => ?_⟩
  · simp [ptVec]
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    simp [ptVec]
theorem not_mem_conePts_top (z : MCone ι1) :
    z ∉ ReciprocityTheory.AnForm.R.conePts (⊤ : Ideal (MRing ι1 ℂ)) := by
  rintro ⟨-, h⟩
  simpa using h 1 Submodule.mem_top
def ptSnc (p : Fin 0 → ℂ) :
    ReciprocityTheory.AnForm.R.SncData (⊥ : Ideal (MvPolynomial (Fin 0) ℂ)) ⊤ p 0 0 where
  r l := l.elim0
  J := ∅
  h := 1
  σ l := l.elim0
  σ_injOn := by simp
  σ_eq_none l := l.elim0
  span_eq := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    conv_rhs => arg 2; rw [ReciprocityTheory.AnForm.R.ptIdeal_fin_zero]
    exact Ideal.map_bot.symm
  eval_h := by simp
  mem_bd := Submodule.mem_top
  le_span g _ := by simp
theorem bind₁_ptLift_isUnit (j : Fin 2) (f : MvPolynomial (Σ _ : Unit, Fin 2) ℂ)
    (hf : eval (ptVec j) f ≠ 0) : IsUnit (bind₁ (ptLift j) f) := by
  have key2 : eval (0 : Fin 0 → ℂ) (bind₁ (ptLift j) f) = eval (ptVec j) f := by
    have h := hom_bind₁ (eval (0 : Fin 0 → ℂ)) (ptLift j) f
    have hc : (eval (0 : Fin 0 → ℂ)).comp C = RingHom.id ℂ := RingHom.ext fun c => by simp
    have hv : (fun i => eval (0 : Fin 0 → ℂ) (ptLift j i)) = ptVec j := funext (eval_ptLift j 0)
    rw [hc, hv, coe_eval₂Hom, eval₂_id] at h
    exact h
  have hC := eq_C_of_isEmpty (bind₁ (ptLift j) f)
  have hc : coeff 0 (bind₁ (ptLift j) f) ≠ 0 := by
    intro h0
    apply hf
    rw [← key2, hC, h0]
    simp
  rw [hC]
  exact (isUnit_iff_ne_zero.mpr hc).map C
def ptAlgRes (j : Fin 2) : ReciprocityTheory.AnForm.R.AlgRes ι1 (ptI j) ⊤ 0 where
  M := Unit
  n := 1
  amb _ := 0
  ideal _ := ⊥
  src _ := Set.univ
  isOpen_alt_bis _ := isOpen_univ
  cover _ := ⟨0, Set.mem_univ _⟩
  coord _ _ := 0
  isEmbedding _ := Topology.IsEmbedding.of_subsingleton _
  image _ := by
    ext y
    constructor
    · rintro - h hh
      rw [Ideal.mem_bot] at hh
      simp [hh]
    · intro _
      exact ⟨(), Set.mem_univ _, Subsingleton.elim _ _⟩
  trans _ _ _ _ := ⟨1, fun l => l.elim0, by simp, fun _ _ _ l => l.elim0⟩
  regular _ _ _ := ReciprocityTheory.AnForm.R.locRing_bot_regular _
  dim _ _ _ := by
    rw [ReciprocityTheory.AnForm.R.locRing_bot_dim]
    rfl
  lift _ := ptLift j
  lift_one _ := ⟨fun _ => j + 1, fun _ => by simp [ptLift]⟩
  lift_mem _ _ _ := by
    convert ptVec_mem j using 1
    funext q
    exact eval_ptLift j _ q
  compat _ _ _ _ := ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩
  surj z hz _ := by
    have hzj : z ⟨(), j⟩ = 0 := by simpa using hz.2 _ (Ideal.subset_span rfl)
    have hz1 : z ⟨(), j + 1⟩ ≠ 0 := by
      obtain ⟨i, hi⟩ := hz.1 ()
      rcases fin_two_eq_or_eq_add_one j i with rfl | rfl
      · exact absurd hzj hi
      · exact hi
    refine ⟨0, (), Set.mem_univ _, fun _ => (z ⟨(), j + 1⟩)⁻¹, fun _ => inv_ne_zero hz1, ?_⟩
    funext q
    rcases q with ⟨⟨⟩, i⟩
    rw [eval_ptLift]
    rcases fin_two_eq_or_eq_add_one j i with rfl | rfl
    · simp [ptVec, hzj]
    · simp [ptVec, hz1]
  inj _ _ x _ x' _ _ _ := Subsingleton.elim x x'
  inv _ _ _ _ _ hp := ⟨Set.univ, isOpen_univ, Set.mem_univ _, subset_rfl, 1, fun l => l.elim0,
    fun _ _ => ⟨hp, by simp, fun l => l.elim0⟩⟩
  bd _ := ⊤
  le_bd _ := le_top
  zero_bd _ _ _ := ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp),
    fun h => absurd h (not_mem_conePts_top _)⟩
  rc := 0
  comp k := k.elim0
  sncAt _ _ _ := ptSnc _
  comp_eq _ _ _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, subset_rfl, fun k => k.elim0⟩
  mult f _ _ _ hz := by
    have hf : eval (ptVec j) f ≠ 0 := fun h0 => not_mem_conePts_top _ (hz _ (ptVec_mem j) h0)
    refine ⟨fun k => k.elim0, fun i x hx => ?_⟩
    refine ⟨algebraMap _ _ (bind₁ (ptLift j) f), (bind₁_ptLift_isUnit j f hf).map _, ?_⟩
    simp only [ptSnc, Finset.prod_empty, mul_one]
def ptRes (j : Fin 2) : Res ι1 (ptI (R := ℂ) j) 0 where
  D := ⊤
  homog _ _ _ := Submodule.mem_top
  not_le h := (isPrime_span_X (R := ℂ) (⟨(), j⟩ : Σ _ : Unit, Fin 2)).ne_top (top_le_iff.mp h)
  R := ptAlgRes j
def qn (z : MCone ι1) : ℝ := ‖z ⟨(), 0⟩‖ ^ 2 + ‖z ⟨(), 1⟩‖ ^ 2
theorem qn_tsmul (c : Unit → ℂ) (z : MCone ι1) : qn (tsmul c z) = ‖c ()‖ ^ 2 * qn z := by
  simp only [qn, tsmul, norm_mul, mul_pow]
  ring
def fubiniStudyLine : HLine ι1 := ReciprocityTheory.ChartRestriction.G.Geo.fsLine 2
def projectiveLineCoordinates (j : Fin 2) (z : MCone ι1) : ℝ := ‖z ⟨(), j⟩‖ ^ 2 / qn z
theorem projLineRatio_torus_smul (j : Fin 2) (c : Unit → ℂ) (hc : ∀ k, c k ≠ 0) (z : MCone ι1) :
    projectiveLineCoordinates j (tsmul c z) = projectiveLineCoordinates j z := by
  rw [projectiveLineCoordinates, projectiveLineCoordinates, qn_tsmul]
  simp only [tsmul, norm_mul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hc ())))
def fsTw : HLine ι1 :=
  ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor fubiniStudyLine
    (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (projectiveLineCoordinates 0) fun c z hc => projLineRatio_torus_smul 0 c hc z)
def projLineFubiniStudyMass : ℝ := zInt (⊥ : Ideal (MRing ι1 ℂ)) 1 ![logH fubiniStudyLine] (fun _ => 1)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


