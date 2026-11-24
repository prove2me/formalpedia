-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartModel
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_ResidueChartModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:52.370564+00:00
-- url     : https://prove2.me/theorems/cab195cb-be16-4b18-b4c5-a6872247f4a2
-- title:
--   Residue Chart Model
-- statement:
--   Definitions and structural lemmas for Residue Chart Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/ResidueChartModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix MvPolynomial
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman (Poly GradedMod Xprod polyPiece polyGraded)
noncomputable section
structure ResidueChartModel (P : RigSymForm ℂ) (a b : ℕ) {r : ℕ} (x : Fin (r + 1) → P.Fn) where

  M : Type
  [grp : AddCommGroup M]
  [modP : Module (Poly ℂ r) M]
  [modC : Module ℂ M]
  [tower : IsScalarTower ℂ (Poly ℂ r) M]

  G : GradedMod ℂ r M

  finite : Module.Finite (Poly ℂ r) M

  ι : M →ₗ[ℂ] P.Fn

  ι_smul : ∀ (p : Poly ℂ r) (m : M), ι (p • m) = P.formSec x p * ι m

  ι_piece : ∀ (c : ℕ) (m : M), m ∈ G.piece c → ι m ∈ P.S (b + a * c)

  ι_neg : ∀ c : ℤ, c < 0 → ∀ m ∈ G.piece c, ι m = 0

  chart_inj : ∀ J : Finset (Fin (r + 1)), J.Nonempty → ∀ (c : ℤ) (m : M), m ∈ G.piece c →
    (∀ z ∈ P.chartSet x J, ι m z = 0) → ∃ l : ℕ, Xprod ℂ r J ^ l • m = 0

  chart_surj : ∀ J : Finset (Fin (r + 1)), J.Nonempty → ∀ (c : ℕ), ∀ f ∈ P.S (b + a * c),
    ∃ (l : ℕ) (m : M), m ∈ G.piece ((c : ℤ) + l * J.card) ∧
      ∀ z ∈ P.chartSet x J, ι m z = (∏ i ∈ J, x i z) ^ l * f z
attribute [instance] ResidueChartModel.grp ResidueChartModel.modP ResidueChartModel.modC
  ResidueChartModel.tower
def siegelPtZero : SiegelPt 0 where
  τ := 0
  isSymm := Matrix.ext fun i _ => i.elim0
  im_posDef := ⟨Matrix.ext fun i _ => i.elim0, fun _v hv => (hv (Finsupp.ext fun i => i.elim0)).elim⟩
theorem mem_thetaSec_siegelPtZero (n : ℕ) (f : (Fin 0 → ℂ) → ℂ) :
    f ∈ thetaSec siegelPtZero (HalfChar.zero 0) n := by
  have hf : f = fun _ => f 0 := funext fun z => congrArg f (Subsingleton.elim z 0)
  refine ⟨?_, fun v z => ?_, fun u z => ?_⟩
  · rw [hf]; exact differentiable_const _
  · rw [Subsingleton.elim (z + intVec v) z]
    simp [perFactor, dotProduct]
  · rw [Subsingleton.elim (z + siegelPtZero.τ *ᵥ intVec u) z]
    simp [autFactor, dotProduct]
def pointForm : RigSymForm ℂ where
  g := 0
  pt := siegelPtZero
  ch := HalfChar.zero 0
  S := fun n => thetaSec siegelPtZero (HalfChar.zero 0) n
  S_le := fun _ _ hf => hf
  one_mem := const_mem_thetaSec_zero _ _ 1
  mul_mem := fun _ _ _ _ hf hh => thetaSec_mul _ _ hf hh
  span_eq := fun n => Submodule.span_eq _
  linIndep := fun _ _ _ h => h
  rig := 1
  rig_mem := fun n f _ => ⟨(1 : ℂ) ^ n * f 0, by simp⟩
theorem pointForm_fn_eq (z w : Fin pointForm.g → ℂ) : z = w :=
  funext fun i => (show Fin 0 from i).elim0
def pointX : Fin (0 + 1) → pointForm.Fn := fun _ _ => 1
theorem polyPiece_eq_zero_of_neg {N : ℕ} {c : ℤ} (hc : c < 0) {m : Poly ℂ N}
    (hm : m ∈ polyPiece ℂ N c) : m = 0 := by
  have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).1 hm
  ext d
  rw [coeff_zero]
  by_contra hd
  have e := hw hd
  have hnn : 0 ≤ Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun i _ => nsmul_nonneg zero_le_one _
  omega
theorem polyPiece_zero_eq_zero_of_eval {c : ℤ} {m : Poly ℂ 0} (hm : m ∈ polyPiece ℂ 0 c)
    (h0 : MvPolynomial.eval (fun _ => (1 : ℂ)) m = 0) : m = 0 := by
  have hw := (mem_weightedHomogeneousSubmodule _ _ _ _).1 hm
  have key : ∀ d d' : Fin (0 + 1) →₀ ℕ, coeff d m ≠ 0 → coeff d' m ≠ 0 → d = d' := by
    intro d d' hd hd'
    have e1 := hw hd
    have e2 := hw hd'
    rw [← e2] at e1
    ext i
    fin_cases i
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using e1
  ext d
  rw [coeff_zero]
  by_contra hd
  apply hd
  rw [MvPolynomial.eval_eq, Finset.sum_eq_single d
    (fun d' hd' hne => absurd (key d d' hd (mem_support_iff.1 hd')).symm hne)
    (fun h => absurd (mem_support_iff.2 hd) h)] at h0
  simpa using h0
def pointι : Poly ℂ 0 →ₗ[ℂ] pointForm.Fn :=
  LinearMap.pi fun z => (aeval fun j => pointX j z).toLinearMap
theorem pointι_apply (p : Poly ℂ 0) (z : Fin pointForm.g → ℂ) :
    pointι p z = MvPolynomial.eval (fun _ => (1 : ℂ)) p := by
  simp [pointι, pointX]
def pointChartModel : ResidueChartModel pointForm 3 0 pointX where
  M := Poly ℂ 0
  G := polyGraded ℂ 0
  finite := Module.Finite.self _
  ι := pointι
  ι_smul p m := by
    funext z
    simp only [smul_eq_mul, Pi.mul_apply, pointι, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      map_mul, RigSymForm.formSec, aeval_def]
  ι_piece c m _ := mem_thetaSec_siegelPtZero _ _
  ι_neg c hc m hm := by
    rw [polyPiece_eq_zero_of_neg hc hm, map_zero]
  chart_inj J _ c m hm h := by
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul]
    refine polyPiece_zero_eq_zero_of_eval hm ?_
    have h1 := h 0 (fun i _ => by simp [pointX])
    rwa [pointι_apply] at h1
  chart_surj J _ c f _ := by
    refine ⟨0, C (f 0) * X 0 ^ c, ?_, fun z _ => ?_⟩
    · have h := (isWeightedHomogeneous_C (fun _ : Fin (0 + 1) => (1 : ℤ)) (f 0)).mul
        ((isWeightedHomogeneous_X ℂ (fun _ : Fin (0 + 1) => (1 : ℤ)) 0).pow c)
      refine (mem_weightedHomogeneousSubmodule _ _ _ _).2 ?_
      convert h using 1 <;> first | rfl | simp
    · rw [pointι_apply, pointForm_fn_eq z 0]
      simp
end
end GroundTheory.Heights₂.Heights.KeyFormula


