-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_MajorantInvolutionDiagonalForm
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_MajorantInvolutionDiagonalForm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:18:50.589908+00:00
-- url     : https://prove2.me/theorems/e59739fe-b092-4732-9280-8b902b5e72ea
-- title:
--   Majorant Involution Diagonal Form
-- statement:
--   Definitions and structural lemmas for Majorant Involution Diagonal Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/MajorantInvolutionDiagonalForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Statements
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
section MatrixLevel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def IsMajorantOf (H P : Matrix ι ι ℂ) : Prop :=
  P.PosDef ∧ H.IsHermitian ∧ IsUnit H.det ∧ P * H⁻¹ * P = H
def majInvolution (H P : Matrix ι ι ℂ) : Matrix ι ι ℂ := H⁻¹ * P
def plusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z + majInvolution H P *ᵥ z)
def minusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z - majInvolution H P *ᵥ z)
def pReflection (P : Matrix ι ι ℂ) (v : ι → ℂ) : Matrix ι ι ℂ :=
  1 - (2 / (star v ⬝ᵥ (P *ᵥ v))) • (vecMulVec v (star v) * P)
def phaseOnMinus (H P : Matrix ι ι ℂ) (c : ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (1 + majInvolution H P) + (c / 2) • (1 - majInvolution H P)
variable (ι)
def MajorantBound.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ,
    ‖star z ⬝ᵥ (H *ᵥ z)‖ ≤ (star z ⬝ᵥ (P *ᵥ z)).re
def EigenspacesOrthogonal.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ a b : ι → ℂ,
    majInvolution H P *ᵥ a = a → majInvolution H P *ᵥ b = -b → star a ⬝ᵥ (P *ᵥ b) = 0
def IsotropicSplit.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ, star z ⬝ᵥ (H *ᵥ z) = 0 →
    majInvolution H P *ᵥ plusPart H P z = plusPart H P z ∧
    majInvolution H P *ᵥ minusPart H P z = -minusPart H P z ∧
    star (plusPart H P z) ⬝ᵥ (P *ᵥ plusPart H P z) =
      star (minusPart H P z) ⬝ᵥ (P *ᵥ minusPart H P z)
def EigenReflection.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ v : ι → ℂ, v ≠ 0 →
    majInvolution H P *ᵥ v = ε • v →
    (pReflection P v)ᴴ * P * pReflection P v = P ∧ (pReflection P v)ᴴ * H * pReflection P v = H ∧
      pReflection P v *ᵥ v = -v ∧ ∀ u : ι → ℂ, star v ⬝ᵥ (P *ᵥ u) = 0 → pReflection P v *ᵥ u = u
def EigenReflectionMaps.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ a a' : ι → ℂ,
    majInvolution H P *ᵥ a = ε • a → majInvolution H P *ᵥ a' = ε • a' →
    star a ⬝ᵥ (P *ᵥ a) = star a' ⬝ᵥ (P *ᵥ a') →
    ∃ α : ℂ, ‖α‖ = 1 ∧ ∃ R : Matrix ι ι ℂ, Rᴴ * P * R = P ∧ Rᴴ * H * R = H ∧ R *ᵥ a' = α • a ∧
      ∀ u : ι → ℂ, majInvolution H P *ᵥ u = (-ε) • u → R *ᵥ u = u
def PhaseOnMinus.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ c : ℂ, ‖c‖ = 1 →
    (phaseOnMinus H P c)ᴴ * P * phaseOnMinus H P c = P ∧
      (phaseOnMinus H P c)ᴴ * H * phaseOnMinus H P c = H ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = u → phaseOnMinus H P c *ᵥ u = u) ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = -u → phaseOnMinus H P c *ᵥ u = c • u)
def KTransitive.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z z' : ι → ℂ, z ≠ 0 → z' ≠ 0 →
    star z ⬝ᵥ (H *ᵥ z) = 0 → star z' ⬝ᵥ (H *ᵥ z') = 0 →
    ∃ k : GL ι ℂ, k ∈ unitaryGroupMatrix (starRingEnd ℂ) H ∧
      k ∈ unitaryGroupMatrix (starRingEnd ℂ) P ∧ ∃ c : ℂ, (k : Matrix ι ι ℂ) *ᵥ z' = c • z
end MatrixLevel
section Places
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def HermAtPlace.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (w : InfinitePlace E) (x y : W),
    w.embedding (h.toSesq x y) = star (vecAt v x w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v y w)
def GramAtData.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ w : InfinitePlace E, (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det
def ArchInvariant.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (g : archUnitary h v) (y z : InfinitePlace E → ι → ℂ) (w : InfinitePlace E),
    star (invApply g y w) ⬝ᵥ (gramAt h v w *ᵥ invApply g z w) =
      star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)
def LenSq.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (y : InfinitePlace E → ι → ℂ),
    (∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re) ∧
      M.len y ^ 2 = ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re
def VecAtNeZero.Statement (v : Basis ι E W) : Prop :=
  ∀ x : W, x ≠ 0 → ∀ w : InfinitePlace E, vecAt v x w ≠ 0
variable (E) in

def IntegerSmallAtPlaces.Statement : Prop :=
  ∀ a ∈ integralClosure ℤ E, (∀ w : InfinitePlace E, w a < 1) → a = 0
end Places
section Line
variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable (E) in

def intSubgroup : AddSubgroup E := (algebraMap (𝓞 E) E).toAddMonoidHom.range
def lineCoeffs (La : AddSubgroup W) (x : W) : AddSubgroup E :=
  La.comap ((smulAddHom E W).flip x)
def weightedEmbed (c : InfinitePlace E → ℝ) : E →+ EuclideanSpace ℝ (InfinitePlace E × Fin 2) where
  toFun a := WithLp.toLp 2 fun p =>
    Real.sqrt (c p.1) * (if p.2 = 0 then (p.1.embedding a).re else (p.1.embedding a).im)
  map_zero' := by
    ext p
    simp
  map_add' a b := by
    ext p
    simp only [map_add, Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> ring
variable (W) in

def LineIndexCoeffs.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), x ≠ 0 →
    lineIndex E La x = (intSubgroup E).relIndex (lineCoeffs La x)
variable (W) in

def LineCoeffsFG.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), La.FG → x ≠ 0 → (lineCoeffs (E := E) La x).FG
variable (E)
def CoeffLatticeBasis.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG → Nonempty (Basis (Fin (finrank ℚ E)) ℤ A)
def IndexLeDet.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → ∀ (e : Basis (Fin (finrank ℚ E)) ℤ A)
    (a : Fin (finrank ℚ E) → 𝓞 E) (T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ),
    LinearIndependent ℚ (fun i => (a i : E)) → (∀ i, (a i : E) = ∑ j, T i j • (e j : E)) →
    ((intSubgroup E).relIndex A : ℝ) ≤ |(T.det : ℝ)|
def WeightedNormSq.Statement : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 ≤ c w) → ∀ a : E,
    ‖weightedEmbed c a‖ ^ 2 = ∑ w, c w * ‖w.embedding a‖ ^ 2
def WeightedSpaceDim.Statement [IsTotallyComplex E] : Prop :=
  finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E
def WeightedIndexBound.Statement [IsTotallyComplex E] : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 < c w) → ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG →
    (∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) →
    ∀ r : ℝ, (∃ a : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r) →
    ((intSubgroup E).relIndex A : ℝ) ≤ (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E
end Line
section Minkowski
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]
def MinkowskiVolumeForm.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (lam : ℝ), 0 < lam →
    (∀ z : Fin d → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) →
    (lam / Real.sqrt d) ^ d ≤ |o.volumeForm b|
def VolumeFormIntComb.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (T : Matrix (Fin d) (Fin d) ℤ),
    o.volumeForm (fun i => ∑ j, (T i j : ℝ) • b j) = (T.det : ℝ) * o.volumeForm b
end Minkowski
section Steps
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def WeightedLenSmul.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W) (a : E),
    M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, ‖w.embedding a‖ ^ 2 *
        (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re
def WeightPos.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W), x ≠ 0 → ∀ w : InfinitePlace E,
    0 < (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re
end Steps
section Inhabitants
open GaussianPlane
def H0 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]
def z0 : Fin 2 → ℂ := fun _ => 1
def e1 : Fin 2 → ℂ := Pi.single 0 1
def e2 : Fin 2 → ℂ := Pi.single 1 1
theorem card_chooseBasisIndex_Eg :
    Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 Eg)) = finrank ℚ Eg := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
def intBasisG : Basis (Fin (finrank ℚ Eg)) ℤ (𝓞 Eg) :=
  (RingOfIntegers.basis Eg).reindex (Fintype.equivFinOfCardEq card_chooseBasisIndex_Eg)
def intSubgroupEquiv (K : Type*) [Field K] [NumberField K] : 𝓞 K ≃ₗ[ℤ] intSubgroup K :=
  (AddMonoidHom.ofInjective (f := (algebraMap (𝓞 K) K).toAddMonoidHom)
    (FaithfulSMul.algebraMap_injective (𝓞 K) K)).toIntLinearEquiv
def intSubgroupBasisG : Basis (Fin (finrank ℚ Eg)) ℤ (intSubgroup Eg) :=
  intBasisG.map (intSubgroupEquiv Eg)
instance fact_finrank_euclidean_fin_one : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1) :=
  ⟨finrank_euclideanSpace_fin⟩
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


