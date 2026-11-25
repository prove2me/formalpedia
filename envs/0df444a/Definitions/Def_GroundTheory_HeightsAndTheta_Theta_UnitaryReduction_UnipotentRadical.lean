-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadical
-- name    : GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadical
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:45:41.613293+00:00
-- url     : https://prove2.me/theorems/48a57106-087d-5cf4-be5e-0de672a38b6f
-- title:
--   Unipotent Radical
-- statement:
--   Definitions and structural lemmas for Unipotent Radical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/UnitaryReduction/UnipotentRadical.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_CMDatum
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_MemRangeIffIsIntegral
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
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Theta
namespace UnitaryReduction
open NumberField GroundTheory.Automorphic Module TensorProduct Matrix FunctionalEquationAlt
variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
section Rational
variable (B : HermitianForm F E V)
def perp (W : Submodule E V) : Submodule E V := W.orthogonalBilin B.toSesq
def nn (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | (∀ u v, B.toSesq (X u) v + B.toSesq u (X v) = 0) ∧ (∀ y, X y ∈ perp B W) ∧
    (∀ y ∈ perp B W, X y ∈ W) ∧ ∀ y ∈ W, X y = 0}
def zz (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | X ∈ nn B W ∧ ∀ y ∈ perp B W, X y = 0}
def NR (W : Submodule E V) : Set (V ≃ₗ[E] V) :=
  {g | g ∈ B.unitaryGroup ∧ (∀ y, g y - y ∈ perp B W) ∧ (∀ y ∈ perp B W, g y - y ∈ W) ∧
    ∀ y ∈ W, g y = y}
def nexp (X : V →ₗ[E] V) : V →ₗ[E] V := 1 + X + (2⁻¹ : E) • (X * X)
def IsIntegralMul (L : Submodule (𝓞 E) V) (c : E) (X : V →ₗ[E] V) : Prop :=
  ∀ y ∈ L, ∃ l ∈ L, X y = c • l
def Gam (L : Submodule (𝓞 E) V) (W : Submodule E V) (g : ℕ) : Set (V ≃ₗ[E] V) :=
  {γ | γ ∈ NR B W ∧ (∀ y, γ y ∈ L ↔ y ∈ L) ∧
    IsIntegralMul L (g : E) ((γ : V →ₗ[E] V) - 1)}
def nnImage (W : Submodule E V) (X : V →ₗ[E] V) : perp B W →ₗ[E] V :=
  X.domRestrict (perp B W)
def hhR (W : Submodule E V) : Set (perp B W →ₗ[E] V) :=
  {T | (∀ y, T y ∈ W) ∧ ∀ y : perp B W, (y : V) ∈ W → T y = 0}
def Lam1 (L : Submodule (𝓞 E) V) (W : Submodule E V) : Set (perp B W →ₗ[E] V) :=
  {T | T ∈ hhR B W ∧ ∀ y : perp B W, (y : V) ∈ L → T y ∈ L}
def Sig (L : Submodule (𝓞 E) V) (W : Submodule E V) : Set (V →ₗ[E] V) :=
  {X | X ∈ zz B W ∧ IsIntegralMul L 1 X}
end Rational
section Algebras
variable (B : HermitianForm F E V) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
variable (k : Type) [CommRing k] [Algebra F k]
def coordK (y : V) : ι → k ⊗[F] E :=
  fun i => (Algebra.TensorProduct.includeRight : E →ₐ[F] k ⊗[F] E) (b.repr y i)
def subK (W : Submodule E V) : Submodule (k ⊗[F] E) (ι → k ⊗[F] E) :=
  Submodule.span (k ⊗[F] E) (coordK b k '' (W : Set V))
def gramK : Matrix ι ι (k ⊗[F] E) :=
  (gram B.toSesq b).map (Algebra.TensorProduct.includeRight : E →ₐ[F] k ⊗[F] E)
def nnK (W : Submodule E V) : Set (Matrix ι ι (k ⊗[F] E)) :=
  {X | (X.map (conjBase F E k))ᵀ * gramK B b k + gramK B b k * X = 0 ∧
    (∀ y, X *ᵥ y ∈ subK b k (perp B W)) ∧ (∀ y ∈ subK b k (perp B W), X *ᵥ y ∈ subK b k W) ∧
    ∀ y ∈ subK b k W, X *ᵥ y = 0}
def zzK (W : Submodule E V) : Set (Matrix ι ι (k ⊗[F] E)) :=
  {X | X ∈ nnK B b k W ∧ ∀ y ∈ subK b k (perp B W), X *ᵥ y = 0}
def NRK (W : Submodule E V) : Set (GL ι (k ⊗[F] E)) :=
  {g | g ∈ unitaryPoints F E (gram B.toSesq b) k ∧
    (∀ y, ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y ∈ subK b k (perp B W)) ∧
    (∀ y ∈ subK b k (perp B W), ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y ∈ subK b k W) ∧
    ∀ y ∈ subK b k W, ((g : Matrix ι ι (k ⊗[F] E)) - 1) *ᵥ y = 0}
def nexpK (X : Matrix ι ι (k ⊗[F] E)) : Matrix ι ι (k ⊗[F] E) :=
  1 + X + (algebraMap F (k ⊗[F] E) 2⁻¹) • (X * X)
end Algebras
def UnipotentAlgebra.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (R : Submodule (𝓞 E) V), IsIsotropic B R →
  let W := espan R
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι E V)
    (k : Type) [CommRing k] [Algebra F k],
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W, ∀ X'' ∈ nnK B b k W, X * X' * X'' = 0) ∧
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W,
      (∀ y ∈ subK b k (perp B W), (X * X') *ᵥ y = 0) ∧ ∀ y, (X * X') *ᵥ y ∈ subK b k W) ∧
    (∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W, X * X' - X' * X ∈ zzK B b k W) ∧
    (∀ Z ∈ zzK B b k W, ∀ X ∈ nnK B b k W, Z * X = X * Z) ∧
    Set.BijOn (nexpK k) (nnK B b k W)
      ((fun g : GL ι (k ⊗[F] E) => (g : Matrix ι ι (k ⊗[F] E))) '' NRK B b k W) ∧
    ∀ X ∈ nnK B b k W, ∀ X' ∈ nnK B b k W,
      nexpK k X * nexpK k X' =
        nexpK k (X + X' + (algebraMap F (k ⊗[F] E) 2⁻¹) • (X * X' - X' * X))
def ExpIntegral.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V), L.FG → IsSelfDual B L →
  ∀ R : Submodule (𝓞 E) V, IsIsotropic B R → ∀ g : ℕ, 1 ≤ g →
  ∀ X ∈ nn B (espan R), IsIntegralMul L (2 * g : E) X →
    ∃ γ ∈ Gam B L (espan R) g, (γ : V →ₗ[E] V) = nexp X
def Lifting.Statement
    (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (B : HermitianForm F E V) (L : Submodule (𝓞 E) V), L.FG → IsSelfDual B L →
  ∀ R : Submodule (𝓞 E) V, SatIn R L → IsIsotropic B R →
    (∀ T ∈ Lam1 B L (espan R), ∃ X ∈ nn B (espan R),
      IsIntegralMul L 1 X ∧ nnImage B (espan R) X = (2 : E) • T) ∧
    ∀ g : ℕ, 1 ≤ g → ∀ T ∈ Lam1 B L (espan R), ∃ X ∈ nn B (espan R),
      IsIntegralMul L (2 * g : E) X ∧ nnImage B (espan R) X = (4 * g : E) • T
section Example
variable (F E)
def hypPlaneSesq : (Fin 2 → E) →ₛₗ[conjHom F E] (Fin 2 → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => conj F E (x 0) * y 1 + conj F E (x 1) * y 0)
    (by intros; simp only [Pi.add_apply, map_add]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [show ∀ c, conjHom F E c = conj F E c from fun _ => rfl]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)
theorem hypPlaneSesq_apply (x y : Fin 2 → E) :
    hypPlaneSesq F E x y = conj F E (x 0) * y 1 + conj F E (x 1) * y 0 := rfl
def hypPlane : HermitianForm F E (Fin 2 → E) where
  toSesq := hypPlaneSesq F E
  isSymm := ⟨fun x y => by
    change conj F E (hypPlaneSesq F E x y) = hypPlaneSesq F E y x
    simp only [hypPlaneSesq_apply, map_add, map_mul, conj_conj]
    ring⟩
  nonsingular := by
    refine ⟨fun x x' h => ?_, fun φ => ?_⟩
    · have h0 := LinearMap.congr_fun h (Pi.single 1 1)
      have h1 := LinearMap.congr_fun h (Pi.single 0 1)
      simp only [hypPlaneSesq_apply, Pi.single_apply] at h0 h1
      norm_num at h0 h1
      have e0 : x 0 = x' 0 := by simpa using congrArg (conj F E) h0
      have e1 : x 1 = x' 1 := by simpa using congrArg (conj F E) h1
      funext i
      fin_cases i
      · exact e0
      · exact e1
    · refine ⟨![conj F E (φ (Pi.single 1 1)), conj F E (φ (Pi.single 0 1))], ?_⟩
      refine LinearMap.ext fun y => ?_
      have hy : y = y 0 • Pi.single 0 1 + y 1 • Pi.single 1 1 := by
        funext i; fin_cases i <;> simp
      conv_rhs => rw [hy]
      simp only [hypPlaneSesq_apply, map_add, map_smul, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, conj_conj]
      ring
def hypLine : Submodule E (Fin 2 → E) := Submodule.span E {Pi.single 0 1}
def hypZ (δ : E) : (Fin 2 → E) →ₗ[E] (Fin 2 → E) :=
  δ • (LinearMap.single E (fun _ : Fin 2 => E) 0 ∘ₗ LinearMap.proj 1)
end Example
end UnitaryReduction
end GroundTheory.Heights₂.Theta


