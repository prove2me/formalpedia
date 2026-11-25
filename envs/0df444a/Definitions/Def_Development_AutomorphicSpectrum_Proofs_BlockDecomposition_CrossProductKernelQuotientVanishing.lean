-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:07:51.072321+00:00
-- url     : https://prove2.me/theorems/bd3cc44b-3c56-57cb-8930-4617e3ecfdbf
-- title:
--   Cross Product Kernel Quotient Vanishing
-- statement:
--   Definitions and structural lemmas for Cross Product Kernel Quotient Vanishing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
abbrev Ar (C : Type) [Category.{0} C] : Type := Σ T : C, Σ T' : C, (T ⟶ T')
def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ x : Ar C, F.obj x.2.1 where
  toFun f x := f x.1 x.2.1 x.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
abbrev E : Type := ∀ x : Ar C × Ar C, F.obj x.1.2.1 ⊗[R] F.obj x.2.2.1
def shuffle : C2 (box F) →ₗ[R] E F where
  toFun z x := z (x.1.1, x.2.1) (x.1.2.1, x.2.1) (x.1.2.1, x.2.2.1) (x.1.2.2, 𝟙 _) (𝟙 _, x.2.2.2)
    - z (x.1.1, x.2.1) (x.1.1, x.2.2.1) (x.1.2.1, x.2.2.1) (𝟙 _, x.2.2.2) (x.1.2.2, 𝟙 _)
  map_add' z z' := by
    funext x
    simp only [Pi.add_apply]
    abel
  map_smul' r z := by
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]
variable {F}
variable (F)
def crossZ : Z1 F ⊗[R] Z1 F →ₗ[R] Z2 (box F) :=
  TensorProduct.lift ((cupZ (box F)).compl₁₂ (boxL F).pullbackOneCocycle (boxR F).pullbackOneCocycle)
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle


