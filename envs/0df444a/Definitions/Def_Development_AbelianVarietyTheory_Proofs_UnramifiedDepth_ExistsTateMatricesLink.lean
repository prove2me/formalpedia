-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:36:54.552853+00:00
-- url     : https://prove2.me/theorems/db3970d8-c7ee-4747-a2ca-8d773c777642
-- title:
--   Exists Tate Matrices Link
-- statement:
--   Definitions and structural lemmas for Exists Tate Matrices Link, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsTateMatricesLink.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Theorems.Thm_ReciprocityTheory_PGsh_FP_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
namespace GlobalTheory
namespace TateMatrices
section Pairing
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}
end Pairing
section Padic
variable {p : ℕ} [Fact p.Prime]
end Padic
section Heights
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀)
end Heights
section Action
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {B : BX R₀} {O : LAlg R₀}
  {O₀ : Type} [CommRing O₀]
def pointAction (f : O₀ → OEnd B O)
    (hf : ∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b,
      (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧ (f (a * b)).f s x = (f a).f s ((f b).f s x)) :
    O₀ →+* AddMonoid.End (B.G O) :=
  RingHom.mk'
    { toFun := fun a => (f a).f (LHom.id O)
      map_one' := AddMonoidHom.ext fun x => (hf _ x).1
      map_mul' := fun a b => AddMonoidHom.ext fun x => ((hf _ x).2 a b).2 }
    fun a b => AddMonoidHom.ext fun x => ((hf _ x).2 a b).1
def padicExtension {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : O₀ →+* Matrix κ κ ℤ_[p]) :
    ℤ_[p] ⊗[ℤ] O₀ →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p] :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] _) ρ.toIntAlgHom
    fun x y => Algebra.commutes x (ρ y)
end Action
end TateMatrices
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory


