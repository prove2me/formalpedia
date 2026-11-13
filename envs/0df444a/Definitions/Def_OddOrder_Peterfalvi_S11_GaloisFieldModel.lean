-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_GaloisFieldModel
-- name    : OddOrder_Peterfalvi_S11_GaloisFieldModel
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:18:14.06886+00:00
-- url     : https://prove2.me/theorems/685dc622-0699-4250-b4fe-18baf6f5ce71
-- title:
--   Peterfalvi (9.7.b): the chief-factor Galois-field model
-- statement:
--   Formalizes Peterfalvi (9.7.b): in Clifford case (b), the faithful image of the $U$-action on the chief factor acts irreducibly, and the Singer construction identifies the factor with a Galois field model with the $W_1$-action.
--
--   Main declarations: `w1ActionHom` (The `W₁`-action on the chief factor `H̄`); `caseB_etaHom` (The map `η` of Peterfalvi (9.7.b)).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_GaloisFieldModel.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_GaloisFieldModel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerLineBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearImprimitiveBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LineScalarCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AInvariantSubrep
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldAut
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory OddOrder.RepresentationTheory OddOrder.Isaacs.Ch03

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- **The `W₁`-action on the chief factor `H̄`** — the `W₁` analogue of `uActionHom`
(`ChiefFactorCore.lean`), both being restrictions of the full `UW₁`-action
`quotientMulAutHom chief.N_aInvariant` to a factor of `U ⊔ W₁`. -/
noncomputable def w1ActionHom {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) →*
      MulAut (↥data.H ⧸ chief.N) :=
  (quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
    (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype

/-- **The map `η` of Peterfalvi (9.7.b)**: the `W₁`-action on `H̄` transported to the field model
by `e`, i.e. `η(w)` is the `e`-conjugate of `w`'s action — the book's defining property
`φ(h)η(w) = φ(h^w)`.

A priori `η(w)` is only an *additive* automorphism of `F`; the upgrade to a field automorphism is
the content of (9.7.b) and goes through `ringAutHomOfAddAutHom`.  `AddAut F` is an additive group
in mathlib, so the codomain is its multiplicative incarnation `Multiplicative (AddAut F)`. -/
noncomputable def caseB_etaHom {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} [Fact chief.p.Prime]
    (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q) :
    ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) →*
      Multiplicative (AddAut (GaloisField chief.p data.q)) :=
  (((MulAutMultiplicative (GaloisField chief.p data.q)).toMonoidHom).comp
      (MulAut.congr (AddEquiv.toMultiplicativeRight e)).toMonoidHom).comp
    (w1ActionHom data chief)

/-- `η(w)` is literally `e`-conjugation of `w`'s action (definitional form). -/
theorem caseB_etaHom_apply' {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} [Fact chief.p.Prime]
    (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
    (w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
    (y : GaloisField chief.p data.q) :
    Multiplicative.toAdd (caseB_etaHom (chief := chief) e w) y
      = e (Additive.ofMul (w1ActionHom data chief w (Additive.toMul (e.symm y)))) := rfl

/-- **The defining property of `η`** (Peterfalvi (9.7.b): `φ(h)η(w) = φ(h^w)`). -/
@[simp] theorem caseB_etaHom_apply {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} [Fact chief.p.Prime]
    (e : Additive (↥data.H ⧸ chief.N) ≃+ GaloisField chief.p data.q)
    (w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
    (h : ↥data.H ⧸ chief.N) :
    Multiplicative.toAdd (caseB_etaHom (chief := chief) e w) (e (Additive.ofMul h))
      = e (Additive.ofMul (w1ActionHom data chief w h)) := by
  rw [caseB_etaHom_apply', e.symm_apply_apply]
  rfl

end OddOrder.Peterfalvi.S11


