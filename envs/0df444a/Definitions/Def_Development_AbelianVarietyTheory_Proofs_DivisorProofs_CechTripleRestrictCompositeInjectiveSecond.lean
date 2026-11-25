-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:16:14.083329+00:00
-- url     : https://prove2.me/theorems/1fd645e0-1d03-4e83-a622-73d54c7d12d7
-- title:
--   Cech Triple Restrict Composite Injective Second
-- statement:
--   Definitions and structural lemmas for Cech Triple Restrict Composite Injective Second, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
section Triple
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
abbrev Triple (ψ : X'' ⟶ X') (φ : X' ⟶ X) : Type :=
  {q : X''.affineOpens × X'.affineOpens × X.affineOpens //
    q.1.1 ≤ ψ ⁻¹ᵁ q.2.1.1 ∧ q.2.1.1 ≤ φ ⁻¹ᵁ q.2.2.1}
variable {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
theorem Triple.le_one {p q : Triple ψ φ} (h : p ≤ q) : p.1.1 ≤ q.1.1 :=
  (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1
theorem Triple.le_two {p q : Triple ψ φ} (h : p ≤ q) : p.1.2.1 ≤ q.1.2.1 :=
  (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).1
theorem Triple.le_three {p q : Triple ψ φ} (h : p ≤ q) : p.1.2.2 ≤ q.1.2.2 :=
  (Prod.le_def.1 (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2).2
def Triple.p12 (q : Triple ψ φ) : Pair ψ := ⟨(q.1.1, q.1.2.1), q.2.1⟩
def Triple.p23 (q : Triple ψ φ) : Pair φ := ⟨(q.1.2.1, q.1.2.2), q.2.2⟩
def Triple.p13 (q : Triple ψ φ) : Pair (ψ ≫ φ) :=
  ⟨(q.1.1, q.1.2.2), fun _ hx ↦ q.2.2 (q.2.1 hx)⟩
theorem Triple.pairFirstThirdComp_monotone : Monotone (Triple.p13 (ψ := ψ) (φ := φ)) := fun _ _ h ↦
  Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨Triple.le_one h, Triple.le_three h⟩)
variable (ψ φ)
def cechTripleProjFirstSecond : (Triple ψ φ)ᵒᵖ ⥤ (Pair ψ)ᵒᵖ :=
  (Monotone.functor (f := Triple.p12) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨Triple.le_one h, Triple.le_two h⟩)).op
def cechTripleProjSecondThird : (Triple ψ φ)ᵒᵖ ⥤ (Pair φ)ᵒᵖ :=
  (Monotone.functor (f := Triple.p23) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨Triple.le_two h, Triple.le_three h⟩)).op
def cechTripleProjFirstThird : (Triple ψ φ)ᵒᵖ ⥤ (Pair (ψ ≫ φ))ᵒᵖ :=
  (Monotone.functor (Triple.pairFirstThirdComp_monotone (ψ := ψ) (φ := φ))).op
abbrev OTriple (s'' : X'' ⟶ Sp R'') : (Triple ψ φ)ᵒᵖ ⥤ CommAlgCat.{0} R'' :=
  cechTripleProjFirstThird ψ φ ⋙ OPair (ψ ≫ φ) s''
def cechTripleRestrictComposite (s'' : X'' ⟶ Sp R'') : CoefMap (RingHom.id R'') (OPair (ψ ≫ φ) s'') (OTriple ψ φ s'') :=
  CoefMap.restrict _ _
def cechTripleRestrictFirst (s'' : X'' ⟶ Sp R'') : CoefMap (RingHom.id R'') (OPair ψ s'') (OTriple ψ φ s'') where
  G := cechTripleProjFirstSecond ψ φ
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl
variable {ψ φ}
def cechTriplePullbackSecond {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {τ : R' →+* R''}
    (h' : ψ ≫ s' = s'' ≫ spMap τ) : CoefMap τ (OPair φ s') (OTriple ψ φ s'') where
  G := cechTripleProjSecondThird ψ φ
  α t := (pairPull h').α ((cechTripleProjFirstSecond ψ φ).obj t)
  naturality a b := (pairPull h').naturality ((cechTripleProjFirstSecond ψ φ).map a) b
  smul t := (pairPull h').smul ((cechTripleProjFirstSecond ψ φ).obj t)
variable (ψ φ)
end Triple
section Comp
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}
end Comp
end GlobalTheory.CechDR


