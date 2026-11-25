-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformizationLinear
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_UniformizationLinear
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:30:09.346359+00:00
-- url     : https://prove2.me/theorems/2367d55c-6a80-59fc-b54a-1bbd4285b7aa
-- title:
--   Uniformization Linear
-- statement:
--   Definitions and structural lemmas for Uniformization Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/UniformizationLinear.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_IsCPPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationLinear
def UnifExists : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (s : GlobalTheory.UU.HidaSetting V A G),
    ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G),
      U.gen = s.gen ∧ U.LG = s.P.L ∧ HEq U.cubG s.P.c ∧ HEq U.symG s.P.sym
section Triples
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def PrincipalGeneric {R : Type} [CommRing R] [IsDomain R] (t : SAB H (Sp R)) : Prop :=
  IsProper ((Over.pullback (jK R)).obj t.G).hom ∧
    RelAmple ((Over.pullback (jK R)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧
    KTriv ((Over.pullback (jK R)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (jK R)))
def SplitClosed {R : Type} [CommRing R] [IsLocalRing R] (t : SAB H (Sp R)) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField R)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)
def IsLinearUnif {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (t : SAB H (Sp R)) {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} (U : Unif I D A t.G) (h : U.LG = t.PP) : Prop :=
  letI := H.starRing
  ∃ (_ : Module (𝓞 E) D.toPre.X) (oD : D.toPre.OAct (𝓞 E)) (oA : A.OAct (𝓞 E))
    (lin : U.toUnifPre.OLinear (𝓞 E) oD oA t.act.toRingAct) (w0 : TraceFormTwistIso D.toPre oD H.w0),
    PELUnif.TorsionIso ({ D := D, oD := oD, A := A, oA := oA, U := U, bundle := h, lin := lin, w0 := w0 } : PELUnif I t)
end Triples
def TripleUnifExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.UU.CDVR V →
    ∀ t : SAB H (Sp V), PrincipalGeneric t → SplitClosed t →
      ∃ P : PELUnif (IsLocalRing.maximalIdeal V) t, P.TorsionIso
def UnifLinear : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.UU.CDVR V →
    ∀ (t : SAB H (Sp V)) (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V)))
      (U : Unif (IsLocalRing.maximalIdeal V) D A t.G) (h : U.LG = t.PP), IsLinearUnif t U h
def TorsDefinedOn {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃! x : TFK (R := R) F ⟶ A.A, QkToAkU U.toUnifPre F k p x
def TorsDefined : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.UU.CDVR V →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
      (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
      ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F],
        TorsDefinedOn U F
def Statement : Prop := UnifExists ∧ TripleUnifExists ∧ UnifLinear ∧ TorsDefined
example (p : ℕ) [Fact p.Prime] : GlobalTheory.UU.CDVR ℤ_[p] := ⟨inferInstance, inferInstance, inferInstance⟩
example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) (hP : P.TorsionIso) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] : TorsDefinedOn P.U F := fun k hk p => by
  obtain ⟨f, hf, -⟩ := hP F k hk
  exact ⟨f p, (hf p _).2 rfl, fun x hx => (hf p x).1 hx⟩
example {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    {I : Ideal R} (t : SAB H (Sp R)) {D : DegData R I} {A : PolAV (Sp (FractionRing R))} (U : Unif I D A t.G)
    (h : U.LG = t.PP) (hU : IsLinearUnif t U h) :
    ∃ P : PELUnif I t, P.D = D ∧ P.A = A ∧ HEq P.U U ∧ P.TorsionIso := by
  obtain ⟨_, _, _, _, _, hT⟩ := hU
  exact ⟨_, rfl, rfl, HEq.rfl, hT⟩
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationLinear
end


