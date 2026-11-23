-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetChartLaws
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetChartLaws
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:22.99391+00:00
-- url     : https://prove2.me/theorems/c74901d3-50c0-4b58-9b31-15dbd7c73ad4
-- title:
--   Jet Chart Laws
-- statement:
--   Definitions and structural lemmas for Jet Chart Laws, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/JetChartLaws.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]
abbrev algO (x : Sp S ⟶ X₀) (B : Type) [CommRing B] [Algebra S B] : Over X₀ :=
  Over.mk (spMap (algebraMap S B) ≫ x)
def algMap (x : Sp S ⟶ X₀) {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B']
    (f : B →ₐ[S] B') : algO x B' ⟶ algO x B :=
  Over.homMk (spMap (f : B →+* B')) (by
    change spMap (f : B →+* B') ≫ spMap (algebraMap S B) ≫ x = spMap (algebraMap S B') ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])
def jetVec {σ : Type} (c : σ → S) : Jet S σ 1 →ₐ[S] DualNumber S :=
  liftJet (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S))
          (MvPolynomial.X i : MvPolynomial σ S)) ≤ Ideal.span {(DualNumber.eps : DualNumber S)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [MvPolynomial.aeval_X, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    refine (Ideal.pow_right_mono h1 _).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)
abbrev JetPts (G : Over X₀) (x : Sp S ⟶ X₀) (d : ℕ) : Type :=
  ∀ m : ℕ, algO x (Jet S (Fin d) m) ⟶ G
section Group
variable (G : Over X₀) [GrpObj G] (x : Sp S ⟶ X₀) {d : ℕ}
def IsFormalParam (j : JetPts G x d) : Prop :=
  (∀ m, algMap x (jetTrunc : Jet S (Fin d) (m + 1) →ₐ[S] Jet S (Fin d) m) ≫ j (m + 1) = j m) ∧
  (∀ m, algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1) ∧
  ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (I : Ideal B), I ^ (m + 1) = ⊥ →
    ∀ g : algO x B ⟶ G, algMap x (Ideal.Quotient.mkₐ S I) ≫ g = 1 →
      ∃! f : Jet S (Fin d) m →ₐ[S] B, algMap x f ≫ j m = g
def LawIs (j : JetPts G x d) (F : Fin d → Germ.PS S 2 d) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (F i) = 0) ∧
  ∀ m, (algMap x (jetIn (0 : Fin 2)) ≫ j m) *
      (algMap x (jetIn (1 : Fin 2)) ≫ j m) =
    algMap x (jetSubstPS (m := m) F) ≫ j m
omit [GrpObj G] in

def EndIs (j : JetPts G x d) (α : G ⟶ G) (φ : Germ.Pt S 1 d) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) ∧
  ∀ m, algMap x (jetIn (0 : Fin 1)) ≫ j m ≫ α =
    algMap x (jetSubstPS (m := m) φ) ≫ j m
omit [GrpObj G] in

def TanIs (j : JetPts G x d) (v : Sp (DualNumber S) ⟶ G.left) (c : Fin d → S) : Prop :=
  v = (algMap x (jetVec c) ≫ j 1).left
def IsGrpChart {O : Type} [CommRing O] (act : OAct O G) {κ : Type} (j : JetPts G x d)
    (F : Fin d → Germ.PS S 2 d) (A : O → Germ.Pt S 1 d)
    (u : κ → (Sp (DualNumber S) ⟶ G.left)) (c : κ → Fin d → S) : Prop :=
  IsFormalParam G x j ∧ LawIs G x j F ∧ (∀ a, EndIs G x j (act.act a) (A a)) ∧
    (∀ k, TanIs G x j (u k) (c k)) ∧
    LinearIndependent S c ∧ Submodule.span S (Set.range c) = ⊤
end Group
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def IsChart (t : SAB H X₀) (x : Sp S ⟶ X₀) {d : ℕ} {κ : Type} (j : JetPts t.G x d)
    (F : Fin d → Germ.PS S 2 d) (A : 𝓞 E → Germ.Pt S 1 d)
    (u : κ → (Sp (DualNumber S) ⟶ t.G.left)) (c : κ → Fin d → S) : Prop :=
  IsGrpChart t.G x t.act j F A u c
abbrev IsChartOf (t : SAB H X₀) (x : Sp S ⟶ X₀) {d : ℕ} {κ : Type} (j : JetPts t.G x d)
    (GG : Germ.FGLaw S d) (A : Germ.OAct (𝓞 E) GG)
    (u : κ → (Sp (DualNumber S) ⟶ t.G.left)) (c : κ → Fin d → S) : Prop :=
  IsChart t x j GG.F A.act u c
end GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws


