-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_CMObjBundlePull
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_CMObjBundlePull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:08.139047+00:00
-- url     : https://prove2.me/theorems/a2917f09-1532-440a-bf1e-3c604deba53c
-- title:
--   CMObj Bundle Pull
-- statement:
--   Definitions and structural lemmas for CMObj Bundle Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/CMObjBundlePull.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM
section Lie
variable {S : Scheme.{0}} {R : Type} [CommRing R]
abbrev epsAt (t : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ t)
def IsTan {G : Over S} [GrpObj G] (t : Sp R ⟶ S) (v : epsAt t ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left
def IsMultiple {G : Over S} {t : Sp R ⟶ S} (x : R) (v w : epsAt t ⟶ G) : Prop :=
  w.left = spMap (epsScaleR x) ≫ v.left
def IsEig {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (ac : Out.RingAct G O)
    (t : Sp R ⟶ S) (χ : O →+* R) (v : epsAt t ⟶ G) : Prop :=
  IsTan t v ∧ ∀ a : O, IsMultiple (χ a) v (v ≫ ac.act a)
def IsEigBasis {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (ac : Out.RingAct G O)
    (t : Sp R ⟶ S) (χ : O →+* R) (v : epsAt t ⟶ G) : Prop :=
  IsEig ac t χ v ∧ ∀ w, IsEig ac t χ w → ∃! x : R, IsMultiple x v w
def EigZero {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (ac : Out.RingAct G O)
    (t : Sp R ⟶ S) (χ : O →+* R) : Prop :=
  ∀ w, IsEig ac t χ w → w = 1
end Lie
section Line
variable {K : Type} [Field K] [NumberField K]
abbrev genPt (K : Type) [Field K] [NumberField K] : Sp K ⟶ Sp (𝓞 K) := spMap (algebraMap (𝓞 K) K)
abbrev locRing (𝔭 : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K 𝔭.asIdeal.primeCompl 𝔭.asIdeal.primeCompl_le_nonZeroDivisors
def IntegralAt (P : Out.PolAV (Sp (𝓞 K))) (v : epsAt (genPt K) ⟶ P.A) (𝔭 : HeightOneSpectrum (𝓞 K)) (x : K) :
    Prop :=
  ∃ u : epsAt (spMap (algebraMap (𝓞 K) (locRing 𝔭))) ⟶ P.A, IsTan _ u ∧
    spMap (dualMap (locRing 𝔭).val.toRingHom) ≫ u.left = spMap (epsScaleR x) ≫ v.left
def LineLocAt (P : Out.PolAV (Sp (𝓞 K))) (v : epsAt (genPt K) ⟶ P.A) (ℓ : MLine K)
    (𝔭 : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x : K, IntegralAt P v 𝔭 x ↔ ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ (s : K) * x ∈ ℓ.I
def LineArchAt (P : Out.PolAV (Sp (𝓞 K))) (v : epsAt (genPt K) ⟶ P.A) (ℓ : MLine K) (σ : K →+* ℂ) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (pr : A.left ⟶ P.A.left) (u : HolUnif A (P.L.pull pr) P.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (vσ : epsR ℂ ⟶ A) (w : Fin P.g → ℂ),
    IsGrpPullback A P.A (spMap (σ.comp (algebraMap (𝓞 K) K))) pr ∧ u.IsAH Hm χ ∧
    vσ.left ≫ pr = spMap (dualMap σ) ≫ v.left ∧ u.IsDiff w vσ ∧
    ℓ.n σ ^ 2 = Real.pi * (w ⬝ᵥ Hm.mulVec (star w)).re
def IsLineOf (P : Out.PolAV (Sp (𝓞 K))) (v : epsAt (genPt K) ⟶ P.A) (ℓ : MLine K) : Prop :=
  IsTan (genPt K) v ∧ v ≠ 1 ∧ ℓ.Good ∧ (∀ 𝔭, LineLocAt P v ℓ 𝔭) ∧ ∀ σ, LineArchAt P v ℓ σ
end Line
section Pol
variable {K : Type} [Field K] [NumberField K]
def WeilPull (A B : Out.PolAV (Sp (𝓞 K))) (φ : A.A ⟶ B.A) (f : A.A ⟶ A.A) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (β : K →+* k) (n : ℕ), 0 < n →
    ∀ x y : Over.mk (spMap β ≫ genPt K) ⟶ A.A, x ^ n = 1 → y ^ n = 1 → ∀ z : kˣ,
      (Out.WeilIs B.A B.L n (x ≫ φ) (y ≫ φ) (unitOn z) ↔ Out.WeilIs A.A A.L n x (y ≫ f) (unitOn z))
def BundlePull {S : Scheme.{0}} (A B : Out.PolAV S) (φ : A.A ⟶ B.A) (f : A.A ⟶ A.A) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    LBIso ((cubeLB B.A ![fst A.A A.A ≫ φ, snd A.A A.A ≫ φ] B.L).pull ((A.A ⊗ A.A).hom ⁻¹ᵁ U).ι)
      ((cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ f] A.L).pull ((A.A ⊗ A.A).hom ⁻¹ᵁ U).ι)
end Pol
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
def psi (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = H.rt0}
def psiBar (H : Host E) : Set (E →+* ℂ) := {τ | τ (H.rt : E) = -H.rt0}
structure CMObj (c : Coeff l) (p q : ℕ) : Type 1 where

  K : Type
  [field : Field K]
  [numberField : NumberField K]
  [alg : Algebra c.F K]

  B : Out.PolAV (Sp (𝓞 K))

  AP : Out.PolAV (Sp (𝓞 K))

  AC : Out.PolAV (Sp (𝓞 K))
  ιB : Out.RingAct B.A (𝓞 E)
  ιP : Out.RingAct AP.A (𝓞 E)
  ιC : Out.RingAct AC.A (𝓞 E)

  φP : Fin p → (AP.A ⟶ B.A)
  φP_hom : ∀ j, IsMonHom (φP j)
  φP_lin : ∀ j a, ιP.act a ≫ φP j = φP j ≫ ιB.act a

  φC : Fin q → (AC.A ⟶ B.A)
  φC_hom : ∀ j, IsMonHom (φC j)
  φC_lin : ∀ j a, ιC.act a ≫ φC j = φC j ≫ ιB.act a

  hP : Fin p → 𝓞 E

  hC : Fin q → 𝓞 E

  ηP : psi H → (epsAt (genPt K) ⟶ AP.A)

  ηC : psiBar H → (epsAt (genPt K) ⟶ AC.A)

  ℓP : psi H → MLine K

  ℓC : psiBar H → MLine K
attribute [instance] CMObj.field CMObj.numberField CMObj.alg
namespace CMObj
variable {c : Coeff l} {p q : ℕ} (o : CMObj c p q)
def emb (τ : E →+* ℂ) : 𝓞 E →+* o.K := (algebraMap c.F o.K).comp (embK c τ)
def Rosati : Prop :=
  (∀ a, Out.RosatiAdj o.B.A o.B.L (o.ιB.act a) (o.ιB.act (H.bar a))) ∧
  (∀ a, Out.RosatiAdj o.AP.A o.AP.L (o.ιP.act a) (o.ιP.act (H.bar a))) ∧
  ∀ a, Out.RosatiAdj o.AC.A o.AC.L (o.ιC.act a) (o.ιC.act (H.bar a))
def Types : Prop :=
  ((∀ τ : psi H, IsEigBasis o.ιP (genPt o.K) (o.emb τ.1) (o.ηP τ)) ∧
    ∀ τ, τ ∉ psi H → EigZero o.ιP (genPt o.K) (o.emb τ)) ∧
  ((∀ τ : psiBar H, IsEigBasis o.ιC (genPt o.K) (o.emb τ.1) (o.ηC τ)) ∧
    ∀ τ, τ ∉ psiBar H → EigZero o.ιC (genPt o.K) (o.emb τ))
def Lines : Prop :=
  (∀ τ, IsLineOf o.AP (o.ηP τ) (o.ℓP τ)) ∧ ∀ τ, IsLineOf o.AC (o.ηC τ) (o.ℓC τ)
def fac : Fin p ⊕ Fin q → Over (Sp (𝓞 o.K))
  | .inl _ => o.AP.A
  | .inr _ => o.AC.A
def sumMap : (∏ᶜ o.fac) ⟶ o.B.A :=
  (List.ofFn fun j => (Pi.π o.fac (.inl j) ≫ o.φP j : (∏ᶜ o.fac) ⟶ o.B.A)).prod *
    (List.ofFn fun j => (Pi.π o.fac (.inr j) ≫ o.φC j : (∏ᶜ o.fac) ⟶ o.B.A)).prod
def Isogeny : Prop := IsFinite o.sumMap.left ∧ Surjective o.sumMap.left
def PolPull : Prop :=
  (∀ j, WeilPull o.AP o.B (o.φP j) (o.ιP.act (o.hP j))) ∧ ∀ j, WeilPull o.AC o.B (o.φC j) (o.ιC.act (o.hC j))
def PolPullBundle : Prop :=
  (∀ j, BundlePull o.AP o.B (o.φP j) (o.ιP.act (o.hP j))) ∧ ∀ j, BundlePull o.AC o.B (o.φC j) (o.ιC.act (o.hC j))
def Bound (La : ℝ) : Prop :=
  (∀ j (τ : E →+* ℂ), ‖τ (o.hP j : E)‖ ≤ La ^ 2) ∧ ∀ j (τ : E →+* ℂ), ‖τ (o.hC j : E)‖ ≤ La ^ 2
def Good (La : ℝ) : Prop :=
  o.Rosati ∧ o.Types ∧ o.Lines ∧ o.Isogeny ∧ o.PolPull ∧ o.Bound La
end CMObj
example {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} {t : Sp R ⟶ S} (v : epsAt t ⟶ G) :
    IsMultiple 1 v v := by
  have : epsScaleR (1 : R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsScaleR]
  simp [IsMultiple, this, spMap]
end GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull


