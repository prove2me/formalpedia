-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:10.961924+00:00
-- url     : https://prove2.me/theorems/1e4c20b6-2d83-4e03-859f-d617f07531c8
-- title:
--   Is Normal Scheme Sp
-- statement:
--   Definitions and structural lemmas for Is Normal Scheme Sp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/IsNormalSchemeSp.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZJ
abbrev OO (p : ℕ) [Fact p.Prime] : ValuationSubring (PadicAlgCl p) := (Valued.v : Valuation (PadicAlgCl p) NNReal).valuationSubring
abbrev cPt (p : ℕ) [Fact p.Prime] : Sp (OO p) := IsLocalRing.closedPoint (OO p)
abbrev gPt (p : ℕ) [Fact p.Prime] : Sp (PadicAlgCl p) ⟶ Sp (OO p) := spMap (OO p).subtype
abbrev kb (p : ℕ) [Fact p.Prime] : Type := IsLocalRing.ResidueField (OO p)
abbrev rPt (p : ℕ) [Fact p.Prime] : Sp (kb p) ⟶ Sp (OO p) := spMap (IsLocalRing.residue (OO p))
structure Core where
  Z : Scheme.{0}
  [integral : IsIntegral Z]
  π : Z ⟶ Sp ℤ
  flat : Flat π
  lft : LocallyOfFiniteType π
  qc : QuasiCompact π
  sep : IsSeparated π
  normal : IsNormalScheme Z
  U : Z.Opens
  ne : (U : Set Z).Nonempty
  g : ℕ
  A : Over U.toScheme
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension g A.hom
  P : Over Z
  [intP : IsIntegral P.left]
  proper : IsProper P.hom
  G : P.left.Opens
  a : A.left ⟶ G.toScheme
  cart : IsPullback (a ≫ G.ι) A.hom P.hom U.ι
  e : Z ⟶ G.toScheme
  e_sec : e ≫ G.ι ≫ P.hom = 𝟙 Z
  e_zero : U.ι ≫ e = (eSec A ≫ a : U.toScheme ⟶ G.toScheme)
attribute [instance] Core.integral Core.grp Core.comm Core.intP
namespace Core
variable (C : Core)
abbrev GG : Over C.Z := Over.mk (C.G.ι ≫ C.P.hom)
def Cl {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) : Prop := Set.range (gPt p ≫ y) ⊆ C.U
structure Test {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  complete : IsAdicComplete (IsLocalRing.maximalIdeal V) V
  j : V →+* OO p
  j_inj : Function.Injective j
  j_loc : IsLocalHom j
  y₀ : Sp V ⟶ C.Z
  fac : spMap j ≫ y₀ = y
  H : Over (Sp V)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]
  smooth : SmoothOfRelativeDimension C.g H.hom
  sep : IsSeparated H.hom
  qc : QuasiCompact H.hom
  split : ∃ S : SplitExt (Sp (IsLocalRing.ResidueField V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj H)
  f : H.left ⟶ C.G.toScheme
  f_over : f ≫ C.GG.hom = H.hom ≫ y₀
  yK : Sp (FractionRing V) ⟶ C.U.toScheme
  yK_fac : yK ≫ C.U.ι = Out.jK V ≫ y₀
  φ : pullback H.hom (Out.jK V) ⟶ C.A.left
  φ_cart : IsGrpPullback ((Over.pullback (Out.jK V)).obj H) C.A yK φ
  φ_f : φ ≫ C.a = pullback.fst H.hom (Out.jK V) ≫ f
  imm : ∀ h : pullback H.hom (rPt p ≫ spMap j) ⟶ pullback C.GG.hom (rPt p ≫ y),
    h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f → h ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion h
  lift : ∀ b : Sp (OO p) ⟶ C.G.toScheme, b ≫ C.GG.hom = y →
    ∃ c : Sp (OO p) ⟶ H.left, c ≫ H.hom = spMap j ∧ c ≫ f = b
attribute [instance] Test.ring Test.dom Test.dvr Test.grp Test.comm
def HasTests : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z), C.Cl y → Nonempty (C.Test y)
def Indep : Prop := ∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' →
  rPt p ≫ y = rPt p ≫ y' → ∀ b : Sp (OO p) ⟶ C.G.toScheme, b ≫ C.GG.hom = y →
  ∃ b' : Sp (OO p) ⟶ C.G.toScheme, b' ≫ C.GG.hom = y' ∧ rPt p ≫ b' = rPt p ≫ b
def Fib : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (x : Sp (kb p) ⟶ C.G.toScheme),
  x ≫ C.GG.hom = rPt p ≫ y → ∃ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j ∧ c ≫ τ.f = x
def Coord (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)) : Prop :=
  IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) =
    Ideal.span (Set.range fun i => (C.G.toScheme.presheaf.germ W w hw).hom (u i)) ⊔
      ((IsLocalRing.maximalIdeal (C.Z.presheaf.stalk (C.GG.hom w))).map (C.GG.hom.stalkMap w).hom).radical
def TestCart : Prop := ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y),
  IsPullback τ.f τ.H.hom C.GG.hom τ.y₀
def FibLaw : Prop := ∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (τ' : C.Test y')
  (K : Type) [Field K] [IsAlgClosed K] (r : Sp K ⟶ Sp τ.V) (r' : Sp K ⟶ Sp τ'.V),
  Set.range r = {IsLocalRing.closedPoint τ.V} → Set.range r' = {IsLocalRing.closedPoint τ'.V} →
  r ≫ τ.y₀ = r' ≫ τ'.y₀ → ∀ (c d : Over.mk r ⟶ τ.H) (c' d' : Over.mk r' ⟶ τ'.H),
  c.left ≫ τ.f = c'.left ≫ τ'.f → d.left ≫ τ.f = d'.left ≫ τ'.f →
  (c * d).left ≫ τ.f = (c' * d').left ≫ τ'.f ∧ (c⁻¹).left ≫ τ.f = (c'⁻¹).left ≫ τ'.f
structure Law where
  [grp : GrpObj C.GG]
  [comm : IsCommMonObj C.GG]
  smooth : SmoothOfRelativeDimension C.g C.GG.hom
  zero : (eSec C.GG : C.Z ⟶ C.G.toScheme) = C.e
  pull : IsGrpPullback C.A C.GG C.U.ι C.a
  test : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), IsGrpPullback τ.H C.GG τ.y₀ τ.f
end Core
theorem isNormalScheme_sp (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := by
  intro x
  refine ⟨inferInstance, ?_⟩
  have : (PrimeSpectrum.asIdeal x).IsPrime := PrimeSpectrum.isPrime x
  have h := StructureSheaf.IsLocalization.to_stalk R x
  exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk x) _ _ (_) _ _
    (PrimeSpectrum.asIdeal x).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
def Core.zero (U : (Sp ℤ).Opens) (hU : (U : Set (Sp ℤ)).Nonempty) : Core where
  Z := Sp ℤ
  π := 𝟙 _
  flat := inferInstance
  lft := inferInstance
  qc := inferInstance
  sep := inferInstance
  normal := isNormalScheme_sp ℤ
  U := U
  ne := hU
  g := 0
  A := 𝟙_ (Over U.toScheme)
  ab :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (𝟙 U.toScheme))
      proper := inferInstanceAs (IsProper (𝟙 U.toScheme))
      geomConnected := by
        change GeometricallyConnected (𝟙 U.toScheme)
        infer_instance }
  dim := inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 U.toScheme))
  P := 𝟙_ (Over (Sp ℤ))
  intP := inferInstanceAs (IsIntegral (Sp ℤ))
  proper := inferInstanceAs (IsProper (𝟙 (Sp ℤ)))
  G := ⊤
  a := U.ι ≫ (Sp ℤ).topIso.inv
  cart := by
    change IsPullback ((U.ι ≫ (Sp ℤ).topIso.inv) ≫ (⊤ : (Sp ℤ).Opens).ι) (𝟙 U.toScheme) (𝟙 (Sp ℤ)) U.ι
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  e := (Sp ℤ).topIso.inv
  e_sec := by
    change (Sp ℤ).topIso.inv ≫ (⊤ : (Sp ℤ).Opens).ι ≫ 𝟙 (Sp ℤ) = _
    simp
  e_zero := by
    change _ = 𝟙 U.toScheme ≫ U.ι ≫ (Sp ℤ).topIso.inv
    simp
instance : Inhabited Core := ⟨Core.zero ⊤ ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ), trivial⟩⟩
example (h : ((⊤ : (Sp ℤ).Opens) : Set (Sp ℤ)).Nonempty) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Sp ℤ) :
    (Core.zero ⊤ h).Cl y := fun _ _ => trivial
example (U : (Sp ℤ).Opens) (hU : (U : Set (Sp ℤ)).Nonempty) : (Core.zero U hU).Indep := by
  intro p _ y y' _ _ h b hb
  have hι : (Core.zero U hU).GG.hom = (⊤ : (Sp ℤ).Opens).ι := Category.comp_id _
  have : IsIso (Core.zero U hU).GG.hom := by
    rw [hι]
    exact inferInstanceAs (IsIso (Sp ℤ).topIso.hom)
  refine ⟨y' ≫ inv (Core.zero U hU).GG.hom, by simp, ?_⟩
  rw [← cancel_mono (Core.zero U hU).GG.hom]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, hb, h]
end GlobalTheory.ZJ
end


