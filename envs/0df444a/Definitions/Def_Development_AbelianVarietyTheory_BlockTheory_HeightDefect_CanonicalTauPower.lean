-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_CanonicalTauPower
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_CanonicalTauPower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:40.768071+00:00
-- url     : https://prove2.me/theorems/7eff941f-b7da-40e2-bc22-6f964ce7dfaa
-- title:
--   Canonical Tau Power
-- statement:
--   Definitions and structural lemmas for Canonical Tau Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/CanonicalTauPower.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalTauPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
def IsBaseChange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (P' : Out.PolAV (Sp R')) (rig' : LB.Gen (P'.L.pull (eSec P'.A)))
    (P : Out.PolAV (Sp R)) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull φ)) : Prop :=
  IsGrpPullback P'.A P.A (spMap f) φ ∧ w.IsGen ∧
    ∃ he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A,
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) rig'
        (rigPullOf φ (spMap f) he P.L rig)
def IsDiagPull {S : Scheme.{0}} (P : Out.PolAV S) (f : P.A ⟶ P.A) : Prop :=
  ∃ u : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(padd P.A (𝟙 _) f).left, 𝟙 P.A.left, f.left, (toUnit P.A ≫ η[P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (eSec P.A)) (LB.oneGen P.L)
def canφ {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) : Fin 8 → ((P.A ⊗ P.A).left ⟶ P.A.left) :=
  ![(padd P.A (fst P.A P.A) (snd P.A P.A)).left, (fst P.A P.A).left, (snd P.A P.A).left,
    (toUnit (P.A ⊗ P.A) ≫ η[P.A]).left,
    (padd P.A (fst P.A P.A ^ k) (snd P.A P.A ^ k)).left, (fst P.A P.A ^ k : P.A ⊗ P.A ⟶ P.A).left,
    (snd P.A P.A ^ k : P.A ⊗ P.A ⟶ P.A).left, (toUnit (P.A ⊗ P.A) ≫ η[P.A]).left]
def canε (k : ℕ) : Fin 8 → ℤ :=
  ![(k : ℤ) ^ 2, -(k : ℤ) ^ 2, -(k : ℤ) ^ 2, (k : ℤ) ^ 2, -1, 1, 1, -1]
section Data
variable {R : Type} [CommRing R] [IsDomain R]
def TauPowCan (D : Out.DegPre R) (k : ℕ) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (canφ D.P k) (canε k)), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (Out.GeneratorPullback.powGen D.P.L _ _ (D.tau y y') (k ^ 2))
        (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (LB.oneGen D.P.L)
def TauSymm (D : Out.DegPre R) : Prop :=
  ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _ (D.tau y y') (D.tau y' y)
def PsiNormOne (D : Out.DegPre R) (s : FractionRing R →+* ℂ) : Prop :=
  ∀ (P' : Out.PolAV (Sp ℂ)) (rig' : LB.Gen (P'.L.pull (eSec P'.A))) (φ : P'.A.left ⟶ D.P.A.left)
    (w : LB.Iso P'.L (D.P.L.pull φ)), rig'.IsGen →
    IsBaseChange (s.comp (algebraMap R (FractionRing R))) P' rig' D.P D.rig φ w →
    ∀ (u : HolUnif P'.A P'.L P'.g) (Hm : Matrix (Fin P'.g) (Fin P'.g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ → u.IsRig rig' →
      ∀ (y : D.X) (z : Fin P'.g → ℂ), (u.ex z).left ≫ φ = spMap s ≫ D.xK y →
        ∀ (j : D.P.L.ι) (i : P'.L.ι),
          ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (D.P.L.pull φ) P'.L).U (fun _ => j, i) →
          ‖valF (F := ℂ) (spMap s) _ ((D.psi y).s (fun _ => j)).val *
              valF (F := ℂ) (u.ex z).left _ (w.s (fun _ => j, i)).val * u.fr i z‖ ^ 2 =
            Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)
end Data
def TorsionTrivialisation : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    letI := H.starRing
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (P : Out.PolAV (Sp (𝓞 K₁)))
      (rig : LB.Gen (P.L.pull (eSec P.A))) (act : P.OAct (𝓞 E))
      (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (c : Y → (𝟙_ (Over (Sp (𝓞 K₁))) ⟶ P.A)) (k : ℕ),
      rig.IsGen → IsDiagPull P (act.act H.w0) →
      (∀ y y', c (y + y') = padd P.A (c y) (c y')) →
      (∀ (a : 𝓞 E) y, c (a • y) = c y ≫ act.act a) →
      1 ≤ k → (∀ y, c y ^ k = 1) →
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K₁ K')
        (D : Out.DegPre (𝓞 K')) (_ : Module (𝓞 E) D.X) (oa : D.OAct (𝓞 E)) (e : Y ≃ₗ[𝓞 E] D.X)
        (φ : D.P.A.left ⟶ P.A.left) (w : LB.Iso D.P.L (P.L.pull φ)),
        IsBaseChange (algebraMap (𝓞 K₁) (𝓞 K')) D.P D.rig P rig φ w ∧
        (∀ a, (oa.onB.act a).left ≫ φ = φ ≫ (act.act a).left) ∧
        (∀ y, (D.c (e y)).left ≫ φ = spMap (algebraMap (𝓞 K₁) (𝓞 K')) ≫ (c y).left) ∧
        TauSymm D ∧ D.TauBimult ∧ TauPowCan D k ∧
        TraceFormTwistIso D oa H.w0 ∧ D.PsiEven ∧
        (∀ y, PsiUnitOn D y Set.univ) ∧
        ∀ s : FractionRing (𝓞 K') →+* ℂ, PsiNormOne D s
example (k : ℕ) : ∑ i, canε k i = 0 := by
  simp [canε, Fin.sum_univ_succ]
example (S : Scheme.{0}) : IsDiagPull (Out.Inh.zeroPolAV S) (𝟙 _) :=
  ⟨⟨fun _ => 1⟩, by
    intro i j; erw [Out.Inh.linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one], by
    intro j j' _ _ _; dsimp only [LB.pullGen, LB.oneGen]; repeat erw [map_one]⟩
end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalTauPower


