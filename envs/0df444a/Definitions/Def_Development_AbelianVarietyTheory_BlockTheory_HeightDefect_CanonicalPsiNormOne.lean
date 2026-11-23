-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_CanonicalPsiNormOne
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_CanonicalPsiNormOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:38.007544+00:00
-- url     : https://prove2.me/theorems/18792945-463a-495f-ba52-7da945ea694a
-- title:
--   Canonical Psi Norm One
-- statement:
--   Definitions and structural lemmas for Canonical Psi Norm One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/CanonicalPsiNormOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalPsiTorsionNorm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
section Can
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
def canφ (k : ℕ) : Fin 8 → ((A ⊗ A).left ⟶ A.left) :=
  ![(padd A (fst A A ^ k) (snd A A ^ k)).left, (fst A A ^ k).left, (snd A A ^ k).left, (pzero A (A ⊗ A)).left,
    (padd A (fst A A) (snd A A)).left, (fst A A).left, (snd A A).left, (pzero A (A ⊗ A)).left]
def canε (k : ℕ) : Fin 8 → ℤ := ![1, -1, -1, 1, -(k : ℤ) ^ 2, (k : ℤ) ^ 2, (k : ℤ) ^ 2, -(k : ℤ) ^ 2]
example (k : ℕ) : ∑ i, canε k i = 0 := by simp [canε, Fin.sum_univ_succ]
def IsCanIso (L : LB A.left) (k : ℕ) (u : LB.Gen (LB.LinComb L (canφ A k) (canε k))) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (Out.zero2 A)) (LB.oneGen L)
def IsDiagPull (L : LB A.left) (f : A ⟶ A) : Prop :=
  ∃ u : LB.Gen (LB.LinComb L (K := Fin 4)
      ![(padd A (𝟙 A) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (eSec A)) (LB.oneGen L)
end Can
section Out
variable {R : Type} [CommRing R] [IsDomain R]
def TauPowCan (D : Out.DegPre R) (k : ℕ) : Prop :=
  (∃ u, IsCanIso D.P.A D.P.L k u) ∧
    ∀ u, IsCanIso D.P.A D.P.L k u → ∀ y y' : D.X,
      LB.Gen.Corr D.P.L _ _ _ _ (Out.GeneratorPullback.powGen D.P.L _ _ (D.tau y y') (k ^ 2))
        (LB.pullGen D.P.L _ _ u (D.pt2 y y'))
def PsiNormOne (D : Out.DegPre R) (σ : FractionRing R →+* ℂ) : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ D.P.A.left)
    (he : eSec A ≫ φ = spMap (σ.comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A),
    IsGrpPullback A D.P.A (spMap (σ.comp (algebraMap R (FractionRing R)))) φ →
    ∀ (u : HolUnif A (D.P.L.pull φ) D.P.g) (Hm : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ → u.IsRig (rigPullOf φ (spMap (σ.comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
      ∀ (y : D.X) (z : Fin D.P.g → ℂ), (u.ex z).left ≫ φ = spMap σ ≫ D.xK y →
        ∀ j : PUnit → D.P.L.ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (D.P.L.pull φ).U j →
          ‖valAt' (X := (Out.TK R).left) (spMap σ) _ ((D.psi y).s j).val * u.fr j z‖ =
            Real.exp (-(Real.pi / 2) * (z ⬝ᵥ Hm.mulVec (star z)).re)
end Out
def TorsionTau : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    letI := H.starRing
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (P : Out.PolAV (Sp (𝓞 K₁)))
      (rig : LB.Gen (P.L.pull (eSec P.A))) (oa : P.OAct (𝓞 E))
      (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [Module (𝓞 E) Y]
      (c₀ : Y → (𝟙_ (Over (Sp (𝓞 K₁))) ⟶ P.A)) (k : ℕ),
      rig.IsGen → IsDiagPull P.A P.L (oa.act H.w0) →
      (∀ y y', c₀ (y + y') = padd P.A (c₀ y) (c₀ y')) →
      (∀ (a : 𝓞 E) y, c₀ (a • y) = c₀ y ≫ oa.act a) →
      1 ≤ k → (∀ y, c₀ y ^ k = 1) →
      ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra K₁ K₂)
        (D₀ : Out.DegPre (𝓞 K₂)) (_ : Module (𝓞 E) D₀.X) (oa₀ : D₀.OAct (𝓞 E))
        (φ : D₀.P.A.left ⟶ P.A.left)
        (he : eSec D₀.P.A ≫ φ = spMap (algebraMap (𝓞 K₁) (𝓞 K₂)) ≫ eSec P.A)
        (w : LB.Iso D₀.P.L (P.L.pull φ)) (e : Y ≃ₗ[𝓞 E] D₀.X),

        (IsGrpPullback D₀.P.A P.A (spMap (algebraMap (𝓞 K₁) (𝓞 K₂))) φ ∧ w.IsGen ∧
          LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D₀.P.A) (fun _ => 1)) D₀.rig
            (rigPullOf φ (spMap (algebraMap (𝓞 K₁) (𝓞 K₂))) he P.L rig) ∧
          (∀ a, (oa₀.onB.act a).left ≫ φ = φ ≫ (oa.act a).left) ∧
          (∀ y, (D₀.c (e y)).left ≫ φ = spMap (algebraMap (𝓞 K₁) (𝓞 K₂)) ≫ (c₀ y).left)) ∧
        D₀.TauBimult ∧ TauPowCan D₀ k ∧
        TraceFormTwistIso D₀ oa₀ H.w0 ∧ D₀.PsiEven ∧
        (∀ y, PsiUnitOn D₀ y Set.univ) ∧
        ∀ σ : FractionRing (𝓞 K₂) →+* ℂ, PsiNormOne D₀ σ
end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalPsiTorsionNorm


