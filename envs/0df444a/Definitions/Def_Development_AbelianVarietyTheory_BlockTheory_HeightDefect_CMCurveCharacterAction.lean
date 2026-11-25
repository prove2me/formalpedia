-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_CMCurveCharacterAction
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_CMCurveCharacterAction
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:56.69588+00:00
-- url     : https://prove2.me/theorems/fb04465d-d3dc-5bce-b300-ad74b6ec804d
-- title:
--   CMCurve Character Action
-- statement:
--   Definitions and structural lemmas for CMCurve Character Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/CMCurveCharacterAction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
def legChar (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
def logPeriod (d : ℕ) [Fact d.Prime] : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt d) -
    (deriv (legChar d).LFunction 1 / (legChar d).LFunction 1).re
def IsConj {K : Type} [Field K] (a b : 𝓞 K) : Prop :=
  ∀ τ : K →+* ℂ, τ (b : K) = starRingEnd ℂ (τ (a : K))
section
variable {R : Type} [CommRing R]
def RosatiConj {K : Type} [Field K] (P : Out.PolAV (Sp R)) (act : OAct (𝓞 K) P.A) : Prop :=
  ∀ a b : 𝓞 K, IsConj a b →
    LBIso (cubeLB P.A ![fst P.A P.A ≫ act.act a, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ act.act b] P.L)
def ActsThrough {O : Type} [CommRing O] (P : Out.PolAV (Sp R)) (act : OAct O P.A) (ρ : O →+* R)
    (v : epsR R ⟶ P.A) : Prop :=
  ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (ρ a)) ≫ v.left
def IsLenSq (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (s : R →+* ℂ) (x : ℝ) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.A.left) (u : HolUnif A (P.L.pull φ) 1)
    (Hm : Matrix (Fin 1) (Fin 1) ℂ) (χ : u.Λ → ℂ) (vs : epsR ℂ ⟶ A) (w : Fin 1 → ℂ),
    IsGrpPullback A P.A (spMap s) φ ∧ u.IsAH Hm χ ∧
    vs.left ≫ φ = spMap (Chart.dualMapR s) ≫ v.left ∧ u.IsDiff w vs ∧
    x = Real.pi * (hermForm Hm w w).re
def IsPrincipalAt {K : Type} [Field K] (d : ℕ) (τ : K →+* ℂ) (P : Out.PolAV (Sp R)) (act : OAct (𝓞 K) P.A)
    (s : R →+* ℂ) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.A.left) (u : HolUnif A (P.L.pull φ) 1) (χ : u.Λ → ℂ),
    IsGrpPullback A P.A (spMap s) φ ∧
    (∀ z : Fin 1 → ℂ, z ∈ u.Λ ↔ ∃ a : 𝓞 K, z 0 = τ (a : K)) ∧
    (∀ (a : 𝓞 K) (z : Fin 1 → ℂ), (u.ex (τ (a : K) • z)).left ≫ φ = (u.ex z).left ≫ φ ≫ (act.act a).left) ∧
    u.IsAH (Matrix.of fun _ _ => ((2 / Real.sqrt d : ℝ) : ℂ)) χ
end
def IsCMCurve {K : Type} [Field K] (d : ℕ) (τ : K →+* ℂ) (logOm : ℝ) (M : Type) [Field M] [NumberField M]
    (P : Out.PolAV (Sp (𝓞 M))) (act : OAct (𝓞 K) P.A) (ρ : 𝓞 K →+* 𝓞 M) (v : epsR (𝓞 M) ⟶ P.A) : Prop :=
  P.g = 1 ∧ RosatiConj P act ∧
  IsLieBasis (fun _ : Fin 1 => v) ∧ ActsThrough P act ρ v ∧
  (∃ σ₀ : M →+* ℂ, (∀ a : 𝓞 K, σ₀ ((ρ a : 𝓞 M) : M) = τ (a : K)) ∧
    IsPrincipalAt d τ P act (σ₀.comp (algebraMap (𝓞 M) M))) ∧
  ∃ len_sq : (M →+* ℂ) → ℝ, (∀ σ, 0 < len_sq σ) ∧
    (∀ σ x, IsLenSq P v (σ.comp (algebraMap (𝓞 M) M)) x ↔ x = len_sq σ) ∧
    (∑ σ, Real.log (len_sq σ)) / (Module.finrank ℚ M : ℝ) = -logOm
def CMCurveExists : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 16 = 7 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (rt : K), rt ^ 2 = -(d : K) →
    ∀ τ : K →+* ℂ, τ rt = Complex.I * (Real.sqrt d : ℝ) →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (P : Out.PolAV (Sp (𝓞 M))) (act : OAct (𝓞 K) P.A)
      (ρ : 𝓞 K →+* 𝓞 M) (v : epsR (𝓞 M) ⟶ P.A), IsCMCurve d τ (logPeriod d) M P act ρ v
example (M : Type) [Field M] [NumberField M] : Fintype.card (M →+* ℂ) = Module.finrank ℚ M :=
  Embeddings.card M ℂ
end GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves


