-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
-- name    : Formalism_HermitianCurvature_TopDensNonnegOfKappa
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:10:55.81265+00:00
-- url     : https://prove2.me/theorems/38ce779e-662b-4e20-b32a-f5f2e6c3fabd
-- title:
--   Top Dens Nonneg Of Kappa
-- statement:
--   Definitions and structural lemmas for Top Dens Nonneg Of Kappa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/TopDensNonnegOfKappa.lean

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
section Her
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (S : Type) [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
  (D : B.RealPlaceData P.k P.r Wp Wq)
def JFOK (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g
def IsRadJF (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π') : Prop :=
  ∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2
inductive HerGen : Fin (P.r + 1) → RadSp P.k P.r z z' π π' → Prop
  | jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π') :
      JFOK P z z' F → IsRadJF P z z' π π' D F Φ → HerGen 0 Φ
  | slice (l : Fin P.r) (w : List (Letter ℂ S)) (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → HerGen l.castSucc Φ → HerGen l.succ ((bTl L l w a b).1 Φ)
  | waveC (l : Fin P.r) (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun c' _ => fsv s (c' l)) → multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l)) →
      HerGen l.castSucc Φ → HerGen l.castSucc ((Vw (mkP Wv Wv') s w a b).1 Φ)
  | waveZ (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) →
      multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
      HerGen (Fin.last P.r) Φ → HerGen (Fin.last P.r) ((Vw (mkP Wv Wv') s w a b).1 Φ)
def herK (i : Fin (P.r + 1)) : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Φ | HerGen S P z z' π π' L st l0 D i Φ}
variable (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'))
def TopTwistDens : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
  ∀ (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
    multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K (Fin.last P.r)) x → InK (K (Fin.last P.r)) y → ∀ c ∈ OmX P.r,
      ∀ g, topDens L st w (act (Vw (mkP Wv Wv') s w) x) y c g = fsv s (zeta P.k P.r z z' g) * topDens L st w x y c g
def FormInt : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → InK (K i) y →
    (∀ (c' : Cf P.r i) (a : Ix S), Integrable (fun g : Mt P.k P.r =>
        B.hsInner ((act (RRi L st i w) x a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
          ((y a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ) ∧
    Integrable (fun c' : Cf P.r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (act (RRi L st i w) x a) (y a) (glue i c c'))
def HerAnalytic : Prop :=
  AdjTop (S := S) P z z' π π' μ L st K l0 ∧ TopDensNonneg (S := S) P z z' π π' L st K l0 ∧
    TopTwistDens S P z z' π π' L st l0 K ∧ StepDens (S := S) P z z' π π' μ L st K l0 ∧
    FormInt S P z z' π π' μ L st l0 K ∧ CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0
end Her
def FormSesqOfInt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    FormInt S P z z' π π' μ L st l0 K → FormSesq (S := S) P z z' π π' μ L st K l0
def RadJFExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (F : Mx P.k P.r → (Wq →L[ℂ] Wp)),
    IsPlace P z z' π π' → D.z = z → D.z' = z' → D.π = π → D.π' = π' → JFOK P z z' F →
    ∃ Φ : RadSp P.k P.r z z' π π', IsRadJF P z z' π π' D F Φ
def HerAnalyticAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    HerAnalytic S P z z' π π' μ L st l0 (herK S P z z' π π' L st l0 D)
def XKappa {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) : Prop :=
  ∃ κ : (M.Ty P → ℂ) →ₐ[ℂ] Pr (RadSp P.k P.r z z' π π'),
    (∀ Y, st.x Y = κ fun ρ => M.x0 P l0 ρ Y) ∧ (∀ Y ∈ st.inv, st.xi Y = κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) ∧
    ∀ f : M.Ty P → ℂ, (∀ ρ, 0 < f ρ) → ∀ (Φ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r),
      0 ≤ B.hsInner (((κ f).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g)
def TopDensNonnegOfKappa : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → XKappa P z z' π π' st l0 →
    TopDensNonneg (S := S) P z z' π π' L st K l0
def TopTwistDensOfWaveQQ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k →
    (∀ (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
      multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
      WaveQQ st.QQ (mkP Wv Wv') (mkP Wv' Wv) s) →
    TopTwistDens S P z z' π π' L st l0 K
def KappaFibrePos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ (X : ActualOps P.k P.r z z' π π') (d : NFData P (Pr (RadSp P.k P.r z z' π π'))),
      IsActualLevel X d.L → Fr.IsStarLevel d.L → d.Rel → (∀ Y, X.QQ Y = d.QQ Y) →
      ∀ f : M.Ty P → ℂ, (∀ ρ, 0 < f ρ) → ∀ (Φ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (g : Mx P.k P.r),
        0 ≤ B.hsInner (((d.κ f).1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g)
def XKappaOfNF : Prop :=
  Q.NormalFormActual → KappaFibrePos →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → XKappa P z z' π π' st l0
def WaveQQTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ (X : ActualOps P.k P.r z z' π π') (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
      multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
      WaveQQ X.QQ (mkP Wv Wv') (mkP Wv' Wv) s
def HerAnalyticC {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) : Prop :=
  AdjTop (S := S) P z z' π π' μ L st K l0 ∧ StepDens (S := S) P z z' π π' μ L st K l0 ∧
    FormInt S P z z' π π' μ L st l0 K ∧ CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0
def HerAnalyticCAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    HerAnalyticC S P z z' π π' μ L st l0 (herK S P z z' π π' L st l0 D)
def HerClassesOfPartsC : Prop :=
  RadJFExists → NormalFormActual → KappaFibrePos → WaveQQTop → HerAnalyticCAll → HerClasses
def HerClassesOfParts : Prop := RadJFExists → HerAnalyticAll → HerClasses
end Formalism.FourierDecayAlt.P5


