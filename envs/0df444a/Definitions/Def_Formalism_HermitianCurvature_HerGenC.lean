-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HerGenC
-- name    : Formalism_HermitianCurvature_HerGenC
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:30:32.157224+00:00
-- url     : https://prove2.me/theorems/e5cb2b78-9773-4264-bcff-097472d5122c
-- title:
--   Her Gen C
-- statement:
--   Definitions and structural lemmas for Her Gen C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HerGenC.lean

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
section HerC
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (S : Type) [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
  (D : B.RealPlaceData P.k P.r Wp Wq)
def JFOKCpt (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  JFOK P z z' F ∧ HasCompactSupport F
inductive HerGenC : Fin (P.r + 1) → RadSp P.k P.r z z' π π' → Prop
  | jf (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π') :
      JFOKCpt P z z' F → IsRadJF P z z' π π' D F Φ → HerGenC 0 Φ
  | slice (l : Fin P.r) (w : List (Letter ℂ S)) (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → HerGenC l.castSucc Φ → HerGenC l.succ ((bTl L l w a b).1 Φ)
  | waveC (l : Fin P.r) (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun c' _ => fsv s (c' l)) → multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l)) →
      HerGenC l.castSucc Φ → HerGenC l.castSucc ((Vw (mkP Wv Wv') s w a b).1 Φ)
  | waveZ (w : List (Letter ℂ S)) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
      (a b : Ix S) (Φ : RadSp P.k P.r z z' π π') :
      WordOK P z z' π π' st l0 w → multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) →
      multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
      HerGenC (Fin.last P.r) Φ → HerGenC (Fin.last P.r) ((Vw (mkP Wv Wv') s w a b).1 Φ)
def herKc (i : Fin (P.r + 1)) : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Φ | HerGenC S P z z' π π' L st l0 D i Φ}
end HerC
def HerClassesCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (A : ℝ) (mm : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    Auser P (Fintype.card S) ≤ A → mmUser P (Fintype.card S) ≤ mm →
    ∃ K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'),
      AdjTop (S := S) P z z' π π' μ L st K l0 ∧ TopDensNonneg (S := S) P z z' π π' L st K l0 ∧
      TopTwist (S := S) P z z' π π' L st K l0 ∧ SliceIn (S := S) P z z' π π' L st K l0 ∧
      StepDens (S := S) P z z' π π' μ L st K l0 ∧ WaveK (S := S) P z z' π π' st K l0 ∧
      FormSesq (S := S) P z z' π π' μ L st K l0 ∧ CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 ∧
      ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
        HasCompactSupport F → (∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g) →
        ∃ Φ ∈ K 0, ∀ x ∈ DomR P.k P.r z z',
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2
def ThmPActualCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (A : ℝ) (mm : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    Auser P (Fintype.card S) ≤ A → mmUser P (Fintype.card S) ≤ mm →
    ∃ K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'),
      ThmPOn (S := S) P z z' π π' μ L st K l0 ∧ SliceIn (S := S) P z z' π π' L st K l0 ∧
      CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 ∧
      ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
        HasCompactSupport F → (∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g) →
        ∃ Φ ∈ K 0, ∀ x ∈ DomR P.k P.r z z',
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2
end Formalism.FourierDecayAlt.P5


