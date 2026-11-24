-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementJCCpt
-- name    : Formalism_HermitianCurvature_StatementJCCpt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:48:47.268685+00:00
-- url     : https://prove2.me/theorems/7e2b856b-ac9b-4e4a-b283-e618ddaec7aa
-- title:
--   Statement JCCpt
-- statement:
--   Definitions and structural lemmas for Statement JCCpt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementJCCpt.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HerGenC
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
namespace Formalism.FourierDecayAlt.JC
open Formalism.FourierDecayAlt
section densityCpt
open scoped ComplexOrder
def PosDensityCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ) (ε : ℝ),
    0 < ε → P5.Auser P0 w.length + 1 ≤ A → P5.mmUser P0 w.length ≤ mm →
    (∀ ε' : ℝ, 0 < ε' → ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, NiceCoef (T.bs j) ε' (x a) ∧ HasCompactSupport (x a)) → 0 ≤ D.formLev T s j w x x) →
    ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, CCCoefM (T.bs j) A mm ε (x a)) → 0 ≤ D.formLev T s j w x x
def ThmPModuleOfActualCpt : Prop :=
  P5.ThmPActualCpt → RadialModuleForm → PosDensityCpt → FormLevSesqMM →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (l0 N : ℕ) (admitted : List C.Letter → Prop) (A : ℝ) (mm : ℕ),
    1 ≤ l0 → l0 ≤ P0.k → (∀ w, admitted w → w.length ≤ N) → P5.Auser P0 N + 1 ≤ A → P5.mmUser P0 N ≤ mm →
    (∀ j : Fin (P0.r + 1),
      ∃ (X : Q.ActualOps (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
        (μ : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt (parLev P0 j).k (parLev P0 j).r))
        (L : R.LevelData (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π')) (parLev P0 j).r)
        (st : Fr.Start (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π'))),
        P5.IsData (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 ∧
        ∀ w, admitted w → P5.WordOK (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' st l0 (D.positionted w)) →
    ∃ KK : ∀ j : Fin (P0.r + 1), Submodule ℂ (B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
      D.ThmPModule T (M.sgn P0 l0) admitted KK ∧
      ∀ (j : Fin (P0.r + 1)) (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → B.InCC A mm F →
        B.CkOn (mm : ℕ∞) (B.GV P0.k (P0.r - j)) F →
        (∀ g ∈ B.GV P0.k (P0.r - j), F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' g) →
        F ∈ KK j
end densityCpt
end Formalism.FourierDecayAlt.JC


