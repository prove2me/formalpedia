-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_IsPairFrame
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussianEigenFrames_IsPairFrame
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T07:01:48.989855+00:00
-- url     : https://prove2.me/theorems/f568efff-c671-502a-bf36-dd6f03176903
-- title:
--   Is Pair Frame
-- statement:
--   Definitions and structural lemmas for Is Pair Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussianEigenFrames/IsPairFrame.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_UniformGaussModelConditionEquivalent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_GoodModelAll
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.GD
open Formalism.L2.Th1.H (matH opU taylorMv)
def InMul (L : PeriodPair) {n : Type} (Λ : AddSubgroup (n → ℂ)) (v : n → ℂ) : Prop :=
  ∀ ω ∈ L.lattice, ω • v ∈ Λ
def hOK (L : PeriodPair) {n : Type} [Fintype n] (h : Matrix n n ℂ) (v v' : n → ℂ) : ℂ :=
  ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) * matH h v v'
def frameM {K : Type} [Field K] (ι : ℂ →+* K) {n J X : Type} [Fintype J] (v : J → n → ℂ) (A : J → X → K) :
    n → X → K :=
  fun i x => ∑ j, ι (v j i) * A j x
def thetaLin {K : Type} [Field K] (ι : ℂ →+* K) {n X κ : Type} [Fintype n] [DecidableEq n] [Fintype X] [Fintype κ]
    (h : Matrix n n ℂ) (θ : (n → ℂ) → ℂ) (r : κ → K) (t : κ → n → ℂ) (M : n → X → K) : MvPowerSeries X K :=
  ∑ k, MvPowerSeries.C (r k) *
    Formalism.L2.Th1.G.linSub M (MvPowerSeries.map ι (taylorMv (opU (matH h) (t k) θ)))
def IsPairFrame {K : Type} [NormedField K] (ι : ℂ →+* K) (L : PeriodPair) {n J H : Type} [Fintype n] [Fintype J]
    [DecidableEq H] {N0 N1 : ℕ} (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (v : J → n → ℂ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → K) (u : H → K) (th : K)
    (q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → K) : Prop :=
  (∀ j, InMul L Λ (v j)) ∧ (∀ j x, ‖A j x‖ ≤ 1) ∧ (∀ x y, ‖q x y‖ ≤ 1) ∧
  ∀ x y, ∑ j, ∑ k, A j x * ι (hOK L h (v j) (v k)) * A k y =
    (if x.1.2 = y.1.2 ∧ x.2 = y.2 ∧ x.1.1 ≠ y.1.1 then u x.1.2 else 0) + th * q x y
end Formalism.L2.Th1.GD


