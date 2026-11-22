-- Prove2me | Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
-- name    : Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:52:36.081909+00:00
-- url     : https://prove2.me/theorems/9b896742-291e-41ae-ae46-343636da1197
-- title:
--   Chain Rule
-- statement:
--   Definitions and structural lemmas for Chain Rule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace Formalism.G.LogCR
variable {R : Type*} [CommRing R] {σ τ : Type*}
def Agree (N : ℕ) (f g : MvPowerSeries σ R) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = coeff d g
theorem Agree.pderiv {N : ℕ} {f g : MvPowerSeries σ R} (h : Agree (N + 1) f g) (i : σ) :
    Agree N (MvPowerSeries.pderiv R i f) (MvPowerSeries.pderiv R i g) := by
  classical
  intro d hd
  rw [coeff_pderiv, coeff_pderiv, h (d + Finsupp.single i 1) ?_]
  rw [map_add, Finsupp.degree_single]
  omega
theorem agree_iff [Finite σ] {N : ℕ} {f g : MvPowerSeries σ R} :
    Agree N f g ↔ truncTotal N f = truncTotal N g := by
  constructor
  · intro h
    ext d
    rw [coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
    split_ifs with hd
    · exact h d hd
    · rfl
  · intro h d hd
    have := congrArg (MvPolynomial.coeff d) h
    rwa [coeff_truncTotal _ hd, coeff_truncTotal _ hd] at this
theorem Agree.subst [Finite σ] [Finite τ] {N : ℕ} {f f' : MvPowerSeries σ R}
    {a a' : σ → MvPowerSeries τ R} (ha : ∀ j, constantCoeff (a j) = 0)
    (ha' : ∀ j, constantCoeff (a' j) = 0) (hf : Agree N f f') (haa : ∀ j, Agree N (a j) (a' j)) :
    Agree N (f.subst a) (f'.subst a') := by
  rw [agree_iff, truncTotal_subst ha, truncTotal_subst ha', agree_iff.mp hf]
  have : (fun i => ((a i).truncTotal N : MvPowerSeries τ R)) =
      fun i => ((a' i).truncTotal N : MvPowerSeries τ R) := by
    funext i; rw [agree_iff.mp (haa i)]
  rw [this]
end Formalism.G.LogCR


