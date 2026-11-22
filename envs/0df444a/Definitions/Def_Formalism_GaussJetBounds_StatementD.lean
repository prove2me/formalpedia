-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementD
-- name    : Formalism_GaussJetBounds_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:27.428208+00:00
-- url     : https://prove2.me/theorems/c4c92da8-5b13-452e-8bd6-cb6b94d851e7
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementD.lean

import Definitions.Def_Formalism_GaussJetBounds_Statement
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
universe u
namespace Formalism.DworkPowerSeriesWeights
def BasisChange : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (J m N : ℕ)
    (lam : Fin J → Fin N → K) (y : Fin m → Fin N → K),
    (∀ i a, ‖lam i a‖ ≤ 1) → (∀ k a, ‖y k a‖ ≤ 1) →
    ∀ e : Fin J → Fin m, Function.Injective e →
    ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1 →
    ∃ T : Matrix (Fin m) (Fin m) K, (∀ k k', ‖T k k'‖ ≤ 1) ∧ ‖T.det‖ = 1 ∧
      ∀ i k, (∑ a, lam i a * ∑ k', T k k' * y k' a) = if k = e i then 1 else 0
def DegProd : Prop :=
  ∀ (R : Type u) [CommRing R] (σ κ : Type) [DecidableEq κ] (blk : σ → Option κ) (n : ℕ)
    (f : Fin n → MvPolynomial σ R) (bd : Fin n → ℕ),
    (∀ c, ∀ mono ∈ (f c).support, ∀ k : κ,
      (mono.support.filter (fun v => blk v = some k)).sum mono ≤ bd c) →
    ∀ mono ∈ (∏ c, f c).support, ∀ k : κ,
      (mono.support.filter (fun v => blk v = some k)).sum mono ≤ ∑ c, bd c
def MinorDegAll : Prop :=
  ∀ (R : Type u) [CommRing R] (m p : ℕ) (T : Fin p → Fin m → R),
    ∀ mono ∈ (Matrix.of fun (i c : Fin p) =>
        (∑ k, MvPolynomial.C (T i k) * MvPolynomial.X (k, c) : MvPolynomial (Fin m × Fin p) R)).det.support,
      ∀ k : Fin m, (∑ c : Fin p, mono (k, c)) ≤ 1
def JCount : Prop :=
  ∀ l a : ℕ, 2 ≤ l → 1 ≤ a →
    (((Finset.Icc (-(a : ℤ)) a).filter (fun j => Odd j ∧ l ^ j.natAbs ≤ a)).card : ℝ) ≤
      2 * Real.logb l a + 1
end Formalism.DworkPowerSeriesWeights


