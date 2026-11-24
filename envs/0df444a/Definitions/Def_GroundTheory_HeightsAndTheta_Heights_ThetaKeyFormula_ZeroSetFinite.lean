-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:06.158856+00:00
-- url     : https://prove2.me/theorems/6736e909-420b-4f71-b3dd-fa8452dbd693
-- title:
--   Zero Set Finite
-- statement:
--   Definitions and structural lemmas for Zero Set Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ZeroSetFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix
noncomputable section
def cechSign {r : ℕ} (J : Finset (Fin (r + 1))) (j : Fin (r + 1)) : ℂ :=
  (-1) ^ (J.filter (· < j)).card
def cechD {X : Type*} {r : ℕ} (φ : Finset (Fin (r + 1)) → X → ℂ) (J : Finset (Fin (r + 1))) :
    X → ℂ :=
  fun z => ∑ j ∈ J, cechSign J j * φ (J.erase j) z
namespace RigSymForm
variable {K : Type} [Field K] [Algebra K ℂ] (P : RigSymForm K)
abbrev Fn : Type := (Fin P.g → ℂ) → ℂ
def IsBasisOf (a : ℕ) {r : ℕ} (x : Fin (r + 1) → P.Fn) : Prop :=
  (∀ i, x i ∈ P.S a) ∧ LinearIndependent K x ∧ Submodule.span K (Set.range x) = P.S a
def chartSet {r : ℕ} (x : Fin (r + 1) → P.Fn) (J : Finset (Fin (r + 1))) : Set (Fin P.g → ℂ) :=
  {z | ∀ i ∈ J, x i z ≠ 0}
def IsChartSec (a n : ℕ) {r : ℕ} (x : Fin (r + 1) → P.Fn) (J : Finset (Fin (r + 1)))
    (φ : P.Fn) : Prop :=
  ∃ k : ℕ, ∃ f ∈ P.S (n + a * J.card * k), ∀ z ∈ P.chartSet x J,
    φ z = f z / (∏ i ∈ J, x i z) ^ k
def IsCochain (a n q : ℕ) {r : ℕ} (x : Fin (r + 1) → P.Fn)
    (φ : Finset (Fin (r + 1)) → P.Fn) : Prop :=
  ∀ J : Finset (Fin (r + 1)), J.card = q + 1 → P.IsChartSec a n x J (φ J)
def IsCocycle (a n q : ℕ) {r : ℕ} (x : Fin (r + 1) → P.Fn)
    (φ : Finset (Fin (r + 1)) → P.Fn) : Prop :=
  P.IsCochain a n q x φ ∧
    ∀ J : Finset (Fin (r + 1)), J.card = q + 2 → ∀ z ∈ P.chartSet x J, cechD φ J z = 0
def IsCoboundary (a n q : ℕ) {r : ℕ} (x : Fin (r + 1) → P.Fn)
    (φ : Finset (Fin (r + 1)) → P.Fn) : Prop :=
  ∃ ψ : Finset (Fin (r + 1)) → P.Fn, P.IsCochain a n q x ψ ∧
    ∀ J : Finset (Fin (r + 1)), J.card = q + 2 → ∀ z ∈ P.chartSet x J, cechD ψ J z = φ J z
def formSec {r : ℕ} (x : Fin (r + 1) → P.Fn) (F : MvPolynomial (Fin (r + 1)) K) : P.Fn :=
  fun z => MvPolynomial.eval₂ (algebraMap K ℂ) (fun j => x j z) F
def ZeroSetFinite (s : Fin P.g → P.Fn) : Prop :=
  ∃ W : Finset (Fin P.g → ℂ), ∀ z : Fin P.g → ℂ, (∀ i, s i z = 0) →
    ∃ w ∈ W, ∃ u v : Fin P.g → ℤ, z = w + P.pt.τ *ᵥ intVec u + intVec v
def relSub (n : ℕ) (s : Fin P.g → P.Fn) (i l : ℕ) : Submodule K P.Fn :=
  Submodule.span K {h | ∃ j : Fin P.g, (j : ℕ) < i ∧ ∃ k, k + n = l ∧ ∃ f ∈ P.S k, h = s j * f}
end RigSymForm
open RigSymForm
def VanishingCech.Statement : Prop :=
  ∀ (K : Type) [Field K] [Algebra K ℂ] (P : RigSymForm K) (a : ℕ), 3 ≤ a →
    ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ n : ℕ, 1 ≤ n → ∀ (q : ℕ) (φ : Finset (Fin (r + 1)) → P.Fn),
      P.IsCocycle a n (q + 1) x φ → P.IsCoboundary a n q x φ
def ExactField.Statement : Prop :=
  ∀ (K : Type) [Field K] [Algebra K ℂ] (P : RigSymForm K) (a n₀ : ℕ), 3 ≤ a → 1 ≤ n₀ →
    ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ F : Fin P.g → MvPolynomial (Fin (r + 1)) K, (∀ i, (F i).IsHomogeneous n₀) →
    P.ZeroSetFinite (fun i => P.formSec x (F i)) →
    ∀ (i : Fin P.g) (l m : ℕ), m + a * n₀ = l → ((i : ℕ) + 1) * (a * n₀) < l →
      ∀ f ∈ P.S m,
        P.formSec x (F i) * f ∈ P.relSub (a * n₀) (fun j => P.formSec x (F j)) i l →
        f ∈ P.relSub (a * n₀) (fun j => P.formSec x (F j)) i m
end
end GroundTheory.Heights₂.Heights.KeyFormula


