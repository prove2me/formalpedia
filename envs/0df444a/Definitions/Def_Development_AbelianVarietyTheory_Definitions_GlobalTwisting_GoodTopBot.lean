-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_GoodTopBot
-- name    : Development_AbelianVarietyTheory_Definitions_GlobalTwisting_GoodTopBot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:58.605797+00:00
-- url     : https://prove2.me/theorems/88096264-b2c1-420b-bc10-59f4394d0a40
-- title:
--   Good Top Bot
-- statement:
--   Definitions and structural lemmas for Good Top Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/GoodTopBot.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace GlobalTheory.Alc
open Formalism.GradedWeylDivisibility
def GlRel {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)
def shift (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : R := μ i + ((N - 1 - i.val : ℕ) : R)
def hcMat (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i l => if l = i then shift R μ i else if i < l then -1 else 0
def hcVal (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) : R := ∑ i, ∑ l, (hcMat R μ ^ k) i l
def rowE (R : Type) [CommRing R] (r n : ℕ) : Matrix (Fin r) (Fin r) (Module.End R (MvPolynomial (Fin r × Fin n) R)) :=
  Matrix.of fun a b => ∑ s : Fin n, (LinearMap.mulLeft R (X (a, s))).comp (pderiv (b, s)).toLinearMap
def gel (R : Type) [CommRing R] (r n k : ℕ) : Module.End R (MvPolynomial (Fin r × Fin n) R) := (rowE R r n ^ k).trace
def Good {R : Type} [CommRing R] {r n : ℕ} (M : Submodule R (MvPolynomial (Fin r × Fin n) R)) : Prop :=
  (∀ a b, ∀ f ∈ M, rowE R r n a b f ∈ M) ∧
  (∀ μ : Fin r → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW r n) μ f ∈ M) ∧
  ∀ σ : Equiv.Perm (Fin r), ∀ f ∈ M, rename (fun v : Fin r × Fin n => (σ v.1, v.2)) f ∈ M
end GlobalTheory.Alc


