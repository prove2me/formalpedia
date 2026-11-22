-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:46.117831+00:00
-- url     : https://prove2.me/theorems/db85f4a2-2e84-4618-826b-4b92dd73ccd6
-- title:
--   Det Rows Zero
-- statement:
--   Definitions and structural lemmas for Det Rows Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
def rel (E : Fin n → Fin n → A) (a b c d : Fin n) : A :=
  E a b * E c d - E c d * E a b - ((if b = c then E a d else 0) - (if d = a then E c b else 0))
def fac (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin t)) : Fin t → A :=
  fun k => Tm E (u - (k : ℂ)) (a (σ k)) (b k)
def Lt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).take (i : ℕ)).prod
def Rt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).drop ((i : ℕ) + 2)).prod
def Md (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) : A :=
  rel E (a (σ i.castSucc)) (b i.castSucc) (a (σ i.succ)) (b i.succ) +
    rel E (a (σ i.castSucc)) (b i.succ) (a (σ i.succ)) (b i.castSucc)
def Ead (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : A :=
  ∑ a, ∑ b, (P a c * Q d b) • E a b
end Formalism.FourierDecayAlt.P.JFxE


