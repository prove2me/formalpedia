-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:32.871374+00:00
-- url     : https://prove2.me/theorems/d1f1c6db-68f8-4750-8ee2-c8d15bc4c676
-- title:
--   Linear Independent Of Lead
-- statement:
--   Definitions and structural lemmas for Linear Independent Of Lead, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LinearIndependentOfLead.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
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
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace leadingTermLemmas
section Lex
variable {σ τ : Type*} [LinearOrder τ] (κ : σ → τ)
def LL (e e' : σ →₀ ℕ) : Prop := ∃ x, e x < e' x ∧ ∀ y, κ y < κ x → e y = e' y
variable {κ}
variable {R : Type*} [CommRing R] (κ)
def Lead (f : MvPolynomial σ R) (d : σ →₀ ℕ) : Prop :=
  coeff d f = 1 ∧ ∀ e ∈ f.support, e ≠ d → LL κ e d
variable {κ}
end Lex
section Det
variable {n : ℕ}
def key (x : Fin n × Fin n) : Fin n ×ₗ Fin n := toLex x
def mon {m : ℕ} (r c : Fin m → Fin n) (π : Equiv.Perm (Fin m)) : Fin n × Fin n →₀ ℕ :=
  ∑ i, Finsupp.single (r i, c (π i)) 1
def colDiag (J : Finset (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ b ∈ J, ∑ a : Fin n, if a.val = (J.filter (· < b)).card then Finsupp.single (a, b) 1 else 0
end Det
section Inj
variable {n C : ℕ}
end Inj
end leadingTermLemmas
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


