-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:54.047356+00:00
-- url     : https://prove2.me/theorems/fd5d9160-c5ae-44c1-9ed2-5f8171778f67
-- title:
--   Permutation Word Gelfand Polynomial Mod Shorter
-- statement:
--   Definitions and structural lemmas for Permutation Word Gelfand Polynomial Mod Shorter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PermutationWordGelfandPolynomialModShorter.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
namespace GlobalTheory.SmoothForms.PermWord
section Comm
variable {S : Type} [CommRing S] {n : ℕ}
end Comm
section NC
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
def wd {B : Type} [Ring B] (E : Fin n → Fin n → B) (l : List (Fin n × Fin n)) : B := (l.map fun z => E z.1 z.2).prod
def shorter (E : Fin n → Fin n → A) (d : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ l : List (Fin n × Fin n), l.length < d ∧ wd E l = x}
def gen (n : ℕ) (a b : Fin n) : MvPolynomial (Fin n × Fin n) ℂ := MvPolynomial.X (a, b)
def order (E : Fin n → Fin n → A) : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] A :=
  (MvPolynomial.basisMonomials (Fin n × Fin n) ℂ).constr ℂ fun s => wd E (Finsupp.toMultiset s).toList
def symb (E : Fin n → Fin n → A) (d : ℕ) : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ × A) :=
  Submodule.span ℂ {x | ∃ l : List (Fin n × Fin n), l.length = d ∧ (wd (gen n) l, wd E l) = x}
end NC
end GlobalTheory.SmoothForms.PermWord
end


