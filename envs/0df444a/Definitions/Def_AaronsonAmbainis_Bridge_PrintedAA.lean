-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
-- name    : AaronsonAmbainis_Bridge_PrintedAA
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:11:17.459564+00:00
-- url     : https://prove2.me/theorems/9bf3ff24-8854-4ef8-8d7e-7ff3583cd95a
-- title:
--   Printed AA
-- statement:
--   Definitions and structural lemmas for Printed AA, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset MvPolynomial
noncomputable def Ex {N : ℕ} (F : (Fin N → Bool) → ℝ) : ℝ := (∑ X, F X) / 2 ^ N
def flipBit {N : ℕ} (X : Fin N → Bool) (i : Fin N) : Fin N → Bool := Function.update X i (!X i)
noncomputable def ev01 {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
noncomputable def evPM {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (-1 : ℝ) else 1) p
def MainBound (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ C * (d : ℝ) ^ 12 * inflR f j ^ 2
noncomputable def evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p
def negBits {N : ℕ} (X : Fin N → Bool) : Fin N → Bool := fun i => !X i
theorem negBits_negBits {N : ℕ} (X : Fin N → Bool) : negBits (negBits X) = X := by
  funext i
  simp [negBits]
def negBitsEquiv (N : ℕ) : (Fin N → Bool) ≃ (Fin N → Bool) :=
  ⟨negBits, negBits, negBits_negBits, negBits_negBits⟩
end AaronsonAmbainis.Bridge


