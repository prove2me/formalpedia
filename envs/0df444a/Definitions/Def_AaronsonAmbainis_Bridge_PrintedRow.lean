-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
-- name    : AaronsonAmbainis_Bridge_PrintedRow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:06:19.422879+00:00
-- url     : https://prove2.me/theorems/00cbff50-a4a6-4b9f-8cae-f4bff4d3a01a
-- title:
--   Printed Row
-- statement:
--   Definitions and structural lemmas for Printed Row, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset MvPolynomial
def PrintedConcl {n : ℕ} (f : (Fin n → Bool) → ℝ) (d : ℕ) : Prop :=
  ∃ c : (Fin n → Bool) → Fin n → ℝ,
    (∀ x y, ∑ i ∈ univ.filter (fun i => x i ≠ y i), c x i ≥ |f x - f y|) ∧
    (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)
def FbsDegPrinted : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
      ∀ x, f x = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) →
    PrintedConcl f d
def FbsDegPrintedML : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ a : Finset (Fin n) → ℝ, (∀ S, d < S.card → a S = 0) ∧
      ∀ x, f x = ∑ S, a S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)) →
    PrintedConcl f d
end AaronsonAmbainis.Bridge


