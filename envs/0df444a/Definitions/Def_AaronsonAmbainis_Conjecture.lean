-- Prove2me | Definitions.Def_AaronsonAmbainis_Conjecture
-- name    : AaronsonAmbainis_Conjecture
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:12:01.587418+00:00
-- url     : https://prove2.me/theorems/ac87666c-d25c-4bfb-b651-f1f309f03f57
-- title:
--   Conjecture
-- statement:
--   Definitions and structural lemmas for Conjecture, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Conjecture.lean

import Mathlib
set_option autoImplicit true
namespace AaronsonAmbainis
def PrintedConjecture : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ (ε / (d : ℝ)) ^ 7
def ExplicitBound : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6
def FbsDegreeBound : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
      ∀ x, f x = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) →
    ∃ c : (Fin n → Bool) → Fin n → ℝ,
      (∀ x y, ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), c x i ≥ |f x - f y|) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)
def ExplicitBoundImproved : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ 32 * Real.sqrt 15 / (125 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6
def ExplicitBoundPM : Prop :=
  ∀ (n d : ℕ) (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin n → Bool, |MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p| ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin n → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p
            - (∑ Y : Fin n → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1) p)
                / 2 ^ n) ^ 2) / 2 ^ n ≥ ε →
      ∃ i : Fin n,
        (∑ X : Fin n → Bool,
          ((MvPolynomial.eval (fun k => if X k then (1 : ℝ) else -1) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else -1) p) / 2) ^ 2)
            / 2 ^ n
          ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6
end AaronsonAmbainis


