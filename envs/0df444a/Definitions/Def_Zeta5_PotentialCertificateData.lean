-- Prove2me | Definitions.Def_Zeta5_PotentialCertificateData
-- name    : Zeta5_PotentialCertificateData
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-13T15:05:49.003986+00:00
-- url     : https://prove2.me/theorems/4c84ff6c-a7a5-4735-92b9-7c576c1a1644
-- title:
--   Rational logarithm and arctangent certificates
-- statement:
--   Finite rational sums encode upper and lower bounds for logarithms and arctangents. A certificate records a rational argument, a rational bound, a series order, and, for logarithms, a power-of-two scale. Its validity predicate checks the domain conditions and the corresponding exact rational truncation inequality.
--
--   This is the arithmetic interface for interpreting finite numerical certificates in the potential inequality of Lemma 6.1. It defines the checker; its analytic soundness is proved separately.
--
--   **Formalization Note** The module imports only Lean's Std library.
-- source:
--   Derived rational-certificate encoding of mo271/Zeta5 at commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Table2/All.lean, potential_ineq_le_two (lines 4116–4120), and the U*.lean/I*.lean certificate files; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Table2/All.lean#L4116-L4120. The certificate datatype and its generic soundness adapter are new formalization infrastructure.

import Std

/-!
Arithmetic-only certificates. This module imports no Mathlib modules and no
definitions of real numbers, logarithms, potentials, or measures.

The interpretation of these certificates is proved in PotentialCertificateSound.
-/

namespace Apery.PotentialCertificate

def sumRange (n : Nat) (f : Nat → Rat) : Rat :=
  match n with
  | 0 => 0
  | n + 1 => sumRange n f + f n

def logUpper (y : Rat) (k m : Nat) : Rat :=
  2 * sumRange m (fun j => (1 / (2 * (j : Rat) + 1)) *
    ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ (2 * j + 1)) +
  2 * ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ (2 * m + 1) /
    ((2 * m + 1) * (1 - ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ 2)) - k * 0.6931471803

def logLower (y : Rat) (k m : Nat) : Rat :=
  2 * sumRange m (fun j => (1 / (2 * (j : Rat) + 1)) *
    ((2 ^ k * y - 1) / (2 ^ k * y + 1)) ^ (2 * j + 1)) - k * 0.6931471808

def arctanPartial (x : Rat) (n : Nat) : Rat :=
  sumRange n (fun i => (-1 : Rat) ^ i * (x ^ (2 * i + 1) / (2 * (i : Rat) + 1)))

inductive Kind where
  | logUpper | logLower | arctanUpper | arctanLower

structure Certificate where
  kind : Kind
  argument : Rat
  bound : Rat
  scale : Nat
  order : Nat

def Certificate.Valid (c : Certificate) : Prop :=
  match c.kind with
  | .logUpper => 0 < c.argument ∧ 1 ≤ 2 ^ c.scale * c.argument ∧
      logUpper c.argument c.scale c.order ≤ c.bound
  | .logLower => 0 < c.argument ∧ 1 ≤ 2 ^ c.scale * c.argument ∧
      c.bound ≤ logLower c.argument c.scale c.order
  | .arctanUpper => 0 ≤ c.argument ∧ c.argument < 1 ∧
      arctanPartial c.argument (2 * c.order + 1) ≤ c.bound
  | .arctanLower => 0 ≤ c.argument ∧ c.argument < 1 ∧
      c.bound ≤ arctanPartial c.argument (2 * c.order)

instance (c : Certificate) : Decidable c.Valid := by
  unfold Certificate.Valid
  cases c.kind <;> infer_instance

def check (cs : List Certificate) : Bool := cs.all (fun c => decide c.Valid)

theorem valid_of_check {cs : List Certificate} (h : check cs = true)
    {c : Certificate} (hc : c ∈ cs) : c.Valid :=
  of_decide_eq_true ((List.all_eq_true.mp h) c hc)

theorem valid_get {cs : List Certificate} (h : check cs = true)
    (i : Nat) (hi : i < cs.length) : cs[i].Valid :=
  valid_of_check h (List.getElem_mem hi)

end Apery.PotentialCertificate


