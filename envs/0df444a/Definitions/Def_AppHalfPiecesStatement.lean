-- Prove2me | Definitions.Def_AppHalfPiecesStatement
-- name    : AppHalfPiecesStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:25:53.478852+00:00
-- url     : https://prove2.me/theorems/7cf8a866-b2fc-479a-bd87-4e0f8d019972
-- title:
--   App Half Pieces Statement
-- statement:
--   Definitions and structural lemmas for App Half Pieces Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/AppHalfPiecesStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.LinearAlgebra.Dimension.Finrank
import Definitions.Def_PiecesStatement
import Definitions.Def_PartitionStatement
set_option autoImplicit false
section
section
namespace AppHalfPieces
open Finset MvPolynomial
def binom (k j : ℤ) : ℤ := if 0 ≤ j then Ring.choose k j.toNat else 0
structure BinomRules : Prop where
  pascal : ∀ k j : ℤ, binom (k + 1) (j + 1) = binom k j + binom k (j + 1)
  vandermonde : ∀ (k k' : ℤ) (i : ℕ), ∑ j ∈ range (i + 1), binom k (i - j) * binom k' j = binom (k + k') i
abbrev Ptn : Type := Multiset ℕ+
def wt (μ : Ptn) : ℕ := (μ.map fun k : ℕ+ => (k : ℕ)).sum
def zz (μ : Ptn) : ℕ := ∏ k ∈ μ.toFinset, (k : ℕ) ^ μ.count k * (μ.count k).factorial
def ptns (E : ℕ) : Finset Ptn := (univ : Finset (Nat.Partition E)).image fun q => q.parts.map Nat.toPNat'
def ptnsZ (E : ℤ) : Finset Ptn := if 0 ≤ E then ptns E.toNat else ∅
def pZ (E : ℤ) : ℕ := if 0 ≤ E then Partitions.p E.toNat else 0
structure PtnFacts : Prop where
  mem : ∀ (E : ℕ) (μ : Ptn), μ ∈ ptns E ↔ wt μ = E
  card : ∀ E : ℕ, #(ptns E) = Partitions.p E
  mono : ∀ E : ℕ, Partitions.p E ≤ Partitions.p (E + 1)
abbrev V : Type := MvPolynomial ℕ+ ℚ
noncomputable def tpow (μ : Ptn) : V := monomial (Multiset.toFinsupp μ) 1
noncomputable def coef (μ : Ptn) (f : V) : ℚ := coeff (Multiset.toFinsupp μ) f
noncomputable def VE (E : ℤ) : Submodule ℚ V :=
  if 0 ≤ E then weightedHomogeneousSubmodule ℚ (fun k : ℕ+ => (k : ℕ)) E.toNat else ⊥
def pn (k : ℤ) : ℕ+ := k.natAbs.toPNat'
noncomputable def nabla (k : ℤ) (f : V) : V :=
  if k < 0 then X (pn k) * f else if 0 < k then (k : ℚ) • pderiv (pn k) f else 0
def Choices (μ : List ℕ+) (r : ℤ) : Set (List ℤ) := {ks | ks.length = μ.length ∧ (∀ k ∈ ks, k ≠ 0) ∧ ks.sum = -r}
noncomputable def term (μ : List ℕ+) (ks : List ℤ) (f : V) : V :=
  (((List.zipWith (fun (m : ℕ+) (k : ℤ) => binom (-k - 1) ((m : ℤ) - 1)) μ ks).prod : ℤ) : ℚ) •
    (ks.filter (· < 0)).foldr nabla ((ks.filter (0 < ·)).foldr nabla f)
noncomputable def opMon (μ : List ℕ+) (r : ℤ) (f : V) : V := ∑ᶠ ks ∈ Choices μ r, term μ ks f
noncomputable def op (a : V) (r : ℤ) (f : V) : V := ∑ m ∈ a.support, coeff m a • opMon (Finsupp.toMultiset m).toList r f
structure OpFacts : Prop where
  finite : ∀ (μ : List ℕ+) (r : ℤ) (f : V), {ks ∈ Choices μ r | term μ ks f ≠ 0}.Finite
  perm : ∀ (μ μ' : List ℕ+) (r : ℤ) (f : V), μ.Perm μ' → opMon μ r f = opMon μ' r f
  mono : ∀ (μ : List ℕ+) (r : ℤ) (f : V), op (tpow (μ : Multiset ℕ+)) r f = opMon μ r f
  add_right : ∀ (a : V) (r : ℤ) (f f' : V), op a r (f + f') = op a r f + op a r f'
  smul_right : ∀ (a : V) (r : ℤ) (q : ℚ) (f : V), op a r (q • f) = q • op a r f
  add_left : ∀ (a a' : V) (r : ℤ) (f : V), op (a + a') r f = op a r f + op a' r f
  smul_left : ∀ (a : V) (r : ℤ) (q : ℚ) (f : V), op (q • a) r f = q • op a r f
def IsInt (f : V) : Prop := ∀ m, ∃ z : ℤ, coeff m f = z
structure O1 : Prop where
  maps : ∀ (a : V) (r E : ℤ) (f : V), f ∈ VE E → op a r f ∈ VE (E + r)
  zero : ∀ (a : V) (r E : ℤ) (f : V), f ∈ VE E → E + r < 0 → op a r f = 0
  int : ∀ (a : V) (r : ℤ) (f : V), IsInt a → IsInt f → IsInt (op a r f)
  one : ∀ (r : ℤ) (f : V), op 1 r f = if r = 0 then f else 0
noncomputable def pairing (h : ℕ) (a b : V) : ℚ := coeff 0 (op a (-(h : ℤ)) b)
structure O3 : Prop where
  number : ∀ (h : ℕ) (a b : V), b ∈ VE h → op a (-(h : ℤ)) b = C (pairing h a b)
  positive : ∀ (h : ℕ) (μ : List ℕ+) (b : V) (ks : List ℤ), b ∈ VE h → ks ∈ Choices μ (-(h : ℤ)) → (∃ k ∈ ks, k < 0) → term μ ks b = 0
noncomputable def part (h' : ℕ) (a : V) : V := weightedHomogeneousComponent (fun k : ℕ+ => (k : ℕ)) h' a
def WtLe (h : ℕ) (a : V) : Prop := a = ∑ h' ∈ range (h + 1), part h' a
noncomputable def angle (h i : ℕ) (a : V) : V := ∑ h' ∈ range (h + 1), ((h' + h).choose i : ℚ) • part h' a
noncomputable def Q (h : ℕ) (s : ℤ) (a b f : V) : V :=
  ∑ i ∈ range (2 * h + 1), (-1 : ℚ) ^ i • op (angle h i a) (s - h + i) (op b (h - s - i) f)
noncomputable def Q' (h : ℕ) (s : ℤ) (a b f : V) : V :=
  ∑ i ∈ range (2 * h + 1), (-1 : ℚ) ^ i • op b (h - s - i) (op (angle h i a) (s - h + i) f)
structure LemmaQ : Prop where
  a : ∀ (h : ℕ) (a b : V), 1 ≤ h → b ∈ VE h → WtLe h a → ∀ (E : ℕ) (f : V), f ∈ VE E → ∀ s : ℤ, Q h s a b f = Q' h s a b f
  b : ∀ (h : ℕ) (a b : V), 1 ≤ h → b ∈ VE h → WtLe h a → ∀ (E : ℕ) (f : V), f ∈ VE E → ∀ s : ℤ, (E : ℤ) + h < |s| → Q h s a b f = 0
  c : ∀ (h : ℕ) (a b : V), 1 ≤ h → b ∈ VE h → WtLe h a → ∀ (E : ℕ) (f : V), f ∈ VE E →
    ∑ s ∈ Icc (-((E : ℤ) + h)) ((E : ℤ) + h), Q h s a b f = pairing h a b • f
noncomputable def y (n : ℕ+) : V := ∑ j ∈ Icc 1 (n : ℕ), ((n : ℕ).choose j : ℚ) • X j.toPNat'
noncomputable def aFam (μ : Ptn) : V := (μ.map fun n : ℕ+ => (-1 : ℚ) ^ ((n : ℕ) - 1) • y n).prod
noncomputable def bFam (μ : Ptn) : V := (((wt μ).factorial : ℚ) / zz μ) • tpow μ
def LemmaDual : Prop := ∀ (h : ℕ) (μ ν : Ptn), wt μ = h → wt ν = h → op (aFam μ) (-(h : ℤ)) (bFam ν) = C (if μ = ν then (h.factorial : ℚ) else 0)
def ZDvd : Prop := ∀ μ : Ptn, zz μ ∣ (wt μ).factorial
noncomputable def hOf (lam : ℕ) : ℕ := sInf {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h}
def HOfSpec : Prop := ∀ lam : ℕ, 2 ≤ hOf lam ∧ 2 ^ lam ≤ Partitions.p (hOf lam) ∧ ∀ h, 2 ≤ h → 2 ^ lam ≤ Partitions.p h → hOf lam ≤ h
def desc (μ : Ptn) : List ℕ := (μ.map fun k : ℕ+ => (k : ℕ)).sort (· ≥ ·)
def lexNum (h : ℕ) (μ : Ptn) : ℕ := #{ν ∈ ptns h | desc ν < desc μ}
def val {lam : ℕ} (x : Pieces.Bits lam) : ℕ := ∑ i : Fin lam, if x i then 2 ^ (i : ℕ) else 0
def IsMu (lam h : ℕ) (mu : Pieces.Bits lam → Ptn) : Prop := ∀ x, mu x ∈ ptns h ∧ lexNum h (mu x) = val x
noncomputable def piece {lam : ℕ} (h : ℕ) (mu : Pieces.Bits lam → Ptn) (s : ℤ) (x y u v : Pieces.Bits lam) : ℚ :=
  coef (mu u) (Q h s (aFam (mu x)) (bFam (mu v)) (tpow (mu y)))
def Rrow (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pZ (s + i)
def Rcol (h : ℕ) (s : ℤ) : ℕ := ∑ i ∈ range (2 * h + 1), pZ (2 * h - s - i)
structure PieceFacts : Prop where
  /-- a^μ is a combination of monomials of weight at most h, as (48) requires. -/
  wtLe : ∀ (h : ℕ) (μ : Ptn), wt μ = h → WtLe h (aFam μ)
  /-- Σ_s A_s = h!·[x = v]·[y = u]. -/
  sum : ∀ (h : ℕ) (ξ η υ ν : Ptn), 1 ≤ h → wt ξ = h → wt η = h → wt υ = h → wt ν = h →
    ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), coef υ (Q h s (aFam ξ) (bFam ν) (tpow η)) = if ξ = ν ∧ η = υ then (h.factorial : ℚ) else 0
  /-- Display (54). -/
  row : ∀ (h : ℕ) (ξ η υ ν : Ptn) (s : ℤ), 1 ≤ h → wt ξ = h → wt η = h → wt υ = h → wt ν = h →
    coef υ (Q h s (aFam ξ) (bFam ν) (tpow η)) = ∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (s + i),
      (-1 : ℚ) ^ i * coef σ (op (angle h i (aFam ξ)) (s - h + i) (tpow η)) * coef υ (op (bFam ν) (h - s - i) (tpow σ))
  /-- Display (55). -/
  col : ∀ (h : ℕ) (ξ η υ ν : Ptn) (s : ℤ), 1 ≤ h → wt ξ = h → wt η = h → wt υ = h → wt ν = h →
    coef υ (Q h s (aFam ξ) (bFam ν) (tpow η)) = ∑ i ∈ range (2 * h + 1), ∑ σ ∈ ptnsZ (2 * h - s - i),
      (-1 : ℚ) ^ i * coef υ (op (angle h i (aFam ξ)) (s - h + i) (tpow σ)) * coef σ (op (bFam ν) (h - s - i) (tpow η))
  /-- All factors are integers. -/
  int_a : ∀ (h i : ℕ) (ξ σ : Ptn) (r : ℤ), IsInt (op (angle h i (aFam ξ)) r (tpow σ))
  int_b : ∀ (ν σ : Ptn) (r : ℤ), IsInt (op (bFam ν) r (tpow σ))
  /-- The numbers of terms are both at least 1. -/
  terms : ∀ (h : ℕ) (s : ℤ), |s| ≤ 2 * h → 1 ≤ Rrow h s ∧ 1 ≤ Rcol h s
def ThmHalfPiecesPure : Prop := ∃ c : ℕ, ∀ lam : ℕ, 1 ≤ lam → ∃ (mu : Pieces.Bits lam → Ptn) (P : Pieces.Family lam),
  IsMu lam (hOf lam) mu ∧ P.Is (1 / Real.sqrt 2) c ∧ P.d = (hOf lam).factorial ∧ P.I = Icc (-(2 * hOf lam : ℤ)) (2 * hOf lam) ∧
    (∀ s x y u v, (P.A s x y u v : ℚ) = piece (hOf lam) mu s x y u v) ∧
    (∀ s, P.crow s = Nat.clog 2 (Rrow (hOf lam) s)) ∧ ∀ s, P.ccol s = Nat.clog 2 (Rcol (hOf lam) s)
end AppHalfPieces


