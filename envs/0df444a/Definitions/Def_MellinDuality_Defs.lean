-- Prove2me | Definitions.Def_MellinDuality_Defs
-- name    : MellinDuality_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:42:47.31784+00:00
-- url     : https://prove2.me/theorems/7f75822f-83be-432d-8ccf-70ae32f31501
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/MellinDuality; see pinned Apache-2.0 LICENSE and README.md)'s pinned MellinDuality: Mellin duality for the band-parity companion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Defs.lean

module
public import Mathlib
public import Definitions.Def_MellinDuality_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MellinDuality
open Finset
variable {p : ℕ} [Fact p.Prime]
def parSign (x : ZMod p) : ℤ := (-1) ^ x.val
def half (p : ℕ) [Fact p.Prime] : Finset (ZMod p) := univ.filter fun n => 2 * n.val < p
variable {R : Type*} [CommRing R]
def fam (χ : MulChar (ZMod p) R) (e : ℕ) (a : ZMod p) : R :=
  ∑ n ∈ half p, χ n * (((-1 : ℤ) ^ (n.val + (a * n ^ e).val) : ℤ) : R)
def G (ψ : MulChar (ZMod p) R) : R := ∑ x : ZMod p, ψ x * (parSign x : R)
def T (ψ : MulChar (ZMod p) R) : R := ∑ x : ZMod p, ψ x * (x.val : R)
noncomputable def bern (ψ : MulChar (ZMod p) ℂ) : ℂ := T ψ / p
def bandSignE (e : ℕ) (x : ZMod p) : ℤ := (-1) ^ (x.val ^ e / p)
def bandSumPow (χ : MulChar (ZMod p) R) (e : ℕ) : R :=
  ∑ n ∈ half p, χ n * (bandSignE e n : R)
noncomputable def oddChars (p : ℕ) [Fact p.Prime] : Finset (DirichletCharacter ℂ p) :=
  univ.filter fun ψ => ψ (-1) = -1
def fiber (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : Finset (ZMod p) :=
  univ.filter fun x => χ x = z
def sigma (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ :=
  ∑ x ∈ fiber χ z, parSign x
def gamma (χ : MulChar (ZMod p) GaussianInt) : GaussianInt := ⟨sigma χ 1, sigma χ gi⟩
def multCorr (X : Finset (ZMod p)) (d : ZMod p) : ℤ := ∑ u ∈ X, parSign u * parSign (d * u)
def eps (p n : ℕ) : ℤ := (-1) ^ (n ^ 2 / p)
noncomputable def quadR (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] : MulChar (ZMod p) R :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom R)
def halfSum (χ : MulChar (ZMod p) R) : R := ∑ n ∈ Icc 1 ((p - 1) / 2), χ (n : ZMod p)
def coprimePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N).filter fun ab => Nat.Coprime ab.1 ab.2
def pairRange (N : ℕ) (ab : ℕ × ℕ) : Finset ℕ := Icc 1 (N / max ab.1 ab.2)
end MellinDuality


