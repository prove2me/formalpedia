-- Prove2me | Definitions.Def_MomentComparison_NoisePolynomial
-- name    : MomentComparison_NoisePolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:14:19.223202+00:00
-- url     : https://prove2.me/theorems/6191cfc6-26c3-4f35-81c1-85645c890a03
-- title:
--   Noise Polynomial
-- statement:
--   Definitions and structural lemmas for Noise Polynomial, from XinyuanXie-hub (XinyuanXie-hub/MomentComparison; see pinned Apache-2.0 LICENSE)'s pinned Sharp two-sided bounds on the moment comparison constant Cstar development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/MomentComparison/blob/30aae604e14c2e7a22e5eb3bcd3cfd6d02f61772/MomentComparison/NoisePolynomial.lean

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open scoped BigOperators
namespace MomentComparison
open Finset
@[expose] noncomputable def complexNoise : {n : ℕ} → ℂ → (Cube n → ℂ) → Cube n → ℂ
  | 0, _, f, x => f x
  | n + 1, w, f, x =>
      let a := complexNoise w (fun y => f (Fin.cons true y : Cube (n + 1))) (Fin.tail x)
      let b := complexNoise w (fun y => f (Fin.cons false y : Cube (n + 1))) (Fin.tail x)
      (a + b) / 2 + (if x 0 then 1 else -1) * w * (a - b) / 2
def tailSet {n : ℕ} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter (fun i => i.succ ∈ s)
end MomentComparison


