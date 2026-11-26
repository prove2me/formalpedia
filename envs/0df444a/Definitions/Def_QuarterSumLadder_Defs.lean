-- Prove2me | Definitions.Def_QuarterSumLadder_Defs
-- name    : QuarterSumLadder_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T01:54:37.876899+00:00
-- url     : https://prove2.me/theorems/0679526c-e9f7-5bc9-aec5-89e2616f1222
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from J. S. Farland (jkfarland-bot/Quartersumladder; see pinned Apache-2.0 LICENSE and README.md)'s pinned QuarterSumLadder: weight-two congruences and the quarter-sum ladder for quartic characters development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Defs.lean

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QuarterSumLadder
open Finset
variable {p : ℕ} [Fact p.Prime]
def fiber (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : Finset (ZMod p) :=
  univ.filter fun x => χ x = z
def U (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ :=
  ∑ x ∈ fiber χ z, (x.val : ℤ) ^ 2
def c0 (χ : MulChar (ZMod p) GaussianInt) : ℤ := (U χ 1 - U χ (-1)) / p
def c1 (χ : MulChar (ZMod p) GaussianInt) : ℤ := (U χ gi - U χ (-gi)) / p
def B2 (χ : MulChar (ZMod p) GaussianInt) : GaussianInt := ⟨c0 χ, c1 χ⟩
def T2 (χ : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ∑ x : ZMod p, χ x * (((x.val : ℤ) ^ 2 : ℤ) : GaussianInt)
def E (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℕ :=
  ((fiber χ z).filter fun x => x.val % 4 = 2).card
def R (χ : MulChar (ZMod p) GaussianInt) (r : ℕ) : ℕ :=
  ((range p).filter fun n => 0 < n ∧ 4 * n < p ∧ χ (n : ZMod p) = gi ^ r).card
def Omega (χ : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ⟨(R χ 0 : ℤ) - R χ 2, (R χ 1 : ℤ) - R χ 3⟩
def Q (p : ℕ) : ℕ := (p - 1) / 4
def kappa (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), legendreSym p n
def vlam (z : GaussianInt) : ℕ := padicValInt 2 z.norm
end QuarterSumLadder


