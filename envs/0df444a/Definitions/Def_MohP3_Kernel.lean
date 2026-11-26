-- Prove2me | Definitions.Def_MohP3_Kernel
-- name    : MohP3_Kernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:54:21.510983+00:00
-- url     : https://prove2.me/theorems/e53aef7b-ee06-4176-aca3-f48ce066dfc0
-- title:
--   Kernel
-- statement:
--   Definitions and structural lemmas for Kernel, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Kernel.lean

module
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Independence
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPolynomial
namespace MohP3
def Good (g : R) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ ∃ p : Fin 8 → Polynomial ℚ, (n : R) * g - ∑ i, iota (p i) * hh i ∈ P
end MohP3


