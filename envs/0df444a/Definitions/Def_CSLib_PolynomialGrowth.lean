-- Prove2me | Definitions.Def_CSLib_PolynomialGrowth
-- name    : CSLib_PolynomialGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T00:58:08.467744+00:00
-- url     : https://prove2.me/theorems/ef6ceff3-a28f-4ff8-adc0-883b88e1c46c
-- title:
--   Polynomial growth of natural-valued functions
-- statement:
--   For a function $f:\mathbb N\to\mathbb N$, `Cslib.PolynomiallyBounded f` means that some fixed power $n^d$ bounds $f(n)$ for all sufficiently large $n$. This is a growth condition only: it does not assert that $f$ is computable or that any implementation has this running time. Imported from CSLib at a pinned revision, with the original definition preserved.
-- source:
--   https://github.com/leanprover/cslib/blob/6ff325e870ed89f86be10515f0e7297fa5a32845/Cslib/Foundations/Data/Nat/PolynomialBound.lean#L27-L29

import Mathlib.Order.Filter.AtTopBot.Basic

namespace Cslib
open Filter
/-- A function is polynomially bounded if a fixed power eventually bounds its values. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, f ≤ᶠ[atTop] (· ^ d)
end Cslib


