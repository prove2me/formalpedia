-- Prove2me | Definitions.Def_CollatzEndpointTransport_Solution
-- name    : CollatzEndpointTransport_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:25:39.25636+00:00
-- url     : https://prove2.me/theorems/a4da4032-2df2-50a7-b210-331606275765
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/Solution.lean

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
namespace CollatzEndpointTransportPalomar
open scoped Real
noncomputable section
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
def logBlockEndpoint (n : ℕ) : ℕ :=
  (shortcut^[Nat.log 2 n]) n
def endpointPullback (S : Set ℕ) : Set ℕ :=
  {n | logBlockEndpoint n ∈ S}
def badPrefix (S : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n => n ∉ S
def IsCDDense (S : Set ℕ) (C D : ℝ) : Prop :=
  0 < C ∧ 0 < D ∧ D ≤ 1 ∧
    ∀ N : ℕ, 0 < N →
      ((badPrefix S N).card : ℝ) ≤ C * (N : ℝ) ^ (1 - D)
def centralRenyiAlpha (theta : ℝ) : ℝ :=
  ((2 : ℝ) ^ theta - 1) / ((3 : ℝ) ^ theta - 1)
def centralRenyiAsymptoticRate (theta : ℝ) : ℝ :=
  theta / (1 + theta) * (Real.log 3 / (2 * Real.log 2))
def holderTargetExponent (theta : ℝ) : ℝ :=
  theta / (1 + theta)
def holderScaleExponent (theta : ℝ) : ℝ :=
  theta / (2 * (1 + theta))
end
end CollatzEndpointTransportPalomar


