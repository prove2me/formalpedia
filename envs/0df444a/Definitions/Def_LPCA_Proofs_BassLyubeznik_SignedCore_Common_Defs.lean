-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:11:28.522201+00:00
-- url     : https://prove2.me/theorems/14fb2951-82a2-48cf-b947-0893dc10d5b2
-- title:
--   Signed incidence and contraction coefficients
-- statement:
--   This bundle supplies signed incidence and contraction coefficients. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
--
--   The included constructions and necessary compatibility results are:
--
--   - `ν_A(j)`: the number of elements of `A` that are smaller than `j`.
--   - Incidence coefficient of a signed subset complex, in the field `k`: `(-1)^{ν_J(j)}` when `J' = J ∪ {j}` with `j ∉ J`, and `0` otherwise.
--   - Coefficient of the signed vertex-erasure operator: `h(e_J) = (-1)^{ν_{J∖j}(j)} e_{J∖j}` when `j ∈ J`, else `0`. `hc k j J J'` is the coefficient of `e_{J'}` in `h(e_J)`.
--   - The sign `ε_G(τ) = (-1)^{|{(g,u) ∈ G × τ : g < u}|}` used in the signed-subset comparison.
--   - A family of finsets is convex if it contains every set lying between two of its members.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/Common.lean, selected declarations in lines 9–28; source SHA-256 1775eea8c54b2c33ccb8058bd5c4de12780e2e619293cb5aa60e6eab7816a515; source certificate Sapelo2 job 49172236.

import Mathlib

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V]

/-- `ν_A(j)`: the number of elements of `A` that are smaller than `j`. -/
def nu (A : Finset V) (j : V) : ℕ := (A.filter (· < j)).card

/-- Incidence coefficient of a signed subset complex, in the field `k`:
`(-1)^{ν_J(j)}` when `J' = J ∪ {j}` with `j ∉ J`, and `0` otherwise. -/
def inc (k : Type*) [Field k] (J J' : Finset V) : k :=
  if J ⊆ J' ∧ J'.card = J.card + 1 then ∑ j ∈ J' \ J, (-1 : k) ^ nu J j else 0

/-- Coefficient of the contracting homotopy "divide by `x_j`": `h(e_J) = (-1)^{ν_{J∖j}(j)} e_{J∖j}`
when `j ∈ J`, else `0`. `hc k j J J'` is the coefficient of `e_{J'}` in `h(e_J)`. -/
def hc (k : Type*) [Field k] (j : V) (J J' : Finset V) : k :=
  if j ∈ J ∧ J' = J.erase j then (-1 : k) ^ nu J' j else 0

/-- The sign `ε_G(τ) = (-1)^{|{(g,u) ∈ G × τ : g < u}|}` of Theorem 3.7(b). -/
def eps (k : Type*) [Field k] (G τ : Finset V) : k :=
  (-1 : k) ^ ((G ×ˢ τ).filter (fun p => p.1 < p.2)).card

/-- A family of finsets is convex if it contains every set lying between two of its members. -/
def IsConvex (𝓕 : Finset V → Prop) : Prop :=
  ∀ ⦃J J' J'' : Finset V⦄, 𝓕 J → 𝓕 J'' → J ⊆ J' → J' ⊆ J'' → 𝓕 J'

end Proofs.BassLyubeznik.SignedCore


