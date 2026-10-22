-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:12:06.026117+00:00
-- url     : https://prove2.me/theorems/40e06507-8a3e-4fa7-8ff2-e77789212338
-- title:
--   Orientation signs under vertex insertion
-- statement:
--   This bundle supplies orientation signs under vertex insertion. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
--
--   The included constructions and necessary compatibility results are:
--
--   - The exponent in `eps` counts, for each `u ∈ τ`, the elements of `G` below `u`.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/eps_insert.lean, selected declarations in lines 11–27; source SHA-256 0d120abd8985050c0e5cc9fafab4f055d3f588c7010274f76a1994daf9b352f5; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN
/-- The exponent in `eps` counts, for each `u ∈ τ`, the elements of `G` below `u`. -/
theorem eps_card_eq_sum_nu (G τ : Finset V) :
    ((G ×ˢ τ).filter (fun p => p.1 < p.2)).card = ∑ u ∈ τ, nu G u := by
  classical
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => (Finset.card_filter (fun x => x < u) G).symm

theorem eps_eq_pow_sum_nu (k : Type*) [Field k] (G τ : Finset V) :
    eps k G τ = (-1 : k) ^ (∑ u ∈ τ, nu G u) := by
  rw [eps, eps_card_eq_sum_nu]
-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem eps_insert {G τ : Finset V} {j : V} (hj : j ∉ τ) :
    eps k G (insert j τ) = eps k G τ * (-1 : k) ^ nu G j
-- SWARM:STATEMENT-END
:= by
  rw [eps_eq_pow_sum_nu, eps_eq_pow_sum_nu, Finset.sum_insert hj, pow_add, mul_comm]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


