-- Prove2me | Definitions.Def_DerivativeChainContinuation_GreedyActual
-- name    : DerivativeChainContinuation_GreedyActual
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T20:15:27.194749+00:00
-- url     : https://prove2.me/theorems/3c4a6276-ee1a-40c8-9177-02c5a45c76ca
-- title:
--   Nearest-parent selection in every actual ordinary derivative row
-- statement:
--   Let a,z∈ℂ^(n+1) and p_a(X)=∏_(j=0)^n (X-a_j). The actual row of degree m is p_a differentiated n+1-m times, for 1 ≤ m ≤ n+1. IsGreedyChain(a,z) means that z is an actual derivative chain and, for every 0 ≤ i<n and every complex root w of row i+2, |z_(i+1)-z_i| ≤ |w-z_i|. All complex parent roots, repeated roots and local ties are included. Also define realHistoryOf(z,k)=Re(z_k) if k<n+1, and zero otherwise.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyActual.lean, lines 35-36, SHA-256 d3ac9fdd06dd387e730b07299cffea9935de88f557ffb857e687a74f824fca1d.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyActual.lean, lines 9-12, SHA-256 d3ac9fdd06dd387e730b07299cffea9935de88f557ffb857e687a74f824fca1d.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

/-- Every step minimizes over all roots of the next ordinary derivative row. -/
def IsGreedyChain {n : ℕ} (a z : Fin (n+1) → ℂ) : Prop :=
  IsChain a z ∧ ∀ i : Fin n, ∀ w : ℂ, (row a (i.val+2)).eval w=0 →
    ‖z i.succ-z i.castSucc‖≤‖w-z i.castSucc‖





def realHistoryOf {n : ℕ} (z : Fin (n+1) → ℂ) (k : ℕ) : ℝ :=
  if h : k<n+1 then (z ⟨k,h⟩).re else 0

















end DerivativeChainContinuation


