-- Prove2me | Definitions.Def_AvgValueAlloc_OPTinvQ
-- name    : AvgValueAlloc_OPTinvQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:03.497885+00:00
-- url     : https://prove2.me/theorems/3622f136-62e5-480d-afe6-f1b6e7335954
-- title:
--   Inventory-known causal optimum $\mathrm{OPT}_{\mathrm{inv}}(Q)$
-- statement:
--   For a known live multiset $Q$ of $T$ items arriving in uniformly random order,
--   $$
--   \mathrm{OPT}_{\mathrm{inv}}(Q)=\sup_{\pi}\ \frac1{T!}\sum_{\tau\in S_T} W\bigl(Q\circ\tau,\pi(Q\circ\tau)\bigr),
--   $$
--   the supremum over causal policies satisfying (1), chosen with knowledge of the multiset but not of the order, starting from zero surplus.
--
--   It is the inner benchmark of the population-known causal comparator and of (16).
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2; §5.3, p.13

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_prefixFeasible
import Definitions.Def_AvgValueAlloc_Policy

namespace AvgValueAlloc

open scoped ENNReal

/-- **The inventory-known causal optimum `OPT_inv(Q)` of a known live multiset in uniform order.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "The population-known causal
OPT_inv(P; S, T) subtracts history to know the remaining multiset, but not its order. It starts the
live stream with zero bank, like the learner."; §5.3, p.13, (16): "For a known live multiset Q,
the inventory-known causal optimum".

`OPTinvQ ρ Q = sup_π (1/T!) Σ_{τ ∈ S_T} welfare(Q ∘ τ, π(Q ∘ τ))`: the best expected welfare of a
causal policy satisfying (1), which may depend on the multiset of `Q`, when the items of `Q` arrive
in uniformly random order (position `t` receives `Q (τ t)`).

**Formalization Note.** Values in `ℝ≥0∞`. Feasibility is required on every sequence, which (by
rejecting violating moves) does not change the value. -/
noncomputable def OPTinvQ {n T : ℕ} (ρ : Fin n → ℚ) (Q : Fin T → Vec n) : ℝ≥0∞ :=
  ⨆ (π : Policy n) (_ : ∀ vs : Fin T → Vec n, prefixFeasible ρ vs (π.run vs)),
    (∑ τ : Equiv.Perm (Fin T), ENNReal.ofReal (welfare (Q ∘ τ) (π.run (Q ∘ τ)))) /
      (T.factorial : ℝ≥0∞)

end AvgValueAlloc


