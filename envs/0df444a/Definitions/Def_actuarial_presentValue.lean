-- Prove2me | Definitions.Def_actuarial_presentValue
-- name    : actuarial_presentValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T14:14:23.976479+00:00
-- url     : https://prove2.me/theorems/465190d8-4b0c-444c-8035-97b8e743c861
-- title:
--   Finite contingent cashflow present value
-- statement:
--   Given a finite set of distinguishable payment obligations, each obligation has a non-negative integer payment time, a real cashflow amount and a payment-triggering event. A deterministic discount function maps time to a real multiplier. The random present value sums the discounted amounts multiplied by their event indicators. Distinct obligations may share a date, event or amount; events may overlap, and payments may be signed.
--
--   **Mathematical statement**
--
--   $$
--   Z(\omega)=\sum_{i\in I}d(t_i)c_i\,\mathbf{1}_{A_i}(\omega)
--   $$
--
--   Here $I$ is a finite set of distinct obligations; $t_i$ is the payment date, $c_i\in\mathbb R$ is its amount, $d(t_i)\in\mathbb R$ is its discount multiplier and $A_i$ is its triggering event. Distinct obligations may share dates.
-- source:
--   *Life Contingencies*, Chapter 3, §3.1, equations (3.2)–(3.3) and §3.1.1 (finite-horizon generalisation); https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html

import Mathlib

namespace ActuarialValuation

noncomputable def presentValue {ι Ω : Type*}
    (payments : Finset ι) (time : ι → ℕ)
    (discount : ℕ → ℝ) (amount : ι → ℝ)
    (trigger : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ i ∈ payments, discount (time i) * amount i *
    (trigger i).indicator (fun _ : Ω => (1 : ℝ)) ω

end ActuarialValuation


