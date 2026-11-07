-- Prove2me | Definitions.Def_AvgValueAlloc_expIID
-- name    : AvgValueAlloc_expIID
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:39:12.828415+00:00
-- url     : https://prove2.me/theorems/ed7a3cc8-96e2-4c83-a353-662b67a4d24b
-- title:
--   Expected learner welfare $\mathbb E\,\mathrm{ALG}$ (i.i.d. and random order)
-- statement:
--   For decisions that depend on the history, the live sequence and randomness $\omega\sim\mu$:
--   $$
--   \mathbb E\,\mathrm{ALG}(D)=\mathbb E_{h\sim D^S}\ \mathbb E_{v\sim D^T}\int W\bigl(v,\mathrm{dec}(h,v,\omega)\bigr)\,d\mu(\omega)
--   $$
--   in the i.i.d. model, and the same expected welfare when a population $P$ of $S+T$ items is put in uniform order, its first $S$ items forming the history.
--
--   Expectations include arrivals, history and coins.
--
--   **Formalization Note** Lower Lebesgue integrals in $[0,\infty]$.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_iidE
import Definitions.Def_AvgValueAlloc_welfare
import Definitions.Def_AvgValueAlloc_popAvg

namespace AvgValueAlloc

open scoped ENNReal

/-- **Expected learner welfare `E ALG` in the i.i.d. and in the random-order model.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "Expectations include arrivals,
history and coins"; "Random order uses an unknown fixed live multiset Q. With history, P has
exactly S + T originals in uniform order".

For decisions `dec hist vs ω` from history, live sequence and randomness `ω ∼ μ`:
`expIID D S T μ dec = E_{hist ∼ D^S} E_{vs ∼ D^T} ∫ welfare(vs, dec hist vs ω) dμ(ω)`, and
`expPop S T P μ dec` is the same expected welfare when the population `P` is put in uniform order,
its first `S` items are the history and its last `T` the live stream.

**Formalization Note.** Lower Lebesgue integrals in `ℝ≥0∞` (no integrability side condition).
History and live items are independent in the i.i.d. model. -/
noncomputable def expIID {n : ℕ} (D : FinLaw n) (S T : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω)
    (dec : (Fin S → Vec n) → (Fin T → Vec n) → Ω → Fin T → Option (Fin n)) : ℝ≥0∞ :=
  iidE D (Fin S) fun h => iidE D (Fin T) fun vs =>
    ∫⁻ ω, ENNReal.ofReal (welfare vs (dec h vs ω)) ∂μ

/-- Expected learner welfare on a population in uniform order. -/
noncomputable def expPop {n : ℕ} (S T : ℕ) (P : Fin (S + T) → Vec n) {Ω : Type}
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (dec : (Fin S → Vec n) → (Fin T → Vec n) → Ω → Fin T → Option (Fin n)) : ℝ≥0∞ :=
  popAvg S T (fun h vs => ∫⁻ ω, ENNReal.ofReal (welfare vs (dec h vs ω)) ∂μ) P

end AvgValueAlloc


