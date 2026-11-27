-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
-- name    : BauerleRiederMDP_LQ_Supplement_Ufrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:10:22.875317+00:00
-- url     : https://prove2.me/theorems/2a1a136c-a3e5-5870-92fa-88c86df0638a
-- title:
--   The set $U$ of admissible fractions
-- statement:
--   **The set $U$ of admissible fractions** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, p.281, PDF 291): $U := \{u \in  \mathbb R ^d | u \ge  0, u \cdot  e \le  1\}$, the fractions of wealth invested in the $d$ stocks (short sales excluded), a compact set.
--
--   **Formalization Note.** A subtype of $Fin d \to  \mathbb R $, with the subspace topology and σ-algebra.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, p.281, PDF 291

import Mathlib

namespace BauerleRiederMDP.LQ.Supplement

/-- **The set `U` of admissible fractions** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §9.3, p.281, PDF 291): `U := {u ∈ ℝ^d | u ≥ 0, u · e ≤ 1}`, the
fractions of wealth invested in the `d` stocks (short sales excluded), a compact set.

**Formalization Note.** A subtype of `Fin d → ℝ`, with the subspace topology and σ-algebra. -/
def Ufrac (d : ℕ) : Type := {u : Fin d → ℝ // (∀ k, 0 ≤ u k) ∧ ∑ k, u k ≤ 1}

instance (d : ℕ) : MeasurableSpace (Ufrac d) := Subtype.instMeasurableSpace
instance (d : ℕ) : TopologicalSpace (Ufrac d) := instTopologicalSpaceSubtype

end BauerleRiederMDP.LQ.Supplement


