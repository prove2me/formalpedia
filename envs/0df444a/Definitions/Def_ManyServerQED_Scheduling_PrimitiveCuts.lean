-- Prove2me | Definitions.Def_ManyServerQED_Scheduling_PrimitiveCuts
-- name    : ManyServerQED_Scheduling_PrimitiveCuts
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T18:54:23.47126+00:00
-- url     : https://prove2.me/theorems/beab9591-c372-409e-914e-8e279dc9fbae
-- title:
--   Deterministic primitive prefixes and suffixes for queueing systems
-- statement:
--   For given arrival indices and nonnegative operational times, collect the information in the arrival, service and abandonment prefixes. A second map gives the vector of counting paths restarted at those deterministic cuts. The coordinates label a primitive, a customer class, and a nonnegative future time.
-- source:
--   Atar, Mandelbaum and Reiman, https://arxiv.org/pdf/math/0407058#page=49, Appendix A.3, proof of admissibility in Proposition 1

import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory
open scoped NNReal

namespace ManyServerQED.Scheduling

/-- Coordinates of the three families of counting paths on nonnegative times. -/
abbrev PrimitiveCoordinate (k : ℕ) :=
  (Fin k × ℝ≥0) ⊕ ((Fin k × ℝ≥0) ⊕ (Fin k × ℝ≥0))

/-- Deterministic arrival, service and abandonment prefixes read up to the specified cuts. -/
noncomputable abbrev primitivePrefixInfo {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0) : MeasurableSpace Ω :=
  (⨆ (i : Fin k) (j : ℕ) (_ : j < d i), MeasurableSpace.comap (M.U i (j + 1)) inferInstance) ⊔
    (⨆ (i : Fin k) (u : ℝ≥0) (_ : u ≤ p i), MeasurableSpace.comap (fun ω => M.S n i ω u) inferInstance) ⊔
    (⨆ (i : Fin k) (u : ℝ≥0) (_ : u ≤ q i), MeasurableSpace.comap (fun ω => M.R n i ω u) inferInstance)

/-- The vector of incremental counting paths after deterministic primitive cuts. -/
noncomputable def primitiveSuffix {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (d : Fin k → ℕ) (p q : Fin k → ℝ≥0)
    (ω : Ω) : PrimitiveCoordinate k → ℝ :=
  Sum.elim (fun z =>
      M.A n z.1 ω (M.arrivalEpoch n z.1 ω (d z.1) + z.2) - M.A n z.1 ω (M.arrivalEpoch n z.1 ω (d z.1)))
    (Sum.elim (fun z => M.S n z.1 ω ((p z.1 : ℝ) + z.2) - M.S n z.1 ω (p z.1))
      (fun z => M.R n z.1 ω ((q z.1 : ℝ) + z.2) - M.R n z.1 ω (q z.1)))

end ManyServerQED.Scheduling


