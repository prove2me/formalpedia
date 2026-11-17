-- Prove2me | Definitions.Def_ReplicableOL_Supplement_seedLaw
-- name    : ReplicableOL_Supplement_seedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:16:18.449333+00:00
-- url     : https://prove2.me/theorems/37014a62-6488-4517-825d-d5aa9331a562
-- title:
--   Seed law of DALR
-- statement:
--   For a chain $(A_i)$ and a level scale $H>0$, the **seed law** of DALR draws
--
--   $$
--   \chi\sim U[-H,H],\qquad \omega_{i,q}\sim U[0,A_i)\quad (i\in[K],\ q=0,\dots,T/A_i-1),
--   $$
--
--   all independent. Every offset is fresh and is used at exactly one anchor; the same seed is shared by the two runs in the definition of replicability.
--
--   **Formalization Note** The uniform law on a set $s$ is Lebesgue measure conditioned on $s$ (`volume[|s]`), and the seed law is the product of these uniforms. It is a probability measure for $H>0$, which the verification file proves.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.1, p.18

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_Seed
open MeasureTheory ProbabilityTheory

namespace ReplicableOL.Supplement

/-- **DALR seed law.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.1, p.18. "χ ∼ U[−H, H] and ω_{i,q} ∼ U[0, A_i) for i ∈ [K] and q = 0, …, T/A_i − 1, all independent."

**Formalization Note.** `μ[|s]` is Lebesgue measure conditioned on `s`, the uniform law on `s`; the law is the product of these uniforms, one factor per offset, so every offset is fresh and used once. It is a probability measure for `H > 0` (proved in the verification file); every theorem of the mission uses it with `H > 0`. -/
noncomputable def seedLaw {T : ℕ} (C : Chain T) (H : ℝ) : Measure (Seed C) :=
  (volume[|Set.Icc (-H) H]).prod
    (Measure.pi fun i : Fin C.K => Measure.pi fun _ : Fin (T / C.A (i.val + 1)) =>
      volume[|Set.Ico (0 : ℝ) (C.A (i.val + 1))])

end ReplicableOL.Supplement


