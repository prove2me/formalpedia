-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_positionRule
-- name    : ReplicableDecisions_Supplement_positionRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:01:51.093235+00:00
-- url     : https://prove2.me/theorems/9b7cd4d5-93ae-4e11-9e03-408e5ef1423d
-- title:
--   The shared uniform seed $U\sim\mathrm{Unif}[d/3,2d/3]$ and the rule $\mathbf 1\{\hat\jmath\ge U\}$
-- statement:
--   Given a position estimate $\hat\jmath\in\{0,\dots,d\}$ computed from the sample, draw $U\sim\mathrm{Unif}[d/3,2d/3]$ independently of the data, shared by every run, and output
--   $$\mathbf 1\{\hat\jmath\ge U\}.$$
--
--   This is the output rule of the change-point algorithm of §4 and of Theorem 4.5.
--
--   **Formalization Note** The seed space is $\mathbb R$ with Lebesgue measure conditioned on $[d/3,2d/3]$ (a probability measure for $d\ge1$).
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), algorithm of §4, p.18 (PDF p.20); Theorem 4.5, p.22 (PDF p.24)

import Mathlib

open MeasureTheory

namespace ReplicableDecisions.Supplement

/-- **The shared seed** `U ∼ Unif[d/3, 2d/3]`. Chen, *Replicable Decisions in Finite Experiments*,
STOC 2027 submission (sha256 52d181db…), the algorithm of §4, p.18 (PDF p.20), and Theorem 4.5,
p.22 (PDF p.24): "U ∼ Unif[d/3, 2d/3] is shared".

**Formalization Note.** The seed space is `ℝ` with its Borel σ-algebra; the law is Lebesgue measure
conditioned on the interval, a probability measure when `d ≥ 1`. -/
noncomputable def positionSeedLaw (d : ℕ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc ((d : ℝ) / 3) (2 * (d : ℝ) / 3))

/-- **The rule `1{ĵ ≥ U}`** for a position estimate `ĵ` of the sample. Chen, STOC 2027 submission
(sha256 52d181db…), Theorem 4.5, p.22 (PDF p.24): "the output 1{ĵ ≥ U}".

**Formalization Note.** `1 = true`; `ĵ` takes values in `{0, …, d}` = `Fin (d + 1)`. -/
noncomputable def positionRule {d n : ℕ} {Z : Type} (jhat : (Fin n → Z) → Fin (d + 1)) :
    (Fin n → Z) → ℝ → Bool :=
  fun x u => decide (u ≤ (((jhat x : ℕ)) : ℝ))

end ReplicableDecisions.Supplement


