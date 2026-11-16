-- Prove2me | Definitions.Def_MetricMinTest_Supplement_coverNumber
-- name    : MetricMinTest_Supplement_coverNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:33:30.238252+00:00
-- url     : https://prove2.me/theorems/a05fb2dd-c401-4f8c-b6c6-eee39ab53a1b
-- title:
--   Covering number $N_d(r)$
-- statement:
--   $N_d(r)$ is the minimum number of radius-$r$ balls $B(j,r)$, $j\in[k]$, covering $[k]$:
--   $$N_d(r)=\min\Big\{|Z|\ :\ \forall i\ \exists z\in Z,\ d(i,z)\le r\Big\}.$$
--   It enters the cover upper bound of Theorem I.1.
--
--   **Formalization Note** A minimum over center sets (natural-number infimum).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem I.1, p.30

import Mathlib

namespace MetricMinTest.Supplement

/-- **Covering number `N_d(r)`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem I.1, p.30: "N_d(r) is the minimum number of
radius-r balls covering [k]" (balls `B(j, r)`, `j ∈ [k]`).

**Formalization Note.** The least cardinality of a set `Z` of centers with
`∀ i, ∃ z ∈ Z, d(i, z) ≤ r`, in `ℕ` (`sInf`); distinct centers with equal balls only waste
balls, so this equals the least number of balls. -/
noncomputable def coverNumber {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (r : ℝ) : ℕ :=
  sInf {n : ℕ | ∃ Z : Finset ι, Z.card = n ∧ ∀ i, ∃ z ∈ Z, d i z ≤ r}

end MetricMinTest.Supplement


