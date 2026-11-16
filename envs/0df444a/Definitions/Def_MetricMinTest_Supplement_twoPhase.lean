-- Prove2me | Definitions.Def_MetricMinTest_Supplement_twoPhase
-- name    : MetricMinTest_Supplement_twoPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:28:55.41134+00:00
-- url     : https://prove2.me/theorems/b4be1165-f052-49db-a2d5-393dd21b807f
-- title:
--   Procedure TwoPhase$(Z,r)$: shared screening with clean-up
-- statement:
--   Let $d$ be a pseudometric, $r\in[0,\gamma)$, $Z$ a nonempty set of targets and $w$ an optimal allocation for the region workload $H_{Z,r}$, so $W=\sum_jw_j=H_{Z,r}$. Put $p=w/W$, $L'=\ln(2/\delta)$ and $T_1=\lceil(8L'+16\ln\rho_{Z,r})H_{Z,r}\rceil$.
--
--   1. **Screening.** Draw $I_1,\dots,I_{T_1}$ i.i.d. from $p$, query them, and form for every $z\in Z$ the statistic $S_z(t)=\sum_{s\le t}\big[a_{I_s}(X_s-r-d(z,I_s))-\tfrac12a_{I_s}^2\big]$, $a_j=(\gamma-r-d(z,j))_+$ (Lemma B.1). Let $\Lambda=\{z\in Z:\max_{t\le T_1}S_z(t)<L'\}$ and $M=|\Lambda|$.
--   2. **Clean-up.** If $M=0$, accept. Otherwise take the targets of $\Lambda$ in a fixed order and run for each the one-stream test on fresh samples from index $z$ with threshold $r$, gap $\gamma-r$, boundary $L'$ and cap $\lceil32(\gamma-r)^{-2}(L'+\ln M)\rceil$; reject at the first failure and accept if all pass.
--
--   This is the tester of Theorem C.1, which gives the expected-cost upper bound of Theorem C.
--
--   **Formalization Note** The allocation $w$ and the fixed order (a list enumerating the indices) are arguments; the private randomness is the i.i.d. draw sequence. The screening statistics are computed from the history.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix C, p.23

import Mathlib
import Definitions.Def_MetricMinTest_Tester
import Definitions.Def_MetricMinTest_drawLaw
import Definitions.Def_MetricMinTest_regionRatio
import Definitions.Def_MetricMinTest_Supplement_seqStatus

namespace MetricMinTest.Supplement

open Classical in
/-- **Procedure TwoPhase(Z, r)** (Appendix C). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix C, p.23: "Let w be optimal for
H_{Z,r}, so W = ∑ⱼ wⱼ = H_{Z,r}. Put p = w/W, L′ = ln(2/δ), and
T₁ = ⌈(8L′ + 16 ln ρ_{Z,r}) H_{Z,r}⌉. Phase 1 (screening). Draw I₁, …, I_{T₁} i.i.d. from p, query
them, and form the statistics S_z(t) of Lemma B.1 for every z ∈ Z. Let
Λ = {z ∈ Z : max_{t≤T₁} S_z(t) < L′} and M = |Λ|. Phase 2 (clean-up). If M = 0, accept.
Otherwise, take the targets z ∈ Λ in a fixed order. For each, run Lemma A.1 on fresh samples from
index z with threshold r, gap γ − r, boundary L′, and cap ⌈32(γ − r)⁻²(L′ + ln M)⌉. Reject at the
first failure, and accept if all pass."

**Formalization Note.** The allocation `w` is an argument (the theorem takes any optimal one).
Private randomness is the i.i.d. draw sequence `ξ : ℕ → ι` with law `(w/W)^⊗ℕ`; the first
`T₁` queries are `ξ 0, …, ξ (T₁ − 1)`. On a history `h`, target `z`'s statistic after `t` steps
is `∑_{s<t} [a(xₛ − r − d(z, jₛ)) − a²/2]` with `a = (γ − r − d(z, jₛ))₊` (Lemma B.1, the published
`screenStat` read off the history). The fixed order of the survivors is the order of the list
`ord` (the theorem takes any enumeration of the indices). Phase 2 is `seqStatus` on the
observations after the first `T₁`, each test on fresh entries of its stream. -/
noncomputable def twoPhase {ι : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    (d : ι → ι → ℝ) (γ δ : ℝ) (Z : Finset ι) (r : ℝ) (w : ι → ℝ) (ord : List ι) : Tester ι :=
  let L' : ℝ := Real.log (2 / δ)
  let T1 : ℕ := ⌈(8 * L' + 16 * Real.log (regionRatio d γ Z r)) * regionWorkload d γ Z r⌉₊
  let stat : ι → List (ι × ℝ) → ℕ → ℝ := fun z h t =>
    ((h.take t).map (fun p => max (γ - r - d z p.1) 0 * (p.2 - r - d z p.1) -
      (max (γ - r - d z p.1) 0) ^ 2 / 2)).sum
  let survivors : List (ι × ℝ) → List ι := fun h =>
    ord.filter (fun z => decide (z ∈ Z ∧ ∀ t ≤ T1, stat z h t < L'))
  let tests : List (ι × ℝ) → List (ι × ℝ × ℝ × ℝ × ℕ) := fun h =>
    (survivors h).map (fun z => (z, r, γ - r, L',
      ⌈32 * ((γ - r) ^ 2)⁻¹ * (L' + Real.log ((survivors h).length : ℝ))⌉₊))
  { Ξ := ℕ → ι
    μξ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => drawLaw w)
    next := fun ξ h =>
      if h.length < T1 then some (ξ h.length)
      else (seqStatus (tests (h.take T1)) ((h.drop T1).map Prod.snd)).elim some (fun _ => none)
    accept := fun _ h =>
      if h.length < T1 then false
      else (seqStatus (tests (h.take T1)) ((h.drop T1).map Prod.snd)).elim (fun _ => false) id }

end MetricMinTest.Supplement


