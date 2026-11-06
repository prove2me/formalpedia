-- Prove2me | Definitions.Def_MetricMinTest_twoRound
-- name    : MetricMinTest_twoRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:08:17.842646+00:00
-- url     : https://prove2.me/theorems/447de33c-520d-484f-9a78-86dfe2a4e3ed
-- title:
--   Procedure TwoRound$(Z,r)$
-- statement:
--   Let $w$ be optimal for $H_{Z,r}$, $W=H_{Z,r}$, $p=w/W$, $L'=\ln(2/\delta)$, $\lambda_Z=\ln(1+\ln|Z|)$ and $T_1=\lceil(8L'+16\ln\rho_{Z,r}+16\lambda_Z)H_{Z,r}\rceil$.
--   1. **Round 1.** Draw $I_1,\dots,I_{T_1}$ i.i.d. from $p$, query them, and let $\Lambda=\{z\in Z : S_z(T_1)<L'\}$ and $M=|\Lambda|$.
--   2. **Round 2.** If $M=0$, accept. Otherwise take $N_2=\lceil32(\gamma-r)^{-2}(L'+\ln M)\rceil$ fresh samples from every $z\in\Lambda$ and run the fixed-sample rule of Lemma A.1 on each with threshold $r$, gap $\gamma-r$ and boundary $L'$. Accept if and only if all of them pass.
--
--   **Formalization Note** A two-round tester whose private randomness is the i.i.d. draw sequence; round 2 reads the stream entries after those read in round 1. The allocation $w$ is an argument.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix C.1, p.25; TwoPhase, p.23

import Mathlib
import Definitions.Def_MetricMinTest_RoundTester
import Definitions.Def_MetricMinTest_drawLaw
import Definitions.Def_MetricMinTest_screenStat
import Definitions.Def_MetricMinTest_oneStreamStat
import Definitions.Def_MetricMinTest_regionWorkload
import Definitions.Def_MetricMinTest_regionRatio

namespace MetricMinTest

/-- **Procedure `TwoRound(Z, r)`** (Appendix C.1). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix C.1, p.25: "Let w,
W = H_{Z,r}, p, and L′ = ln(2/δ) be as in TwoPhase(Z, r), put λ_Z = ln(1 + ln |Z|), and let
T₁ = ⌈(8L′ + 16 ln ρ_{Z,r} + 16λ_Z)H_{Z,r}⌉. Round 1. Draw I₁, …, I_{T₁} i.i.d. from p, query them,
and let Λ = {z ∈ Z : S_z(T₁) < L′} and M = |Λ|, with S_z as in Lemma B.1. Round 2. If M = 0,
accept. Otherwise take N₂ = ⌈32(γ − r)⁻²(L′ + ln M)⌉ fresh samples from every index z ∈ Λ, and
run the fixed-sample rule of Lemma A.1 on each with threshold r, gap γ − r, and boundary L′.
Accept if and only if all of them pass." TwoPhase (p.23): "Let w be optimal for H_{Z,r}, so
W = ∑ⱼ wⱼ = H_{Z,r}. Put p = w/W".

**Formalization Note.** Private randomness is the i.i.d. sequence `ξ : ℕ → ι` with law `(w/W)^⊗ℕ`;
round 1 (`Fin 2` index `0`) queries `ξ 0, …, ξ (T₁ − 1)`, i.e. `#{s < T₁ : ξ s = j}` samples of
each `j`. Round 2 (index `1`) takes `N₂` samples at each `z ∈ Λ`, the entries of stream `z` after
those read in round 1. The fixed-sample rule passes iff `S_{N₂} ≥ L′` (`oneStreamStat` with gap
`γ − r` and threshold `r`). If `M = 0` round 2 is empty and the tester accepts. The argument `w` is
the optimal allocation of the paper; `T₁` uses `H_{Z,r}` as printed. -/
noncomputable def twoRound {ι : Type} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    (d : ι → ι → ℝ) (γ δ : ℝ) (Z : Finset ι) (r : ℝ) (w : ι → ℝ) : RoundTester ι 2 :=
  let H : ℝ := regionWorkload d γ Z r
  let L' : ℝ := Real.log (2 / δ)
  let lam : ℝ := Real.log (1 + Real.log (Z.card : ℝ))
  let T1 : ℕ := ⌈(8 * L' + 16 * Real.log (regionRatio d γ Z r) + 16 * lam) * H⌉₊
  let c1 : (ℕ → ι) → ι → ℕ := fun ξ j => ((Finset.range T1).filter (fun s => ξ s = j)).card
  let Λ : (ℕ → ι) → (ι → ℕ → ℝ) → Finset ι := fun ξ ω =>
    haveI := Classical.decPred (fun z => screenStat d γ r z ξ ω T1 < L')
    Z.filter (fun z => screenStat d γ r z ξ ω T1 < L')
  let N2 : (ℕ → ι) → (ι → ℕ → ℝ) → ℕ := fun ξ ω =>
    ⌈32 * ((γ - r) ^ 2)⁻¹ * (L' + Real.log ((Λ ξ ω).card : ℝ))⌉₊
  { Ξ := ℕ → ι
    μξ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => drawLaw w)
    counts := fun s ξ ω j => if s = 0 then c1 ξ j else if j ∈ Λ ξ ω then N2 ξ ω else 0
    accept := fun ξ ω =>
      haveI := Classical.propDecidable
        (∀ z ∈ Λ ξ ω, L' ≤ oneStreamStat (γ - r) r (fun t => ω z (c1 ξ z + t)) (N2 ξ ω))
      decide (∀ z ∈ Λ ξ ω, L' ≤ oneStreamStat (γ - r) r (fun t => ω z (c1 ξ z + t)) (N2 ξ ω)) }

end MetricMinTest


