-- Prove2me | Definitions.Def_MetricMinTest_Supplement_randBall
-- name    : MetricMinTest_Supplement_randBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:29:24.684203+00:00
-- url     : https://prove2.me/theorems/3d9a45b3-e195-42c8-b30a-ca04e7661152
-- title:
--   Procedure RandBall$_u(y)$: random ball selection with sequential certification
-- statement:
--   Let $y$ be a fractional ball cover and $u>0$. Independently select every indexed ball $B_{j\ell}=B(j,r_{j\ell})$ with $y_{j\ell}>0$ with probability $\pi_{j\ell}=\min\{1,uy_{j\ell}\}$; let $S$ be the selected list in a fixed order and $\nu=|S|$. Reject if $\nu=0$. Otherwise, for each selected ball run the one-stream test at index $j$ with threshold $r_{j\ell}$, gap $a_{j\ell}=\gamma-r_{j\ell}$, boundary $u$ and cap $\lceil32a_{j\ell}^{-2}(u+\ln\nu)\rceil$, on fresh samples; reject at the first failed test and accept if all pass.
--
--   This is the tester of Theorem D.2, the building block of the randomized-certificate bounds of Theorems D.3 and D.
--
--   **Formalization Note** Indexed balls are encoded as in the published certificate workload: a pair $(j,i)$ with $d(j,i)<\gamma$ is the ball $B(j,d(j,i))$. The private randomness is one independent Boolean coin per pair; the fixed order is a list enumerating the pairs.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix D, p.26

import Mathlib
import Definitions.Def_MetricMinTest_Tester
import Definitions.Def_MetricMinTest_Supplement_seqStatus

namespace MetricMinTest.Supplement

open Classical in
/-- **Procedure RandBall_u(y)** (Appendix D). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix D, p.26: "Independently select every
ball with positive weight with probability π_{jℓ} = min{1, u y_{jℓ}}. Let S be the selected list in
a fixed order and ν = |S|. Reject if ν = 0. Otherwise, for each selected ball run Lemma A.1 with
threshold r_{jℓ}, gap a_{jℓ}, boundary u, and cap N_{jℓ} = ⌈32 a_{jℓ}⁻²(u + ln ν)⌉. Use fresh
samples for different tests, including tests sharing a center. Reject at the first failed test;
accept if all pass."

**Formalization Note.** Indexed balls use the encoding of the published `certWorkload`: a pair
`(j, i)` with `d j i < γ` is the ball `B(j, d j i)`, threshold `r = d j i`, gap `γ − d j i`.
A pair with `d j i ≥ γ` or `y (j, i) ≤ 0` is never selected. Private randomness is
`ξ : ι × ι → Bool` with independent coordinates, `ξ (j, i) = true` with probability `π_{ji}`
(product measure). The fixed order of the selected list is that of the list `ord` (the theorem
takes any enumeration of the pairs). -/
noncomputable def randBall {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (γ u : ℝ)
    (y : ι × ι → ℝ) (ord : List (ι × ι)) : Tester ι :=
  let π : ι × ι → ℝ := fun p => if d p.1 p.2 < γ ∧ 0 < y p then min 1 (u * y p) else 0
  let sel : (ι × ι → Bool) → List (ι × ι) := fun ξ =>
    ord.filter (fun p => decide (ξ p = true ∧ 0 < π p))
  let tests : (ι × ι → Bool) → List (ι × ℝ × ℝ × ℝ × ℕ) := fun ξ =>
    (sel ξ).map (fun p => (p.1, d p.1 p.2, γ - d p.1 p.2, u,
      ⌈32 * ((γ - d p.1 p.2) ^ 2)⁻¹ * (u + Real.log ((sel ξ).length : ℝ))⌉₊))
  { Ξ := ι × ι → Bool
    μξ := MeasureTheory.Measure.pi (fun p : ι × ι =>
      (Real.toNNReal (π p)) • MeasureTheory.Measure.dirac true +
        (Real.toNNReal (1 - π p)) • MeasureTheory.Measure.dirac false)
    next := fun ξ h =>
      if sel ξ = [] then none else (seqStatus (tests ξ) (h.map Prod.snd)).elim some (fun _ => none)
    accept := fun ξ h =>
      if sel ξ = [] then false else (seqStatus (tests ξ) (h.map Prod.snd)).elim (fun _ => false) id }

end MetricMinTest.Supplement


