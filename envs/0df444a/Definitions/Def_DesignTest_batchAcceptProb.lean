-- Prove2me | Definitions.Def_DesignTest_batchAcceptProb
-- name    : DesignTest_batchAcceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:12:16.171324+00:00
-- url     : https://prove2.me/theorems/6e5735fa-4fc5-4fc4-857d-016f929a5fed
-- title:
--   One batch of the frame-potential tester: $m_0=\lceil 256\sqrt{D_{\mathrm{Sym}}}/\varepsilon_{\mathrm{far}}^2\rceil$ samples, $D_{\mathrm{Sym}}$ SWAP tests per pair, threshold (63)
-- statement:
--   Fix $d,t$ and $\varepsilon_{\mathrm{far}}>0$, and let $C=256$, $D=D_{\mathrm{Sym}}$,
--   $$m_0=\Big\lceil \frac{C\sqrt{D}}{\varepsilon_{\mathrm{far}}^2}\Big\rceil .$$
--   One **batch** of the tester of Theorem 4.11 draws $m_0$ independent samples $\psi_1,\dots,\psi_{m_0}\sim\nu$ and, for each unordered pair $\{i,j\}$, performs $D$ independent SWAP tests between $|\psi_i\rangle^{\otimes t}$ and $|\psi_j\rangle^{\otimes t}$, recording $Z_{ij,\ell}=+1$ for the symmetric and $-1$ for the antisymmetric outcome ($\ell\in[D]$). Conditional on the samples the outcomes are independent and $\Pr[Z_{ij,\ell}=+1\mid\psi]=(1+h_{ij})/2$, so that $\mathbb E[Z_{ij,\ell}\mid\psi]=h_{ij}$. With $L=D\binom{m_0}2$ the statistic is
--   $$\widetilde F=\frac1L\sum_{i<j}\sum_{\ell=1}^{D}Z_{ij,\ell},$$
--   and the batch **accepts** iff
--   $$\widetilde F\le\frac1{D}+\frac{2\varepsilon_{\mathrm{far}}^2}{D}.$$
--   The batch acceptance probability on $\nu$ is the average over $\psi\sim\nu^{\otimes m_0}$ of the conditional acceptance probability.
--
--   This is the building block whose two error probabilities are bounded in (64) and (66).
--
--   **Formalization Note** The batch is described through its classical outcome law, the conditional law of the SWAP outcomes given the samples (the outcome law of one SWAP test is the milestone `swap_test_expectation`). The conditional acceptance probability is a finite sum over all outcome records.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), proof of Theorem 4.11, pp.38–39, eq. (63)

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_empFrame

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- The batch size `m₀ := ⌈C √D_Sym / ε_far²⌉` with `C := 256` (STOC 2027 submission
(sha256 e2f0a429…), proof of Theorem 4.11, p.38). -/
noncomputable def batchSize (d t : ℕ) (εfar : ℝ) : ℕ :=
  ⌈256 * Real.sqrt (DSym d t) / εfar ^ 2⌉₊

/-- A record of all SWAP-test outcomes of one batch: for every unordered pair `{i, j}` and every
repetition `ℓ ∈ [D]`, `true` is the symmetric outcome (value `Z_{ij,ℓ} = +1`) and `false` the
antisymmetric outcome (value `−1`) (STOC 2027 submission (sha256 e2f0a429…), p.38). -/
abbrev SwapOutcome (m D : ℕ) : Type := Pair m → Fin D → Bool

/-- The conditional probability of the outcome record `z` given the sampled states `ψ`: conditional on
the samples the `Z_{ij,ℓ}` are independent, and the symmetric outcome has probability `(1 + h_ij)/2`, so
that `E[Z_{ij,ℓ} | ψ] = h_ij` (STOC 2027 submission (sha256 e2f0a429…), p.38; the outcome law of the SWAP
test is the milestone `DesignTest.swap_test_expectation`). -/
noncomputable def outcomeProb {d m : ℕ} (t D : ℕ) (ψ : Fin m → PureVec d) (z : SwapOutcome m D) : ℝ :=
  ∏ p : Pair m, ∏ l : Fin D,
    if z p l then (1 + overlapPow t (ψ p.1.1) (ψ p.1.2)) / 2
    else (1 - overlapPow t (ψ p.1.1) (ψ p.1.2)) / 2

/-- The observable statistic `F̃ := L⁻¹ Σ_{i<j} Σ_{ℓ=1}^{D} Z_{ij,ℓ}` with `L := D · C(m, 2)` (STOC 2027
submission (sha256 e2f0a429…), p.38). -/
noncomputable def swapStat {m D : ℕ} (z : SwapOutcome m D) : ℝ :=
  ((D * Nat.choose m 2 : ℕ) : ℝ)⁻¹ * ∑ p : Pair m, ∑ l : Fin D, if z p l then (1 : ℝ) else -1

/-- The conditional acceptance probability of one batch of the frame-potential tester, given its
`m₀` sampled states: `D_Sym` SWAP tests per unordered pair, accept iff
`F̃ ≤ 1/D_Sym + 2ε_far²/D_Sym` (STOC 2027 submission (sha256 e2f0a429…), eq. (63), p.39). -/
noncomputable def batchAccept {d : ℕ} (t : ℕ) (εfar : ℝ)
    (ψ : Fin (batchSize d t εfar) → PureVec d) : ℝ :=
  ∑ z : SwapOutcome (batchSize d t εfar) (DSym d t),
    outcomeProb t (DSym d t) ψ z *
      if swapStat z ≤ 1 / (DSym d t : ℝ) + 2 * εfar ^ 2 / (DSym d t : ℝ) then 1 else 0

/-- **The acceptance probability of one batch** of the frame-potential tester of Theorem 4.11 on the
input `ν`: the batch draws `m₀ = batchSize d t ε_far` independent samples from `ν`, runs the SWAP tests
and applies the threshold (63) (STOC 2027 submission (sha256 e2f0a429…), pp.38–39).

**Formalization Note.** The batch is described classically (its outcome law given the samples, decision
12 of the plan); the integrand is a polynomial in the overlaps, hence continuous and bounded. -/
noncomputable def batchAcceptProb {d : ℕ} (t : ℕ) (εfar : ℝ) (ν : Measure (PureVec d)) : ℝ :=
  ∫ ψ, batchAccept t εfar ψ ∂(Measure.pi fun _ : Fin (batchSize d t εfar) => ν)

end DesignTest


