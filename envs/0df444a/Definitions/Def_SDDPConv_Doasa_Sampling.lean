-- Prove2me | Definitions.Def_SDDPConv_Doasa_Sampling
-- name    : SDDPConv_Doasa_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:29:44.900334+00:00
-- url     : https://prove2.me/theorems/3aed9cef-fd4e-4974-870d-c7bc31d32a2b
-- title:
--   FPSP, BPSP, per-scenario BPSP and the joint prefix sampling property J (p. 8)
-- statement:
--   Let $(\Omega',\mathbb P)$ be a probability space carrying the sampling: $\omega^k(w)$ is the forward scenario of iteration $k$ and $\Omega^k_t(w)\subseteq\Omega_t$ the backward sample.
--
--   1. **FPSP** (Forward Pass Sampling Property, p. 8): for each scenario $\omega(j)$, with probability 1, $|\{k:\omega^k=\omega(j)\}|=\infty$.
--   2. **BPSP** (Backward Pass Sampling Property, p. 8): for each $t=2,\dots,T$ and $i=1,\dots,q_t$, with probability 1, $|\{k:\omega_{ti}\in\Omega^k_t\}|=\infty$.
--   3. **Per-scenario BPSP** for DOASA-N, whose samples $\Omega^k_{s,t}$ depend on the scenario $s$: for each $s$, $t$ and $i$, with probability 1, $|\{k:\omega_{ti}\in\Omega^k_{s,t}\}|=\infty$.
--   4. **The joint prefix sampling property (J)**: for each $t=2,\dots,T$, each scenario $\omega(j)$ and each outcome $\omega_{ti}$, with probability 1 there are infinitely many iterations $k$ at which the forward scenario agrees with $\omega(j)$ in stages $2,\dots,t-1$ **and** $\omega_{ti}\in\Omega^k_t$:
--   $$\mathbb P\Big(\big|\{k:\ \omega^k_u=\omega_u(j)\ (2\le u\le t-1),\ \ \omega_{ti}\in\Omega^k_t\}\big|=\infty\Big)=1.$$
--
--   FPSP and BPSP are the paper's hypotheses; J is the property the convergence proof actually needs, because a stage-$t$ cut can only become exact at a state if the outcome's dual is collected at that state. J implies FPSP (take $t=T$) and BPSP, and it holds for the sampling schemes the paper names: SDDP, AND and ReSa use $\Omega^k_t=\Omega_t$, and independent forward and backward sampling satisfies it by the Borel–Cantelli lemma.
--
--   **Formalization Note** "With probability 1" is `∀ᵐ w ∂P`, stated separately for each scenario, stage and outcome as on p. 8. No measurability of the sample maps is assumed (none is needed for `∀ᵐ`). Scenario coordinate $u$ is the outcome of stage $u+2$.
-- source:
--   Philpott & Guan, On the convergence of stochastic dual dynamic programming and related methods, authors' manuscript v24 (2008-02-25), p. 8, FPSP and BPSP; p. 9, DOASA-N samples Ω^k_{s,t}; J is this mission's correction

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts
import Definitions.Def_SDDPConv_Doasa_Run

open MeasureTheory

namespace SDDPConv.Doasa

variable (I : Instance) {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')

/-- Forward Pass Sampling Property (FPSP, p. 8): for each scenario `sc`, with probability 1 the
forward scenario `fw w k` of iteration `k` equals `sc` for infinitely many `k`. -/
def FPSP (fw : Ω' → ℕ → Scen I) : Prop :=
  ∀ sc : Scen I, ∀ᵐ w ∂P, {k | fw w k = sc}.Infinite

/-- Backward Pass Sampling Property (BPSP, p. 8): for each stage `2 ≤ t ≤ T` and each outcome `i`
of stage `t`, with probability 1 the outcome `i` lies in the backward sample `Ω^k_t = bw w k t`
for infinitely many `k`. -/
def BPSP (bw : Ω' → ℕ → (t : ℕ) → Finset (Fin (I.q t))) : Prop :=
  ∀ t, 2 ≤ t → t ≤ I.T → ∀ i : Fin (I.q t), ∀ᵐ w ∂P, {k | i ∈ bw w k t}.Infinite

/-- BPSP read per scenario, for DOASA-N (p. 10): for each scenario `sc` of the list, each stage
`2 ≤ t ≤ T` and each outcome `i` of stage `t`, with probability 1 the outcome `i` lies in the
backward sample `Ω^k_{sc,t} = bw w k sc t` for infinitely many `k`. -/
def BPSPN (bw : Ω' → ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t))) : Prop :=
  ∀ sc : Scen I, ∀ t, 2 ≤ t → t ≤ I.T → ∀ i : Fin (I.q t),
    ∀ᵐ w ∂P, {k | i ∈ bw w k sc t}.Infinite

/-- Two scenarios agree before stage `t`: they have the same outcomes in stages `2, …, t − 1`. -/
def AgreeBefore (t : ℕ) (sc sc' : Scen I) : Prop :=
  ∀ u (hu : u < I.T - 2), u + 2 < t → sc ⟨u, hu⟩ = sc' ⟨u, hu⟩

/-- The joint prefix sampling property (J): for each stage `2 ≤ t ≤ T`, each scenario `sc` and each
outcome `i` of stage `t`, with probability 1 there are infinitely many iterations `k` at which the
forward scenario agrees with `sc` in stages `2, …, t − 1` and `i` lies in the backward sample
`Ω^k_t`. -/
def JointSP (fw : Ω' → ℕ → Scen I) (bw : Ω' → ℕ → (t : ℕ) → Finset (Fin (I.q t))) : Prop :=
  ∀ t, 2 ≤ t → t ≤ I.T → ∀ sc : Scen I, ∀ i : Fin (I.q t),
    ∀ᵐ w ∂P, {k | AgreeBefore I t (fw w k) sc ∧ i ∈ bw w k t}.Infinite

end SDDPConv.Doasa


