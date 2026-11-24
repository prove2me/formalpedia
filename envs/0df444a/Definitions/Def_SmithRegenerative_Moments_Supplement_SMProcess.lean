-- Prove2me | Definitions.Def_SmithRegenerative_Moments_Supplement_SMProcess
-- name    : SmithRegenerative_Moments_Supplement_SMProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:43:43.028152+00:00
-- url     : https://prove2.me/theorems/cdb00195-3c7a-411a-8d1b-58e4d94d206f
-- title:
--   S.M. realization, right-continuous occupation, finite hitting and extended return means
-- statement:
--   A realization of an S.M. kernel has successive state labels $Y_n$ and waits $W_n\in[0,\infty]$ on one probability space for each initial label $z$. At epoch zero the process freshly enters $z$. Given the entire finite past and the present state $i$, the joint law of the next state and wait is $p_{ij}G_{ij}$. Put
--   $$S_0=0,\quad S_n=\sum_{k<n}W_k,\quad \{x_t=i\}=\bigcup_n\{Y_n=i,\ S_n\le t<S_{n+1}\}.$$
--   The half-open intervals express right continuity, including instantaneous transitions. The probability $Q_i(z)$ is the probability of a finite indexed first entry, including entry at zero when $z=i$; the recurrence mean $l_i$ is the extended expectation of the first return after index zero from fresh entry into $i$. These are computed from the path, rather than free quantities pinned by hypotheses.
--
--   **Formalization Note** The source does not specify a continuation beyond explosion. The realization uses the minimal completion: occupation of every ordinary state is false after infinitely many transitions have accumulated. This explicitly permits killing at explosion, and never assumes nonexplosion or arbitrary resurrection. It agrees with the source's positive-integer step process whenever the latter is defined without explosion. The source's regularity condition does not by itself rule out explosion (see DISPROOF.md). Means and absent hitting times take extended values. The Markov-renewal conditional law is the independent-trials meaning of (M1)–(M3); state-dependent waits need not be unconditionally independent.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, §4·1–4·2, pp. 19–20

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_SMKernel

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- Smith (1955), §4·1, pp. 19–20: the past at the n-th fresh entry.
Formalization Note: includes states 0,...,n and completed waits 0,...,n-1. -/
def smHistory {Ω : Type*} (Y : ℕ → Ω → ℕ) (W : ℕ → Ω → ENNReal)
    (n : ℕ) (ω : Ω) : (Fin (n + 1) → ℕ) × (Fin n → ENNReal) :=
  (fun k => Y k ω, fun k => W k ω)

/-- Smith (1955), (M1)–(M4), pp. 19–20, the Markov-renewal path model.
Formalization Note: the initial state is freshly entered at epoch zero. The conditional
joint law of the next state and wait, given the entire past, is p_ij G_ij; this is
the operational independent-trials reading of (M1)–(M3), not unconditional independence
of state-dependent waits. Occupation is constructed below from the successive entries.
After explosion it is killed (no positive-integer state), explicitly extending the
source where it does not specify a continuation. No nonexplosion assumption is made. -/
structure SMProcess (Ω : Type*) [MeasurableSpace Ω] where
  S : SMKernel
  P : ℕ → Measure Ω
  probability : ∀ z, IsProbabilityMeasure (P z)
  Y : ℕ → Ω → ℕ
  W : ℕ → Ω → ENNReal
  measurable_Y : ∀ n, Measurable (Y n)
  measurable_W : ∀ n, Measurable (W n)
  initial : ∀ z, ∀ᵐ ω ∂P z, Y 0 ω = z
  conditional : ∀ z n (B : Set Ω),
    @MeasurableSet Ω (MeasurableSpace.comap (smHistory Y W n) inferInstance) B →
    ∀ j (C : Set ENNReal), MeasurableSet C →
      P z (B ∩ {ω | Y (n + 1) ω = j ∧ W n ω ∈ C}) =
        ∫⁻ ω in B, S.p (Y n ω) j * S.G (Y n ω) j C ∂P z

/-- Smith (1955), §4·1, pp. 19–20: successive transition epochs, starting at zero.
Formalization Note: an infinite wait prevents every subsequent indexed transition. -/
noncomputable def SMProcess.epoch {Ω : Type*} [MeasurableSpace Ω] (M : SMProcess Ω)
    (n : ℕ) (ω : Ω) : ENNReal := ∑ k ∈ Finset.range n, M.W k ω

/-- Smith (1955), §4·2, p. 20: state at a real time, continuous to the right.
Formalization Note: the disjoint half-open occupation intervals implement (M4), including
instantaneous transitions. After an accumulation of infinitely many transitions no
interval contains t; this is the explicitly killed extension, not a chosen positive state. -/
def SMProcess.inState {Ω : Type*} [MeasurableSpace Ω] (M : SMProcess Ω)
    (μ : ℕ) (t : ℝ) : Set Ω :=
  {ω | 0 ≤ t ∧ ∃ n : ℕ, M.Y n ω = μ ∧
    M.epoch n ω ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < M.epoch (n + 1) ω}

/-- Smith (1955), §4·2, p. 20: the first finite entry into μ, including entry at zero.
Formalization Note: infimum in [0,∞] returns infinity when no entry occurs; no real default. -/
noncomputable def SMProcess.firstEntry {Ω : Type*} [MeasurableSpace Ω]
    (M : SMProcess Ω) (μ : ℕ) (ω : Ω) : ENNReal :=
  ⨅ n : ℕ, if M.Y n ω = μ then M.epoch n ω else ⊤

/-- Smith (1955), §4·2, p. 20: probability of finite first entry from z. -/
noncomputable def SMProcess.Q {Ω : Type*} [MeasurableSpace Ω]
    (M : SMProcess Ω) (z μ : ℕ) : ENNReal :=
  M.P z {ω | M.firstEntry μ ω < ⊤}

/-- Smith (1955), §4·2, p. 20: first return after a fresh entry, excluding index zero.
Formalization Note: zero-time returns are allowed; absent returns give infinity. -/
noncomputable def SMProcess.firstReturn {Ω : Type*} [MeasurableSpace Ω]
    (M : SMProcess Ω) (μ : ℕ) (ω : Ω) : ENNReal :=
  ⨅ n : ℕ, if M.Y (n + 1) ω = μ then M.epoch (n + 1) ω else ⊤

/-- Smith (1955), §4·2, p. 20: the cycle law of entries into μ. -/
noncomputable def SMProcess.returnLaw {Ω : Type*} [MeasurableSpace Ω]
    (M : SMProcess Ω) (μ : ℕ) : Measure ENNReal :=
  (M.P μ).map (M.firstReturn μ)

/-- Smith (1955), (4·2·1), p. 20: the extended mean recurrence time. -/
noncomputable def SMProcess.l {Ω : Type*} [MeasurableSpace Ω]
    (M : SMProcess Ω) (μ : ℕ) : ENNReal :=
  ∫⁻ ω, M.firstReturn μ ω ∂M.P μ

end SmithRegenerative.Moments.Supplement


