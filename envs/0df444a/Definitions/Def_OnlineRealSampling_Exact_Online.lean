-- Prove2me | Definitions.Def_OnlineRealSampling_Exact_Online
-- name    : OnlineRealSampling_Exact_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:53.517673+00:00
-- url     : https://prove2.me/theorems/8c74e97e-3b11-4e90-9ae2-a3728d41c184
-- title:
--   Algorithm 2, adaptive environments and the entropy loss
-- statement:
--   **Algorithm 2.** The persistent state is $(t,\Delta,Z,M)$, initially $(0,0,0,1)$. For each request: if $\epsilon t<0.1$, set $t\leftarrow t+1$ and $\Delta\leftarrow 5000\,t\lceil\lg(t+2)\rceil$. Then receive the oracle of the next target, run $(X,(Z,M))\leftarrow\mathrm{Sample}(F,(Z,M),\Delta)$ on the fresh bits not yet consumed, and emit $X$. Only $(t,\Delta,Z,M)$ survives between requests, and its persistent storage is the sum of the bit lengths of these four registers. The value of $\Delta$ in iteration $i\ge1$ is $\Delta_i=D_{t_i}$, where $D_j=5000j\lceil\lg(j+2)\rceil$ and $t_i$ is the counter after the update of iteration $i$. For $\epsilon=0$, $t_i=i$.
--
--   **Environments.** The target of iteration $i$ is chosen as $F_i=\mathrm{env}(\xi,[X_1,\dots,X_{i-1}])$. Here $\xi\sim\mu$ is external randomness, independent of the fair bits, and the rule sees only $\xi$ and the public history, never the sampler's state or future bits. An environment is *admissible* if every oracle it can produce is valid and the CDF values, answers and evaluation costs are measurable in $\xi$.
--
--   **Entropy loss.** With $T_n$ the number of fresh bits consumed in the first $n$ iterations,
--   $$L_n=\mathbb E\Big[T_n-\sum_{i=1}^n\lg\frac1{f_i(X_i)}\Big]\qquad(3),$$
--   the expectation, under $\mu\otimes(\text{fair bits})$, of the centred variable. The variable is set to $0$ on the event that some iteration never halts.
--
--   **Per-iteration observables.** For iteration $i$ the definitions name the record of the iteration, the resources of the iteration (time, oracle calls, big-integer operations, largest operand bit length, temporary storage), and the output $X_i$ with $\log X_i$. The temporary storage is the peak storage of Sample plus the registers $t,\Delta$ and the update arithmetic. The resources are elements of $[0,\infty]$, equal to $\infty$ if an iteration never halts. The definitions also give the history before iteration $i$ and the quantity $C_{F_i}(X_i,i)+\log(X_i)\,C_{F_i}(X_i,X_i)$ of clause 1.2.5.
--
--   **Formalization Note** The test $\epsilon t<0.1$ is a comparison of reals with the fixed parameter $\epsilon$; it is not charged. The update of $t$ and $\Delta$ is charged.
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Algorithm 2 (PDF 9 / printed 8); eq. (3) (PDF 2 / printed 1); §1 online model (PDF 2); §6 indexing (PDF 14–15 / printed 13–14), eq. (55)

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

namespace OnlineRealSampling.Exact

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Algorithm 2: online sampling with randomness recycling (PDF 9 / printed 8) -/

/-- The persistent state `(t, Δ, Z, M)` of Algorithm 2: the only data kept between requests. -/
structure PState where
  t : ℕ
  Δ : ℕ
  Z : ℕ
  M : ℕ

/-- Line 1: `t ← 0, Δ ← 0, (Z, M) ← (0, 1)`. -/
def PState.init : PState := ⟨0, 0, 0, 1⟩

/-- Bits of persistent storage: the bit lengths of `t, Δ, Z, M`. -/
def PState.bits (p : PState) : ℕ := bitLen p.t + bitLen p.Δ + bitLen p.Z + bitLen p.M

/-- `D_j = 5000 j ⌈lg (j + 2)⌉`, the value of `Δ` when the counter is `j` ((55), PDF 15). -/
def Dval (j : ℕ) : ℕ := 5000 * j * Nat.clog 2 (j + 2)

/-- The counter `t` of Algorithm 2 after the update of iteration `i` (lines 3–4); `tSched ε 0 = 0`. -/
def tSched (ε : ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if ε * (tSched ε n : ℝ) < 0.1 then tSched ε n + 1 else tSched ε n

/-- `Δ_i`, the value of `Δ` used in iteration `i ≥ 1` of Algorithm 2. -/
def deltaSched (ε : ℝ) (i : ℕ) : ℕ := Dval (tSched ε i)

section Online

variable (w : ℕ)

/-- Lines 3–5 of Algorithm 2: if `ε t < 0.1` then `t ← t + 1` and `Δ ← 5000 t ⌈lg (t + 2)⌉`.
Returns the new `(t, Δ)`. -/
def schedule (ε : ℝ) (p : PState) : Charged (ℕ × ℕ) :=
  if ε * (p.t : ℝ) < 0.1 then do
    let t' ← addZ w p.t 1
    let c ← ceilLog2Ratio w (t' + 2) 1
    let d1 ← mulZ w 5000 t'
    let d ← mulZ w d1 c
    pure (t'.toNat, d.toNat)
  else pure (p.t, p.Δ)

/-- What one iteration of Algorithm 2 produces: the emitted `X`, the Sample call, the persistent
state after the iteration, and the resources of the whole iteration (update of `t, Δ`, then
Sample; the storage counts the persistent registers `t, Δ` alongside Sample's workspace). -/
structure IterRecord where
  X : ℕ
  sample : SampleOut
  after : PState
  usage : Usage

/-- One iteration of Algorithm 2 (lines 3–8) with target oracle `O`, from persistent state `p`,
on the fair-bit stream `ω` (the bits not yet consumed). `none` if Sample never halts. -/
def iteration (ε : ℝ) (O : OracleAccess) (p : PState) (ω : ℕ → Bool) : Option IterRecord :=
  let pre := schedule w ε p
  match sampleRun w O p.Z p.M pre.val.2 ω with
  | none => none
  | some out =>
    let after : PState := ⟨pre.val.1, pre.val.2, out.Z', out.M'⟩
    some
      { X := out.X, sample := out, after := after,
        usage :=
          { bits := out.usage.bits
            time := out.usage.time + pre.led.time + 1
            calls := out.usage.calls
            ops := out.usage.ops + pre.led.ops
            maxBits := max out.usage.maxBits pre.led.maxBits
            space := out.usage.space + bitLen after.t + bitLen after.Δ + pre.led.maxBits } }

/-- The state of Algorithm 2 after some iterations: persistent state, number of fresh bits
consumed so far (`T_n`), and the records of the iterations so far. -/
structure OnlineState where
  ps : PState
  pos : ℕ
  recs : List IterRecord

/-- The first `n` iterations of Algorithm 2 against the adaptive target rule `orc`, which maps
the public history `[X₁, …, X_{i-1}]` to the oracle of the `i`-th request. Each iteration reads
the fair bits after the ones already consumed. `none` if some iteration never halts. -/
def onlineRun (ε : ℝ) (orc : List ℕ → OracleAccess) (ω : ℕ → Bool) : ℕ → Option OnlineState
  | 0 => some ⟨PState.init, 0, []⟩
  | n + 1 =>
    match onlineRun ε orc ω n with
    | none => none
    | some st =>
      match iteration w ε (orc (st.recs.map (·.X))) st.ps (fun j => ω (st.pos + j)) with
      | none => none
      | some rec => some ⟨rec.after, st.pos + rec.usage.bits, st.recs ++ [rec]⟩

/-! ## Adaptive environments with external randomness -/

/-- The joint law of the external randomness `ξ ∼ μ` of the environment and the fair bits,
independent of each other. -/
def onlineMeasure {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) : Measure (Ξ × (ℕ → Bool)) :=
  μ.prod coinMeasure

/-- An environment `env : Ξ → List ℕ → CDFOracle` chooses the `i`-th target oracle from its
external randomness `ξ` and the public history `[X₁, …, X_{i-1}]` only: it never sees the
sampler's state or the fair bits. Admissibility: every oracle it can produce is valid, and the
choice is measurable in `ξ` (the CDF values, oracle answers and evaluation costs). -/
structure AdmissibleEnv {Ξ : Type} [MeasurableSpace Ξ] (env : Ξ → List ℕ → CDFOracle) : Prop where
  valid : ∀ ξ h, (env ξ h).Valid
  meas_F : ∀ h x, Measurable (fun ξ => (env ξ h).F x)
  meas_φ : ∀ h x k, Measurable (fun ξ => (env ξ h).φ x k)
  meas_cost : ∀ h x k, Measurable (fun ξ => (env ξ h).cost x k)

/-- The outputs `[X₁, …, X_n]` of the first `n` iterations with the oracle rule `env ξ`. -/
def outputs {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle) (ξ : Ξ) (ω : ℕ → Bool) (n : ℕ) :
    Option (List ℕ) :=
  (onlineRun w ε (fun h => (env ξ h).toOracleAccess) ω n).map (fun st => st.recs.map (·.X))

/-- The record of iteration `i ≥ 1` on the outcome `(ξ, ω)`, if the first `i` iterations halt. -/
def record {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle) (i : ℕ) (p : Ξ × (ℕ → Bool)) :
    Option IterRecord :=
  (onlineRun w ε (fun h => (env p.1 h).toOracleAccess) p.2 i).bind (fun st => st.recs.getLast?)

/-- The surprisal `∑_{i ≤ n} lg (1 / f_i(X_i))` of an output history `xs`, where `f_i` is the
PMF of the oracle chosen after the history `xs.take (i-1)`. (Zero-mass outputs occur with
probability zero.) -/
def surprisal {Ξ : Type} (env : Ξ → List ℕ → CDFOracle) (ξ : Ξ) (xs : List ℕ) : ℝ :=
  ∑ i ∈ Finset.range xs.length, lg (1 / pmf (env ξ (xs.take i)).F (xs.getD i 0))

/-- The centered variable `T_n - ∑_{i ≤ n} lg (1 / f_i(X_i))` of (3) (`0` off the event that the
first `n` iterations halt). -/
def lossVar {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle) (n : ℕ) (p : Ξ × (ℕ → Bool)) : ℝ :=
  match onlineRun w ε (fun h => (env p.1 h).toOracleAccess) p.2 n with
  | none => 0
  | some st => (st.pos : ℝ) - surprisal env p.1 (st.recs.map (·.X))

/-- The entropy loss `L_n = E[T_n - ∑_{i ≤ n} lg (1 / f_i(X_i))]` of (3), the expectation of the
centered variable (meaningful when `lossVar` is integrable). -/
def entropyLoss {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) (ε : ℝ)
    (env : Ξ → List ℕ → CDFOracle) (n : ℕ) : ℝ :=
  ∫ p, lossVar w ε env n p ∂(onlineMeasure μ)

/-! ## Per-iteration observables -/

/-- A resource of iteration `i`, as an extended nonnegative number (`⊤` if one of the first `i`
iterations never halts). -/
def iterResource {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle) (f : IterRecord → ℕ) (i : ℕ)
    (p : Ξ × (ℕ → Bool)) : ℝ≥0∞ :=
  match record w ε env i p with
  | some r => (f r : ℝ≥0∞)
  | none => ⊤

/-- The output `X_i` (`none` if one of the first `i` iterations never halts). -/
def iterOutput {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle) (i : ℕ) (p : Ξ × (ℕ → Bool)) :
    Option ℕ :=
  (record w ε env i p).map (·.X)

/-- `log X_i` with the clamped logarithm (`log 0 = 1` on the null event of non-termination). -/
def logOutput {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle) (i : ℕ) (p : Ξ × (ℕ → Bool)) :
    ℝ≥0∞ :=
  ENNReal.ofReal (slog ((iterOutput w ε env i p).getD 0 : ℝ))

/-- The public history `[X₁, …, X_{i-1}]` before iteration `i`. -/
def history {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle) (i : ℕ) (p : Ξ × (ℕ → Bool)) :
    List ℕ :=
  (outputs w ε env p.1 p.2 (i - 1)).getD []

/-- The quantity `C_i(X_i, i) + log(X_i) · C_i(X_i, X_i)` of clause 1.2.5, where `C_i = Cb ξ hist`
is the cost function of the `i`-th oracle (`0` on the null event of non-termination). -/
def iterCostTerm {Ξ : Type} (ε : ℝ) (env : Ξ → List ℕ → CDFOracle)
    (Cb : Ξ → List ℕ → ℝ → ℝ → ℝ) (i : ℕ) (p : Ξ × (ℕ → Bool)) : ℝ≥0∞ :=
  match iterOutput w ε env i p with
  | some x => ENNReal.ofReal (Cb p.1 (history w ε env i p) x i +
      slog x * Cb p.1 (history w ε env i p) x x)
  | none => 0

end Online

end

end OnlineRealSampling.Exact


