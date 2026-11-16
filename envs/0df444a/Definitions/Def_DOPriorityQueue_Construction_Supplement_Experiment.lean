-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_Supplement_Experiment
-- name    : DOPriorityQueue_Construction_Supplement_Experiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:39:32.409201+00:00
-- url     : https://prove2.me/theorems/fd23574d-7c7b-445b-8f22-0d2cfe7a5111
-- title:
--   §6.1 — normalized trace experiment and conditional entropy
-- statement:
--   Let $n\ge2$ and let $b_1,\ldots,b_n$ be distinct fixed tokens. Choose priorities $X_1,\ldots,X_n$ independently and uniformly from $[n]=\{1,\ldots,n\}$. The history $\sigma(X)$ first inserts $(X_i,b_i)$ in index order and then performs $n$ minimum extractions. Let $\Pi(X)$ list insertion indices in stable increasing order of $(X_i,i)$.
--
--   A trace kernel assigns a probability mass function to each operation history. It has no payload indivisibility, private-space, or computation restriction. Insertion-field privacy is defined using the published adjacency and queue domain. The joint experiment first chooses $X$ uniformly and then draws the call-grouped address/direction trace from the kernel. If $V$ denotes that trace,
--   $$H(\Pi\mid V)=\sum_v\Pr[V=v]H(\Pi\mid V=v),\qquad P(v)=\sum_j|v_j|.$$
--   The imported Shannon entropy is in bits. Null fibers have zero weight; $0\log0=0$. The expectation of $P$ is a nonnegative extended sum and may be infinite. The finite range of $\Pi$ makes its conditional entropy finite for every normalized law.
--
--   The information-loss parameter is
--   $$\gamma_n=\frac{\varepsilon+1}{\ln2}+\frac{\delta\log_2n}{1-e^{-1}}.$$
--   This interface gives Lemma 6.2 its full scope, including encoded payloads. Zero-based finite indices encode the source's one-based priorities by adding one. Token identities are semantic labels, not extra words accessible to a queue.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), pp. 28–30, equation (7), equations (8)–(15)

import Definitions.Def_DOPriorityQueue_Construction_Queue
import Definitions.Def_DOPriorityQueue_Construction_RAM
import Definitions.Def_SpanForestStream_Unrestricted_Info

set_option autoImplicit false

namespace DOPriorityQueue.Construction.Supplement

/-- General normalized trace mechanism. No token-routing or memory axiom occurs
here: Lemma 6.2 also applies to queues with jointly encoded payloads. -/
abbrev TraceKernel (w : ℕ) := List (Operation ℕ) → PMF (RAM.Trace w)

noncomputable def kernelEvent {w : ℕ} (K : TraceKernel w)
    (h : List (Operation ℕ)) (A : Set (RAM.Trace w)) : ENNReal :=
  SpanForestStream.Unrestricted.probOf (K h) A

noncomputable def insertionDO {w : ℕ} (K : TraceKernel w) (T U : ℕ) (ε δ : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ δ ≤ 1 ∧
  ∀ h h', validHistory T U h → validHistory T U h' → insertionNeighbors h h' →
    ∀ A : Set (RAM.Trace w),
      kernelEvent K h A ≤ ENNReal.ofReal (Real.exp ε) * kernelEvent K h' A + ENNReal.ofReal δ

/-- Equation (7). Fin indices are zero-based; actual priorities are i.val + 1. -/
def experimentHistory {n : ℕ} (b : Fin n → ℕ) (X : Fin n → Fin n) :
    List (Operation ℕ) :=
  (List.ofFn fun i => Operation.insert ((X i).val + 1) (b i)) ++
    List.replicate n Operation.extractMin

/-- Π is represented by its list of insertion indices in stable output order.
This is a permutation, not an arbitrary output supplied by the implementation. -/
def stablePermutation {n : ℕ} (X : Fin n → Fin n) : List (Fin n) :=
  (List.finRange n).mergeSort fun i j =>
    decide ((X i).val < (X j).val ∨ ((X i).val = (X j).val ∧ i.val ≤ j.val))

noncomputable def experimentLaw {n w : ℕ} (K : TraceKernel w) (b : Fin n → ℕ) :
    PMF ((Fin n → Fin n) × RAM.Trace w) := by
  classical
  letI : Nonempty (Fin n → Fin n) := ⟨id⟩
  exact (PMF.uniformOfFintype (Fin n → Fin n)).bind fun X =>
    (K (experimentHistory b X)).map fun v => (X, v)

/-- Countable trace conditioning; null fibers receive weight zero. The imported
entropy uses nonnegative extended sums, bits, and 0 log 0 = 0. -/
noncomputable def residualEntropy {n w : ℕ} (K : TraceKernel w) (b : Fin n → ℕ) :
    ENNReal :=
  let law := experimentLaw K b
  ∑' v : RAM.Trace w,
    (law.map Prod.snd) v *
      SpanForestStream.Unrestricted.entropyBits
        (SpanForestStream.Unrestricted.condLaw law Prod.snd
          (fun z => stablePermutation z.1) v)

def probeCount {w : ℕ} (v : RAM.Trace w) : ℕ := v.flatten.length

/-- Extended nonnegative expectation, including +∞ for unbounded probe cost. -/
noncomputable def expectedProbes {w : ℕ} (K : TraceKernel w)
    (h : List (Operation ℕ)) : ENNReal :=
  ∑' v : RAM.Trace w, K h v * (probeCount v : ENNReal)

noncomputable def mixedProbes {n w : ℕ} (K : TraceKernel w) (b : Fin n → ℕ) :
    ENNReal :=
  ∑' v : RAM.Trace w, ((experimentLaw K b).map Prod.snd) v * (probeCount v : ENNReal)

/-- Section 6.1: ln 2 in the first term is a natural logarithm. -/
noncomputable def gamma (n : ℕ) (ε δ : ℝ) : ℝ :=
  (ε + 1) / Real.log 2 + δ * Real.logb 2 n / (1 - Real.exp (-1))

end DOPriorityQueue.Construction.Supplement


