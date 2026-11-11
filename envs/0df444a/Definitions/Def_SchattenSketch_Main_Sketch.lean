-- Prove2me | Definitions.Def_SchattenSketch_Main_Sketch
-- name    : SchattenSketch_Main_Sketch
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:37.608172+00:00
-- url     : https://prove2.me/theorems/07d300c2-b575-4c25-b06f-c3d94527064f
-- title:
--   Randomized linear sketches of $n\times n$ matrices with measurable decoders, and the $(1\pm\varepsilon)$ guarantee (1.1)
-- statement:
--   A **randomized $k$-dimensional linear sketch** of real $n\times n$ matrices consists of
--
--   - a probability space $(\Omega,P)$ of random seeds $\omega$;
--   - a linear map $S_\omega:\mathbb R^{n\times n}\to\mathbb R^k$, chosen without seeing the input and depending measurably on $\omega$; it is stored as a $k\times n^2$ array whose row $r$ is a linear functional on the matrix space, so that $(S_\omega A)_r=\sum_{i,j}(S_\omega)_{r,(i,j)}A_{ij}$;
--   - a decoder $d_\omega:\mathbb R^k\to\mathbb R$ that may depend on the seed and is jointly measurable in $(\omega,y)$.
--
--   On input $A$ the sketch stores $S_\omega A$ and outputs $d_\omega(S_\omega A)$. The dimension $k$ counts real measurements; $k=0$ is allowed. Given a functional $\Phi$ on $\mathbb R^{n\times n}$ and $\varepsilon\in\mathbb R$, the sketch is **$(1\pm\varepsilon)$-valid for $\Phi$** if for every fixed matrix $A$
--   $$P_\omega\bigl\{(1-\varepsilon)\,\Phi(A)\le d_\omega(S_\omega A)\le(1+\varepsilon)\,\Phi(A)\bigr\}\ \ge\ \tfrac23 .$$
--   This is the "for each" guarantee (1.1) of the paper, for $\Phi$ the nuclear norm; Lemma 4.1 uses it for a general nonnegative measurable $\Phi$.
--
--   **Formalization Note.** `LinearSketch n k` bundles a seed type `Ω : Type`, a probability measure `P`, the measurable map `S : Ω → (Fin k → Fin n × Fin n → ℝ)` and the decoder `dec : Ω → (Fin k → ℝ) → ℝ` with `Function.uncurry dec` measurable. `sketchApply S A` is the measurement vector $S A$. The probability is compared in `ℝ≥0∞`.
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 4, (1.1) and the definition of k_ε(n); p. 13, §4.1

import Mathlib

open MeasureTheory

namespace SchattenSketch.Main

/-- The measurement vector `S A ∈ ℝ^k` of a linear map `S : ℝ^{n×n} → ℝ^k`, written as its
`k × n²` array: row `r` of `S` is a linear functional on the matrix space, and
`(S A)_r = ∑_{(i,j)} S_r(i,j) A_{ij}` (Frobenius pairing). Yang, arXiv:2608.22247, p. 4, (1.1),
and p. 13, §4.1. -/
def sketchApply {n k : ℕ} (S : Fin k → Fin n × Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Fin k → ℝ :=
  fun r => ∑ p : Fin n × Fin n, S r p * A p.1 p.2

/-- A randomized `k`-dimensional linear sketch of real `n × n` matrices (Yang, p. 4): a probability
space `(Ω, P)` of seeds, a measurable choice `ω ↦ S_ω` of a linear map `ℝ^{n×n} → ℝ^k`, and a
decoder `d_ω : ℝ^k → ℝ` that may depend on the seed and is jointly measurable in the seed and the
measurement vector. On input `A` the sketch outputs `d_ω (S_ω A)`. -/
structure LinearSketch (n k : ℕ) where
  /-- the seed space -/
  Ω : Type
  /-- its σ-algebra -/
  [mΩ : MeasurableSpace Ω]
  /-- the law of the seed -/
  P : Measure Ω
  /-- the law of the seed is a probability measure -/
  [isProb : IsProbabilityMeasure P]
  /-- the sampled linear map, as a `k × n²` matrix -/
  S : Ω → (Fin k → Fin n × Fin n → ℝ)
  /-- the sampled map depends measurably on the seed -/
  S_measurable : Measurable S
  /-- the decoder -/
  dec : Ω → (Fin k → ℝ) → ℝ
  /-- the decoder is jointly measurable in the seed and the measurement vector -/
  dec_measurable : Measurable (Function.uncurry dec)

attribute [instance] LinearSketch.mΩ LinearSketch.isProb

/-- The `(1 ± ε)` "for each" guarantee (1.1) of a sketch for a functional `Φ` (Yang, p. 4): for
every fixed input `A`, with probability at least `2/3` over the seed,
`(1 - ε) Φ(A) ≤ d_ω(S_ω A) ≤ (1 + ε) Φ(A)`. -/
def LinearSketch.IsValid {n k : ℕ} (sk : LinearSketch n k)
    (Φ : Matrix (Fin n) (Fin n) ℝ → ℝ) (ε : ℝ) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (2 / 3 : ENNReal) ≤
      sk.P {ω | (1 - ε) * Φ A ≤ sk.dec ω (sketchApply (sk.S ω) A) ∧
                sk.dec ω (sketchApply (sk.S ω) A) ≤ (1 + ε) * Φ A}

end SchattenSketch.Main


