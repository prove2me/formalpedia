-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_averages
-- name    : MaxCutSample2027_Coreset_averages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:35.996659+00:00
-- url     : https://prove2.me/theorems/37af0b62-5244-4b31-ba89-2763846b72a8
-- title:
--   Finite probability vectors, samples, and independent sign averages
-- statement:
--   For a finite type $V$, a probability vector $r$ has $r_v\ge0$ and $\sum_v r_v=1$. A positive probability vector $p$ has $p_v>0$ and the same normalization. For $x:\{0,\ldots,k-1\}\to V$, set
--   $$P_x(v)=\frac{|\{i:x_i=v\}|}{k},\qquad w_p(x)=\prod_{i=0}^{k-1}p_{x_i},\qquad
--   \mathbb E_X f(X)=\sum_{x:V^k}w_p(x)f(x).$$
--   Boolean signs are $\varepsilon(\mathrm{false})=1$ and $\varepsilon(\mathrm{true})=-1$. Their average is
--   $$\mathbb E_\sigma h(\sigma)=2^{-k}\sum_{\sigma:\{0,\ldots,k-1\}\to\mathrm{Bool}}h(\sigma).$$
--   The joint average first averages signs and then two independent samples $X,Y$ with weights $w_p(x)w_p(y)$. Thus all $2k$ vertex draws and $k$ signs have exactly the independent product law stated in the source.
--
--   These are reusable finite probability operations, separate from the graph model. Claims involving empirical frequencies require $k\ge1$. At $k=0$, empirical frequencies are zero by total real division; the sample and sign averages each have one empty assignment. No theorem about normalized sample errors uses that case.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §2, p. 6; Lemma 2.7, p. 11; Appendix A.1–A.2, p. 33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Mathlib
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset

/-- Zero coordinates are allowed in a probability vector. -/
def IsProbabilityVector {V : Type*} [Fintype V] (r : V → ℝ) : Prop :=
  (∀ v, 0 ≤ r v) ∧ ∑ v, r v = 1

/-- The sampling law has full support. -/
def IsPositiveProbabilityVector {V : Type*} [Fintype V] (p : V → ℝ) : Prop :=
  (∀ v, 0 < p v) ∧ ∑ v, p v = 1

/-- Empirical frequencies of k draws with replacement; only k ≥ 1 is used. -/
def empirical {V : Type*} [DecidableEq V] {k : ℕ} (x : Fin k → V) (v : V) : ℝ :=
  ((Finset.univ.filter (fun i => x i = v)).card : ℝ) / (k : ℝ)

/-- Weight of one ordered sample under the product law. -/
def sampleWeight {V : Type*} {k : ℕ} (p : V → ℝ) (x : Fin k → V) : ℝ :=
  ∏ i, p (x i)

/-- Explicit finite expectation under k independent draws from p. -/
def sampleAverage {V : Type*} [Fintype V] (p : V → ℝ) (k : ℕ)
    (f : (Fin k → V) → ℝ) : ℝ :=
  ∑ x : Fin k → V, sampleWeight p x * f x

/-- false represents +1 and true represents -1. -/
def signValue (b : Bool) : ℝ := if b then -1 else 1

/-- Uniform expectation over the 2^k independent sign vectors. -/
def signAverage (k : ℕ) (f : (Fin k → Bool) → ℝ) : ℝ :=
  (∑ σ : Fin k → Bool, f σ) / (2 : ℝ) ^ k

/-- X, Y have independent law p^k, and the signs are independent and uniform. -/
def jointAverage {V : Type*} [Fintype V] (p : V → ℝ) (k : ℕ)
    (f : (Fin k → V) → (Fin k → V) → (Fin k → Bool) → ℝ) : ℝ :=
  sampleAverage p k (fun x => sampleAverage p k (fun y => signAverage k (f x y)))

end MaxCutSample2027.Coreset


