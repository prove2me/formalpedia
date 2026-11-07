-- Prove2me | Definitions.Def_BetheKS_sbmProb
-- name    : BetheKS_sbmProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:50.399841+00:00
-- url     : https://prove2.me/theorems/5774f06f-5366-4a7b-97fa-402584ef706e
-- title:
--   The stochastic block model $\mathrm{SBM}_n(P,\pi)$ as a finite probability law on graphs
-- statement:
--   For a label map $\sigma:[n]\to[r]$, the random graph $G\sim\mathrm{SBM}_n(P,\pi)$ includes every pair $uv$ of distinct vertices independently, with probability $\frac1n P_{\sigma(u)\sigma(v)}$. The probability of an event $E$ is
--   $$
--   \mathbb P(G\in E)=\sum_{\omega}\ \prod_{\{u,v\}}p_{uv}^{\omega_{uv}}(1-p_{uv})^{1-\omega_{uv}}\ \mathbf 1\{G(\omega)\in E\},
--   $$
--   the sum running over all edge-indicator vectors $\omega\in\{0,1\}^{\binom{[n]}2}$, and the expectation of a function of the graph is defined likewise. The file also fixes the modes of convergence used throughout, all as $n\to\infty$ along $\mathcal N_\pi$ for a sequence of exact-size label maps $\sigma_n$: "with probability tending to one", convergence in probability $X_n\xrightarrow{\mathbb P}c$, and convergence in $L^2$, $\mathbb E|X_n-c|^2\to0$.
--
--   **Formalization Note** The edge probability is capped, $p_{uv}=\min\{1,P_{\sigma(u)\sigma(v)}/n\}$, which changes only finitely many $n$ and no limit statement. Labels are deterministic, as in the paper.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), §2.1, p.3–4 (steps 1–2)

import Mathlib
import Definitions.Def_BetheKS_SBMParams

set_option autoImplicit false

open Filter Topology

namespace BetheKS

variable {r : ℕ}

/-- Unordered pairs `{u, v}` of distinct vertices of `[n]`. -/
abbrev VPair (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- A sample of the edge indicators: which pairs `{u, v}` are edges. -/
abbrev EdgeSample (n : ℕ) := VPair n → Bool

/-- The graph on `[n]` whose edges are the pairs marked `true`. -/
def graphOf {n : ℕ} (ω : EdgeSample n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬ e.IsDiag, ω ⟨e, h⟩ = true}

/-- The edge probability `P_{σ(u)σ(v)}/n` of the pair `{u, v}` (§2.1, step 2, p.4), capped at `1`. -/
noncomputable def edgeProb (p : SBMParams r) {n : ℕ} (σ : Fin n → Fin r) (e : VPair n) : ℝ :=
  Sym2.lift ⟨fun u v => min 1 (p.P (σ u) (σ v) / n), fun u v => by
    simp only [p.P_symm.apply (σ u) (σ v)]⟩ e.1

/-- The probability of the edge sample `ω` under `SBMₙ(P, π)` with labels `σ`: the pairs are
independent, `{u, v}` being an edge with probability `edgeProb p σ {u,v}`. -/
noncomputable def sampleWeight (p : SBMParams r) {n : ℕ} (σ : Fin n → Fin r) (ω : EdgeSample n) : ℝ :=
  ∏ e, if ω e then edgeProb p σ e else 1 - edgeProb p σ e

/-- **The stochastic block model `SBMₙ(P, π)`** — Dong, McKenzie, arXiv:2610.41802 (held version,
sha256 4da41e16…), §2.1, p.3–4: for the label map `σ : [n] → [r]`, include each pair `uv`
independently with probability `P_{σ(u)σ(v)}/n`. `sbmProb p σ E` is the probability that the
random graph `G ∼ SBMₙ(P, π)` satisfies `E`.

**Formalization Note.** The probability space is the finite set of edge samples
`{pairs} → Bool` with the product weight `sampleWeight`; the graph is `graphOf ω`. For `n` below
`max P` the ratio `P/n` can exceed `1`; it is capped, `min 1 (P/n)`, which changes nothing in the
`n → ∞` statements of the paper. The labels `σ` are deterministic, as in the paper. -/
noncomputable def sbmProb (p : SBMParams r) {n : ℕ} (σ : Fin n → Fin r)
    (E : SimpleGraph (Fin n) → Prop) : ℝ :=
  ∑ ω : EdgeSample n, sampleWeight p σ ω * ({ω | E (graphOf ω)} : Set (EdgeSample n)).indicator 1 ω

/-- The expectation `E[Z(G)]` of a real function of `G ∼ SBMₙ(P, π)` with labels `σ`. -/
noncomputable def sbmExp (p : SBMParams r) {n : ℕ} (σ : Fin n → Fin r)
    (Z : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ ω : EdgeSample n, sampleWeight p σ ω * Z (graphOf ω)

/-- A sequence of label maps `σₙ` with the exact community sizes for every `n ∈ 𝒩_π`. -/
def IsExactSeq (p : SBMParams r) (σs : ∀ n : ℕ, Fin n → Fin r) : Prop :=
  ∀ n : ℕ, (∀ i, ∃ k : ℕ, p.pi i * n = k) → IsExactSize p (σs n)

/-- "With probability tending to one" along `𝒩_π`, for `Gₙ ∼ SBMₙ(P, π)` with labels `σₙ`. -/
def Whp (p : SBMParams r) (σs : ∀ n : ℕ, Fin n → Fin r)
    (E : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n => sbmProb p (σs n) (E n)) (sizeFilter p) (𝓝 1)

/-- Convergence in probability `Xₙ(Gₙ) →ᴾ c` along `𝒩_π`. -/
def ConvInProb (p : SBMParams r) (σs : ∀ n : ℕ, Fin n → Fin r)
    (X : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => sbmProb p (σs n) (fun G => ε < |X n G - c|)) (sizeFilter p) (𝓝 0)

/-- Convergence in `L²`, `E|Xₙ(Gₙ) − c|² → 0` along `𝒩_π`. -/
def ConvL2 (p : SBMParams r) (σs : ∀ n : ℕ, Fin n → Fin r)
    (X : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun n => sbmExp p (σs n) (fun G => (X n G - c) ^ 2)) (sizeFilter p) (𝓝 0)

end BetheKS


