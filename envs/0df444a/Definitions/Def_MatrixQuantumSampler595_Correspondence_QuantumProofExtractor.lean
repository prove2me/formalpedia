-- Prove2me | Definitions.Def_MatrixQuantumSampler595_Correspondence_QuantumProofExtractor
-- name    : MatrixQuantumSampler595_Correspondence_QuantumProofExtractor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:48:04.19353+00:00
-- url     : https://prove2.me/theorems/1760b8a3-9726-4590-82d4-376c6e93ec54
-- title:
--   Definition 1.4 — strong and weak bounded-storage quantum-proof extractors
-- statement:
--   Let $F:\{0,1\}^n\times[t]\to\{0,1\}^m$. A **classical–quantum (cq) source** with quantum register $E=\mathbb C^q$ is a family of positive semidefinite matrices $(\sigma_x)_{x\in\{0,1\}^n}$ in $\mathbb C^{q\times q}$ with $\sum_x\operatorname{Tr}\sigma_x=1$; it represents
--   $$\rho_{XE}=\sum_x|x\rangle\langle x|\otimes\sigma_x,\qquad \Pr[X=x]=\operatorname{Tr}\sigma_x,\qquad \rho_E=\sum_x\sigma_x .$$
--   Its classical min-entropy satisfies $H_\infty(X)\ge k$ exactly when $\operatorname{Tr}\sigma_x\le2^{-k}$ for every $x$ ($k$ real).
--
--   With a uniform seed $I\in[t]$ independent of $XE$, the **actual strong output** $\rho_{F(X,I)IE}$ is block diagonal over $(z,i)\in\{0,1\}^m\times[t]$ with blocks $\frac1t\sum_{x:F(x,i)=z}\sigma_x$, and the **ideal strong output** $\tau_m\otimes\tau_{[t]}\otimes\rho_E$ has every block equal to $\frac{1}{t2^m}\rho_E$. Discarding the seed gives the **weak** states $\rho_{F(X,I)E}$, with blocks $\frac1t\sum_{(x,i):F(x,i)=z}\sigma_x$, and $\tau_m\otimes\rho_E$, with blocks $2^{-m}\rho_E$. The trace distance is $\Delta(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$, $\|A\|_1=\operatorname{Tr}\sqrt{A^*A}$.
--
--   For real $b,k,\eta$:
--   1. $F$ is a **strong $b$-qubit-proof $(k,\eta)$ extractor** if for every $q$ with $q\le2^b$ and every cq source with $H_\infty(X)\ge k$,
--   $$\Delta\bigl(\rho_{F(X,I)IE},\ \tau_m\otimes\tau_{[t]}\otimes\rho_E\bigr)\le\eta .$$
--   2. $F$ is a **weak $b$-qubit-proof $(k,\eta)$ extractor** if for every such $q$ and source,
--   $$\Delta\bigl(\rho_{F(X,I)E},\ \tau_m\otimes\rho_E\bigr)\le\eta .$$
--
--   These are the bounded-storage extractor predicates of the extractor–sampler correspondence (Theorem 1.5): the adversary holds a quantum register of dimension at most $2^b$, and the source is constrained only through the min-entropy of its classical marginal. The comparison state always uses the actual marginal $\rho_E$.
--
--   **Formalization Note** Normalized blocks, block-diagonal cq matrices and deterministic processing are the published `NormalizedBlocks`, `cqBlockMatrix`, `processBlocks` and `cqMarginal`; the trace distance is the published `QAlgorithms.traceDistance`. The register dimension ranges over all natural numbers $q$ with $q\le 2^b$ (real power), so $b=\log_2(2D)$ gives exactly $\dim E\le 2D$ without rounding to an integral number of qubits; $q=0$ admits no normalized source. The seed set $[t]$ is `Fin t`.
-- source:
--   Kuan Cheng, Ruiyang Wu, Matrix Samplers and Quantum-Proof Extractors: Their Correspondence and Almost-Optimal Constructions, STOC 2027 submission #595 (October 2026), Definition 1.4 and Eqs. (1.1)–(1.2), p.4; §2.2, p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02
import Definitions.Def_MatrixQuantumSampler595_Correspondence_MatrixSampler

namespace MatrixQuantumSampler595.Correspondence

open QAlgorithms.Papers.Independent.Advance50.P02
  (NormalizedBlocks cqMarginal cqBlockMatrix processBlocks)

/-- §2.2 (p.12): the classical marginal of the cq state `ρ_{XE} = ∑_x |x⟩⟨x| ⊗ σ_x`
satisfies `H_∞(X) ≥ k`, i.e. `Pr[X = x] = Tr σ_x ≤ 2^{-k}` for every `x`. -/
def MinEntropyAtLeast {X : Type} {q : ℕ} (σ : X → Matrix (Fin q) (Fin q) ℂ) (k : ℝ) :
    Prop :=
  ∀ x, (σ x).trace.re ≤ (2 : ℝ) ^ (-k)

/-- Eq. (1.2) (p.4): the actual state `ρ_{F(X,I) I E}` for a uniform seed `I ∈ [t]` independent
of the cq source with blocks `σ_x`; its `(z,i)` block is `(1/t) ∑_{x : F(x,i) = z} σ_x`. -/
noncomputable def strongOutputState {n m t q : ℕ} (F : BitString n → Fin t → BitString m)
    (σ : BitString n → Matrix (Fin q) (Fin q) ℂ) :
    Matrix ((BitString m × Fin t) × Fin q) ((BitString m × Fin t) × Fin q) ℂ :=
  cqBlockMatrix (processBlocks (fun p : BitString n × Fin t => (F p.1 p.2, p.2))
    (fun p : BitString n × Fin t => (t : ℂ)⁻¹ • σ p.1))

/-- Eq. (1.2) (p.4): the ideal state `τ_m ⊗ τ_{[t]} ⊗ ρ_E`, every `(z,i)` block equal to
`(1/(t 2^m)) ρ_E` with `ρ_E = ∑_x σ_x` the actual side-information marginal. -/
noncomputable def strongIdealState {n m t q : ℕ} (σ : BitString n → Matrix (Fin q) (Fin q) ℂ) :
    Matrix ((BitString m × Fin t) × Fin q) ((BitString m × Fin t) × Fin q) ℂ :=
  cqBlockMatrix (fun _ : BitString m × Fin t => ((t : ℂ) * (2 : ℂ) ^ m)⁻¹ • cqMarginal σ)

/-- Eq. (1.1) (p.4): the actual state `ρ_{F(X,I) E}` with the seed discarded; its `z` block
is `(1/t) ∑_{(x,i) : F(x,i) = z} σ_x`. -/
noncomputable def weakOutputState {n m t q : ℕ} (F : BitString n → Fin t → BitString m)
    (σ : BitString n → Matrix (Fin q) (Fin q) ℂ) :
    Matrix (BitString m × Fin q) (BitString m × Fin q) ℂ :=
  cqBlockMatrix (processBlocks (fun p : BitString n × Fin t => F p.1 p.2)
    (fun p : BitString n × Fin t => (t : ℂ)⁻¹ • σ p.1))

/-- Eq. (1.1) (p.4): the ideal state `τ_m ⊗ ρ_E`, every `z` block equal to `2^{-m} ρ_E`. -/
noncomputable def weakIdealState {n m q : ℕ} (σ : BitString n → Matrix (Fin q) (Fin q) ℂ) :
    Matrix (BitString m × Fin q) (BitString m × Fin q) ℂ :=
  cqBlockMatrix (fun _ : BitString m => ((2 : ℂ) ^ m)⁻¹ • cqMarginal σ)

/-- Definition 1.4 (p.4): `F` is a strong `b`-qubit-proof `(k, η)` extractor if Eq. (1.2),
`Δ(ρ_{F(X,I) I E}, τ_m ⊗ τ_{[t]} ⊗ ρ_E) ≤ η`, holds for every normalized cq state `ρ_{XE}`
with `H_∞(X) ≥ k` and `dim E ≤ 2^b`. The register `E` is `ℂ^q`, `q` any natural number with
`q ≤ 2^b`; `Δ(ρ,σ) = ½ ‖ρ - σ‖₁` is `QAlgorithms.traceDistance`. -/
def IsStrongQubitProofExtractor {n m t : ℕ} (F : BitString n → Fin t → BitString m)
    (b k η : ℝ) : Prop :=
  ∀ q : ℕ, (q : ℝ) ≤ (2 : ℝ) ^ b → ∀ σ : BitString n → Matrix (Fin q) (Fin q) ℂ,
    NormalizedBlocks σ → MinEntropyAtLeast σ k →
      QAlgorithms.traceDistance (strongOutputState F σ) (strongIdealState (m := m) (t := t) σ)
        ≤ η

/-- Definition 1.4 (p.4): `F` is a weak `b`-qubit-proof `(k, η)` extractor if Eq. (1.1),
`Δ(ρ_{F(X,I) E}, τ_m ⊗ ρ_E) ≤ η`, holds for every normalized cq state `ρ_{XE}` with
`H_∞(X) ≥ k` and `dim E ≤ 2^b`. -/
def IsWeakQubitProofExtractor {n m t : ℕ} (F : BitString n → Fin t → BitString m)
    (b k η : ℝ) : Prop :=
  ∀ q : ℕ, (q : ℝ) ≤ (2 : ℝ) ^ b → ∀ σ : BitString n → Matrix (Fin q) (Fin q) ℂ,
    NormalizedBlocks σ → MinEntropyAtLeast σ k →
      QAlgorithms.traceDistance (weakOutputState F σ) (weakIdealState (m := m) σ) ≤ η

end MatrixQuantumSampler595.Correspondence


