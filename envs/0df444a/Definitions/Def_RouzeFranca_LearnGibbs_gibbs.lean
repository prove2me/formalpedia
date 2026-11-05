-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_gibbs
-- name    : RouzeFranca_LearnGibbs_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:02.017495+00:00
-- url     : https://prove2.me/theorems/54040986-ba46-43a3-b905-9e9063260400
-- title:
--   The Gibbs family $\sigma(\mu)=e^{-\beta H(\mu)}/\mathcal Z(\mu)$, $\log\mathcal Z$, $e(\mu)$ and the ball $B_{\ell_\infty}(0,1)$
-- statement:
--   Let $E_1,\dots,E_m$ be operators on $n$ qubits, i.e. $2^n\times 2^n$ complex matrices indexed by bit strings $x\in\{0,1\}^n$, and let $\beta\in\mathbb R$. For a parameter vector $\mu\in\mathbb R^m$ define
--
--   1. the **Hamiltonian** $H(\mu)=\sum_{i=1}^m\mu_iE_i$;
--   2. the **partition function** $\mathcal Z(\mu)=\operatorname{tr}\bigl[e^{-\beta H(\mu)}\bigr]$;
--   3. the **Gibbs state**
--   $$
--   \sigma(\mu)=\frac{e^{-\beta H(\mu)}}{\mathcal Z(\mu)};
--   $$
--   4. the **log-partition function** $\mu\mapsto\log\mathcal Z(\mu)$ (natural logarithm);
--   5. the **expectation vector** $e(\mu)=\bigl(\operatorname{tr}[E_i\,\sigma(\mu)]\bigr)_{i=1}^m\in\mathbb R^m$;
--   6. the **unit ball of the sup norm** $B_{\ell_\infty}(0,1)=\{\mu\in\mathbb R^m:\ |\mu_i|\le 1\ \text{for all } i\}$.
--
--   When the $E_i$ are Hermitian, $H(\mu)$ is Hermitian, $\mathcal Z(\mu)>0$ and $\sigma(\mu)$ is a full-rank density operator. These are the objects of Definition A.1: the unknown state of the learning problem is $\sigma(\lambda)$ for some $\lambda\in B_{\ell_\infty}(0,1)$.
--
--   **Formalization Note** The matrix exponential is the continuous functional calculus `cfc (fun x => Real.exp (-β * x))` of the Hermitian matrix $H(\mu)$; for non-Hermitian input `cfc` returns $0$, a case excluded by the Hermitian hypothesis of every theorem. $\mathcal Z$ and $e_i$ are real parts of traces, which are real here. $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`, so its norm is Euclidean; the ball $B_{\ell_\infty}(0,1)$ is written out coordinatewise. The restrictions of Definition A.1 ($\|\lambda\|_{\ell_\infty}\le1$, $\beta>0$, linear independence, $\|E_i\|_\infty\le1$) are hypotheses of the theorems, not part of the definition.
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, Definition A.1, Eq. (19), p. 14; Proposition A.2, p. 15 (e(λ)); Eq. (24), p. 15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open Matrix

namespace RouzeFranca.LearnGibbs

/-- Operators on `n` qubits: complex matrices indexed by the computational basis
`QAlgorithms.Qubits n = Fin n → Bool`, i.e. the paper's `M_{2^n}`.

Rouzé, Stilck França, *Learning quantum many-body systems from a few copies*,
arXiv:2107.03333v4, App. A, p. 14 (notation `M_{d^n}`, `d = 2`). -/
abbrev Mat (n : ℕ) : Type := Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ

/-- The Hamiltonian `H(μ) = ∑ᵢ μᵢ Eᵢ` of the parameter vector `μ ∈ ℝ^m`.

Rouzé, Stilck França, arXiv:2107.03333v4, Definition A.1 (Gibbs state with respect to
observables), Eq. (19), p. 14. -/
noncomputable def hamiltonian {n m : ℕ} (E : Fin m → Mat n) (μ : EuclideanSpace ℝ (Fin m)) :
    Mat n :=
  ∑ i, ((μ i : ℝ) : ℂ) • E i

/-- The partition function `Z(μ) = tr[exp(−β H(μ))]`.

Rouzé, Stilck França, arXiv:2107.03333v4, Definition A.1, Eq. (19), p. 14.

**Formalization Note.** The matrix exponential `exp(−β H)` is Mathlib's continuous functional
calculus `cfc (fun x => Real.exp (-β * x)) H` for the Hermitian matrix `H`; `Z` is the real part of
its trace (which is a positive real number when `H` is Hermitian). If `H` is not Hermitian, `cfc`
returns `0`; every theorem of the mission assumes the `Eᵢ` Hermitian, so this case never occurs. -/
noncomputable def partitionFn {n m : ℕ} (E : Fin m → Mat n) (β : ℝ)
    (μ : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (trace (cfc (fun x => Real.exp (-β * x)) (hamiltonian E μ))).re

/-- The Gibbs state `σ(μ) = exp(−β ∑ᵢ μᵢ Eᵢ) / Z(μ)` at inverse temperature `β`.

Rouzé, Stilck França, arXiv:2107.03333v4, Definition A.1 (Gibbs state with respect to
observables), Eq. (19), p. 14: "σ = exp(−β Σ_{i=1}^m λ_i E_i)/Z(λ)".

**Formalization Note.** Defined for every `μ ∈ ℝ^m`; the paper's restriction `‖λ‖_ℓ∞ ≤ 1`, the
linear independence of the `Eᵢ`, `‖Eᵢ‖∞ ≤ 1` and `β > 0` are hypotheses of the theorems that need
them, not part of the definition. -/
noncomputable def gibbs {n m : ℕ} (E : Fin m → Mat n) (β : ℝ) (μ : EuclideanSpace ℝ (Fin m)) :
    Mat n :=
  (((partitionFn E β μ)⁻¹ : ℝ) : ℂ) • cfc (fun x => Real.exp (-β * x)) (hamiltonian E μ)

/-- The log-partition function `μ ↦ log Z(μ)`.

Rouzé, Stilck França, arXiv:2107.03333v4, §3.1, Eq. (16), p. 8, and Eq. (24), p. 15.
Natural logarithm. -/
noncomputable def logPartition {n m : ℕ} (E : Fin m → Mat n) (β : ℝ) :
    EuclideanSpace ℝ (Fin m) → ℝ :=
  fun μ => Real.log (partitionFn E β μ)

/-- The expectation vector `e(μ) = (tr[Eᵢ σ(μ)])ᵢ ∈ ℝ^m`.

Rouzé, Stilck França, arXiv:2107.03333v4, Proposition A.2, p. 15: "Denote
e(λ) = (tr[σ(λ)E_i])_i ∈ R^m".

**Formalization Note.** Lean records the real part of the trace; for Hermitian `Eᵢ` and the
Hermitian `σ(μ)` the trace is real. `tr[Eᵢ σ] = tr[σ Eᵢ]` by cyclicity. -/
noncomputable def expect {n m : ℕ} (E : Fin m → Mat n) (β : ℝ) (μ : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => (trace (E i * gibbs E β μ)).re)

/-- The unit ball of the sup norm, `B_ℓ∞(0, 1) = {μ ∈ ℝ^m : |μᵢ| ≤ 1 for all i}`.

Rouzé, Stilck França, arXiv:2107.03333v4, Definition A.1 (`‖λ‖_ℓ∞ ≤ 1`), p. 14, and Theorem C.1
(Fast learning of Gibbs states), p. 26 ("L, U strongly convex in B_ℓ∞(0, 1)").

**Formalization Note.** This is the ℓ∞ ball; it is not `Metric.closedBall 0 1`, which on
`EuclideanSpace` is the ℓ² ball. -/
def supBall (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {μ | ∀ i, |μ i| ≤ 1}

end RouzeFranca.LearnGibbs


