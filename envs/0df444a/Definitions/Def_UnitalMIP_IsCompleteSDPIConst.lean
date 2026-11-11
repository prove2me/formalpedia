-- Prove2me | Definitions.Def_UnitalMIP_IsCompleteSDPIConst
-- name    : UnitalMIP_IsCompleteSDPIConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:40:54.572835+00:00
-- url     : https://prove2.me/theorems/35beb5ff-4a6f-48d5-982d-8844777e1fb5
-- title:
--   Complete-SDPI constant of a two-qubit state; the map $\Pi(X)=\tau_2(X)\mathbb 1$
-- statement:
--   Let $\Pi(X)=\tau_2(X)\mathbb 1$. A number $\alpha$ is a **complete-SDPI constant** of the two-qubit state $\psi$ if, for every canonical form $\psi_{\boldsymbol\lambda}=(U_A\otimes U_B)\psi(U_A\otimes U_B)^\dagger$ of $\psi$ with correlation channel $\mathcal K_{\psi_{\boldsymbol\lambda}}$, every $m\ge1$ and every density matrix $\rho\in M_m\otimes M_2$,
--
--   $$
--   D\bigl((\mathrm{id}_{M_m}\otimes\mathcal K_{\psi_{\boldsymbol\lambda}})(\rho)\,\big\|\,(\mathrm{id}_{M_m}\otimes\Pi)(\rho)\bigr)\le\alpha\,D\bigl(\rho\,\big\|\,(\mathrm{id}_{M_m}\otimes\Pi)(\rho)\bigr).
--   $$
--
--   Lemma 4.1 provides such a constant below $1$ when $\rho_{\max}(\psi)<1$; it controls the cost of smoothing in Theorem 3.2.
--
--   Here $D(\rho\|\sigma)=\mathrm{Tr}(\rho(\log\rho-\log\sigma))$ is the quantum relative entropy with the natural logarithm, $+\infty$ unless $\mathrm{supp}\,\rho\subseteq\mathrm{supp}\,\sigma$.
--
--   **Formalization Note** $\mathrm{id}\otimes\Phi$ is the published `QAlgorithms.idTensorSuperop` (ancilla first); $D$ is the published `LindenReversibility.relEntropy` (natural logarithm, valued in $[0,\infty]$, exact on density matrices), and the constant enters as `ENNReal.ofReal α`. The right side is finite. The constant is required for every canonical form of $\psi$ (they differ by local unitaries, which leave the inequality invariant).
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Lemma 4.1, p.32; §2.1, (5), p.10; Definition 2.9, p.13

import Mathlib
import Definitions.Def_LindenReversibility_relEntropy
import Definitions.Def_UnitalMIP_canonicalState

open scoped Matrix ENNReal

namespace UnitalMIP

/-- The map `Π(X) := τ₂(X)𝟙` on `M₂` (arXiv:2609.39318, version of 2026-11-03, Definition 2.9, p.13;
Lemma 4.1, p.32). -/
noncomputable def piMap : QAlgorithms.Superop (Fin 2) (Fin 2) :=
  fun X => ntr X • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- `α` is a **complete-SDPI constant** of the two-qubit state `ψ` (arXiv:2609.39318, version of
2026-11-03, sha256 56ebc59e…, Lemma 4.1, p.32): for every canonical form `ψ_λ` of `ψ` (single-qubit
unitaries `U_A`, `U_B` and real `λ` with `λ₀ = 1` and `(U_A ⊗ U_B)ψ(U_A ⊗ U_B)† = ψ_λ`), every
ancilla dimension `m ≥ 1` and every density matrix `ρ ∈ M_m ⊗ M₂`,
`D((id_{M_m} ⊗ K_{ψ_λ})(ρ) ‖ (id_{M_m} ⊗ Π)(ρ)) ≤ α · D(ρ ‖ (id_{M_m} ⊗ Π)(ρ))`.

**Formalization Note** `id_{M_m} ⊗ Φ` is the published `QAlgorithms.idTensorSuperop` (ancilla
first); the ancilla is `Fin m`. `D` is the published `LindenReversibility.relEntropy` (natural
logarithm, `+∞` off support, valued in `ℝ≥0∞`, which loses nothing on the density matrices to which
it is applied here); the constant enters as `ENNReal.ofReal α`. The right side is finite, because
`(id ⊗ Π)(ρ) = ρ_m ⊗ 𝟙/2` has support containing that of `ρ`. The constant is required to work for
every canonical form of `ψ`: two canonical forms differ by local unitaries, under which the
inequality is invariant, so this is the constant "depending only on ψ" of Lemma 4.1. -/
def IsCompleteSDPIConst (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (α : ℝ) : Prop :=
  ∀ (lam : Fin 2 × Fin 2 → ℝ) (UA UB : Matrix (Fin 2) (Fin 2) ℂ),
    UA ∈ Matrix.unitaryGroup (Fin 2) ℂ → UB ∈ Matrix.unitaryGroup (Fin 2) ℂ → lam 0 = 1 →
    Matrix.kronecker UA UB * ψ * (Matrix.kronecker UA UB)ᴴ = canonicalState lam →
    ∀ (m : ℕ), 1 ≤ m → ∀ ρ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ,
      QAlgorithms.IsDensityMatrix ρ →
        LindenReversibility.relEntropy
            (QAlgorithms.idTensorSuperop (corrChannel (canonicalState lam)) ρ)
            (QAlgorithms.idTensorSuperop piMap ρ) ≤
          ENNReal.ofReal α * LindenReversibility.relEntropy ρ (QAlgorithms.idTensorSuperop piMap ρ)

end UnitalMIP


