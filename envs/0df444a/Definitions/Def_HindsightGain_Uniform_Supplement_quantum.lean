-- Prove2me | Definitions.Def_HindsightGain_Uniform_Supplement_quantum
-- name    : HindsightGain_Uniform_Supplement_quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:55.427206+00:00
-- url     : https://prove2.me/theorems/e1e7519d-8f76-4263-be4f-b54d6c702e54
-- title:
--   Local Hamiltonians, ground-state energy and minimum product-state energy
-- statement:
--   Consider $n$ particles, each with state space $\mathbb C^d$, and the global space $(\mathbb C^d)^{\otimes n}$. A local term $h_e$ is a matrix on the space of the particles of $e\subseteq[n]$, extended by identities on the other particles; there is at most one term per subset. For $U\subseteq[n]$, $H_U=\sum_{e\subseteq U}h_e$. The **ground-state energy** is
--   $$E_0(H)=\lambda_{\min}(H)=\min_{\|v\|=1}\langle v,Hv\rangle,$$
--   over all unit vectors, including entangled states. The **minimum product-state energy** is
--   $$P(H_U)=\min_{\psi_i\in\mathbb C^d,\ \|\psi_i\|=1}\ \sum_{e\subseteq U}\mathrm{tr}\Big(h_e\bigotimes_{i\in e}\psi_i\psi_i^*\Big).$$
--   A matrix has operator norm at most one if $\|Av\|\le\|v\|$ for all $v$.
--
--   These are the energies of Section 7 and Theorem 6.
--
--   **Formalization Note** Basis vectors of the global space are labelings $[n]\to[d]$, which fixes the tensor factor order canonically. $H_U$ acts on the whole $n$-particle space (with identities outside $U$), which has the same minimum eigenvalue as $H_U$ on the particles of $U$; for $U=\emptyset$ it is $0$. Product states are chosen for all particles; those outside $U$ do not affect the value.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §1.3 p.8, §7 pp.28-31 eq. (37)

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_subsets

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Classical

namespace HindsightGain.Uniform.Supplement

/-- Basis labels of the particles in `e`, each of local dimension `d`; the space of `e` is
`ℂ^{d^{|e|}}` with basis indexed by these labels. -/
abbrev LocalConfig {n : ℕ} (e : Finset (Fin n)) (d : ℕ) : Type := {i // i ∈ e} → Fin d

/-- A local term `h_e` acting on the particles of `e`, tensored with identities on the remaining
particles of the `n`-particle space `(ℂ^d)^{⊗n}` (basis indexed by `Fin n → Fin d`). -/
def embed {n d : ℕ} (e : Finset (Fin n)) (he : Matrix (LocalConfig e d) (LocalConfig e d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun x y => if ∀ i, i ∉ e → x i = y i then he (fun i => x i) (fun i => y i) else 0

/-- `H_U = Σ_{e ⊆ U} h_e`, with at most one term per subset (absent terms are zero). -/
def restrictHam {n d : ℕ} (h : (e : Finset (Fin n)) → Matrix (LocalConfig e d) (LocalConfig e d) ℂ)
    (U : Finset (Fin n)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ e ∈ U.powerset, embed e (h e)

/-- `‖A‖_op ≤ 1` for a square complex matrix (Euclidean norms). -/
def OpNormLeOne {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, ∑ x, ‖(A *ᵥ v) x‖ ^ 2 ≤ ∑ x, ‖v x‖ ^ 2

/-- `E_0(H) = λ_min(H)` for Hermitian `H`, as the minimum of `⟨v, H v⟩` over all unit vectors
(entangled states allowed). -/
def groundEnergy {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) : ℝ :=
  ⨅ v : {v : ι → ℂ // ∑ x, ‖v x‖ ^ 2 = 1}, (star v.1 ⬝ᵥ (H *ᵥ v.1)).re

/-- The product vector `⊗_{i ∈ e} ψ_i` in the space of the particles of `e`. -/
def prodVec {n d : ℕ} (ψ : Fin n → Fin d → ℂ) (e : Finset (Fin n)) : LocalConfig e d → ℂ :=
  fun x => ∏ i : {i // i ∈ e}, ψ i (x i)

/-- Equation (37): `P(H_U)`, the minimum over pure product states `ρ_i = ψ_i ψ_i^*`, `‖ψ_i‖ = 1`,
of `Σ_{e ⊆ U} tr(h_e ⊗_{i∈e} ρ_i)`. -/
def productEnergy {n d : ℕ}
    (h : (e : Finset (Fin n)) → Matrix (LocalConfig e d) (LocalConfig e d) ℂ)
    (U : Finset (Fin n)) : ℝ :=
  ⨅ ψ : {ψ : Fin n → Fin d → ℂ // ∀ i, ∑ a, ‖ψ i a‖ ^ 2 = 1},
    ∑ e ∈ U.powerset, (star (prodVec ψ.1 e) ⬝ᵥ (h e *ᵥ prodVec ψ.1 e)).re

end HindsightGain.Uniform.Supplement


