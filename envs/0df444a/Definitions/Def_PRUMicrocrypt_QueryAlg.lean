-- Prove2me | Definitions.Def_PRUMicrocrypt_QueryAlg
-- name    : PRUMicrocrypt_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:37.288985+00:00
-- url     : https://prove2.me/theorems/3a1d74eb-e74f-4b1f-8340-82e1707ac9d1
-- title:
--   Query algorithms in the model of Section 3 and their trajectories (3.18)
-- statement:
--   A **$t$-query algorithm** in the model of Section 3 acts on a selector register $\mathbb C^5$, the $n$-qubit query register and an arbitrary finite reference register $\mathcal W$. It is given by a unit initial vector $|\psi_0\rangle$ and inter-query unitaries $A_1,\dots,A_t$. With oracle $U$ its states are
--
--   $$|\psi_0(U)\rangle=|\psi_0\rangle,\qquad |\psi_j(U)\rangle=(\mathrm{Select}(U)\otimes I_{\mathcal W})\,A_j\,|\psi_{j-1}(U)\rangle\quad(1\le j\le t),$$
--
--   and $\rho^U_j=|\psi_j(U)\rangle\langle\psi_j(U)|$. With a final two-outcome measurement given by an effect $0\le E\le I$, the acceptance probability is $\Pr[A^U=1]=\langle\psi_t(U)|E|\psi_t(U)\rangle$. The module also defines the uniform average $\mathbb E_S$ over five-table samples and the generic trajectory $x_0,\ x_{i+1}=F_i(x_i)$ of a sequence of maps.
--
--   These are the algorithms of Theorem 4.1 and Theorem H.2.
--
--   **Formalization Note** The paper's inter-query isometries between growing spaces are represented by unitaries on one fixed finite space (ancillas are part of $|\psi_0\rangle$, and an isometry on the reachable subspace extends to a unitary). In Lean `A j` is $A_{j+1}$.
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), (3.18), p.23; Theorem 4.1, p.24

import Mathlib
import Definitions.Def_PRUMicrocrypt_phaseHadamardU

set_option autoImplicit false

namespace PRUMicrocrypt

open Matrix
open scoped ComplexOrder

/-- The trajectory `x₀, x₁ = F₀ x₀, x₂ = F₁ x₁, …` of a sequence of maps: `trajectory F x₀ 0 = x₀`
and `trajectory F x₀ (i + 1) = F i (trajectory F x₀ i)`. Used for the recurrences (3.18) and for
`|K_i⟩ = M_i|K_{i−1}⟩`, `|Φ_i⟩ = U_i|Φ_{i−1}⟩` in Lemma H.1 (with the paper's step `i + 1` stored
at index `i`).
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), (3.18), p.23; Lemma H.1, p.81. -/
def trajectory {X : Type*} (F : ℕ → X → X) (x₀ : X) : ℕ → X
  | 0 => x₀
  | i + 1 => F i (trajectory F x₀ i)

/-- The accessible registers of a query algorithm in the model of Section 3: the selector
`ℂ⁵`, the `n`-qubit query register, and an arbitrary finite reference/workspace `W`. -/
abbrev Acc (n : ℕ) (W : Type*) := Fin 5 × Idx n × W

/-- **A `t`-query algorithm in the model of Section 3** (§3.1–3.2, pp.21–23; Theorem 4.1, p.24):
a unit initial vector `|ψ₀⟩` on selector ⊗ query ⊗ reference and inter-query operations
`A₁, …, A_t` on the same space.
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), (3.18), p.23.

**Formalization Note.** The paper's inter-query isometries between growing spaces are represented
by unitaries on one fixed finite space `ℂ⁵ ⊗ ℂᴺ ⊗ ℂ^W` (ancillas are part of `|ψ₀⟩`, and an
isometry defined on the reachable subspace extends to a unitary); `W` is arbitrary. `A j` is the
paper's `A_{j+1}`. The selector is `ℂ⁵` with `P_a = |a⟩⟨a|` (see `selectOp`). -/
structure QueryAlg (n t : ℕ) (W : Type*) [Fintype W] [DecidableEq W] where
  /-- The initial state `|ψ₀⟩`. -/
  ψ₀ : Acc n W → ℂ
  /-- `|ψ₀⟩` is a unit vector. -/
  unit : ∑ i, Complex.normSq (ψ₀ i) = 1
  /-- The inter-query operations; `A j` is the paper's `A_{j+1}`. -/
  A : Fin t → Matrix.unitaryGroup (Acc n W) ℂ

/-- `Select(U) ⊗ I_W` on selector ⊗ query ⊗ reference. -/
noncomputable def selectAcc {n : ℕ} {W : Type*} [DecidableEq W] (U : Matrix (Idx n) (Idx n) ℂ) :
    Matrix (Acc n W) (Acc n W) ℂ :=
  fun p q => if p.2.2 = q.2.2 then selectOp U (p.1, p.2.1) (q.1, q.2.1) else 0

/-- The `j`-th inter-query operation, extended by the identity for `j ≥ t` (never used there). -/
noncomputable def QueryAlg.op {n t : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (alg : QueryAlg n t W) (j : ℕ) : Matrix (Acc n W) (Acc n W) ℂ :=
  if h : j < t then (alg.A ⟨j, h⟩ : Matrix (Acc n W) (Acc n W) ℂ) else 1

/-- **The physical trajectory** (3.18): `|ψ₀(U)⟩ = |ψ₀⟩`, `|ψ_j(U)⟩ = U A_j |ψ_{j−1}(U)⟩`, where
the query `U` is the coherent interface `Select(U) ⊗ I_W`. `alg.state U j` is `|ψ_j(U)⟩`.
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), (3.18), p.23. -/
noncomputable def QueryAlg.state {n t : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (alg : QueryAlg n t W) (U : Matrix (Idx n) (Idx n) ℂ) : ℕ → (Acc n W → ℂ) :=
  trajectory (fun j ψ => (selectAcc U * alg.op j) *ᵥ ψ) alg.ψ₀

/-- The density matrix `ρ^U_j = |ψ_j(U)⟩⟨ψ_j(U)|` (3.18). -/
noncomputable def QueryAlg.rho {n t : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (alg : QueryAlg n t W) (U : Matrix (Idx n) (Idx n) ℂ) (j : ℕ) :
    Matrix (Acc n W) (Acc n W) ℂ :=
  Matrix.vecMulVec (alg.state U j) (star (alg.state U j))

/-- An effect (two-outcome POVM element) `0 ≤ E ≤ I`. -/
def IsEffect {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Matrix ι ι ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

/-- `Pr[A^U = 1]`: the probability that the final measurement `{E, I − E}` of the algorithm
outputs `1` after its `t` queries to `U`, i.e. `⟨ψ_t(U)|E|ψ_t(U)⟩`.

**Formalization Note.** A final two-outcome measurement is an effect `E` (by Naimark's theorem
this covers every final measurement, including measuring an output qubit). -/
noncomputable def QueryAlg.accept {n t : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (alg : QueryAlg n t W) (E : Matrix (Acc n W) (Acc n W) ℂ) (U : Matrix (Idx n) (Idx n) ℂ) :
    ℝ :=
  (star (alg.state U t) ⬝ᵥ (E *ᵥ alg.state U t)).re

/-- The average `E_S[f(S)]` over a uniform sample `S = (h₁, …, h₅)` of five independent uniform
phase tables. -/
noncomputable def tableAvg (n : ℕ) (f : Tables n → ℝ) : ℝ :=
  (Fintype.card (Tables n) : ℝ)⁻¹ * ∑ S : Tables n, f S

end PRUMicrocrypt


