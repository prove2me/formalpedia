-- Prove2me | Definitions.Def_DeFinettiSDP_Hierarchy_Problem
-- name    : DeFinettiSDP_Hierarchy_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:40.539725+00:00
-- url     : https://prove2.me/theorems/8970741e-fa34-4c80-967b-d86127bffedd
-- title:
--   Problems (2), (3), p. 1–2, and the hierarchy SDPₙ of Theorem 3.1, p. 11
-- statement:
--   This file defines the constrained bilinear program $Q$ and its semidefinite hierarchy.
--
--   Fix $G_{AB}\in\mathcal S_A\otimes\mathcal S_B$, linear maps $\Lambda_{A\to C_A}:\mathcal S_A\to\mathcal S_{C_A}$ and $\Gamma_{B\to C_B}:\mathcal S_B\to\mathcal S_{C_B}$, and matrices $X_{C_A}\in\mathcal S_{C_A}$, $Y_{C_B}\in\mathcal S_{C_B}$.
--
--   1. **The program (2)** (p. 1; restated in §3, p. 11):
--   $$Q=\max\ \mathrm{Tr}[G_{AB}(W_A\otimes W_B)]\quad\text{s.t. } W_A\succeq0,\ W_B\succeq0,\ \mathrm{Tr}W_A=\mathrm{Tr}W_B=1,\ \Lambda_{A\to C_A}(W_A)=X_{C_A},\ \Gamma_{B\to C_B}(W_B)=Y_{C_B}.$$
--   2. **The convexified program (3)** (p. 2): the same objective over mixtures $\sum_{i\in I}p_iW_A^i\otimes W_B^i$ of finitely many feasible product pairs, $p$ a probability vector.
--   3. **The hierarchy** (Theorem 3.1, p. 11): for $N$ copies of $B$,
--   $$\mathrm{SDP}_N=\max\ \mathrm{Tr}[G_{AB}W_{AB_1}]\quad\text{s.t. } W_{AB_1^N}\succeq0,\ \mathrm{Tr}W_{AB_1^N}=1,\ W_{AB_1^N}=\mathcal U^\pi_{B_1^N}(W_{AB_1^N})\ \forall\pi\in\mathfrak S_N,$$
--   $$\Lambda_{A\to C_A}(W_{AB_1^N})=X_{C_A}\otimes W_{B_1^N},\qquad \Gamma_{B_N\to C_B}(W_{B_1^N})=W_{B_1^{N-1}}\otimes Y_{C_B},$$
--   where $\Lambda$ acts on $A$ (tensored with the identity on $B_1^N$) and $\Gamma$ acts on the last copy $B_N$ of the $B$-marginal.
--
--   These are the objects of Theorem 3.1: every level is an outer bound on $Q$, and the levels converge to $Q$.
--
--   **Formalization Note** The objective is the real part $\mathrm{Re}\,\mathrm{Tr}[G\,W]$, which equals $\mathrm{Tr}[G\,W]$ when $G$ is Hermitian; the page does not say that $G$ is Hermitian. Each "max" is the supremum (`sSup`) of the set of objective values of feasible points; these sets are bounded by $\|G\|_\infty$, and Lean's `sSup ∅ = 0` applies only when the feasible set is empty. The level with $n+1$ copies of $B$ is `SDPval … n`, i.e. `SDPval … n` is the page's $\mathrm{SDP}_{n+1}$; this avoids the empty level $N=0$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §1, pp. 1–2, (2) and (3); §3, p. 11, Q and SDPₙ of Theorem 3.1

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems

/-!
Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, §1 (problems (2) and (3), pp. 1–2) and §3
(the problem `Q` and the hierarchy `SDP_n` of Theorem 3.1, p. 11).

Data: an objective `G` on `A ⊗ B` (`G ∈ S_A ⊗ S_B`), arbitrary ℂ-linear maps
`Λ : S_A → S_{C_A}` and `Γ : S_B → S_{C_B}`, and matrices `X ∈ S_{C_A}`, `Y ∈ S_{C_B}`.
The objective value of an operator `W` is the real part of `Tr[G W]` (equal to `Tr[G W]`
whenever `G` and `W` are Hermitian). The page's `max` is the supremum of the set of objective
values of feasible points.
-/

namespace DeFinettiSDP.Hierarchy

open Matrix
open scoped Kronecker ComplexOrder

/-- The objective values of the constrained bilinear program (2): `Re Tr[G (W_A ⊗ W_B)]` over
states `W_A` on `A` and `W_B` on `B` with `Λ(W_A) = X` and `Γ(W_B) = Y`. -/
def Qset {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) : Set ℝ :=
  {r | ∃ (WA : Matrix (Fin dA) (Fin dA) ℂ) (WB : Matrix (Fin dB) (Fin dB) ℂ),
      WildeQIT.IsDensityOperator WA ∧ WildeQIT.IsDensityOperator WB ∧
      Λ WA = X ∧ Γ WB = Y ∧ r = (Matrix.trace (G * (WA ⊗ₖ WB))).re}

/-- The optimal value `Q` of the constrained bilinear program (2) / §3, p. 11. -/
noncomputable def Qval {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) : ℝ :=
  sSup (Qset G Λ Γ X Y)

/-- The objective values of the convexified program (3), p. 2: `Re Tr[G (∑_i p_i W_A^i ⊗ W_B^i)]`
over finite probability vectors `p` and states `W_A^i`, `W_B^i` with `Λ(W_A^i) = X` and
`Γ(W_B^i) = Y` for every `i`. -/
def Qmixset {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) : Set ℝ :=
  {r | ∃ (N : ℕ) (p : Fin N → ℝ) (WA : Fin N → Matrix (Fin dA) (Fin dA) ℂ)
      (WB : Fin N → Matrix (Fin dB) (Fin dB) ℂ),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      (∀ i, WildeQIT.IsDensityOperator (WA i) ∧ Λ (WA i) = X) ∧
      (∀ i, WildeQIT.IsDensityOperator (WB i) ∧ Γ (WB i) = Y) ∧
      r = (Matrix.trace (G * ∑ i, (p i : ℂ) • (WA i ⊗ₖ WB i))).re}

/-- Feasibility for the level of the hierarchy with `n + 1` copies of `B` (Theorem 3.1, p. 11):
`W` on `A ⊗ B₁ ⋯ B_{n+1}` is a state (`W ⪰ 0`, `Tr W = 1`), is invariant under every
permutation of `B₁, …, B_{n+1}`, and satisfies the lifted constraints
`(Λ ⊗ I_{B₁⋯B_{n+1}})(W) = X ⊗ W_{B₁⋯B_{n+1}}` and
`(I_{B₁⋯B_n} ⊗ Γ_{B_{n+1}})(W_{B₁⋯B_{n+1}}) = W_{B₁⋯B_n} ⊗ Y`. -/
def SDPFeasible {dA dB cA cB : ℕ}
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) (n : ℕ)
    (W : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ) :
    Prop :=
  WildeQIT.IsDensityOperator W ∧ (∀ π : Equiv.Perm (Fin (n + 1)), permB π W = W) ∧
    applyFirst Λ W = X ⊗ₖ trA W ∧
    applyLast Γ (splitLast (trA W)) = trLast (trA W) ⊗ₖ Y

/-- The objective values `Re Tr[G W_{AB₁}]` of the feasible points of the level with `n + 1`
copies of `B`. -/
def SDPset {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) (n : ℕ) : Set ℝ :=
  {r | ∃ W : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ,
      SDPFeasible Λ Γ X Y n W ∧ r = (Matrix.trace (G * keepAB1 W)).re}

/-- The optimal value of the hierarchy level with `n + 1` copies of `B`: `SDPval … n` is the
page's `SDP_{n+1}` (Theorem 3.1, p. 11). -/
noncomputable def SDPval {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) (n : ℕ) : ℝ :=
  sSup (SDPset G Λ Γ X Y n)

end DeFinettiSDP.Hierarchy


