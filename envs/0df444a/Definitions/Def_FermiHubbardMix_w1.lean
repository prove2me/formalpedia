-- Prove2me | Definitions.Def_FermiHubbardMix_w1
-- name    : FermiHubbardMix_w1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:47.096846+00:00
-- url     : https://prove2.me/theorems/e45c4f91-de3e-438b-8a3d-d05ff8c2a1c0
-- title:
--   Fermionic transport plans, Wasserstein norm $\|\cdot\|_{W_1}$, update matrices, Dobrushin influence matrix
-- statement:
--   Let $X$ be a traceless Hermitian even operator. A **fermionic transport plan** for $X$ (Definition 12.8) is a family $(X_i)_{i\in\Lambda}$ with
--   $$
--   X=\sum_iX_i,\qquad X_i=X_i^\dagger,\qquad X_i\in\mathfrak A^{\mathrm{ev}}_\Lambda,\qquad \operatorname{tr}_i(X_i)=0,
--   $$
--   and its cost vector is $x_i=\tfrac12\|X_i\|_1$ (trace norm). The **fermionic Wasserstein norm** (Definition 12.17) is $\|X\|_{W_1}=\inf\{\|x\|_1\}$ over the cost vectors of transport plans of $X$.
--
--   For a linear map $\Phi$ on even operators preserving Hermiticity and trace, a $\Lambda\times\Lambda$ matrix $Q$ is a **fermionic update matrix** (Definition 12.10) if for every traceless Hermitian even $X$ and every transport plan of $X$ with cost vector $x$, $\Phi(X)$ has a transport plan with cost vector $y\le Qx$ entrywise. For $\Phi=\frac1n(\Phi_1+\dots+\Phi_n)$, $n=|\Lambda|$, the **Dobrushin influence matrix** (Definition 12.19) is
--   $$
--   D^{(\Phi)}_{ij}=\frac1n\max\{\|\Phi_i(X)\|_{W_1}: X\in\mathfrak A^{\mathrm{ev}}_\Lambda,\ X=X^\dagger,\ \operatorname{tr}_j(X)=0,\ \|X\|_{W_1}=1\}.
--   $$
--   Also $\|A\|_{1\to1}=\max_j\sum_i|A_{ij}|$, and $E_S=e_Se_S^{\mathsf T}$ is the $0/1$ matrix supported on $S\times S$ (§4).
--
--   These are the objects of the fermionic Dobrushin argument of Sections 12–15.
--
--   **Formalization Note** "$\Phi$ has update matrix $Q$" includes the standing hypothesis that $\Phi$ preserves evenness, Hermiticity and trace on even operators. The maximum in $D^{(\Phi)}$ is a supremum. $E_S$ here is the matrix, not the normalized partial trace of Definition 12.1.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definitions 12.8, 12.10, p.55; Definitions 12.17, 12.19, p.58; §4, p.15

import Mathlib
import Definitions.Def_FermiHubbardMix_ptr
import Definitions.Def_WildeQIT_traceNorm
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix

variable {Λ : Type*} [Fintype Λ] {m N : ℕ}

/-- **Definition 12.8 (Fermionic transport plan)** (arXiv:2604.08408, held version sha256
055b8f8f…, p.55): a family `(X_i)_{i ∈ Λ}` with `X = ∑_i X_i`, each `X_i` Hermitian and even, and
`tr_i(X_i) = 0`. (For such a family `X` is automatically even, Hermitian and traceless.) -/
def IsTransportPlan (ord : Λ × Fin m ≃ Fin N) (X : Op N) (Xs : Λ → Op N) : Prop :=
  ∑ i, Xs i = X ∧ ∀ i, (Xs i).IsHermitian ∧ IsEven (Xs i) ∧ ptr ord {i} (Xs i) = 0

/-- The cost vector `x_i = ½‖X_i‖₁` of a transport plan (arXiv:2604.08408, held version sha256
055b8f8f…, Definition 12.8, p.55), with the trace norm `‖A‖₁ = tr √(A†A)`
(`WildeQIT.traceNorm`). -/
def planCost (Xs : Λ → Op N) (i : Λ) : ℝ := WildeQIT.traceNorm (Xs i) / 2

/-- **Definition 12.17 (Fermionic Wasserstein norm)** (arXiv:2604.08408, held version sha256
055b8f8f…, p.58): `‖X‖_{W₁} = inf {‖x‖₁ : x the cost vector of a fermionic transport plan of X}`,
for traceless Hermitian even `X`.

**Formalization Note** `‖x‖₁ = ∑_i x_i` since costs are nonnegative. Every traceless Hermitian even
`X` has a transport plan (Proposition 12.13 with `S = Λ`), so the infimum is over a nonempty set
bounded below by `0`. -/
def w1 (ord : Λ × Fin m ≃ Fin N) (X : Op N) : ℝ :=
  sInf {s : ℝ | ∃ Xs : Λ → Op N, IsTransportPlan ord X Xs ∧ s = ∑ i, planCost Xs i}

/-- The standing hypothesis of Definitions 12.10 and 12.19 (arXiv:2604.08408, held version sha256
055b8f8f…, pp.55, 58): `Φ` maps `𝔄^ev_Λ` to itself, maps even Hermitian operators to Hermitian ones,
and preserves the trace of even operators.

**Formalization Note** A linear map `𝔄^ev_Λ → 𝔄^ev_Λ` is represented by a linear map on all
operators, of which only the restriction to even operators is constrained. -/
def PreservesEvenHermTrace (Φ : Op N →ₗ[ℂ] Op N) : Prop :=
  ∀ X : Op N, IsEven X → IsEven (Φ X) ∧ (X.IsHermitian → (Φ X).IsHermitian) ∧ (Φ X).trace = X.trace

/-- **Definition 12.10 (Fermionic update matrix)** (arXiv:2604.08408, held version sha256
055b8f8f…, p.55): for a linear map `Φ` on even operators preserving Hermiticity and trace, `Q`
(indexed by `Λ × Λ`) is a fermionic update matrix if for every traceless Hermitian even `X` and every
transport plan of `X` with cost vector `x`, `Φ(X)` has a transport plan with cost vector `y ≤ Qx`
entrywise.

**Formalization Note** "`Φ` has a fermionic update matrix `Q`" asserts the standing hypothesis on
`Φ` (`PreservesEvenHermTrace`) together with the cost condition. -/
def IsUpdateMatrix (ord : Λ × Fin m ≃ Fin N) (Φ : Op N →ₗ[ℂ] Op N) (Q : Matrix Λ Λ ℝ) : Prop :=
  PreservesEvenHermTrace Φ ∧
  ∀ X : Op N, X.IsHermitian → IsEven X → X.trace = 0 →
    ∀ Xs : Λ → Op N, IsTransportPlan ord X Xs →
      ∃ Ys : Λ → Op N, IsTransportPlan ord (Φ X) Ys ∧ ∀ i, planCost Ys i ≤ ∑ j, Q i j * planCost Xs j

/-- **Definition 12.19 (Fermionic Dobrushin influence matrix)** (arXiv:2604.08408, held version
sha256 055b8f8f…, p.58): for `Φ = (1/n)(Φ_1 + ⋯ + Φ_n)`,
`D_{ij} = (1/n) max {‖Φ_i(X)‖_{W₁} : X ∈ 𝔄^ev_Λ, X = X†, tr_j(X) = 0, ‖X‖_{W₁} = 1}`, `n = |Λ|`.

**Formalization Note** The maximum is a supremum (`sSup`); the set is bounded and attained. -/
def dobrushin (ord : Λ × Fin m ≃ Fin N) (Φs : Λ → Op N →ₗ[ℂ] Op N) : Matrix Λ Λ ℝ :=
  Matrix.of fun i j => (Fintype.card Λ : ℝ)⁻¹ *
    sSup {s : ℝ | ∃ X : Op N, X.IsHermitian ∧ IsEven X ∧ ptr ord {j} X = 0 ∧ w1 ord X = 1 ∧
      s = w1 ord (Φs i X)}

/-- The `1 → 1` norm `‖A‖_{1→1} = max_j ∑_i |A_{ij}|` (arXiv:2604.08408, held version sha256
055b8f8f…, §4, p.15). -/
def norm11 (A : Matrix Λ Λ ℝ) : ℝ := ⨆ j : Λ, ∑ i, |A i j|

open scoped Classical in
/-- `E_S = e_S e_Sᵀ`, the `Λ × Λ` matrix with entry `1` on `S × S` and `0` elsewhere
(arXiv:2604.08408, held version sha256 055b8f8f…, §4, p.15). This is the `E_S` of the update matrices
`Q^{(i)}` in §14, not the normalized partial trace of Definition 12.1. -/
def blockOnes (S : Set Λ) : Matrix Λ Λ ℝ := Matrix.of fun a b => if a ∈ S ∧ b ∈ S then 1 else 0

end FermiHubbardMix


