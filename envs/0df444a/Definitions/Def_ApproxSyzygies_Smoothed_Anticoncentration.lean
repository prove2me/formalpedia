-- Prove2me | Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration
-- name    : ApproxSyzygies_Smoothed_Anticoncentration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:10.144735+00:00
-- url     : https://prove2.me/theorems/09a49951-4373-4791-b869-ec34a29e79b9
-- title:
--   Tensor products of Euclidean spaces, subspace anticoncentration (Definition 4.5), small singular values, symmetric tensors
-- statement:
--   A Euclidean space is $\mathbb R^\iota$ for a finite index set $\iota$. The tensor product of $U=\mathbb R^\iota$ and $W=\mathbb R^\kappa$ is $\mathbb R^{\iota\times\kappa}$ with
--   $$(u\otimes w)_{(a,b)}=u_a\,w_b$$
--   (`tens u w`; `tensLeft u` is the linear map $w\mapsto u\otimes w$), normed by the Frobenius norm.
--
--   **Subspace anticoncentration (Definition 4.5).** For $\gamma,\eta_0>0$, a random vector $\zeta\in\mathbb R^N$ with law $\mu$ is $(\theta,\eta_0,\gamma)$-subspace anticoncentrated if for every fixed subspace $E\subseteq\mathbb R^N$ with $\dim E\ge\theta N$,
--   $$\Pr\big[\|\Pi_E\zeta\|_2\le\eta_0\big]\le e^{-\gamma},$$
--   $\Pi_E$ the orthogonal projection onto $E$ (`SubspaceAnticonc θ η₀ γ μ`).
--
--   **Small singular values.** For a linear map $M:W\to V$ between finite-dimensional inner product spaces and $\lambda\ge0$, $\nu_\lambda(M)$ (`numSmallSV M λ`) is the number of singular values of $M$ (the $\dim W$ values, with multiplicity, Mathlib's `LinearMap.singularValues`) that are at most $\lambda$.
--
--   **Symmetric tensors.** $\mathrm{Sym}^D(\mathbb R^n)$ (`symTensors n D`) is the subspace of $(\mathbb R^n)^{\otimes D}=\mathbb R^{[n]^D}$ of tensors invariant under every permutation of the $D$ slots, and $a^{\otimes D}=(a_{k_1}\cdots a_{k_D})_{k\in[n]^D}$ (`tensPow a D`).
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 32 (Definition 4.5), pp. 33-34 (§4.5)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed

/-! ### Tensor products of Euclidean spaces, subspace anticoncentration, small singular values,
symmetric tensors

Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, *Approximate Syzygies of Smoothed Polynomials
and Applications*, STOC 2027 submission, §4.5 (pp. 31–35).

A Euclidean space is `EuclideanSpace ℝ ι` for a finite index type `ι` (every finite-dimensional
real inner product space is isometric to one). The tensor product `U ⊗ W` of `U = ℝ^ι` and
`W = ℝ^κ` is `ℝ^{ι × κ}` with `u ⊗ w = (u_a w_b)_{(a, b)}`; its norm is the Hilbert–Schmidt
(Frobenius) norm. -/

/-- `u ⊗ w ∈ ℝ^{ι × κ}`, `(u ⊗ w)_{(a,b)} = u_a w_b`. -/
noncomputable def tens {ι κ : Type*} [Fintype ι] [Fintype κ] (u : EuclideanSpace ℝ ι)
    (w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ (ι × κ) :=
  WithLp.toLp 2 fun p => u p.1 * w p.2

/-- The linear map `w ↦ u ⊗ w` from `W = ℝ^κ` to `U ⊗ W = ℝ^{ι × κ}`, for fixed `u ∈ U = ℝ^ι`. -/
noncomputable def tensLeft {ι κ : Type*} [Fintype ι] [Fintype κ] (u : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun w := tens u w
  map_add' w w' := by
    ext p
    simp [tens, mul_add]
  map_smul' c w := by
    ext p
    simp [tens]
    ring

/-- Definition 4.5: a random vector of `ℝ^N` with law `μ` is `(θ, η₀, γ)`-subspace
anticoncentrated (`γ, η₀ > 0`) iff for every fixed subspace `E ⊆ ℝ^N` of dimension at least
`θ N`, `P[‖Π_E ζ‖₂ ≤ η₀] ≤ exp(−γ)`, `Π_E` the orthogonal projection onto `E`. -/
def SubspaceAnticonc {ι : Type*} [Fintype ι] (θ η₀ γ : ℝ) (μ : Measure (EuclideanSpace ℝ ι)) :
    Prop :=
  0 < γ ∧ 0 < η₀ ∧
    ∀ E : Submodule ℝ (EuclideanSpace ℝ ι), θ * (Fintype.card ι : ℝ) ≤ (Module.finrank ℝ E : ℝ) →
      μ {x | ‖E.starProjection x‖ ≤ η₀} ≤ ENNReal.ofReal (Real.exp (-γ))

/-- `ν_λ(M)`: the number of singular values of a linear map `M : W → V` between
finite-dimensional inner product spaces that are at most `λ` (counted with multiplicity; `M` has
`dim W` singular values `σ_0 ≥ σ_1 ≥ ⋯`, Mathlib's `LinearMap.singularValues`). -/
noncomputable def numSmallSV {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (M : W →ₗ[ℝ] V) (lam : ℝ) : ℕ :=
  ((Finset.range (Module.finrank ℝ W)).filter fun k => M.singularValues k ≤ lam).card

/-- The symmetric tensors `Sym^D(ℝ^n)` inside `(ℝ^n)^{⊗D} = ℝ^{[n]^D}`: the tensors invariant
under every permutation of the `D` tensor slots. -/
def symTensors (n D : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin D → Fin n)) where
  carrier := {T | ∀ π : Equiv.Perm (Fin D), ∀ k : Fin D → Fin n, T (k ∘ π) = T k}
  add_mem' {S T} hS hT π k := by
    simp only [Set.mem_ofPred_eq] at hS hT
    simp [hS π k, hT π k]
  zero_mem' π k := by simp
  smul_mem' c T hT π k := by
    simp only [Set.mem_ofPred_eq] at hT
    simp [hT π k]

/-- The tensor power `a^{⊗D} = (a_{k_1} ⋯ a_{k_D})_{k ∈ [n]^D}` of `a ∈ ℝ^n`. -/
noncomputable def tensPow {n : ℕ} (a : Fin n → ℝ) (D : ℕ) :
    EuclideanSpace ℝ (Fin D → Fin n) :=
  WithLp.toLp 2 fun k => ∏ j, a (k j)

end ApproxSyzygies.Smoothed


