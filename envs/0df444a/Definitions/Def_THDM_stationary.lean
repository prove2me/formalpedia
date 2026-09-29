-- Prove2me | Definitions.Def_THDM_stationary
-- name    : THDM_stationary
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T23:51:19.622524+00:00
-- url     : https://prove2.me/theorems/6f8267bb-4cda-457f-af27-874a035678fb
-- title:
--   THDM: four-vector notation $(\tilde K,\tilde\xi,\tilde E,\tilde g)$ and stationary points
-- statement:
--   Four-vector notation for the THDM potential and the notion of a stationary point, following Section 5 of arXiv:hep-ph/0605184.
--
--   Writing $\tilde K=(K_0,K)$, $\tilde\xi=(\xi_0,\xi)$ and $\tilde E=\begin{pmatrix}\eta_{00}&\eta^{\mathsf T}\\ \eta&E\end{pmatrix}$ (5.1), the potential becomes $V=\tilde K^{\mathsf T}\tilde\xi+\tilde K^{\mathsf T}\tilde E\tilde K$ (5.2) on the domain $\tilde K^{\mathsf T}\tilde g\tilde K\ge0$, $K_0\ge0$ (5.3), where $\tilde g=\mathrm{diag}(1,-1,-1,-1)$ (5.4). Stationarity is the disjunction of the three situations distinguished in the paper: the trivial configuration $\tilde K=0$; an interior point with $K_0>0$ and $\tilde K^{\mathsf T}\tilde g\tilde K>0$ solving $\tilde E\tilde K=-\tfrac12\tilde\xi$ (5.5); and a boundary point with $K_0>0$ and $\tilde K^{\mathsf T}\tilde g\tilde K=0$ solving $(\tilde E-u\tilde g)\tilde K=-\tfrac12\tilde\xi$ for some Lagrange multiplier $u$ (5.10). The candidate solutions $\tilde K(u)=-\tfrac12(\tilde E-u\tilde g)^{-1}\tilde\xi$ (5.11) and the functions $\tilde f$ (5.16) and $\tilde f'$ (5.17) are recorded as well.
-- source:
--   M. Maniatis, A. von Manteuffel, O. Nachtmann, F. Nagel, 'Stability and Symmetry Breaking in the General Two-Higgs-Doublet Model', Eur. Phys. J. C 48 (2006) 805-823, arXiv:hep-ph/0605184v3, https://arxiv.org/abs/hep-ph/0605184, Sect. 5 (eqs. 5.1-5.5, 5.10, 5.11, 5.16, 5.17)

import Definitions.Def_THDM_potential

/-!
# Four-vector notation and stationary points of the THDM potential

Notions from Section 5 of arXiv:hep-ph/0605184.
-/

open scoped BigOperators
open Matrix

namespace THDM

/-- Index type of the Minkowski-type four-vectors `K̃ = (K₀, K)`: the component
`Sum.inl ()` is `K₀`, the components `Sum.inr a` are `K₁, K₂, K₃`. -/
abbrev Idx := Unit ⊕ Fin 3

/-- Scalar product of two four-component vectors (no metric). -/
def dot4 (x y : Idx → ℝ) : ℝ := ∑ i, x i * y i

/-- `ξ̃ = (ξ₀, ξ)`, see (5.1). -/
def xiT (xi0 : ℝ) (xi : Fin 3 → ℝ) : Idx → ℝ := Sum.elim (fun _ => xi0) xi

/-- `Ẽ = ((η₀₀, ηᵀ), (η, E))`, see (5.1). -/
def ET (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) : Matrix Idx Idx ℝ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => eta00) (Matrix.of fun _ a => eta a)
    (Matrix.of fun a _ => eta a) E

/-- The metric `g̃ = diag(1, -1, -1, -1)`, see (5.4). -/
def gT : Matrix Idx Idx ℝ := Matrix.fromBlocks 1 0 0 (-1)

/-- The Minkowski square `K̃ᵀ g̃ K̃ = K₀² - |K|²`. -/
def mink (x : Idx → ℝ) : ℝ := dot4 x (gT *ᵥ x)

/-- The `K₀` component of a four-vector. -/
def comp0 (x : Idx → ℝ) : ℝ := x (Sum.inl ())

/-- The potential in four-vector notation, `V = K̃ᵀ ξ̃ + K̃ᵀ Ẽ K̃`, see (5.2). -/
def VT (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (x : Idx → ℝ) : ℝ :=
  dot4 x (xiT xi0 xi) + dot4 x (ET eta00 eta E *ᵥ x)

/-- A point of the physical domain (5.3): `K̃ᵀ g̃ K̃ ≥ 0` and `K₀ ≥ 0`. -/
def inDomain (x : Idx → ℝ) : Prop := 0 ≤ mink x ∧ 0 ≤ comp0 x

/-- `K̃(u) = -½ (Ẽ - u g̃)⁻¹ ξ̃`, see (5.11).  Only meaningful for `u` with
`det (Ẽ - u g̃) ≠ 0`; otherwise the Mathlib inverse returns the zero matrix. -/
noncomputable def KT (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : Idx → ℝ :=
  (-(1 / 2 : ℝ)) • ((ET eta00 eta E - u • gT)⁻¹ *ᵥ xiT xi0 xi)

/-- `u` is a regular value for the four-dimensional problem: `det (Ẽ - u g̃) ≠ 0`. -/
def RegT (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : Prop :=
  IsUnit (ET eta00 eta E - u • gT).det

/-- `f̃(u) = -¼ ξ̃ᵀ (Ẽ - u g̃)⁻¹ ξ̃`, see (5.16). -/
noncomputable def fT (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : ℝ :=
  -(1 / 4 : ℝ) * dot4 (xiT xi0 xi) ((ET eta00 eta E - u • gT)⁻¹ *ᵥ xiT xi0 xi)

/-- `f̃'(u) = -¼ ξ̃ᵀ (Ẽ - u g̃)⁻¹ g̃ (Ẽ - u g̃)⁻¹ ξ̃`, see (5.17). -/
noncomputable def fTPrime (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ) : ℝ :=
  -(1 / 4 : ℝ) *
    dot4 (xiT xi0 xi)
      (((ET eta00 eta E - u • gT)⁻¹ * gT * (ET eta00 eta E - u • gT)⁻¹) *ᵥ xiT xi0 xi)

/-- `K̃` is a stationary point of the potential on its domain: either the trivial
configuration `K̃ = 0`, or an interior point `K₀ > 0`, `K̃ᵀ g̃ K̃ > 0` solving
`Ẽ K̃ = -½ ξ̃` (5.5), or a boundary point `K₀ > 0`, `K̃ᵀ g̃ K̃ = 0` solving
`(Ẽ - u g̃) K̃ = -½ ξ̃` for some Lagrange multiplier `u` (5.10). -/
def IsStatPoint (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (x : Idx → ℝ) : Prop :=
  x = 0 ∨
  (0 < comp0 x ∧ 0 < mink x ∧ ET eta00 eta E *ᵥ x = (-(1 / 2 : ℝ)) • xiT xi0 xi) ∨
  (0 < comp0 x ∧ mink x = 0 ∧
    ∃ u : ℝ, (ET eta00 eta E - u • gT) *ᵥ x = (-(1 / 2 : ℝ)) • xiT xi0 xi)

end THDM


