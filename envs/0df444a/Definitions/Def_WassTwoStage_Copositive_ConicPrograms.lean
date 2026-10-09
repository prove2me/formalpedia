-- Prove2me | Definitions.Def_WassTwoStage_Copositive_ConicPrograms
-- name    : WassTwoStage_Copositive_ConicPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:57:48.784593+00:00
-- url     : https://prove2.me/theorems/68aff926-a21e-4110-9ecf-59880fb88c87
-- title:
--   The copositive programs (10)/(24), the completely positive programs (14)/(25), and problems (1) and (28)
-- statement:
--   Use the data, the worst-case expectation $\mathcal Z(x)$ and the extended data $\mathcal Q, \boldsymbol q, \mathcal T(x), \boldsymbol h(x), \mathcal W$ of the setting. Let $\delta \ge 0$.
--
--   **Copositive program (24).** $\overline{\mathcal Z}_\delta(x)$ is the infimum of
--   $$\epsilon^2\lambda + \frac1I\sum_{i\in[I]}\Big[s_i + \boldsymbol q^\top\psi_i - \lambda\|\hat\xi_i\|_2^2 + \sum_{j\in[N_2+J]}\phi_{ij}\boldsymbol q_j^2\Big]$$
--   over $\lambda \in \mathbb R_+$, $s_i \in \mathbb R$, $\psi_i, \phi_i \in \mathbb R^{N_2+J}$ ($i \in [I]$), subject to, for every $i \in [I]$,
--   $$\begin{bmatrix} \lambda\mathbb I + \mathcal Q^\top \mathrm{diag}(\phi_i)\mathcal Q & -\tfrac12\mathcal T(x)^\top - \mathcal Q^\top\mathrm{diag}(\phi_i)\mathcal W^\top & -\lambda\hat\xi_i - \tfrac12\mathcal Q^\top\psi_i \\ -\tfrac12\mathcal T(x) - \mathcal W\mathrm{diag}(\phi_i)\mathcal Q & \mathcal W\mathrm{diag}(\phi_i)\mathcal W^\top + \delta\mathbb I & \tfrac12(\mathcal W\psi_i - \boldsymbol h(x)) \\ (-\lambda\hat\xi_i - \tfrac12\mathcal Q^\top\psi_i)^\top & \tfrac12(\mathcal W\psi_i - \boldsymbol h(x))^\top & s_i \end{bmatrix} \succeq_{\mathcal C} 0.$$
--   The blocks have sizes $K$, $M+J$ and $1$. For $\delta = 0$ this is the program (10), and $\overline{\mathcal Z}(x) = \overline{\mathcal Z}_0(x)$.
--
--   **Completely positive program (25).** $\underline{\mathcal Z}_\delta(x)$ is the supremum of
--   $$\frac1I\sum_{i\in[I]}\Big[\mathrm{tr}(\mathcal T(x)Y_i) + \boldsymbol h(x)^\top\gamma_i - \delta\,\mathrm{tr}(\Gamma_i)\Big]$$
--   over $\gamma_i \in \mathbb R^{M+J}_+$, $\mu_i \in \mathbb R^K_+$, $\Gamma_i \in \mathbb S^{M+J}_+$, $\Omega_i \in \mathbb S^K_+$, $Y_i \in \mathbb R^{K\times(M+J)}$ ($i\in[I]$), subject to
--   $$\mathcal Q\mu_i + \boldsymbol q = \mathcal W^\top\gamma_i,\qquad \mathcal Q_{j:}^\top\Omega_i\mathcal Q_{j:} - 2\mathcal Q_{j:}^\top Y_i\mathcal W_{:j} + \mathcal W_{:j}^\top\Gamma_i\mathcal W_{:j} = \boldsymbol q_j^2\ \ \forall j\in[N_2+J],$$
--   $$\frac1I\sum_{i\in[I]}\Big(\mathrm{tr}(\Omega_i) - 2\hat\xi_i^\top\mu_i + \hat\xi_i^\top\hat\xi_i\Big) \le \epsilon^2,\qquad \begin{bmatrix}\Omega_i & Y_i & \mu_i\\ Y_i^\top & \Gamma_i & \gamma_i\\ \mu_i^\top & \gamma_i^\top & 1\end{bmatrix} \succeq_{\mathcal C^*} 0 .$$
--   Here $\mathcal Q_{j:}$ is the $j$-th row of $\mathcal Q$ and $\mathcal W_{:j}$ the $j$-th column of $\mathcal W$. For $\delta = 0$ this is the program (14), and $\underline{\mathcal Z}(x) = \underline{\mathcal Z}_0(x)$.
--
--   **Problems (1) and (28).** For a cost vector $c \in \mathbb R^{N_1}$ and a feasible set $\mathcal X \subseteq \mathbb R^{N_1}$, the optimal value of (1) is $\inf_{x\in\mathcal X} c^\top x + \mathcal Z(x)$, and the optimal value of (28) is the infimum of $c^\top x$ plus the objective of (24), jointly over $x \in \mathcal X$ and the variables of (24) subject to its constraints. A point $x$ is a **minimizer for (1)** if $x \in \mathcal X$ and $c^\top x + \mathcal Z(x) \le c^\top x' + \mathcal Z(x')$ for all $x' \in \mathcal X$; it is a **minimizer for (28)** at $\delta$ if $x\in\mathcal X$ and $c^\top x + \overline{\mathcal Z}_\delta(x) \le c^\top x' + \overline{\mathcal Z}_\delta(x')$ for all $x' \in \mathcal X$.
--
--   These are the programs compared in Theorems 2–5 and Propositions 1–2.
--
--   **Formalization Note** All optimal values are infima or suprema in `EReal`, so an infeasible copositive program has value $+\infty$ (as in the paper's Example 1) and an infeasible completely positive program has value $-\infty$. The $3\times3$ block matrices are indexed by `Fin K ⊕ ((Fin M ⊕ Fin J) ⊕ Unit)`, in the order displayed. $\mathbb S_+$ is Mathlib's `PosSemidef` (symmetric and positive semidefinite). A minimizer for (28) is the first-stage part of a solution, exactly as the proof of Theorem 5 uses $x^\star_\delta \in \arg\min_{x\in\mathcal X} c^\top x + \overline{\mathcal Z}_\delta(x)$; attainment of the inner infimum over $(\lambda, s, \psi, \phi)$ is not required.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 5 (1), p. 8 (10), p. 10 (14), p. 17 (24), (25), p. 18 (28), p. 19 (minimizers)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_WassTwoStage_Copositive_Cones
import Definitions.Def_WassTwoStage_Copositive_Setting

open Matrix

namespace WassTwoStage.Copositive

variable {K J M N₁ N₂ I : ℕ}

/-- The `3 × 3` block matrix of the copositive programs (10) (p. 8), (24) (p. 17) and (28)
(p. 18) of Hanasusanto–Kuhn, arXiv:1609.07505v3, for one sample `ξ̂ = ξ̂_i`:

```
⎡ λ𝕀 + 𝒬ᵀdiag(φ)𝒬            −½𝒯(x)ᵀ − 𝒬ᵀdiag(φ)𝒲ᵀ    −λξ̂ − ½𝒬ᵀψ ⎤
⎢ −½𝒯(x) − 𝒲diag(φ)𝒬          𝒲diag(φ)𝒲ᵀ + δ𝕀          ½(𝒲ψ − 𝒽(x)) ⎥
⎣ (−λξ̂ − ½𝒬ᵀψ)ᵀ               ½(𝒲ψ − 𝒽(x))ᵀ             s           ⎦
```

with the extended data `𝒬, 𝒯(x), 𝒲, 𝒽(x)` of (11). The blocks have sizes `K`, `M + J` and `1`;
rows and columns are indexed by `Fin K ⊕ ((Fin M ⊕ Fin J) ⊕ Unit)` in this order. `δ = 0` gives
the matrix of (10). -/
noncomputable def Data.copMatrix (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ) (δ lam s : ℝ)
    (ψ φ : Fin N₂ ⊕ Fin J → ℝ) (ξh : Fin K → ℝ) :
    Matrix (Fin K ⊕ ((Fin M ⊕ Fin J) ⊕ Unit)) (Fin K ⊕ ((Fin M ⊕ Fin J) ⊕ Unit)) ℝ :=
  Matrix.fromBlocks
    (lam • (1 : Matrix (Fin K) (Fin K) ℝ) + d.bQᵀ * diagonal φ * d.bQ)
    (Matrix.fromCols (-(1 / 2 : ℝ) • (d.bT x)ᵀ - d.bQᵀ * diagonal φ * d.bWᵀ)
      (replicateCol Unit (-lam • ξh - (1 / 2 : ℝ) • (d.bQᵀ *ᵥ ψ))))
    (Matrix.fromRows (-(1 / 2 : ℝ) • d.bT x - d.bW * diagonal φ * d.bQ)
      (replicateRow Unit (-lam • ξh - (1 / 2 : ℝ) • (d.bQᵀ *ᵥ ψ))))
    (Matrix.fromBlocks (d.bW * diagonal φ * d.bWᵀ + δ • (1 : Matrix (Fin M ⊕ Fin J) (Fin M ⊕ Fin J) ℝ))
      (replicateCol Unit ((1 / 2 : ℝ) • (d.bW *ᵥ ψ - d.bh x)))
      (replicateRow Unit ((1 / 2 : ℝ) • (d.bW *ᵥ ψ - d.bh x)))
      (fun _ _ => s))

/-- The objective of the copositive programs (10)/(24)/(28) (pp. 8, 17, 18), without the
first-stage cost:
`ε²λ + (1/I) Σ_{i∈[I]} [ s_i + 𝓆ᵀψ_i − λ‖ξ̂_i‖₂² + Σ_{j∈[N₂+J]} φ_{ij} 𝓆_j² ]`. -/
noncomputable def Data.copObjective (d : Data K J M N₁ N₂ I) (lam : ℝ) (s : Fin I → ℝ)
    (ψ φ : Fin I → Fin N₂ ⊕ Fin J → ℝ) : ℝ :=
  d.ε ^ 2 * lam + (1 / (I : ℝ)) *
    ∑ i, (s i + d.bq ⬝ᵥ ψ i - lam * ‖d.ξhat i‖ ^ 2 + ∑ j, φ i j * d.bq j ^ 2)

/-- Feasibility in the copositive program (24) (p. 17) for given `x` and `δ`: `λ ≥ 0`,
`s_i ∈ ℝ`, `ψ_i, φ_i ∈ ℝ^{N₂+J}`, and the block matrix `copMatrix` built from `ξ̂_i` is
copositive (`⪰_C 0`) for every `i ∈ [I]`. -/
def Data.CopFeasible (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ) (δ lam : ℝ) (s : Fin I → ℝ)
    (ψ φ : Fin I → Fin N₂ ⊕ Fin J → ℝ) : Prop :=
  0 ≤ lam ∧ ∀ i, MurtyKabadi.Reduction.Copositive
    (d.copMatrix x δ lam (s i) (ψ i) (φ i) (WithLp.ofLp (d.ξhat i)))

/-- The optimal value `𝒵̄_δ(x)` of the copositive program (24) (p. 17); `δ = 0` is the program
(10) of Theorem 2 (p. 8), `𝒵̄(x) = 𝒵̄_0(x)`. An infimum in `EReal`: `+∞` if the program is
infeasible, `−∞` if it is unbounded below. -/
noncomputable def Data.upperValue (d : Data K J M N₁ N₂ I) (δ : ℝ) (x : Fin N₁ → ℝ) : EReal :=
  ⨅ (lam : ℝ) (s : Fin I → ℝ) (ψ : Fin I → Fin N₂ ⊕ Fin J → ℝ) (φ : Fin I → Fin N₂ ⊕ Fin J → ℝ)
    (_ : d.CopFeasible x δ lam s ψ φ), ((d.copObjective lam s ψ φ : ℝ) : EReal)

/-- The `3 × 3` moment matrix of the completely positive programs (14) (p. 10) and (25) (p. 17),
`[[Ω, Y, µ], [Yᵀ, Γ, γ], [µᵀ, γᵀ, 1]]`, with rows and columns indexed by
`ιK ⊕ (ιMJ ⊕ Unit)` in this order. -/
def cpMatrix {ιK ιMJ : Type*} (Ω : Matrix ιK ιK ℝ) (Y : Matrix ιK ιMJ ℝ) (μ : ιK → ℝ)
    (Γ : Matrix ιMJ ιMJ ℝ) (γ : ιMJ → ℝ) : Matrix (ιK ⊕ (ιMJ ⊕ Unit)) (ιK ⊕ (ιMJ ⊕ Unit)) ℝ :=
  Matrix.fromBlocks Ω (Matrix.fromCols Y (replicateCol Unit μ))
    (Matrix.fromRows Yᵀ (replicateRow Unit μ))
    (Matrix.fromBlocks Γ (replicateCol Unit γ) (replicateRow Unit γ) (fun _ _ => 1))

/-- Feasibility in the completely positive programs (14) (p. 10) and (25) (p. 17): for every
`i ∈ [I]`,
* `γ_i ∈ ℝ^{M+J}_+`, `µ_i ∈ ℝ^K_+`, `Γ_i ∈ 𝕊^{M+J}_+`, `Ω_i ∈ 𝕊^K_+`, `Y_i ∈ ℝ^{K×(M+J)}`;
* `𝒬µ_i + 𝓆 = 𝒲ᵀγ_i`;
* `𝒬_{j:}ᵀΩ_i𝒬_{j:} − 2𝒬_{j:}ᵀY_i𝒲_{:j} + 𝒲_{:j}ᵀΓ_i𝒲_{:j} = 𝓆_j²` for all `j ∈ [N₂+J]`;
* the moment matrix `[[Ω_i, Y_i, µ_i], [Y_iᵀ, Γ_i, γ_i], [µ_iᵀ, γ_iᵀ, 1]]` is completely positive;

and `(1/I) Σ_{i∈[I]} (tr(Ω_i) − 2ξ̂_iᵀµ_i + ξ̂_iᵀξ̂_i) ≤ ε²`. Here `𝒬_{j:}` is the `j`-th row of
`𝒬` and `𝒲_{:j}` the `j`-th column of `𝒲`. -/
def Data.CPFeasible (d : Data K J M N₁ N₂ I) (γ : Fin I → Fin M ⊕ Fin J → ℝ)
    (μ : Fin I → Fin K → ℝ) (Γ : Fin I → Matrix (Fin M ⊕ Fin J) (Fin M ⊕ Fin J) ℝ)
    (Ω : Fin I → Matrix (Fin K) (Fin K) ℝ) (Y : Fin I → Matrix (Fin K) (Fin M ⊕ Fin J) ℝ) :
    Prop :=
  (∀ i, 0 ≤ γ i ∧ 0 ≤ μ i ∧ (Γ i).PosSemidef ∧ (Ω i).PosSemidef) ∧
  (∀ i, d.bQ *ᵥ μ i + d.bq = d.bWᵀ *ᵥ γ i) ∧
  (∀ i j, d.bQ j ⬝ᵥ (Ω i *ᵥ d.bQ j) - 2 * (d.bQ j ⬝ᵥ (Y i *ᵥ d.bWᵀ j))
      + d.bWᵀ j ⬝ᵥ (Γ i *ᵥ d.bWᵀ j) = d.bq j ^ 2) ∧
  (1 / (I : ℝ)) * ∑ i, (trace (Ω i) - 2 * (WithLp.ofLp (d.ξhat i) ⬝ᵥ μ i)
      + WithLp.ofLp (d.ξhat i) ⬝ᵥ WithLp.ofLp (d.ξhat i)) ≤ d.ε ^ 2 ∧
  (∀ i, CompletelyPositive (cpMatrix (Ω i) (Y i) (μ i) (Γ i) (γ i)))

/-- The objective of the completely positive program (25) (p. 17):
`(1/I) Σ_{i∈[I]} [ tr(𝒯(x)Y_i) + 𝒽(x)ᵀγ_i − δ tr(Γ_i) ]`; `δ = 0` is the objective of (14). -/
noncomputable def Data.cpObjective (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ) (δ : ℝ)
    (γ : Fin I → Fin M ⊕ Fin J → ℝ) (Γ : Fin I → Matrix (Fin M ⊕ Fin J) (Fin M ⊕ Fin J) ℝ)
    (Y : Fin I → Matrix (Fin K) (Fin M ⊕ Fin J) ℝ) : ℝ :=
  (1 / (I : ℝ)) * ∑ i, (trace (d.bT x * Y i) + d.bh x ⬝ᵥ γ i - δ * trace (Γ i))

/-- The optimal value `𝒵̲_δ(x)` of the completely positive program (25) (p. 17); `δ = 0` is the
program (14) of Proposition 1 (p. 10), `𝒵̲(x) = 𝒵̲_0(x)`. A supremum in `EReal`: `−∞` if the
program is infeasible. -/
noncomputable def Data.lowerValue (d : Data K J M N₁ N₂ I) (δ : ℝ) (x : Fin N₁ → ℝ) : EReal :=
  ⨆ (γ : Fin I → Fin M ⊕ Fin J → ℝ) (μ : Fin I → Fin K → ℝ)
    (Γ : Fin I → Matrix (Fin M ⊕ Fin J) (Fin M ⊕ Fin J) ℝ)
    (Ω : Fin I → Matrix (Fin K) (Fin K) ℝ) (Y : Fin I → Matrix (Fin K) (Fin M ⊕ Fin J) ℝ)
    (_ : d.CPFeasible γ μ Γ Ω Y), ((d.cpObjective x δ γ Γ Y : ℝ) : EReal)

/-- The optimal value of problem (1) (p. 5): `inf_{x ∈ 𝒳} c ᵀx + 𝒵(x)`, in `EReal`. -/
noncomputable def Data.val1 (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ)
    (X : Set (Fin N₁ → ℝ)) : EReal :=
  ⨅ (x : Fin N₁ → ℝ) (_ : x ∈ X), ((c ⬝ᵥ x : ℝ) : EReal) + d.worstCase x

/-- The optimal value of problem (28) (p. 18): the infimum of
`cᵀx + ε²λ + (1/I) Σ_i [s_i + 𝓆ᵀψ_i − λ‖ξ̂_i‖₂² + Σ_j φ_{ij}𝓆_j²]` jointly over `x ∈ 𝒳` and the
variables `(λ, s, ψ, φ)` of (24), subject to the constraints of (24). -/
noncomputable def Data.val28 (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ)
    (X : Set (Fin N₁ → ℝ)) (δ : ℝ) : EReal :=
  ⨅ (x : Fin N₁ → ℝ) (_ : x ∈ X) (lam : ℝ) (s : Fin I → ℝ) (ψ : Fin I → Fin N₂ ⊕ Fin J → ℝ)
    (φ : Fin I → Fin N₂ ⊕ Fin J → ℝ) (_ : d.CopFeasible x δ lam s ψ φ),
    ((c ⬝ᵥ x + d.copObjective lam s ψ φ : ℝ) : EReal)

/-- `x` is a minimizer for problem (1): `x ∈ 𝒳` and `cᵀx + 𝒵(x) ≤ cᵀx' + 𝒵(x')` for all
`x' ∈ 𝒳`. -/
def Data.IsMinimizer1 (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ) (X : Set (Fin N₁ → ℝ))
    (x : Fin N₁ → ℝ) : Prop :=
  x ∈ X ∧ ∀ x' ∈ X, ((c ⬝ᵥ x : ℝ) : EReal) + d.worstCase x ≤ ((c ⬝ᵥ x' : ℝ) : EReal) + d.worstCase x'

/-- `x` is a minimizer for problem (28) at parameter `δ` (the first-stage part of a solution,
as in the proof of Theorem 5, p. 19: `x⋆_δ ∈ arg min_{x∈𝒳} cᵀx + 𝒵̄_δ(x)`): `x ∈ 𝒳` and
`cᵀx + 𝒵̄_δ(x) ≤ cᵀx' + 𝒵̄_δ(x')` for all `x' ∈ 𝒳`. -/
def Data.IsMinimizer28 (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ) (X : Set (Fin N₁ → ℝ))
    (δ : ℝ) (x : Fin N₁ → ℝ) : Prop :=
  x ∈ X ∧ ∀ x' ∈ X, ((c ⬝ᵥ x : ℝ) : EReal) + d.upperValue δ x ≤
    ((c ⬝ᵥ x' : ℝ) : EReal) + d.upperValue δ x'

end WassTwoStage.Copositive


