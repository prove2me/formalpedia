-- Prove2me | Definitions.Def_SymPolyOpt_Putinar_Setting
-- name    : SymPolyOpt_Putinar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:46.472702+00:00
-- url     : https://prove2.me/theorems/ed0da20c-9b59-4652-b8ba-f39e8f438ad0
-- title:
--   §2.1, §3, pp. 3–10 — the action p^σ(x) = p(σ⁻¹x), K (2.1), Assumption 2.1, G-linear maps, the forms 𝓛^G_{g_j} (3.1), G-invariant measures
-- statement:
--   This module fixes the setting of §2.1 and §3 of Riener, Theobald, Jansson Andrén and Lasserre.
--
--   Write $\mathbb R[X]=\mathbb R[X_1,\dots,X_n]$ for the real polynomial ring in $n$ variables and let $G$ be a finite subgroup of $\mathrm{GL}_n(\mathbb R)$. The module defines:
--
--   1. **The action on points.** For $\sigma\in\mathrm{GL}_n(\mathbb R)$ and $x\in\mathbb R^n$, $\sigma(x)=\sigma x$ is the matrix–vector product.
--   2. **The action on polynomials** (§3, p. 9). For $p\in\mathbb R[X]$, $p^\sigma(x):=p(\sigma^{-1}(x))$; as a polynomial, $p^\sigma$ is obtained from $p$ by the linear substitution $X_i\mapsto\sum_j(\sigma^{-1})_{ij}X_j$.
--   3. **Invariant polynomials.** $p$ is $G$-invariant if $p^\sigma=p$ for every $\sigma\in G$.
--   4. **The feasible set** (2.1). For $g_1,\dots,g_m\in\mathbb R[X]$,
--   $$K=\{x\in\mathbb R^n:\ g_j(x)\ge 0,\ j=1,\dots,m\}.$$
--   5. **Assumption 2.1** (p. 4). $K$ is compact, and there is $u\in\mathbb R[X]$ with compact superlevel set $\{x:u(x)\ge0\}$ and a representation $u=u_0+\sum_{j=1}^m u_jg_j$ with sums of squares $u_0,\dots,u_m$.
--   6. **$G$-linear maps** (p. 10). A linear map $L^G:\mathbb R[X]\to\mathbb R$ with $L^G(f)=L^G(f^\sigma)$ for all $f\in\mathbb R[X]$ and $\sigma\in G$.
--   7. **The list $g_0:=1,g_1,\dots,g_m$**, indexed by $0,\dots,m$.
--   8. **The symmetrized localizing forms** (3.1):
--   $$\mathcal L^G_{g}(p,q)=L^G\Big(\frac1{|G|}\sum_{\sigma\in G}(p\cdot q)^\sigma\cdot g\Big).$$
--   9. **Invariant measures** (p. 9). For a Borel measure $\mu$ on $\mathbb R^n$ and $\sigma\in G$, $\mu^\sigma(B)=\mu(\sigma^{-1}(B))$, the image of $\mu$ under $x\mapsto\sigma x$; $\mu$ is $G$-invariant if $\mu^\sigma=\mu$ for all $\sigma\in G$.
--
--   These are the objects of the symmetry-adapted version of Putinar's theorem (Theorem 3.2) and of the symmetry-adapted moment relaxation built on it.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin n) ℝ`, points are `Fin n → ℝ`, and $G$ is a `Subgroup (GL (Fin n) ℝ)`; finiteness of $G$ is a `Fintype` instance supplied by the theorems. Sums of squares are Mathlib's `IsSumSq` (the empty sum $0$ counts). With $\mu^\sigma$ the image measure under $x\mapsto\sigma x$, one has $\int h^\sigma\,d\mu=\int h\,d\mu^{\sigma^{-1}}$; the paper writes $\int h\,d\mu^\sigma$ there. The difference is immaterial wherever all $\sigma\in G$ are quantified, since $G$ is a group.
-- source:
--   Riener, Theobald, Jansson Andrén and Lasserre, Exploiting symmetries in SDP-relaxations for polynomial optimization, arXiv:1103.0486v3, p. 1 (the group G), p. 3 (2.1), p. 4 Assumption 2.1 (2.2), p. 9 (§3, the action and invariant measures), p. 10 (G-linear maps, (3.1))

import Mathlib

namespace SymPolyOpt.Putinar

open MeasureTheory MvPolynomial

variable {n m : ℕ}

/-- A matrix `σ ∈ GL_n(ℝ)` acting on a point: `σ(x) = σ x` (matrix–vector product). -/
def ptAct (σ : GL (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (σ : Matrix (Fin n) (Fin n) ℝ).mulVec x

/-- The induced action on polynomials (§3, p. 9): `p^σ(x) := p(σ⁻¹ x)`, i.e. the linear
substitution `X_i ↦ ∑_j (σ⁻¹)_{ij} X_j`. -/
noncomputable def polyAct (σ : GL (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  aeval (fun i => ∑ j, ((σ⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j • X j) p

/-- A polynomial `p` is `G`-invariant if `p^σ = p` for all `σ ∈ G` (§3, p. 9). -/
def IsGInvariant (G : Subgroup (GL (Fin n) ℝ)) (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ σ ∈ G, polyAct σ p = p

/-- The basic closed semialgebraic set (2.1): `K = {x : g_j(x) ≥ 0, j = 1, …, m}`. -/
def feasK (g : Fin m → MvPolynomial (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, 0 ≤ eval x (g j)}

/-- Assumption 2.1 (p. 4): `K` is compact and some `u = u₀ + ∑_j u_j g_j` with sums of squares
`u₀, …, u_m` has a compact superlevel set `{u ≥ 0}`. -/
def Assumption21 (g : Fin m → MvPolynomial (Fin n) ℝ) : Prop :=
  IsCompact (feasK g) ∧
    ∃ (u u₀ : MvPolynomial (Fin n) ℝ) (us : Fin m → MvPolynomial (Fin n) ℝ),
      IsCompact {x : Fin n → ℝ | 0 ≤ eval x u} ∧ IsSumSq u₀ ∧ (∀ j, IsSumSq (us j)) ∧
        u = u₀ + ∑ j, us j * g j

/-- A `G`-linear map (p. 10): a linear `L : ℝ[X] → ℝ` with `L(f) = L(f^σ)` for all `f`, `σ ∈ G`. -/
def IsGLinear (G : Subgroup (GL (Fin n) ℝ)) (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ σ ∈ G, ∀ f, L f = L (polyAct σ f)

/-- The list `g₀ := 1, g₁, …, g_m`, indexed by `Fin (m + 1)` (index `0` is `g₀ = 1`). -/
noncomputable def gExt (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (m + 1) → MvPolynomial (Fin n) ℝ :=
  Fin.cons 1 g

/-- The symmetrized localizing form (3.1):
`𝓛^G_g(p, q) = L((1/|G|) ∑_{σ ∈ G} (p q)^σ · g)`. -/
noncomputable def symForm (G : Subgroup (GL (Fin n) ℝ)) [Fintype G]
    (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (g p q : MvPolynomial (Fin n) ℝ) : ℝ :=
  L ((1 / (Fintype.card G : ℝ)) • ∑ σ : G, polyAct (σ : GL (Fin n) ℝ) (p * q) * g)

/-- A measure `μ` on `ℝⁿ` is `G`-invariant (§3, p. 9) if `μ^σ = μ` for all `σ ∈ G`, where
`μ^σ(B) = μ(σ⁻¹(B))` is the pushforward of `μ` under `x ↦ σ x`. -/
def IsGInvariantMeasure (G : Subgroup (GL (Fin n) ℝ)) (μ : Measure (Fin n → ℝ)) : Prop :=
  ∀ σ ∈ G, μ.map (ptAct σ) = μ

end SymPolyOpt.Putinar


