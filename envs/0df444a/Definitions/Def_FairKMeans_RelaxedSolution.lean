-- Prove2me | Definitions.Def_FairKMeans_RelaxedSolution
-- name    : FairKMeans_RelaxedSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:11.802057+00:00
-- url     : https://prove2.me/theorems/a2659b5f-603b-42f7-af74-f26fd539436b
-- title:
--   Relaxed solutions: centroids $\pi(t)$, means $\nu_p$, $C_T$, drift $C_\nu$, $\Psi$, linearized cost, stationarity, mixtures
-- statement:
--   A **relaxed solution** $(T,\phi_T)$ is a finite indexed family $T$ of candidates in $\mathbb R^d$ with an $(\alpha,\beta)$-fair fractional assignment $\phi_T$ of $P$ to $T$. The column of a candidate $t$ is its fragment cluster, with weight and centroid
--
--   $$w(t)=\sum_{p}\phi_T(p,t),\qquad \pi(t)=\frac1{w(t)}\sum_p\phi_T(p,t)\,p .$$
--
--   Each point is moved to $\nu_p=\sum_t\phi_T(p,t)\pi(t)$. The cost after moving candidates to their centroids, the drift, the weight of the drift and the drift-regularized cost are
--
--   $$C_T=\sum_p\sum_t\phi_T(p,t)\|p-\pi(t)\|^2,\quad C_\nu=\sum_p\|p-\nu_p\|^2,\quad \lambda=\frac{\rho}{1+\rho},\quad \Psi(\phi_T)=C_T+\lambda C_\nu .$$
--
--   The **linearized cost** at $(T,\phi_T)$ of another relaxed solution $(T',\phi_{T'})$ is
--
--   $$L(\phi_{T'})=C_{T'}+2\lambda\sum_p(\nu_p-p)^\top(\nu_p(\phi_{T'})-p),$$
--
--   with $\nu_p$ those of $(T,\phi_T)$. The solution is **$\tau$-stationary** if $L(\phi_T)\le L(\phi_{T'})+\tau$ for every relaxed solution $(T',\phi_{T'})$. The **$\theta$-mixture** of two relaxed solutions has candidate family $T_1\uplus T_2$ and assignment $(1-\theta)\phi_{T_1}\oplus\theta\phi_{T_2}$. Finally $u_p=\lambda(\nu_p-p)$ and $p_\lambda=p-u_p$ define the indexed families $P_\lambda$ and $U$ of (26).
--
--   These are the objects of the first stage of Algorithm 1 and of its analysis.
--
--   **Formalization Note** All these quantities depend on $\phi_T$ only, so they take the assignment matrix as argument. The centroid of a zero column is Lean's value $0$; it is always multiplied by a zero weight. $T_1\uplus T_2$ is `Fin.append`.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 5, (18)–(23), p.22 (PDF p.24); (26), p.23 (PDF p.25); Definitions 8–9, pp.9–10 (PDF pp.11–12)

import Mathlib
import Definitions.Def_FairKMeans_Model

namespace FairKMeans

/-!
# Relaxed solutions: centroids, weighted means, costs, drift, mixtures, linearized cost

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 5, "Notation
recalled from Section 2.2", (18)–(23), p.22 (PDF 24); shifted points (26), p.23 (PDF 25);
Definitions 8–9, pp.9–10 (PDF 11–12).

**Formalization Note.** A relaxed solution is a candidate family `T : Fin s → E d` with an
`(α, β)`-fair fractional assignment `φ : Fin n → Fin s → ℝ`. The quantities `w, π, ν, C_T, C_ν,
Ψ, L` depend on `φ` only (p.9), so they take `φ` and not `T`. The centroid `π(t)` of a zero
column is Lean's junk value `0⁻¹ • 0 = 0`; every sum multiplies it by `φ(p,t) = 0`. The disjoint
union `T₁ ⊎ T₂` is `Fin.append`. The weight of the drift is `λ = ρ/(1+ρ)` (22).
-/

variable {d n m : ℕ}

/-- The centroid `π(t) = (1/w(t)) ∑_p φ(p,t) p` of the fragment cluster of `t` (18). -/
noncomputable def cen {s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) (t : Fin s) : E d :=
  (clusterWeight φ t)⁻¹ • ∑ p, φ p t • I.pts p

/-- The weighted mean `ν_p = ∑_t φ(p,t) π(t)` to which `p` is moved (19). -/
noncomputable def nu {s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) (p : Fin n) : E d :=
  ∑ t, φ p t • cen I φ t

/-- `C_T = ∑_p ∑_t φ(p,t) ‖p − π(t)‖²`, the cost after every candidate is moved to its
centroid (20). -/
noncomputable def CT {s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) : ℝ :=
  ∑ p, ∑ t, φ p t * ‖I.pts p - cen I φ t‖ ^ 2

/-- The drift `C_ν = ∑_p ‖p − ν_p‖²` (21). -/
noncomputable def Cnu {s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) : ℝ :=
  ∑ p, ‖I.pts p - nu I φ p‖ ^ 2

/-- The weight of the drift `λ = ρ/(1+ρ)` (22). -/
noncomputable def lam (ρ : ℝ) : ℝ := ρ / (1 + ρ)

/-- The drift-regularized cost `Ψ(φ_T) = C_T + λ C_ν` (22; Definition 8, p.9). -/
noncomputable def Psi {s : ℕ} (I : Instance d n m) (ρ : ℝ) (φ : Fin n → Fin s → ℝ) : ℝ :=
  CT I φ + lam ρ * Cnu I φ

/-- The linearized cost at `(T, φ)` of another assignment `φ'` (23):
`L(φ') = C_{T'} + 2λ ∑_p (ν_p − p)ᵀ(ν_p(φ') − p)`, with `ν_p` those of `φ`. -/
noncomputable def linCost {s s' : ℕ} (I : Instance d n m) (ρ : ℝ) (φ : Fin n → Fin s → ℝ)
    (φ' : Fin n → Fin s' → ℝ) : ℝ :=
  CT I φ' + 2 * lam ρ * ∑ p, inner ℝ (nu I φ p - I.pts p) (nu I φ' p - I.pts p)

/-- A relaxed solution (p.22): `φ` is an `(α, β)`-fair fractional assignment (the candidate
positions are unconstrained). -/
def IsRelaxed {s : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) : Prop :=
  IsAssignment φ ∧ IsFair I φ

/-- τ-stationarity (Definition 9, p.10; p.22): `L(φ_T) ≤ L(φ_{T'}) + τ` for every relaxed
solution `(T', φ_{T'})`, of any size, where `L` is the linearized cost at `φ`. -/
def IsStationary {s : ℕ} (I : Instance d n m) (ρ τ : ℝ) (φ : Fin n → Fin s → ℝ) : Prop :=
  ∀ (s' : ℕ) (φ' : Fin n → Fin s' → ℝ), IsRelaxed I φ' →
    linCost I ρ φ φ ≤ linCost I ρ φ φ' + τ

/-- The candidate family `T₁ ⊎ T₂` of a mixture (p.22). -/
def mixCand {s₁ s₂ : ℕ} (T₁ : Fin s₁ → E d) (T₂ : Fin s₂ → E d) : Fin (s₁ + s₂) → E d :=
  Fin.append T₁ T₂

/-- The assignment `(1 − θ) φ₁ ⊕ θ φ₂` of the θ-mixture (p.22): `p` gets `(1−θ) φ₁(p,t)` at
`t ∈ T₁` and `θ φ₂(p,t)` at `t ∈ T₂`. -/
def mixAssign {s₁ s₂ : ℕ} (θ : ℝ) (φ₁ : Fin n → Fin s₁ → ℝ) (φ₂ : Fin n → Fin s₂ → ℝ) :
    Fin n → Fin (s₁ + s₂) → ℝ :=
  fun p => Fin.append ((1 - θ) • φ₁ p) (θ • φ₂ p)

/-- `u_p = λ (ν_p − p)` (26). -/
noncomputable def uvec {s : ℕ} (I : Instance d n m) (ρ : ℝ) (φ : Fin n → Fin s → ℝ)
    (p : Fin n) : E d :=
  lam ρ • (nu I φ p - I.pts p)

/-- The shifted point `p_λ = p − u_p` (26); `P_λ` and `U` are indexed by `P`. -/
noncomputable def plam {s : ℕ} (I : Instance d n m) (ρ : ℝ) (φ : Fin n → Fin s → ℝ)
    (p : Fin n) : E d :=
  I.pts p - uvec I ρ φ p

end FairKMeans


