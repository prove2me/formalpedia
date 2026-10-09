-- Prove2me | Definitions.Def_SLQSolv_MinSeq_Sequence
-- name    : SLQSolv_MinSeq_Sequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:04.003997+00:00
-- url     : https://prove2.me/theorems/680a47b8-8e65-4382-bf21-6236d24fc63e
-- title:
--   (4.11), (4.28), (6.1)–(6.2), §6, pp. 2285–2302 — the Riccati feedback sequence u_ε, the BSDE (4.11), weak and strong convergence in 𝒰[t, T], convexity of the cost
-- statement:
--   Let $P$ be a matrix function on $[0,T]$ and write $\Sigma(P)=R+D^\top PD$, $K(P)=B^\top P+D^\top PC+S$. The **feedback** and the **affine term** attached to $P$ and a pair of processes $(\eta,\zeta)$ are
--
--   $$
--   \Theta=-\Sigma(P)^{-1}K(P),\qquad v=-\Sigma(P)^{-1}\big(B^\top\eta+D^\top\zeta+D^\top P\sigma+\rho\big),
--   $$
--
--   as in (4.28) (p. 2291); for the data with $R$ replaced by $R+\varepsilon I$ and $P=P_\varepsilon$ they are $\Theta_\varepsilon,v_\varepsilon$ of (6.1). The pair $(\eta,\zeta)$ is the **adapted solution of the BSDE (4.11)** (p. 2285) if $\eta,\zeta\in L^2_{\mathbb F}(0,T;\mathbb R^n)$ and
--
--   $$
--   \begin{aligned}
--   d\eta=-\Big\{&\big[A^\top-K(P)^\top\Sigma(P)^\dagger B^\top\big]\eta+\big[C^\top-K(P)^\top\Sigma(P)^\dagger D^\top\big]\zeta+\big[C^\top-K(P)^\top\Sigma(P)^\dagger D^\top\big]P\sigma\\&-K(P)^\top\Sigma(P)^\dagger\rho+Pb+q\Big\}ds+\zeta\,dW,\qquad \eta(T)=g,
--   \end{aligned}
--   $$
--
--   where $K(P)^\top=PB+C^\top PD+S^\top$ for symmetric $P$. Given families $P_\varepsilon$, $(\eta_\varepsilon,\zeta_\varepsilon)$ and $X_\varepsilon$, the **sequence (6.2)** is $u_\varepsilon=\Theta_\varepsilon X_\varepsilon+v_\varepsilon$, $\varepsilon>0$.
--
--   On the Hilbert space $\mathcal U[t,T]=L^2_{\mathbb F}(t,T;\mathbb R^m)$ with inner product $\langle u,v\rangle=\mathbb E\int_t^T\langle u(s),v(s)\rangle ds$, a sequence $u_k$ **converges weakly** to $u$ if $\langle u_k,v\rangle\to\langle u,v\rangle$ for every $v\in\mathcal U[t,T]$, and **strongly** if $\mathbb E\int_t^T|u_k-u|^2ds\to0$. Finally, $u\mapsto J(t,x;u)$ is **convex** if $J(t,x;\theta u+(1-\theta)v)\le\theta J(t,x;u)+(1-\theta)J(t,x;v)$ for all $u,v\in\mathcal U[t,T]$ and $\theta\in[0,1]$; the hypothesis of Theorem 6.2 is that $u\mapsto J^0(0,0;u)$ is convex.
--
--   These are the objects of Section 6: the regularized Riccati feedback controls and the two topologies in which their convergence characterizes open-loop solvability.
--
--   **Formalization Note** $\Theta$ and $v$ use Lean's matrix inverse, which returns $0$ on a singular matrix; wherever they are used, $\Sigma\ge\lambda I$ with $\lambda>0$ (strong regularity), so the inverse is the true one. The BSDE uses the pseudoinverse $\Sigma(P)^\dagger$ as (4.11) prints it, and is stated through the published `Peng1990.SMP.SolvesBSDE` with the one-dimensional Brownian motion of the basis. Weak and strong convergence are stated for the process representatives; the limit's membership in $\mathcal U[t,T]$ is required separately in each statement. Convexity is written as the inequality, not through Mathlib's `ConvexOn` (which would add a convex-domain conjunct).
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), (4.11), pp. 2285–2286; (4.28), p. 2291; (6.1)–(6.2), p. 2301; §6, proof of Theorem 6.2, p. 2302; Corollary 3.4, p. 2283

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Riccati

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal Matrix

namespace SLQSolv.MinSeq

open Peng1990.SMP

variable {Ω : Type*} {n m : ℕ}

/-- The feedback `Θ = −(R + DᵀPD)⁻¹(BᵀP + DᵀPC + S)` attached to a matrix function `P`, as in
(4.28) (p. 2291) and, for the data `d.addR ε` and `P = P_ε`, `Θ_ε` of (6.1) (p. 2301). The page
prints the inverse `⁻¹`; Lean's matrix inverse is `0` on a singular matrix, a value never reached
where the paper uses `Θ` (there `R + DᵀPD ≥ λI` with `λ > 0`). -/
noncomputable def thetaOf (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin n) ℝ :=
  -((sigmaR d P s)⁻¹ * gainK d P s)

/-- The affine term `v = −(R + DᵀPD)⁻¹(Bᵀη + Dᵀζ + DᵀPσ + ρ)` of (4.28) (p. 2291); for the data
`d.addR ε`, `P = P_ε` and `(η, ζ) = (η_ε, ζ_ε)` it is `v_ε` of (6.1) (p. 2301). -/
noncomputable def vOf (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (η ζ : ℝ≥0 → Ω → Fin n → ℝ) (s : ℝ≥0) (ω : Ω) : Fin m → ℝ :=
  -((sigmaR d P s)⁻¹ *ᵥ ((d.B s)ᵀ *ᵥ η s ω + (d.D s)ᵀ *ᵥ ζ s ω
    + (d.D s)ᵀ *ᵥ (P s *ᵥ d.σ s ω) + d.ρ s ω))

/-- The sequence (6.2) (p. 2301): `u_ε = Θ_ε X_ε + v_ε`, built from the strongly regular solution
`P_ε` of (5.7), the adapted solution `(η_ε, ζ_ε)` of the BSDE of Theorem 6.1 and the closed-loop
state `X_ε`, all for the data `d.addR ε` (`R` replaced by `R + εI`). -/
noncomputable def uEps (d : Data Ω n m) (Pε : ℝ → ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (η ζ X : ℝ → ℝ≥0 → Ω → Fin n → ℝ) (ε : ℝ) (s : ℝ≥0) (ω : Ω) : Fin m → ℝ :=
  thetaOf (d.addR ε) (Pε ε) s *ᵥ X ε s ω + vOf (d.addR ε) (Pε ε) (η ε) (ζ ε) s ω

variable [MeasurableSpace Ω]

/-- `(η, ζ)` is the adapted solution on `[0, T]` of the BSDE (4.11) (pp. 2285–2286) for `P`:
`dη = −{[Aᵀ − (PB + CᵀPD + Sᵀ)(R + DᵀPD)†Bᵀ]η + [Cᵀ − (PB + CᵀPD + Sᵀ)(R + DᵀPD)†Dᵀ]ζ
  + [Cᵀ − (PB + CᵀPD + Sᵀ)(R + DᵀPD)†Dᵀ]Pσ − (PB + CᵀPD + Sᵀ)(R + DᵀPD)†ρ + Pb + q} ds + ζ dW`,
`η(T) = g`, in the sense of the published `Peng1990.SMP.SolvesBSDE` (`η, ζ ∈ L²_𝔽(0, T; ℝⁿ)` and
the integral form, a.s. for every `t ∈ [0, T]`), with the one-dimensional `W` of the basis.
Applied to `d.addR ε` and `P_ε` it is the BSDE of Theorem 6.1 (p. 2300). -/
def IsAdjointEta (Bs : Basis Ω) (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (η ζ : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  let KT : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ := fun s =>
    P s * d.B s + (d.C s)ᵀ * P s * d.D s + (d.S s)ᵀ
  SolvesBSDE (filt Bs) Bs.P d.T Bs.W d.g
    (fun s ω y z =>
      ((d.A s)ᵀ - KT s * mpinv (sigmaR d P s) * (d.B s)ᵀ) *ᵥ y
      + ((d.C s)ᵀ - KT s * mpinv (sigmaR d P s) * (d.D s)ᵀ) *ᵥ z 0
      + ((d.C s)ᵀ - KT s * mpinv (sigmaR d P s) * (d.D s)ᵀ) *ᵥ (P s *ᵥ d.σ s ω)
      - (KT s * mpinv (sigmaR d P s)) *ᵥ d.ρ s ω + P s *ᵥ d.b s ω + d.q s ω)
    η (fun _ => ζ)

/-- `E ∫ₜᵀ ⟨u(s), v(s)⟩ ds`, the inner product of the Hilbert space `𝒰[t, T] = L²_𝔽(t, T; ℝᵐ)`. -/
noncomputable def innerU (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0)
    (u v : ℝ≥0 → Ω → Fin m → ℝ) : ℝ :=
  ∫ ω, ∫ s in Icc (t : ℝ) d.T, u s.toNNReal ω ⬝ᵥ v s.toNNReal ω ∂volume ∂Bs.P

/-- `uₖ → u` weakly in `𝒰[t, T] = L²_𝔽(t, T; ℝᵐ)`: `E∫ₜᵀ⟨uₖ, v⟩ ds → E∫ₜᵀ⟨u, v⟩ ds` for every
`v ∈ 𝒰[t, T]`. (Statements require `u ∈ 𝒰[t, T]` separately.) -/
def WeakConvU (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (uk : ℕ → ℝ≥0 → Ω → Fin m → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  ∀ v, Adm Bs d t v → Tendsto (fun k => innerU Bs d t (uk k) v) atTop (𝓝 (innerU Bs d t u v))

/-- `uₖ → u` strongly in `𝒰[t, T]`: `E∫ₜᵀ|uₖ − u|² ds → 0`. -/
def StrongConvU (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (uk : ℕ → ℝ≥0 → Ω → Fin m → ℝ)
    (u : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  Tendsto (fun k => sqNorm Bs d t (uk k - u)) atTop (𝓝 0)

/-- `u ↦ J(t, x; u)` is convex on `𝒰[t, T]`:
`J(t, x; θu + (1 − θ)v) ≤ θJ(t, x; u) + (1 − θ)J(t, x; v)` for `u, v ∈ 𝒰[t, T]`, `θ ∈ [0, 1]`. -/
def IsConvexJ (Bs : Basis Ω) (d : Data Ω n m) (t : ℝ≥0) (x : Fin n → ℝ) : Prop :=
  ∀ u v, Adm Bs d t u → Adm Bs d t v → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    J Bs d t x (θ • u + (1 - θ) • v) ≤ θ * J Bs d t x u + (1 - θ) * J Bs d t x v

/-- `u ↦ J⁰(0, 0; u)` is convex on `𝒰[0, T]` (the hypothesis of Theorem 6.2 and Proposition 6.4,
p. 2301, p. 2303). -/
def IsConvexJ0 (Bs : Basis Ω) (d : Data Ω n m) : Prop :=
  IsConvexJ Bs d.hom 0 0

end SLQSolv.MinSeq


