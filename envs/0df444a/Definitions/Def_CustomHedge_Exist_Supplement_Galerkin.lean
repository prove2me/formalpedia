-- Prove2me | Definitions.Def_CustomHedge_Exist_Supplement_Galerkin
-- name    : CustomHedge_Exist_Supplement_Galerkin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:38:19.344697+00:00
-- url     : https://prove2.me/theorems/52215c0d-11ff-4e05-ae3e-58a8a26d4cb7
-- title:
--   (EC.12), Theorem EC.1, pp. ec12, ec38–ec39 — basis of L²_{X,0}, orthonormal frames, matrices T_n and M_n, Galerkin system and approximants
-- statement:
--   Let $\mathbb H_X$ ($=L^2_{X,0}$) be the space of $\sigma(X)$-measurable, $\mathbb P$-centered random variables of finite variance, with the $L^2(\mathbb P)$ inner product $\langle U,V\rangle=\mathbb E[UV]$, and let $\mathscr I=T$ be the operator $T[Z]=\mathbb E[\mathbb E[Z\mid\mathcal F_I]\mid\mathcal F_X]$.
--
--   1. A sequence $w_1,w_2,\dots$ is a **basis of $\mathbb H_X$** if every $w_j\in\mathbb H_X$, the family is linearly independent (no nontrivial finite combination vanishes $\mathbb P$-a.s.), and its finite linear combinations are dense in $\mathbb H_X$.
--   2. A **Galerkin frame at level $n$** is a family $e_1,\dots,e_n$, orthonormal in $L^2(\mathbb P)$, with a matrix $T_n=(T_{kj})$ such that $w_j=\sum_{k=1}^nT_{kj}e_k$ a.s. for $j=1,\dots,n$; then $(e_k)$ is an orthonormal basis of $\operatorname{Span}\langle w_1,\dots,w_n\rangle$ and $T_n$ the change of basis.
--   3. $M_n=(\langle\mathscr I[e_k],e_j\rangle)_{k,j=1,\dots,n}$ (row $k$, column $j$), and $\gamma^n=T_n^{-1}\big(\langle\Pi^X_0,e_j\rangle\big)_{j=1,\dots,n}$, where $\Pi^X_0=-\mathbb E[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\mid\mathcal F_X]$.
--   4. The **Galerkin system** for $h^n\in\mathbb R^n$ is
--   $$T_n^{-1}(\mathbb I_n-M_n)T_n\,h^n=\gamma^n,$$
--   and the **Galerkin approximant** is $H^*_{0,n}=\sum_{j=1}^nh^n_jw_j$.
--
--   These objects define the numerical scheme of Theorem EC.1 for the design equation $H_0=\Pi^X_0+\mathscr I[H_0]$.
--
--   **Formalization Note** Everything is stated for random variables on $\Omega$ (the paper writes payoff functions $w(x)$ in $L^2_X$; $w\mapsto w(X)$ is an isometry and $\mathscr I[w](X)=T[w(X)]$, p. ec12). The basis is indexed from $1$ (Lean index $j$ stands for $w_{j+1}$). The vector $\gamma^n$ is the coordinate vector of the projection of $\Pi^X_0$ in the $w$-basis, as in (EC.61)–(EC.62); Theorem EC.1 prints $\gamma^n=(\langle\Pi^X_0,e_j\rangle)_j$, see that item.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. ec12 (PDF 43), (EC.12), L²_{X,0}, Theorem EC.1; pp. ec38–ec39 (PDF 69–70), (EC.53), (EC.56)–(EC.62)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist.Supplement

open MeasureTheory ProbabilityTheory Matrix

variable {Ω EX EY EI : Type*} [MeasurableSpace Ω] [MeasurableSpace EX]
  [MeasurableSpace EY] [MeasurableSpace EI]

/-- `w` is a basis of `ℍ_X = L²_{X,0}` (the Lean index `j` stands for the paper's `w_{j+1}`):
every `w j` is a `P`-centered finite-variance claim on `X`, the family is linearly independent
modulo `P`-null functions, and its finite linear combinations are dense in `ℍ_X` for the
`L²(P)` norm. -/
def IsCenteredBasis (M : Market Ω EX EY EI) (w : ℕ → Ω → ℝ) : Prop :=
  (∀ j, InCentered M.P M.FX (w j)) ∧
    (∀ (n : ℕ) (c : Fin n → ℝ),
      (fun ω => ∑ j : Fin n, c j * w j ω) =ᵐ[M.P] (0 : Ω → ℝ) → c = 0) ∧
    (∀ Z : Ω → ℝ, InCentered M.P M.FX Z → ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (c : Fin n → ℝ), l2norm M.P (fun ω => Z ω - ∑ j : Fin n, c j * w j ω) < ε)

/-- The data `(e₁, …, eₙ)`, `Tₙ` of Theorem EC.1 at level `n`: `e` is orthonormal in `L²(P)`
and `w_j = ∑_k (Tₙ)_{kj} e_k` (`P`-a.s.) for `j = 1, …, n`; hence `e` is an orthonormal basis
of `Span⟨w₁, …, wₙ⟩` and `Tₙ` is the change-of-basis matrix. -/
def IsGalerkinFrame (M : Market Ω EX EY EI) (w : ℕ → Ω → ℝ) (n : ℕ) (e : Fin n → Ω → ℝ)
    (Tn : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ j k : Fin n, ∫ ω, e j ω * e k ω ∂M.P = if j = k then 1 else 0) ∧
    (∀ j : Fin n, w j =ᵐ[M.P] fun ω => ∑ k : Fin n, Tn k j * e k ω)

/-- `Mₙ = (⟨𝓘[e_k], e_j⟩)_{k,j}` (row `k`, column `j`), with `𝓘 = T = E[E[· | 𝓕_I] | 𝓕_X]`
and the `L²(P)` inner product. -/
noncomputable def galerkinM (M : Market Ω EX EY EI) {n : ℕ} (e : Fin n → Ω → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun k j => ∫ ω, M.T (e k) ω * e j ω ∂M.P

/-- The coordinates `(⟨Π^X_0, e_j⟩)_j` of the projection of `Π^X_0` in the basis `e`. -/
noncomputable def galerkinCoord (M : Market Ω EX EY EI) {n : ℕ} (e : Fin n → Ω → ℝ) :
    Fin n → ℝ :=
  fun j => ∫ ω, M.Pi0X ω * e j ω ∂M.P

/-- The right-hand side `γⁿ := Tₙ⁻¹ (⟨Π^X_0, e_j⟩)_j` (the coordinates of `𝒫ₙ Π^X_0` in the
basis `w₁, …, wₙ`, as in (EC.61)–(EC.62)). -/
noncomputable def galerkinGamma (M : Market Ω EX EY EI) {n : ℕ} (e : Fin n → Ω → ℝ)
    (Tn : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  Tn⁻¹ *ᵥ galerkinCoord M e

/-- The `n`-dimensional linear system `Tₙ⁻¹ (𝕀ₙ - Mₙ) Tₙ hⁿ = γⁿ`. -/
def GalerkinSystem (M : Market Ω EX EY EI) {n : ℕ} (e : Fin n → Ω → ℝ)
    (Tn : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : Prop :=
  (Tn⁻¹ * (1 - galerkinM M e) * Tn) *ᵥ h = galerkinGamma M e Tn

/-- The approximation `H*_{0,n} = ∑_{j=1}^n hⁿ_j w_j`. -/
noncomputable def galerkinApprox (w : ℕ → Ω → ℝ) {n : ℕ} (h : Fin n → ℝ) : Ω → ℝ :=
  fun ω => ∑ j : Fin n, h j * w j ω

end CustomHedge.Exist.Supplement


