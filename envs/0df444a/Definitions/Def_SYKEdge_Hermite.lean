-- Prove2me | Definitions.Def_SYKEdge_Hermite
-- name    : SYKEdge_Hermite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:56.757476+00:00
-- url     : https://prove2.me/theorems/0faf7208-f997-4b46-86f9-6bebd76a27d4
-- title:
--   Normalized Hermite polynomials $h_n$, matrix-valued polynomials $\mathcal K(\mathbb R^m;\mathbb C^{N\times N})$, the embedding $U$ and the multiplication map $M$
-- statement:
--   The **normalized probabilists' Hermite polynomials** $h_n$ satisfy $h_0=1$, $h_1=X$ and $Xh_n=\sqrt n\,h_{n-1}+\sqrt{n+1}\,h_{n+1}$; equivalently $h_n=\mathrm{He}_n/\sqrt{n!}$. They are orthonormal for $N(0,1)$. For $r\in\mathbb Z_{\ge0}^m$, $h_r(g)=\prod_ih_{r_i}(g_i)$.
--
--   A **matrix-valued polynomial** $p\in\mathcal K(\mathbb R^m;\mathbb C^{N\times N})$ is $p(g)=\sum_r\big(\prod_ig_i^{r_i}\big)M_r$ with finitely many nonzero coefficient matrices $M_r$; its degree is $\max\{|r|:M_r\ne0\}$. With $g\sim N(0,\mathrm{Id}_m)$,
--   $$\langle F,G\rangle_{\mathcal K}=\mathbb E_g\operatorname{tr}(F(g)^*G(g)),\qquad \|F(g)\|_p=\big(\mathbb E_g\|F(g)\|_{HS}^p\big)^{1/p}.$$
--   For a hypergraph $\mathcal H=(S_1,\dots,S_m)$ and Majorana operators, $\Gamma^r=\Gamma_{S_1}^{r_1}\cdots\Gamma_{S_m}^{r_m}$, the **embedding** $U$ of the Fock space is the linear map with
--   $$(Uf_r)(g)=h_r(g)\,\Gamma^r,$$
--   and $M$ is left multiplication by the Hamiltonian, $(MF)(g)=H(g)F(g)$.
--
--   $U$ is the twisted Wiener–Itô map that carries the Krylov witness from the twisted boson space to matrix-valued functions of the disorder.
--
--   **Formalization Note** $\mathrm{He}_n$ is Mathlib's monic probabilists' Hermite polynomial. Elements of $\mathcal K$ are coefficient families; $U\psi$ and $MF$ are recorded as functions of $g$.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Definitions 3.5, 3.6 and 'Matrix-Valued Polynomials', p.18; inner product, p.19; Γ^r, p.29; (26) and M, p.30

import Mathlib
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_Fock

open Matrix MeasureTheory

namespace SYKEdge

/-!
# Normalized Hermite polynomials, matrix-valued polynomials and the embedding `U`

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, Definitions 3.5, 3.6, "Matrix-Valued Polynomials" and "Gaussian Concentration
and Gaussian Chaos", p.18; the inner product on `ℂ^{N×N}`, p.19; `Γ^r` and (26), pp.29–30; `M`,
p.30.

**Formalization Note.**
* `hermN j x = h_j(x) = He_j(x)/√(j!)` with `He_j` Mathlib's monic probabilists' Hermite polynomial
  `Polynomial.hermite j`. This is Definition 3.5: `h₀ = 1`, `h₁ = X` and
  `X h_j = √j h_{j−1} + √(j+1) h_{j+1}` follow from `X He_j = He_{j+1} + j He_{j−1}`.
* `hMulti r g = h_r(g) = Π_i h_{r_i}(g_i)` (Definition 3.6).
* `MatPoly m ι` is `K(ℝ^m; ℂ^{N×N})`: finitely supported coefficient families `r ↦ M_r` over
  exponent vectors `r ∈ ℤ^m_{⩾0}`, evaluated as `Σ_r (Π_i g_i^{r_i}) M_r`; `DegLE P L` says
  `|r| ⩽ L` whenever `M_r ≠ 0`, i.e. the degree is `⩽ L` (p.18).
* `gaussNorm p F = ‖F(g)‖_p = (E_g ‖F(g)‖_HS^p)^{1/p}` with `g ∼ N(0, Id_m)` and the normalized
  Hilbert–Schmidt norm (the Hilbert-space norm of `⟨X,Y⟩ = tr(X*Y)`, p.19).
* `Kinner F G = ⟨F, G⟩_K = E_g tr(F(g)* G(g))` (p.18).
* `GammaPow γ S r = Γ^r = Γ_{S₁}^{r₁} ⋯ Γ_{S_m}^{r_m}` (p.29), in the index order of `Fin m`.
* `Mmap γ S F = MF`, `(MF)(g) := H(g) F(g)` with `H(g) = syk γ S g` (p.30).
* `Umap γ S ψ = Uψ`, the linear extension of `U f_r := (g ↦ h_r(g) Γ^r)`, (26), recorded as the
  function `g ↦ (Uψ)(g)`; that it is a matrix-valued polynomial of degree `⩽ t` for `ψ ∈ ⊕_{ℓ⩽t}F_ℓ`
  is a fact, stated where the page uses it (Lemma 4.16).
-/

/-- The normalized probabilists' Hermite polynomial `h_j = He_j/√(j!)` (Definition 3.5). -/
noncomputable def hermN (j : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite j) / Real.sqrt (j.factorial : ℝ)

/-- The multivariate normalized Hermite polynomial `h_r(g) = Π_i h_{r_i}(g_i)` (Definition 3.6). -/
noncomputable def hMulti {m : ℕ} (r : Fin m → ℕ) (g : Fin m → ℝ) : ℝ :=
  ∏ i, hermN (r i) (g i)

/-- Matrix-valued polynomials `K(ℝ^m; ℂ^{N×N})`: coefficient families `r ↦ M_r`, finitely many
nonzero. -/
abbrev MatPoly (m : ℕ) (ι : Type*) := (Fin m → ℕ) →₀ Matrix ι ι ℂ

/-- Evaluation `p(g) = Σ_r (Π_i g_i^{r_i}) · M_r`. -/
noncomputable def MatPoly.eval {m : ℕ} {ι : Type*} (P : MatPoly m ι) (g : Fin m → ℝ) :
    Matrix ι ι ℂ :=
  P.sum fun r M => (((∏ i, g i ^ r i : ℝ)) : ℂ) • M

/-- The degree of `P` is at most `L`: `|r| ⩽ L` whenever `M_r ≠ 0`. -/
def MatPoly.DegLE {m : ℕ} {ι : Type*} (P : MatPoly m ι) (L : ℕ) : Prop :=
  ∀ r ∈ P.support, ∑ i, r i ≤ L

/-- `‖F(g)‖_p := (E_{g∼N(0,Id_m)} ‖F(g)‖_HS^p)^{1/p}` (p.18). -/
noncomputable def gaussNorm {m : ℕ} {ι : Type*} [Fintype ι] (p : ℝ)
    (F : (Fin m → ℝ) → Matrix ι ι ℂ) : ℝ :=
  (∫ g, hsNorm (F g) ^ p ∂stdGauss (Fin m)) ^ (1 / p)

/-- `⟨F, G⟩_K := E_{g∼N(0,Id_m)} tr(F(g)* G(g))` (p.18). -/
noncomputable def Kinner {m : ℕ} {ι : Type*} [Fintype ι] (F G : (Fin m → ℝ) → Matrix ι ι ℂ) : ℂ :=
  ∫ g, ntr ((F g)ᴴ * G g) ∂stdGauss (Fin m)

/-- `Γ^r := Γ_{S₁}^{r₁} ⋯ Γ_{S_m}^{r_m}` (p.29). -/
noncomputable def GammaPow {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Fin n → Matrix ι ι ℂ) (S : Fin m → Finset (Fin n)) (r : Fin m → ℕ) : Matrix ι ι ℂ :=
  (List.ofFn fun i : Fin m => monomial γ (S i) ^ r i).prod

/-- The embedding `U : F → K(ℝ^m; ℂ^{N×N})`, `(U f_r)(g) := h_r(g) Γ^r`, (26), extended linearly. -/
noncomputable def Umap {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Fin n → Matrix ι ι ℂ) (S : Fin m → Finset (Fin n)) (ψ : Fock m) (g : Fin m → ℝ) :
    Matrix ι ι ℂ :=
  ψ.sum fun r c => (c * ((hMulti r g : ℝ) : ℂ)) • GammaPow γ S r

/-- The left multiplication operator `(MF)(g) := H(g) · F(g)` (p.30). -/
noncomputable def Mmap {n m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : Fin n → Matrix ι ι ℂ) (S : Fin m → Finset (Fin n)) (F : (Fin m → ℝ) → Matrix ι ι ℂ)
    (g : Fin m → ℝ) : Matrix ι ι ℂ :=
  syk γ S g * F g

end SYKEdge


