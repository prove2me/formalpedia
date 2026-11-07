-- Prove2me | Definitions.Def_FermiHubbardMix_ckgLind
-- name    : FermiHubbardMix_ckgLind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:03.059656+00:00
-- url     : https://prove2.me/theorems/0d829603-57de-48b7-9dc2-a4c5771f3096
-- title:
--   Generalized CKG Lindbladian: $A_B(\omega)$, $\gamma_B$, $b_1$, $b_2$, $C_B$, $\mathcal L_B$
-- statement:
--   Let $\beta>0$ and $H$ be a fermionic Hamiltonian. For each site $i$ let $\mathcal B_i\subseteq\mathfrak A_{\{i\}}$ be a finite adjoint-closed set of homogeneous operators, and for each $B\in\mathcal B_i$ choose $\Delta_B,\sigma_B,\eta_B>0$ with
--   $$
--   \beta(\eta_B^2+\sigma_B^2)=2\Delta_B,\qquad \Delta_B=\Delta_{B^\dagger},\ \sigma_B=\sigma_{B^\dagger},\ \eta_B=\eta_{B^\dagger}.\tag{16}
--   $$
--   With the filter $f_B(t)=\sqrt{\sigma_B}(2/\pi)^{1/4}e^{-\sigma_B^2t^2}$, the jump operators are
--   $$
--   A_B(\omega)=\frac1{\sqrt{2\pi}}\int_{-\infty}^{\infty}e^{iHt}Be^{-iHt}e^{-i\omega t}f_B(t)\,dt,\tag{17}
--   $$
--   the transition weight is $\gamma_B(\omega)=\exp(-(\omega+\Delta_B)^2/(2\eta_B^2))$, and the dissipative part is $\mathcal L_{\mathrm{diss},B}(\rho)=\int\gamma_B(\omega)\bigl(A_B(\omega)\rho A_B(\omega)^\dagger-\tfrac12\{A_B(\omega)^\dagger A_B(\omega),\rho\}\bigr)d\omega$. With the kernels
--   $$
--   b_1(t,\sigma)=\frac{\sigma}{\pi\beta}e^{\beta^2\sigma^2/8}\Bigl(\operatorname{sech}\tfrac{2\pi t}{\beta}*_t\sin(-\beta\sigma^2t)e^{-2\sigma^2t^2}\Bigr),\qquad b_2(t,\eta,\Delta)=2\eta\exp\Bigl(-\frac{4\Delta t^2}{\beta}-2i\Delta t\Bigr),
--   $$
--   the coherent term is
--   $$
--   C_B=\int b_1(t,\sigma_B)\,e^{-iHt}\Bigl(\int b_2(t',\eta_B,\Delta_B)\,e^{iHt'}B^\dagger e^{-2iHt'}Be^{iHt'}\,dt'\Bigr)e^{iHt}\,dt,\tag{18}
--   $$
--   and $\mathcal L_B(\rho)=-i[C_B,\rho]+\mathcal L_{\mathrm{diss},B}(\rho)$, $\mathcal L=\sum_i\sum_{B\in\mathcal B_i}\mathcal L_B$ (Definition 13.1).
--
--   This is the Gibbs sampler of the paper: the Chen–Kastoryano–Gilyén Lindbladian with jump-dependent parameters.
--
--   **Formalization Note** All operator integrals are entrywise Bochner integrals; every integrand is Gaussian-dominated. The convolution is $\int\operatorname{sech}(2\pi s/\beta)\sin(-\beta\sigma^2(t-s))e^{-2\sigma^2(t-s)^2}ds$. The superoperators are the linear extensions of their values on matrix units. The jump family is indexed by a finite type with an involution pairing each jump with its adjoint (a set closed under adjoints is the injective case).
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 13.1, pp.59–60, eqs. (16)–(18)

import Mathlib
import Definitions.Def_FermiHubbardMix_localAlg
import Definitions.Def_FermiHubbardMix_gibbs
open scoped BigOperators
open Matrix Real
noncomputable section

namespace FermiHubbardMix

variable {N : ℕ}

/-- The filter function `f_B(t) = √σ_B (2/π)^{1/4} e^{-σ_B² t²}` (arXiv:2604.08408, held version
sha256 055b8f8f…, Definition 13.1, p.59). -/
def filt (σ t : ℝ) : ℝ := Real.sqrt σ * (2 / π) ^ (1 / 4 : ℝ) * Real.exp (-(σ ^ 2 * t ^ 2))

/-- The filtered jump operator, eq. (17) (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 13.1, p.59): `A_B(ω) = (2π)^{-1/2} ∫ e^{iHt} B e^{-iHt} e^{-iωt} f_B(t) dt`.

**Formalization Note** The operator-valued integral is taken entrywise (Bochner integrals of
complex functions). The integrand is bounded by a Gaussian, so it is integrable and the entrywise
integral is the paper's integral. -/
def jumpOp (H B : Op N) (σ ω : ℝ) : Op N :=
  Matrix.of fun x y => ((Real.sqrt (2 * π))⁻¹ : ℂ) *
    ∫ t : ℝ, heis H t B x y * Complex.exp (-(Complex.I * ω * t)) * (filt σ t : ℂ)

/-- The transition weight `γ_B(ω) = exp(-(ω + Δ_B)² / (2η_B²))` (arXiv:2604.08408, held version
sha256 055b8f8f…, Definition 13.1, p.59). -/
def gammaW (Δ η ω : ℝ) : ℝ := Real.exp (-((ω + Δ) ^ 2 / (2 * η ^ 2)))

/-- The dissipator `D_A(X) = A X A† - ½{A†A, X}` (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 13.1, p.59, and Lemma 14.4, p.66). -/
def dissipator (A X : Op N) : Op N := A * X * Aᴴ - (1 / 2 : ℂ) • (Aᴴ * A * X + X * (Aᴴ * A))

/-- The dissipative part `L_diss,B(ρ) = ∫ γ_B(ω) D_{A_B(ω)}(ρ) dω` (arXiv:2604.08408, held version
sha256 055b8f8f…, Definition 13.1, p.59), as a function; entrywise integral (see `jumpOp`). -/
def dissipFun (H B : Op N) (σ η Δ : ℝ) (ρ : Op N) : Op N :=
  Matrix.of fun x y => ∫ ω : ℝ, (gammaW Δ η ω : ℂ) * dissipator (jumpOp H B σ ω) ρ x y

/-- The kernel `b₁(t, σ) = σ/(πβ) e^{β²σ²/8} (sech(2πt/β) ∗_t sin(-βσ²t) e^{-2σ²t²})`
(arXiv:2604.08408, held version sha256 055b8f8f…, Definition 13.1, p.59).

**Formalization Note** The convolution `(f ∗ g)(t) = ∫ f(s) g(t - s) ds` is written out with
`f(s) = sech(2πs/β) = 1/cosh(2πs/β)` and `g(u) = sin(-βσ²u) e^{-2σ²u²}`. -/
def b1 (β σ t : ℝ) : ℝ :=
  σ / (π * β) * Real.exp (β ^ 2 * σ ^ 2 / 8) *
    ∫ s : ℝ, (Real.cosh (2 * π * s / β))⁻¹ *
      (Real.sin (-(β * σ ^ 2 * (t - s))) * Real.exp (-(2 * σ ^ 2 * (t - s) ^ 2)))

/-- The kernel `b₂(t, η, Δ) = 2η exp(-4Δt²/β - 2iΔt)` (arXiv:2604.08408, held version sha256
055b8f8f…, Definition 13.1, p.59). -/
def b2 (β η Δ t : ℝ) : ℂ :=
  2 * (η : ℂ) * Complex.exp (-((4 * Δ * t ^ 2 / β : ℝ) : ℂ) - 2 * Complex.I * Δ * t)

/-- The coherent term, eq. (18) (arXiv:2604.08408, held version sha256 055b8f8f…,
Definition 13.1, p.60):
`C_B = ∫ b₁(t, σ_B) e^{-iHt} (∫ b₂(t', η_B, Δ_B) e^{iHt'} B† e^{-2iHt'} B e^{iHt'} dt') e^{iHt} dt`;
entrywise integrals (see `jumpOp`). -/
def cohTerm (H B : Op N) (β σ η Δ : ℝ) : Op N :=
  let inner : Op N := Matrix.of fun x y => ∫ t' : ℝ, b2 β η Δ t' *
    (NormedSpace.exp ((Complex.I * t') • H) * Bᴴ * NormedSpace.exp ((-(2 * Complex.I * t')) • H) * B *
      NormedSpace.exp ((Complex.I * t') • H)) x y
  Matrix.of fun x y => ∫ t : ℝ, (b1 β σ t : ℂ) *
    (NormedSpace.exp ((-(Complex.I * t)) • H) * inner * NormedSpace.exp ((Complex.I * t) • H)) x y

/-- The linear extension of a map on operators from its values on the matrix units
`|x⟩⟨y|` of the occupation basis.

**Formalization Note** The paper's superoperators (`L_diss,B`, `L_B`) are linear in `ρ`
(their integrals converge absolutely), so each equals the linear extension of its values on a
basis; this is how they are made into `ℂ`-linear maps here. -/
def linExt (f : Op N → Op N) : Op N →ₗ[ℂ] Op N :=
  (Matrix.stdBasis ℂ (Fin N → Fin 2) (Fin N → Fin 2)).constr ℂ
    (fun p => f (Matrix.stdBasis ℂ (Fin N → Fin 2) (Fin N → Fin 2) p))

/-- The commutator map `X ↦ [C, X] = CX - XC`. -/
def commLin (C : Op N) : Op N →ₗ[ℂ] Op N := LinearMap.mulLeft ℂ C - LinearMap.mulRight ℂ C

/-- **Definition 13.1**, the Lindbladian generated by one jump `B` (arXiv:2604.08408, held version
sha256 055b8f8f…, p.60): `L_B(ρ) = -i[C_B, ρ] + L_diss,B(ρ)`, for the Hamiltonian `H`, inverse
temperature `β` and parameters `σ_B, η_B, Δ_B`. -/
def jumpLind (H B : Op N) (β σ η Δ : ℝ) : Op N →ₗ[ℂ] Op N :=
  (-Complex.I) • commLin (cohTerm H B β σ η Δ) + linExt (dissipFun H B σ η Δ)

/-- The jump data of **Definition 13.1** (arXiv:2604.08408, held version sha256 055b8f8f…,
pp.59–60): a finite family of jumps `B_j` located at sites `site j`, with parameters
`Δ_j, σ_j, η_j` and an involution `adj` that pairs each jump with its adjoint.

**Formalization Note** The paper's finite adjoint-closed sets `B_i ⊆ 𝔄_{{i}}` are the special case of
an injective family; `adj j` indexes `B_j†`. -/
structure CKGFamily (Λ : Type*) (N : ℕ) (ι : Type*) where
  /-- the site of each jump -/
  site : ι → Λ
  /-- the jump operators -/
  B : ι → Op N
  /-- the parameters `Δ_B` -/
  Δ : ι → ℝ
  /-- the parameters `σ_B` -/
  σ : ι → ℝ
  /-- the parameters `η_B` -/
  η : ι → ℝ
  /-- the index of the adjoint jump -/
  adj : ι → ι

/-- The hypotheses of **Definition 13.1** on the jump data (arXiv:2604.08408, held version sha256
055b8f8f…, p.59, eq. (16)): each `B_j ∈ 𝔄_{{site j}}` is homogeneous, the family is closed under
adjoints (`B_{adj j} = B_j†`, same site), `Δ_B, σ_B, η_B > 0`, `β(η_B² + σ_B²) = 2Δ_B`, and the
parameters of `B` and `B†` agree. -/
def CKGFamily.Admissible {Λ : Type*} {m : ℕ} {ι : Type*} (ord : Λ × Fin m ≃ Fin N) (β : ℝ)
    (F : CKGFamily Λ N ι) : Prop :=
  (∀ j, F.B j ∈ localAlg ord {F.site j}) ∧ (∀ j, IsEven (F.B j) ∨ IsOdd (F.B j)) ∧
  (∀ j, F.adj (F.adj j) = j ∧ F.site (F.adj j) = F.site j ∧ F.B (F.adj j) = (F.B j)ᴴ) ∧
  (∀ j, 0 < F.Δ j ∧ 0 < F.σ j ∧ 0 < F.η j) ∧
  (∀ j, β * (F.η j ^ 2 + F.σ j ^ 2) = 2 * F.Δ j) ∧
  (∀ j, F.Δ (F.adj j) = F.Δ j ∧ F.σ (F.adj j) = F.σ j ∧ F.η (F.adj j) = F.η j)

/-- **Definition 13.1 (Generalization of CKG Lindbladian)** (arXiv:2604.08408, held version sha256
055b8f8f…, pp.59–60): `L = ∑_i ∑_{B ∈ B_i} L_B`. -/
def ckgLind {Λ : Type*} {ι : Type*} [Fintype ι] (H : Op N) (β : ℝ) (F : CKGFamily Λ N ι) :
    Op N →ₗ[ℂ] Op N :=
  ∑ j, jumpLind H (F.B j) β (F.σ j) (F.η j) (F.Δ j)

end FermiHubbardMix


