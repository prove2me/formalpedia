-- Prove2me | Definitions.Def_WHAdditivity_Renyi_Model
-- name    : WHAdditivity_Renyi_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:20.30644+00:00
-- url     : https://prove2.me/theorems/18e68d26-b4da-4014-a426-0a7d46fb5554
-- title:
--   (1), (6), pp. 1–3 — Werner–Holevo channel, tensor product of channels, pure states, von Neumann and p-Rényi entropies, minimal output entropy, reduced density matrices
-- statement:
--   The objects of Alicki and Fannes, *Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels*.
--
--   **Sites and configurations.** There are $N$ sites, site $j$ carrying the space $\mathbb C^{d_j}$. The joint space $\bigotimes_{j=1}^N \mathbb C^{d_j}$ has the product basis $|x\rangle = |x_1\rangle\otimes\cdots\otimes|x_N\rangle$, labelled by configurations $x = (x_1,\dots,x_N)$ with $x_j \in \{0,\dots,d_j-1\}$. For a set of sites $\Lambda \subset \{1,\dots,N\}$, a configuration of $\Lambda$ is the restriction $x|_\Lambda$.
--
--   **The Werner–Holevo channel** (6). For $d \ge 2$,
--   $$\Gamma_d(X) = \frac{1}{d-1}\bigl(\operatorname{Tr}(X)\,\mathbb 1 - X^{\mathsf T}\bigr),$$
--   where $X^{\mathsf T}$ is the transpose in the standard basis of $\mathbb C^d$. On a density matrix $\rho$ (trace one) this is the paper's $\Gamma_d(\rho) = \frac{1}{d-1}(\mathbb 1 - \rho^{\mathsf T})$.
--
--   **Tensor product of channels.** For linear maps $\Phi_j$ on $d_j\times d_j$ matrices, $\bigotimes_j \Phi_j$ is the linear map on matrices of $\bigotimes_j\mathbb C^{d_j}$ with
--   $$\langle y|\Bigl(\bigotimes_j\Phi_j\Bigr)(X)|y'\rangle = \sum_{x,x'} X_{x x'} \prod_{j=1}^N \langle y_j|\Phi_j\bigl(|x_j\rangle\langle x'_j|\bigr)|y'_j\rangle,$$
--   i.e. it acts as $\Phi_1\otimes\cdots\otimes\Phi_N$ on product matrix units and is extended linearly. It is defined for any family $\Phi$, not only for Werner–Holevo channels.
--
--   **Vectors and states.** A vector $v$ is a unit vector when $\sum_i |v_i|^2 = 1$; $|v\rangle\langle v|$ is the matrix with entries $v_i\overline{v_k}$; $\bar v$ is the entrywise complex conjugate. A density matrix is a positive semidefinite matrix of trace one.
--
--   **Entropies.** With the natural logarithm and the functional calculus of Hermitian matrices, the von Neumann entropy is $S(\rho) = -\operatorname{Tr}\rho\log\rho$ (with $0\log 0 = 0$), and the $p$-Rényi entropy for $p\ne 1$ is
--   $$S_p(\rho) = -\frac{1}{p-1}\log\operatorname{Tr}\rho^p .$$
--   At $p = 1$, $S_1$ is set equal to $S$.
--
--   **Minimal output entropy** (1). For a map $\Phi$ from matrices on an input space to matrices on an output space,
--   $$\mathrm{MEO}_p[\Phi] = \inf_{\varphi,\ \|\varphi\|=1} S_p\bigl(\Phi(|\varphi\rangle\langle\varphi|)\bigr),$$
--   the infimum over **all** unit vectors of the input space; for a product space this includes entangled vectors.
--
--   **Reduced matrices and products.** For a matrix $\rho$ on $\bigotimes_j\mathbb C^{d_j}$ and $\Lambda\subset\{1,\dots,N\}$, $\rho_\Lambda = \operatorname{Tr}_{\Lambda^{\mathrm c}}\rho$ is its partial trace over the sites outside $\Lambda$; $\sigma\otimes\mathbb 1_{\Lambda^{\mathrm c}}$ is a matrix $\sigma$ on the sites of $\Lambda$ tensored with the identity on the other sites (in the natural order of sites); $\bigotimes_j\rho_j$ is the tensor product of single-site matrices.
--
--   These are the objects in which the paper's additivity statement (7) and the steps of its proof are stated.
--
--   **Formalization Note.** Sites are `Fin N`, numbered from 0. Configurations are dependent functions `(j : Fin N) → Fin (d j)`, and the configurations of $\Lambda$ are functions on the subtype of $\Lambda$. Vectors are plain functions to $\mathbb C$, and $\bar v$ is `star v`. $\Gamma_d$ is written for every $d$; at $d = 1$ Lean's $0^{-1} = 0$ makes it the zero map, so every theorem assumes $d_j \ge 2$. The entropies use Mathlib's `cfc` on `Matrix ι ι ℂ` and are only meaningful on Hermitian inputs; every theorem applies them to channel outputs of pure states or to density matrices. $\mathrm{MEO}_p$ is a real `sInf`, which is $0$ on a set that is empty or unbounded below, so every theorem using it also concludes that the set is bounded below. The same channel body appears on the platform as `QAlgorithms.Papers.Independent.Information100.P60.wernerHolevo`, and the same matrix-unit tensor product, for one common site dimension, as `QAlgorithms.Defs.Channel.piSuperop`; neither is imported, the first because its module pulls in four unrelated layers, the second because the paper needs site-dependent dimensions $d_j$.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, pp. 1–3, (1), (6)

import Mathlib

noncomputable section

namespace WHAdditivity.Renyi

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

/-- Joint basis labels of ⊗_j ℂ^{d_j}; site j of the paper is `j : Fin N` (counted from 0). -/
abbrev Config {N : ℕ} (d : Fin N → ℕ) : Type := (j : Fin N) → Fin (d j)

/-- Basis labels of the sites in Λ ⊂ {1, …, N}. -/
abbrev SubConfig {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) : Type := (j : Λ) → Fin (d j)

/-- (6), p. 2, extended linearly: Γ_d(X) = (Tr X · 𝟙 − Xᵀ)/(d − 1); on a trace-one ρ this is
(𝟙 − ρᵀ)/(d − 1). -/
def wernerHolevo (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((d : ℂ) - 1)⁻¹ • (X.trace • (1 : Matrix (Fin d) (Fin d) ℂ) - Xᵀ)

/-- ⊗_j Φ_j on ⊗_j ℂ^{d_j}, through matrix units:
⟨y|(⊗_j Φ_j)(X)|y′⟩ = Σ_{x,x′} X_{x x′} Π_j ⟨y_j|Φ_j(|x_j⟩⟨x′_j|)|y′_j⟩, for any family Φ. -/
def tensorChannel {N : ℕ} (d : Fin N → ℕ)
    (Φ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ → Matrix (Fin (d j)) (Fin (d j)) ℂ)
    (X : Matrix (Config d) (Config d) ℂ) : Matrix (Config d) (Config d) ℂ :=
  Matrix.of fun y y' => ∑ x : Config d, ∑ x' : Config d,
    X x x' * ∏ j, Φ j (Matrix.single (x j) (x' j) 1) (y j) (y' j)

/-- ‖v‖ = 1. -/
def IsUnitVector {ι : Type*} [Fintype ι] (v : ι → ℂ) : Prop := ∑ i, Complex.normSq (v i) = 1

/-- |v⟩⟨v|, with entries v_i · conj v_k. -/
def pureState {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec v (star v)

/-- ρ is a density matrix: positive semidefinite with trace one. -/
def IsDensity {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- S(ρ) = −Tr ρ log ρ (natural log, 0 log 0 = 0), by the continuous functional calculus. -/
def vonNeumannEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) : ℝ :=
  (cfc Real.negMulLog ρ).trace.re

/-- Tr ρᵖ, by the continuous functional calculus. -/
def traceRpow {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (ρ : Matrix ι ι ℂ) : ℝ :=
  (cfc (fun x : ℝ => x ^ p) ρ).trace.re

/-- S_p(ρ) = −(1/(p − 1)) log Tr ρᵖ for p ≠ 1, and S_1 = S (the paper's extension to p = 1). -/
def renyiEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (ρ : Matrix ι ι ℂ) : ℝ :=
  if p = 1 then vonNeumannEntropy ρ else (1 - p)⁻¹ * Real.log (traceRpow p ρ)

/-- The values S_p(Φ(|φ⟩⟨φ|)) over all unit vectors φ (entangled ones included when ι is a
product of sites). -/
def outputEntropies {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ℝ)
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) : Set ℝ :=
  {s | ∃ φ : ι → ℂ, IsUnitVector φ ∧ s = renyiEntropy p (Φ (pureState φ))}

/-- (1), p. 1: MEO_p(Φ) = inf_{‖φ‖=1} S_p(Φ(|φ⟩⟨φ|)). Theorems using it conclude `BddBelow`
of `outputEntropies p Φ`. -/
def minOutputEntropy {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ℝ)
    (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ) : ℝ :=
  sInf (outputEntropies p Φ)

/-- The labels of y on the sites in Λ. -/
def restrict {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (y : Config d) : SubConfig d Λ :=
  fun j => y j

/-- ρ_Λ = Tr_{Λᶜ} ρ, the reduced matrix of ρ on the sites in Λ. -/
def reducedMatrix {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N))
    (ρ : Matrix (Config d) (Config d) ℂ) : Matrix (SubConfig d Λ) (SubConfig d Λ) ℂ :=
  Matrix.of fun a b => ∑ z : Config d, ∑ z' : Config d,
    if restrict d Λ z = a ∧ restrict d Λ z' = b ∧ (∀ j, j ∉ Λ → z j = z' j) then ρ z z' else 0

/-- σ ⊗ 𝟙_{Λᶜ}, in the natural site order. -/
def tensorIdentity {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N))
    (σ : Matrix (SubConfig d Λ) (SubConfig d Λ) ℂ) : Matrix (Config d) (Config d) ℂ :=
  Matrix.of fun y y' =>
    if ∀ j, j ∉ Λ → y j = y' j then σ (restrict d Λ y) (restrict d Λ y') else 0

/-- ⊗_j ρ_j. -/
def tensorMatrix {N : ℕ} (d : Fin N → ℕ) (ρ : (j : Fin N) → Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    Matrix (Config d) (Config d) ℂ :=
  Matrix.of fun y y' => ∏ j, ρ j (y j) (y' j)

end WHAdditivity.Renyi


