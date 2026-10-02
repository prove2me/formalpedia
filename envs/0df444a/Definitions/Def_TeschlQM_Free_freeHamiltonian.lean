-- Prove2me | Definitions.Def_TeschlQM_Free_freeHamiltonian
-- name    : TeschlQM_Free_freeHamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T00:03:49.589698+00:00
-- url     : https://prove2.me/theorems/c8039e9d-6e29-4f95-8700-dd03692900b9
-- title:
--   The free Schrödinger operator H₀ = −Δ with domain H²(ℝⁿ) (7.20)–(7.24)
-- statement:
--   For a function $g : \mathbb R^n \to \mathbb C$, the **maximally defined multiplication operator** by $g$ in $L^2(\mathbb R^n)$ acts by $(g\varphi)(x) = g(x)\varphi(x)$ on the domain $\{\varphi \in L^2(\mathbb R^n) \mid g\varphi \in L^2(\mathbb R^n)\}$.
--
--   The **free Schrödinger operator** is $H_0 = -\Delta$, $\Delta = \sum_{j=1}^n \partial^2/\partial x_j^2$, with domain the Sobolev space $\mathfrak D(H_0) = H^2(\mathbb R^n) = \{\psi \in L^2(\mathbb R^n) \mid p^2 \hat\psi(p) \in L^2(\mathbb R^n)\}$, where it acts by
--   $$H_0 \psi = -\Delta\psi = \mathcal F^{-1}\big(p^2 \hat\psi(p)\big).$$
--   Equivalently, $\mathcal F H_0 \mathcal F^{-1}$ is the maximally defined multiplication operator by $p^2$. The units are $\hbar = 1$ and mass $m = 1/2$.
--
--   $H_0$ is the Hamiltonian of $N$ non-interacting particles in $\mathbb R^d$, $n = Nd$, and the reference operator for every Schrödinger operator $H_0 + V$ in the rest of the book.
--
--   **Formalization Note.** `mulOp n g` is the maximal multiplication operator as a `LinearPMap` on `Lp ℂ 2 volume` over `EuclideanSpace ℝ (Fin n)`. `freeHamiltonian n` is $\mathcal F_{\mathrm M}^{-1} \circ$ `mulOp n (4π²‖ξ‖²)` $\circ\, \mathcal F_{\mathrm M}$ with domain $\{\psi \mid \mathcal F_{\mathrm M}\psi \in \mathfrak D(\text{mulOp})\}$, where $\mathcal F_{\mathrm M}$ is Mathlib's unitary $L^2$ Fourier transform (normalization $e^{-2\pi i\langle x,\xi\rangle}$). In that normalization $-\Delta$ is multiplication by $4\pi^2|\xi|^2$, so this is the same operator as Teschl's $\mathcal F^{-1} p^2 \mathcal F$: $-\Delta$ does not depend on the normalization, and $\{|\xi|^2 \mathcal F_{\mathrm M}\psi \in L^2\}$ is Teschl's $H^2(\mathbb R^n)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 167, Section 7.2, Eqs. (7.20)–(7.24)

import Mathlib

namespace TeschlQM.Free

open MeasureTheory FourierTransform

/-- The maximal domain `{φ ∈ L²(ℝⁿ) | g φ ∈ L²(ℝⁿ)}` of the multiplication operator by a function
`g : ℝⁿ → ℂ` (Teschl (7.24), p. 167, for `g(p) = p²`). -/
noncomputable def mulDomain (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) where
  carrier := {φ | MemLp (fun x => g x * φ x) 2 volume}
  add_mem' := by
    intro a b ha hb
    refine (ha.add hb).ae_eq ?_
    filter_upwards [Lp.coeFn_add a b] with x hx
    simp only [Pi.add_apply, hx, mul_add]
  zero_mem' := by
    refine (MemLp.zero (ε := ℂ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))] with x hx
    simp only [Pi.zero_apply, hx, mul_zero]
  smul_mem' := by
    intro c a ha
    refine (ha.const_smul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c a] with x hx
    simp only [Pi.smul_apply, hx, smul_eq_mul]
    ring

theorem mem_mulDomain {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℂ}
    {φ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))} :
    φ ∈ mulDomain n g ↔ MemLp (fun x => g x * φ x) 2 volume :=
  Iff.rfl

/-- Teschl (7.24), p. 167: the maximally defined multiplication operator by `g` in `L²(ℝⁿ)`,
`(g φ)(x) = g(x) φ(x)` with domain `{φ ∈ L² | g φ ∈ L²}`. -/
noncomputable def mulOp (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℂ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  domain := mulDomain n g
  toFun :=
    { toFun := fun φ => MemLp.toLp (fun x => g x * (φ : Lp ℂ 2 volume) x) (mem_mulDomain.1 φ.2)
      map_add' := by
        intro a b
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_add (a : Lp ℂ 2 _) (b : Lp ℂ 2 _)] with x hx
        simp only [Submodule.coe_add, Pi.add_apply, hx, mul_add]
      map_smul' := by
        intro c a
        rw [← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        filter_upwards [Lp.coeFn_smul c (a : Lp ℂ 2 _)] with x hx
        simp only [SetLike.val_smul, Pi.smul_apply, hx, smul_eq_mul, RingHom.id_apply]
        ring }

/-- Teschl (7.20)–(7.24), pp. 167–168: the **free Schrödinger operator** `H₀ = -Δ` on
`L²(ℝⁿ)` with domain `𝔇(H₀) = H²(ℝⁿ)`, defined as the Fourier conjugate of the maximally defined
multiplication operator by the symbol of `-Δ`: `H₀ = 𝓕⁻¹ ∘ M ∘ 𝓕` with domain
`{ψ ∈ L² | 𝓕ψ ∈ 𝔇(M)}`.

Here `𝓕` is Mathlib's unitary Fourier transform on `L²(ℝⁿ)` (normalization `e^{-2πi⟪x, ξ⟫}`),
under which `-Δ` is multiplication by `4π²‖ξ‖²`; this is the same operator as Teschl's
`F⁻¹ p² F` with his normalization (7.3), since `-Δ` does not depend on the normalization, and the
domain `{ψ | ‖ξ‖² 𝓕ψ(ξ) ∈ L²}` is Teschl's `H²(ℝⁿ) = {ψ ∈ L² | |p|² ψ̂(p) ∈ L²}` (7.12). -/
noncomputable def freeHamiltonian (n : ℕ) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  domain := (mulDomain n fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)).comap
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).toLinearEquiv.toLinearMap
  toFun :=
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).symm.toLinearEquiv.toLinearMap ∘ₗ
      (mulOp n fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)).toFun ∘ₗ
        LinearMap.codRestrict (mulDomain n fun ξ => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))
          ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).toLinearEquiv.toLinearMap ∘ₗ
            Submodule.subtype _)
          (fun ψ => Submodule.mem_comap.1 ψ.2)

end TeschlQM.Free


