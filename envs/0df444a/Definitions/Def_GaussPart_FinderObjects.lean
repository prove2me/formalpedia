-- Prove2me | Definitions.Def_GaussPart_FinderObjects
-- name    : GaussPart_FinderObjects
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:17.346094+00:00
-- url     : https://prove2.me/theorems/27f82315-be59-4d07-9ecb-bbf7039948e1
-- title:
--   Objects of the moment discrepancy finder (Algorithm 2)
-- statement:
--   For $P=N(0,I_d)$ and a distribution $Q$ on $\mathbb R^d$:
--   1. the **$V$-assumption** $\mathbb E_Q[p^2]\le V\|p\|^2_{L^2(P)}$ for every polynomial $p$ of degree at most $k$;
--   2. $F_k=(2k)^{2k}$, $\tau=\Delta/(100\,k\,2^kF_k)$ and $\rho=\Delta/(100\,kF_kH)$;
--   3. the moment discrepancy $F_\ell(z)=\mathbb E_Q[(z\cdot x)^\ell]-\mathbb E_P[(z\cdot x)^\ell]$, the Gaussian reference moment $\mathbb E_{Z\sim N(0,1)}[Z^\ell]$ and the empirical discrepancy $\hat F_\ell(z)=\frac1n\sum_s(z\cdot x^{(s)})^\ell-\mathbb E[Z^\ell]$;
--   4. for an order-$(m+1)$ tensor, the Gram matrix $\hat M\hat M^\top$ of its flattening $\hat M\in\mathbb R^{d\times d^m}$, and $U$, the sum of the eigenspaces of $\hat M\hat M^\top$ for eigenvalues at least $\tau^2$ (the span of the left singular vectors with singular value at least $\tau$);
--   5. the bound $\|\mathrm{proj}_{U^\perp}\hat M\|_{op}\le\tau$, tensor symmetry, the augmentation $W'$ of $W$ (equal to $W$ if $W=\mathbb R^d$, else $W+\mathrm{span}\{e\}$ for a unit $e\perp W$), $\rho$-nets of $W'\cap S^{d-1}$, and the explicit grid net of the proof of Claim 3.20 (grid of spacing $\rho/(4\sqrt r)$ in $[-1-\rho,1+\rho]^r$, nonzero points normalized).
--
--   **Formalization Note** The $V$-assumption is written with lower Lebesgue integrals of $p^2$: under an arbitrary $Q$ the square of a polynomial need not be integrable, and a Bochner integral would then be $0$. Polynomials are `MvPolynomial (Fin d) ℝ` of total degree at most $k$.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Proposition 3.3, p.15 (PDF p.17); Algorithm 2, p.29 (PDF p.31); proofs pp.30–34

import Mathlib
import Definitions.Def_GaussPart_Cell

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussPart

/-- The V-assumption of **Proposition 3.3**, arXiv:2611.05264 (sha256 7e0ca6d4…), p.15 (PDF p.17):
`E_{x∼Q}[p(x)²] ≤ V ‖p‖²_{L²(P)}` for every polynomial `p` of degree at most `k`, `P = N(0, I_d)`.

**Formalization Note.** It is written with lower integrals. Under an arbitrary `Q` the function
`p²` need not be integrable, and a Bochner integral would then be `0`, making the assumption vacuous
there. -/
def PolyMomentBound {d : ℕ} (Q : Measure (Vec d)) (V : ℝ) (k : ℕ) : Prop :=
  ∀ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ k →
    ∫⁻ x, ENNReal.ofReal (MvPolynomial.eval (fun i => x i) p ^ 2) ∂Q ≤
      ENNReal.ofReal V *
        ∫⁻ x, ENNReal.ofReal (MvPolynomial.eval (fun i => x i) p ^ 2) ∂(stdGaussian (Vec d))

/-- `F_k = (2k)^{2k}` (Algorithm 2, line 3, p.29, PDF p.31). -/
noncomputable def finderF (k : ℕ) : ℝ := (2 * (k : ℝ)) ^ (2 * k)

/-- `τ = Δ/(100 k 2^k F_k)` (Algorithm 2, line 3, p.29). -/
noncomputable def finderTau (k : ℕ) (Δ : ℝ) : ℝ := Δ / (100 * k * 2 ^ k * finderF k)

/-- `ρ = Δ/(100 k F_k H)` (Algorithm 2, line 12, p.29). -/
noncomputable def finderRho (k : ℕ) (Δ H : ℝ) : ℝ := Δ / (100 * k * finderF k * H)

/-- The degree-`ℓ` moment discrepancy at `z` (proof of Proposition 3.3, p.31):
`F_ℓ(z) = E_Q[(z · x)^ℓ] − E_P[(z · x)^ℓ]`, `P = N(0, I_d)`. -/
noncomputable def momentGap {d : ℕ} (Q : Measure (Vec d)) (ℓ : ℕ) (z : Vec d) : ℝ :=
  ∫ x, ⟪z, x⟫ ^ ℓ ∂Q - ∫ x, ⟪z, x⟫ ^ ℓ ∂(stdGaussian (Vec d))

/-- The Gaussian reference moment `E_{Z∼N(0,1)}[Z^ℓ]`. -/
noncomputable def gaussianMoment (ℓ : ℕ) : ℝ := ∫ z, z ^ ℓ ∂(gaussianReal 0 1)

/-- The empirical discrepancy (p.33): `F̂_ℓ(z) = (1/n) ∑_s (z · x⁽ˢ⁾)^ℓ − E_{Z∼N(0,1)}[Z^ℓ]`. -/
noncomputable def empiricalGap {n d : ℕ} (xs : Fin n → Vec d) (ℓ : ℕ) (z : Vec d) : ℝ :=
  (1 / (n : ℝ)) * ∑ s, ⟪z, xs s⟫ ^ ℓ - gaussianMoment ℓ

/-- `M̂ M̂ᵀ` for the flattening `M̂ ∈ ℝ^{d × d^{m}}` of an order-`(m+1)` tensor (p.32): the first index
is the row, the others the column. -/
noncomputable def flattenGram {m d : ℕ} (A : (Fin (m + 1) → Fin d) → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => ∑ J : Fin m → Fin d,
    A (Fin.cons a J : Fin (m + 1) → Fin d) * A (Fin.cons b J : Fin (m + 1) → Fin d)

/-- `U_i`, "the span of the left singular vectors with singular value at least `τ`" (Algorithm 2,
line 9, p.29): the sum of the eigenspaces of `M̂ M̂ᵀ` for eigenvalues at least `τ²`. It does not
depend on a choice of eigenbasis. -/
noncomputable def singularSubspace {m d : ℕ} (A : (Fin (m + 1) → Fin d) → ℝ) (τ : ℝ) :
    Submodule ℝ (Vec d) :=
  ⨆ (μ : ℝ) (_ : τ ^ 2 ≤ μ),
    Module.End.eigenspace (Matrix.toEuclideanLin (flattenGram A)) μ

/-- `‖proj_{U^⊥} M̂‖_op ≤ τ` for the flattening `M̂` of `A` (p.33): the bilinear form of `M̂` is at
most `τ ‖w‖ ‖z‖_F` for `w ∈ U^⊥` and every `z ∈ ℝ^{d^m}`. -/
def OpBoundOn {m d : ℕ} (U : Submodule ℝ (Vec d)) (A : (Fin (m + 1) → Fin d) → ℝ) (τ : ℝ) : Prop :=
  ∀ w ∈ Uᗮ, ∀ z : (Fin m → Fin d) → ℝ,
    |∑ a, ∑ J : Fin m → Fin d, w a * A (Fin.cons a J : Fin (m + 1) → Fin d) * z J| ≤
      τ * ‖w‖ * Real.sqrt (∑ J, z J ^ 2)

/-- Every permutation of the indices fixes the tensor. -/
def IsSymmetricTensor {i d : ℕ} (A : (Fin i → Fin d) → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin i)) (J : Fin i → Fin d), A (J ∘ π) = A J

/-- `W′` of Algorithm 2, line 11 (p.29): if `W ≠ ℝᵈ`, then `W′ = W + span{e}` for a unit `e ∈ W^⊥`;
otherwise `W′ = W`. -/
def IsAugmented {d : ℕ} (W W' : Submodule ℝ (Vec d)) : Prop :=
  (W = ⊤ ∧ W' = W) ∨ ∃ e ∈ Wᗮ, ‖e‖ = 1 ∧ W' = W ⊔ Submodule.span ℝ {e}

/-- `C` is a `ρ`-net of `W ∩ S^{d−1}` (Algorithm 2, line 12, p.29): its points are unit vectors of
`W`, and every unit vector of `W` is within `ρ` of one of them. -/
def IsNet {d : ℕ} (W : Submodule ℝ (Vec d)) (ρ : ℝ) (C : Finset (Vec d)) : Prop :=
  (∀ z ∈ C, z ∈ W ∧ ‖z‖ = 1) ∧ ∀ u ∈ W, ‖u‖ = 1 → ∃ z ∈ C, ‖z - u‖ ≤ ρ

open Classical in
/-- The explicit net of the proof of Claim 3.20 (p.34, PDF p.36) in `ℝʳ`: the grid of spacing
`ρ/(4√r)` in `[−1−ρ, 1+ρ]ʳ`, without `0`, with every point normalized. -/
noncomputable def gridNet (r : ℕ) (ρ : ℝ) : Finset (Vec r) :=
  let h : ℝ := ρ / (4 * Real.sqrt r)
  let N : ℤ := ⌊(1 + ρ) / h⌋
  ((Fintype.piFinset fun _ : Fin r => Finset.Icc (-N) N).filter fun g => g ≠ 0).image fun g =>
    let y : Vec r := WithLp.toLp 2 fun i => h * (g i : ℝ)
    (‖y‖)⁻¹ • y

end GaussPart


