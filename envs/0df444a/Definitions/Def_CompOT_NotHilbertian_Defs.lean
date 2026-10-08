-- Prove2me | Definitions.Def_CompOT_NotHilbertian_Defs
-- name    : CompOT_NotHilbertian_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:26.672987+00:00
-- url     : https://prove2.me/theorems/c493e5cd-4d2f-457a-a061-1e4da1e1562e
-- title:
--   Def 8.3, Def 8.4, (2.10)–(2.11), (2.18), pp. 370–377, 501, 506–507 — negative definiteness, Hilbertian distances, W_p on ℝ^d, the four corners and the 1/4-grid of Σ₄
-- statement:
--   These are the objects of §8.3 (*Wasserstein Spaces Are Not Hilbertian*), together with the transport objects they use.
--
--   1. **Hilbertian functions (Definition 8.4).** Let $\mathcal Z$ be a set. A function $d:\mathcal Z\times\mathcal Z\to\mathbb R$ is *Hilbertian* if there exist a real Hilbert space $\mathcal H$ and a map $\phi:\mathcal Z\to\mathcal H$ such that
--   $$d(z,z')=\|\phi(z)-\phi(z')\|_{\mathcal H}\qquad\text{for all } z,z'\in\mathcal Z.$$
--   2. **Negative definiteness (Definition 8.3, conditional form).** A function $\varphi:\mathcal Z\times\mathcal Z\to\mathbb R$ is *negative definite* if it is symmetric and, for every $n\ge0$, every family $x_1,\dots,x_n\in\mathcal Z$ and every $r\in\mathbb R^n$ with $\sum_i r_i=0$,
--   $$\sum_{i,j=1}^n r_ir_j\,\varphi(x_i,x_j)\le 0.$$
--   3. **Wasserstein space.** On $\mathbb R^d$ with the Euclidean norm, $\mathcal P_p(\mathbb R^d)$ is the set of Borel probability measures $\mu$ with $\int\|x\|_2^p\,d\mu(x)<\infty$. For $\mu,\nu$ in it, $\mathcal W_p(\mu,\nu)=\big(\inf_{\pi\in\mathcal U(\mu,\nu)}\int\|x-y\|_2^p\,d\pi(x,y)\big)^{1/p}$ (2.18), the infimum over couplings of $\mu$ and $\nu$; this value is finite on $\mathcal P_p(\mathbb R^d)$, and $\mathcal W_p$ is regarded as a real-valued function there.
--   4. **Discrete transport (2.10)–(2.11).** For histograms $a,b\in\mathbb R^n$, $U(a,b)$ is the set of nonnegative $n\times n$ matrices with row sums $a$ and column sums $b$, and for a cost matrix $C$, $L_C(a,b)=\min_{P\in U(a,b)}\sum_{i,j}C_{i,j}P_{i,j}$. For points $x_1,\dots,x_n\in\mathbb R^d$ the discrete measure with weights $a$ is $\sum_i a_i\delta_{x_i}$.
--   5. **The configuration of the proof of Proposition 8.2.** The four corners of the unit square $x^1=[0,0]$, $x^2=[1,0]$, $x^3=[0,1]$, $x^4=[1,1]$ in $\mathbb R^2$; the grid of the simplex $\Sigma_4$ with increments $1/4$, i.e. the histograms with entries in $\{0,\tfrac14,\tfrac12,\tfrac34,1\}$ summing to $1$; and the centering matrix $J=I_n-\tfrac1n\mathbb 1_{n,n}$.
--
--   Items 1–2 are the notions linked by Proposition 8.1 (p. 506); items 3–5 are what is needed to state Proposition 8.2 and to follow its proof.
--
--   **Formalization Note** The Wasserstein distance is the published definition `WassersteinDRO.Duality.wassersteinDistance` (an $[0,\infty]$-valued infimum over all measures on $\mathbb R^d\times\mathbb R^d$ with the two marginals), converted to a real number; outside $\mathcal P_p$ this conversion would give the junk value $0$, which is why the distance is considered only on $\mathcal P_p(\mathbb R^d)$. As printed, Definition 8.3 quantifies over all $r\in\mathbb R^n$; under that reading no nonzero squared distance is negative definite and Proposition 8.1 is false, so the zero-sum condition the book uses in the proof of Proposition 8.1 ("taking advantage of the fact that $\sum r_i=0$") is part of the definition. The Hilbert space is real and lives in the same universe as $\mathcal Z$. Indices are 0-based: the corners are indexed $0,\dots,3$ and $\{1,\dots,n\}$ is `Fin n`. Weights enter the discrete measure through `ENNReal.ofReal`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Definition 8.3, p. 501; Definition 8.4, p. 506; proof of Proposition 8.2 (x¹–x⁴, grid, J), p. 507; (2.10)–(2.11), pp. 370–371; Remark 2.13, p. 375; (2.18), p. 377

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_W1_Defs

namespace CompOT.NotHilbertian

open MeasureTheory

universe u

/-- Definition 8.4, p. 506: a function `d` on `Z × Z` is **Hilbertian** if there are a (real)
Hilbert space `H` and a map `φ : Z → H` with `d z z' = ‖φ z - φ z'‖` for all `z, z'`.
The Hilbert space is taken in the universe of `Z`. -/
def IsHilbertian {Z : Type u} (d : Z → Z → ℝ) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
    (φ : Z → H), ∀ z z', d z z' = ‖φ z - φ z'‖

/-- Definition 8.3, p. 501, negative-definite case in its *conditional* (zero-sum) reading,
the one used in the proof of Proposition 8.1 (p. 507): a symmetric `ϕ` on `Z × Z` such that
`∑_{i,j} r_i r_j ϕ(x_i, x_j) ≤ 0` for every `n`, every family `x_1, …, x_n` in `Z` and every
`r ∈ ℝⁿ` with `∑_i r_i = 0`. -/
def IsCondNegDef {Z : Type u} (ϕ : Z → Z → ℝ) : Prop :=
  (∀ x y, ϕ x y = ϕ y x) ∧
    ∀ (n : ℕ) (x : Fin n → Z) (r : Fin n → ℝ), ∑ i, r i = 0 →
      ∑ i, ∑ j, r i * r j * ϕ (x i) (x j) ≤ 0

/-- The Euclidean space `ℝ^d` with the norm `‖x - y‖₂`. -/
abbrev E (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The probability measures on `ℝ^d` with finite `p`-th moment, `∫ ‖x‖^p dμ < ∞`: the set on
which the `p`-Wasserstein distance is finite. -/
def Pp (d : ℕ) (p : ℝ) : Set (Measure (E d)) :=
  {μ | IsProbabilityMeasure μ ∧ ∫⁻ x, ENNReal.ofReal (‖x‖ ^ p) ∂μ < ⊤}

/-- The real value of the `p`-Wasserstein distance (2.18) on `ℝ^d` with ground distance
`‖x - y‖₂`, from the published `WassersteinDRO.Duality.wassersteinDistance`. It is finite on
`Pp d p`; elsewhere `toReal` of `⊤` is the junk value `0`. -/
noncomputable def wp {d : ℕ} (p : ℝ) (μ ν : Measure (E d)) : ℝ :=
  (WassersteinDRO.Duality.wassersteinDistance p μ ν).toReal

/-- The `p`-Wasserstein distance as a function on `Pp d p × Pp d p`. -/
noncomputable def Wp (d : ℕ) (p : ℝ) : Pp d p → Pp d p → ℝ :=
  fun μ ν => wp p (μ : Measure (E d)) (ν : Measure (E d))

/-- The discrete Kantorovich cost `L_C(a, b) = min_{P ∈ U(a, b)} ∑_{i,j} C_{i,j} P_{i,j}`
of (2.11), as a real infimum over `U(a, b)` (used only for `a, b` in the simplex, where
`U(a, b)` is nonempty and compact). -/
noncomputable def otCost {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) : ℝ :=
  ⨅ P : CompOT.W1.couplings a b, ∑ i, ∑ j, C i j * (P : Matrix (Fin n) (Fin n) ℝ) i j

/-- The discrete measure `∑_i a_i δ_{x_i}` (Remark 2.1). -/
noncomputable def discreteMeasure {d n : ℕ} (x : Fin n → E d) (a : Fin n → ℝ) :
    Measure (E d) :=
  ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)

/-- The four vectors of the proof of Proposition 8.2, p. 507:
`x¹ = [0, 0]`, `x² = [1, 0]`, `x³ = [0, 1]`, `x⁴ = [1, 1]` (indexed `0, 1, 2, 3`). -/
noncomputable def corners : Fin 4 → E 2 :=
  ![!₂[0, 0], !₂[1, 0], !₂[0, 1], !₂[1, 1]]

/-- The regular grid on the simplex `Σ₄` with increments `1/4` (proof of Proposition 8.2,
p. 507): histograms whose entries lie in `{0, 1/4, 1/2, 3/4, 1}` and sum to `1`. -/
def gridHists : Set (Fin 4 → ℝ) :=
  {a | ∃ k : Fin 4 → ℕ, ∑ i, k i = 4 ∧ ∀ i, a i = (k i : ℝ) / 4}

/-- The centering matrix `J = Iₙ - (1/n) 𝟙_{n,n}` (proof of Proposition 8.2, p. 507). -/
noncomputable def centering (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (1 / (n : ℝ)) • Matrix.of (fun _ _ => 1)

end CompOT.NotHilbertian


