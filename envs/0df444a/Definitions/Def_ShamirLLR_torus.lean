-- Prove2me | Definitions.Def_ShamirLLR_torus
-- name    : ShamirLLR_torus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:59.396699+00:00
-- url     : https://prove2.me/theorems/c4bbb1dc-a82a-425f-9ba6-b17df85f0678
-- title:
--   Torus $\mathbb T^d$, Fourier coefficients, Fejér means and torus Lipschitz norms
-- statement:
--   Let $\mathbb T^d=(\mathbb R/\mathbb Z)^d$ with Haar probability measure. For $\varphi:\mathbb T^d\to\mathbb C$ and $k\in\mathbb Z^d$ the **torus Fourier coefficient** is
--   $$
--   \widehat\varphi(k)=\int_{\mathbb T^d}\varphi(t)\,e(-k\cdot t)\,dt,
--   $$
--   and $\varphi$ has Fourier support in $[-T,T]^d$ when $\widehat\varphi(k)=0$ for $\|k\|_\infty>T$. The **Fejér kernel** is $K_T(t)=\sum_{|k|<T}(1-|k|/T)e(kt)$ and the positive product Fejér convolution is
--   $$
--   A_T(x)=\int_{\mathbb T^d}A(x-t)\prod_{j}K_T(t_j)\,dt .
--   $$
--   The $\ell^1$ torus distance is $\sum_j\|x_j-y_j\|_{\mathbb T}$; the product metric is $\max_j\|x_j-y_j\|_{\mathbb T}$, and $\|A\|_{\mathrm{Lip}}=\|A\|_\infty+\sup_{x\neq y}|A(x)-A(y)|/d(x,y)$ for it. Finally $v\mapsto v/p$ embeds $\mathbb F_p^d$ into the $p$-torsion of $\mathbb T^d$.
--
--   These objects carry the quadratic torus models of the structured estimate.
--
--   **Formalization Note** $\mathbb T^d$ is `Fin d → UnitAddCircle`. The Fejér kernel is the sum of real parts (it is real). A bound $\|A\|_{\mathrm{Lip}}\le K$ is written $a+l\le K$ with $a$ a sup bound and $l\ge0$ a Lipschitz constant.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), §2.3, Eq. (14), pp.17–18; Lemma 7.4 and proof, pp.53–54; §7.4, p.54 (PDF pp.18–19, 54–55)

import Mathlib

set_option autoImplicit false

namespace ShamirLLR

/-- The torus `𝕋^d = (ℝ/ℤ)^d` (§2.3, p.17).

**Formalization Note.** `Fin d → UnitAddCircle`. Its product metric is the sup of the circle
distances `‖x_j − y_j‖_𝕋`, and its volume is the Haar probability measure. -/
abbrev Torus (d : ℕ) : Type := Fin d → UnitAddCircle

/-- The character `t ↦ e(k · t)` of `𝕋^d` for `k ∈ ℤ^d`. -/
noncomputable def torusChar {d : ℕ} (k : Fin d → ℤ) (t : Torus d) : ℂ :=
  ∏ j, fourier (k j) (t j)

/-- The torus Fourier coefficient `φ̂(k) = ∫_{𝕋^d} φ(t) e(−k · t) dt`, Eq. (14), p.18.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Eq. (14), p.18. -/
noncomputable def torusFourier {d : ℕ} (φ : Torus d → ℂ) (k : Fin d → ℤ) : ℂ :=
  ∫ t, φ t * torusChar (-k) t

/-- The Fourier support of `φ : 𝕋^d → ℝ` lies in `[−T, T]^d`: `φ̂(k) = 0` whenever
`‖k‖_∞ > T` (Lemma 7.4, p.53; Eq. (57), p.55). A function with this property is a
trigonometric polynomial. -/
def FourierSuppIn {d : ℕ} (φ : Torus d → ℝ) (T : ℕ) : Prop :=
  ∀ k : Fin d → ℤ, (∃ j, (T : ℤ) < |k j|) → torusFourier (fun t => (φ t : ℂ)) k = 0

/-- The one-dimensional Fejér kernel `K_T(t) = ∑_{|k| < T} (1 − |k|/T) e(kt)`, proof of
Lemma 7.4, p.53.

**Formalization Note.** The sum is real (it is symmetric in `k`), so it is the sum of the real
parts. -/
noncomputable def fejerKernel (T : ℕ) (t : UnitAddCircle) : ℝ :=
  ∑ k ∈ Finset.Ioo (-(T : ℤ)) T, (1 - (|k| : ℝ) / T) * (fourier k t).re

/-- The positive product Fejér convolution `A_T(x) = ∫_{𝕋^d} A(x − t) ∏_j K_T(t_j) dt` of
Lemma 7.4 and its proof, pp.53–54. -/
noncomputable def fejerMean {d : ℕ} (T : ℕ) (A : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∫ t, A (x - t) * ∏ j, fejerKernel T (t j)

/-- The `ℓ¹` torus distance `∑_j ‖x_j − y_j‖_𝕋` (proof of Lemma 7.4, p.54). -/
noncomputable def l1dist {d : ℕ} (x y : Torus d) : ℝ :=
  ∑ j, dist (x j) (y j)

/-- `‖A‖_{Lip} ≤ K` on the torus with its product (sup) metric: `‖A‖_∞ + Lip(A) ≤ K`
(Lemma 7.3, p.50; the Lipschitz norm of §3.1, p.19).

**Formalization Note.** Written as `a + l ≤ K` with `a` a sup bound and `l ≥ 0` a Lipschitz
constant. -/
def TorusLipNormLE {d : ℕ} (A : Torus d → ℝ) (K : ℝ) : Prop :=
  ∃ a l : ℝ, 0 ≤ l ∧ a + l ≤ K ∧ (∀ t, |A t| ≤ a) ∧ ∀ t s, |A t - A s| ≤ l * dist t s

/-- The embedding `v ↦ v/p` of `𝔽_p^d` into the `p`-torsion of `𝕋^d` (§2.3, p.17; §7.4, p.54). -/
noncomputable def fpToTorus {d : ℕ} (p : ℕ) (v : Fin d → ZMod p) : Torus d :=
  fun j => (((v j).val : ℝ) / (p : ℝ) : UnitAddCircle)

end ShamirLLR


