-- Prove2me | Definitions.Def_NonadaptiveSFT_LeastSquares
-- name    : NonadaptiveSFT_LeastSquares
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:52.465488+00:00
-- url     : https://prove2.me/theorems/052c2f88-3c7c-4063-bf6b-c6783eb05dfc
-- title:
--   The least-squares fit $C_S$, the residual $z_S$, the certificate $M_S$, the heavy set $\Omega$ and the event of Lemma 14
-- statement:
--   Let $s\ge1$, $\tau\ge0$, $\bar\sigma=\sqrt s\,\tau$, and $\Omega=\{f:|\widehat X(f)|>\tau/4\}$. With $n$ sample points $t_1,\dots,t_n\in G$ define
--
--   $$A_{bf}=\chi_f(t_b)/\sqrt n,\qquad b_b=X(t_b)/\sqrt n.$$
--
--   For $S\subseteq G$, $A_S$ is the submatrix of columns in $S$, $C_S=(A_S^*A_S)^{-1}A_S^*b$ is the least-squares fit (extended by zero outside $S$; $C_\emptyset=0$), $z_S=b-A_SC_S$, and
--
--   $$M_S=2\|z_S\|_2+3b_{ls}\bar\sigma,\qquad b_{ls}=\sqrt{255}/2,\qquad n_{ls}=170s\lceil\log(2040s)\rceil.$$
--
--   The **event of Lemma 14** for a sample holds when, for every $S\subseteq\Omega$ simultaneously, $A_S^*A_S$ is nonsingular and
--
--   $$\|\widehat X-C_S\|_2\le\sqrt2(\|z_S\|_2+b_{ls}\bar\sigma)+\|\widehat X_{G\setminus\Omega}\|_2,\qquad\|z_S\|_2\le\sqrt{3/2}\,\|\widehat X_{\Omega\setminus S}\|_2+b_{ls}\bar\sigma,$$
--
--   $$\|\widehat X-C_S\|_2\le M_S,\qquad M_S^2\le12\|\widehat X_{\Omega\setminus S}\|_2^2+50b_{ls}^2\bar\sigma^2.$$
--
--   The probability of an event under $n$ independent uniform points of $G$ is its proportion among all $n$-tuples.
--
--   **Formalization Note** Logarithms are base 2, and $\lceil\log m\rceil$ for an integer $m\ge1$ is `Nat.clog 2 m`. Lean's matrix inverse is zero on singular matrices, so the fit is used only together with the nonsingularity that the event or the routine's abort rule provides.
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), §5, Lemma 14 and its proof, pp.30–31 (PDF pp.32–33)

import Mathlib
import Definitions.Def_NonadaptiveSFT_Fourier

open scoped BigOperators Matrix

namespace NonadaptiveSFT

/-!
# The least-squares residual norm estimate of §5 (Lemma 14)

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…), §5, Lemma 14 and its proof, pp.30–32 (PDF pp.32–34).

"Define Ω = {f : |X̂(f)| > τ/4}, σ̄ = √s τ. Use n_ls = 170s⌈log(2040s)⌉ samples t_b ∈ G. Define
A ∈ C^{n_ls×G}, b ∈ C^{n_ls} by A_{bf} = χ_f(t_b)/√n_ls and b_b = X(t_b)/√n_ls. Let b_ls = √255/2,
δ_ls = 1/30 be universal constants. Define C_S = argmin_{c∈C^S}∥b − A_S c∥_2 as the least-squares
fit on the columns A_S, extended by zero outside S; we specifically designate C_∅ = 0. Let
z_S = b − A_S C_S, M_S = 2∥z_S∥_2 + 3b_ls σ̄."

**Formalization Note.**
* `log` is base 2 (p.17); for an integer `m ≥ 1`, `⌈log m⌉ = Nat.clog 2 m`.
* The fit is `C_S = (A_S^*A_S)^{−1}A_S^*b` (proof of Lemma 14, p.30), extended by zero outside `S`.
  It is the unique least-squares minimizer whenever the Gram matrix `A_S^*A_S` is nonsingular; Mathlib's
  matrix inverse is `0` for a singular matrix, so `fit` is only meaningful together with the
  nonsingularity that `LSGood` and the routine's abort rule carry. For `S = ∅` the Gram matrix is
  the empty matrix and `fit = 0 = C_∅`.
* `LSGood X U s τ` is the event of Lemma 14 for the sample `U`: for **every** `S ⊆ Ω`
  simultaneously, the Gram matrix is nonsingular (so `C_S` is the unique fit and the routine does
  not abort) and (28), (29) hold.
* `sampleProb n E` is the probability of `E` under `n` independent uniform points of `G`, written
  as a count over `G^n` divided by `N^n`.
* `restrict v S` is `v` on `S` and `0` off `S` (the paper's `v_S`, p.17).
-/

/-- `n_ls = 170 s ⌈log(2040 s)⌉`. -/
def nls (s : ℕ) : ℕ := 170 * s * Nat.clog 2 (2040 * s)

/-- `b_ls = √255 / 2`. -/
noncomputable def bls : ℝ := Real.sqrt 255 / 2

/-- `v_S`: `v` on `S`, `0` elsewhere. -/
noncomputable def restrict {ι : Type*} (v : ι → ℂ) (S : Set ι) : ι → ℂ := by
  classical exact fun f => if f ∈ S then v f else 0

/-- The heavy set `Ω = {f : |X̂(f)| > τ/4}`. -/
noncomputable def Omega {a d : ℕ} (X : G a d → ℂ) (τ : ℝ) : Finset (G a d) := by
  classical exact Finset.univ.filter fun f => τ / 4 < ‖hat X f‖

/-- The sampling matrix `A_{bf} = χ_f(t_b)/√n`. -/
noncomputable def Amat {a d n : ℕ} (U : Fin n → G a d) : Matrix (Fin n) (G a d) ℂ :=
  fun b f => chi f (U b) / (Real.sqrt n : ℂ)

/-- The observation vector `b_b = X(t_b)/√n`. -/
noncomputable def bvec {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) : Fin n → ℂ :=
  fun b => X (U b) / (Real.sqrt n : ℂ)

/-- The columns `A_S`. -/
noncomputable def AS {a d n : ℕ} (U : Fin n → G a d) (S : Finset (G a d)) :
    Matrix (Fin n) S ℂ :=
  fun b f => Amat U b f

/-- The Gram matrix `A_S^* A_S`. -/
noncomputable def gram {a d n : ℕ} (U : Fin n → G a d) (S : Finset (G a d)) : Matrix S S ℂ :=
  (AS U S)ᴴ * AS U S

/-- The least-squares fit `C_S = (A_S^*A_S)^{−1}A_S^*b`, extended by zero outside `S`. -/
noncomputable def fit {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (S : Finset (G a d)) :
    G a d → ℂ := by
  classical exact fun f =>
    if h : f ∈ S then ((gram U S)⁻¹ *ᵥ ((AS U S)ᴴ *ᵥ bvec X U)) ⟨f, h⟩ else 0

/-- The least-squares residual `z_S = b − A_S C_S`. -/
noncomputable def zres {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (S : Finset (G a d)) :
    Fin n → ℂ :=
  bvec X U - Amat U *ᵥ fit X U S

/-- The residual norm certificate `M_S = 2‖z_S‖₂ + 3 b_ls σ̄`. -/
noncomputable def Mval {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (S : Finset (G a d))
    (σbar : ℝ) : ℝ :=
  2 * l2 (zres X U S) + 3 * bls * σbar

/-- The event of Lemma 14 for the sample `U`: for every `S ⊆ Ω` simultaneously, `A_S^*A_S` is
nonsingular and (28), (29) hold, with `σ̄ = √s τ`. -/
def LSGood {a d n : ℕ} (X : G a d → ℂ) (U : Fin n → G a d) (s : ℕ) (τ : ℝ) : Prop :=
  let σbar := Real.sqrt s * τ
  ∀ S : Finset (G a d), S ⊆ Omega X τ →
    (gram U S).det ≠ 0 ∧
    l2 (hat X - fit X U S) ≤
      Real.sqrt 2 * (l2 (zres X U S) + bls * σbar) +
        l2 (restrict (hat X) (↑(Omega X τ))ᶜ) ∧
    l2 (zres X U S) ≤
      Real.sqrt (3 / 2) * l2 (restrict (hat X) (↑(Omega X τ \ S))) + bls * σbar ∧
    l2 (hat X - fit X U S) ≤ Mval X U S σbar ∧
    Mval X U S σbar ^ 2 ≤
      12 * l2 (restrict (hat X) (↑(Omega X τ \ S))) ^ 2 + 50 * bls ^ 2 * σbar ^ 2

/-- The probability of an event `E` under `n` independent uniform points of `G`. -/
noncomputable def sampleProb {a d : ℕ} (n : ℕ) (E : (Fin n → G a d) → Prop) : ℝ := by
  classical exact
    ((Finset.univ.filter E).card : ℝ) / (Fintype.card (G a d) : ℝ) ^ n

end NonadaptiveSFT


