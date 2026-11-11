-- Prove2me | Definitions.Def_HermiteLaptop_MaxAgree_Hermite
-- name    : HermiteLaptop_MaxAgree_Hermite
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:16:21.693837+00:00
-- url     : https://prove2.me/theorems/621bdaf4-4cef-42d6-afe6-dfe5c45e3ca5
-- title:
--   Hermite polynomials, Hermite coefficients of the argmax indicators, level weights W_m and the coefficients c_{k,m} (Eqs. (1)–(4), (9))
-- statement:
--   $H_j$ is the probabilists' (monic) Hermite polynomial ($H_0=1$, $H_1=z$, $H_{j+1}=zH_j-jH_{j-1}$) and $h_j=H_j/\sqrt{j!}$. For $\alpha\in\mathbb N_0^k$, $h_\alpha(z)=\prod_r h_{\alpha_r}(z_r)$ and $|\alpha|=\sum_r\alpha_r$. For $p\in[k]$ let $A_p=\{x\in\mathbb R^k: x_p=\max_q x_q\}$ and $f_p=\mathbf 1_{A_p}$. The Hermite coefficients, level weights and power-series coefficients are
--   $$\hat f_p(\alpha)=\mathbb E_{Z\sim N(0_k,I_k)}\big[f_p(Z)h_\alpha(Z)\big],\qquad W_m(f_p)=\sum_{|\alpha|=m}\hat f_p(\alpha)^2,\qquad c_{k,m}=\sum_{p=1}^k W_m(f_p).$$
--
--   **Formalization Note.** `Hpoly j` is Mathlib's `Polynomial.hermite j` mapped to `ℝ[X]`; `H j z`, `hNorm j z`, `hMulti α z`. Coordinates are 0-based: the paper's $A_1,f_1$ are `argmaxRegion ⟨0, _⟩`. `hermCoeff p α` is the Bochner integral against `gaussPi k`; `levelWeight p m` sums over `Finset.Nat.antidiagonalTuple k m` (the finite set of $\alpha$ with $|\alpha|=m$); `coeffC k m = ∑ p : Fin k, levelWeight p m`, the defining expression of Eq. (9).
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), pp. 11–12 (PDF 14–15), §2.1, Eqs. (1)–(4); pp. 13–14 (PDF 16–17), §2.3, Eq. (9)

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_KSpokes

open MeasureTheory

/-!
# Hermite polynomials, Hermite coefficients of the argmax indicators, and `c_{k,m}`

García-Soriano, Miyauchi, *Hermite Brings a Laptop*, arXiv:2609.35453 (held version, sha256
97504f90…), §2.1 pp. 11–12 (PDF 14–15), Eqs. (1)–(4); §2.3 pp. 13–14 (PDF 16–17), Eq. (9).

"We use the normalized Hermite polynomials hj(z) = Hj(z)/√j! … hα(z) = Π_r hαr(zr) …
f̂(α) = ⟨f, hα⟩ … Wm(f) = Σ_{|α|=m} f̂(α)^2 … Ap = {x ∈ ℝᵏ : xp = max_q xq}, fp = 1_{Ap} …
ck,m = Σ_{p=1}^{k} Wm(fp)."

Conventions.
* `H j` is the probabilists' (monic) Hermite polynomial: Mathlib's `Polynomial.hermite j`
  (`H_0 = 1`, `H_1 = X`, `H_2 = X² − 1`), cast to `ℝ[X]`. `hNorm j = H_j / √(j!)`.
* Multi-indices are `α : Fin k → ℕ`; `|α| = m` ranges over `Finset.Nat.antidiagonalTuple k m`
  (a finite set). Coordinates and argmax regions are 0-based: the paper's `A_1, f_1` are
  `argmaxRegion ⟨0, _⟩`.
* `hermCoeff p α = f̂_p(α) = E_{Z∼γ_k}[1_{A_p}(Z) h_α(Z)]` (a Bochner integral; the integrand is a
  polynomial times an indicator, integrable for the Gaussian measure).
* `levelWeight p m = W_m(f_p) = Σ_{|α|=m} f̂_p(α)²` (Eq. (4), a finite sum), and
  `coeffC k m = c_{k,m} = Σ_{p∈[k]} W_m(f_p)` (Eq. (9), its defining expression).
-/

namespace HermiteLaptop.MaxAgree

/-- The probabilists' Hermite polynomial `H_j ∈ ℝ[X]` (Eq. (1)–(2)). -/
noncomputable def Hpoly (j : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite j).map (Int.castRingHom ℝ)

/-- `H_j(z)`. -/
noncomputable def H (j : ℕ) (z : ℝ) : ℝ := (Hpoly j).eval z

/-- The normalized Hermite polynomial `h_j(z) = H_j(z)/√(j!)`. -/
noncomputable def hNorm (j : ℕ) (z : ℝ) : ℝ := H j z / Real.sqrt (Nat.factorial j)

/-- `h_α(z) = Π_r h_{α_r}(z_r)`. -/
noncomputable def hMulti {k : ℕ} (α : Fin k → ℕ) (z : Fin k → ℝ) : ℝ :=
  ∏ r, hNorm (α r) (z r)

/-- The argmax region `A_p = {x ∈ ℝᵏ : x_p = max_q x_q}`. -/
def argmaxRegion {k : ℕ} (p : Fin k) : Set (Fin k → ℝ) :=
  {x | ∀ q, x q ≤ x p}

/-- The Hermite coefficient `f̂_p(α) = E_{Z∼N(0,I_k)}[1_{A_p}(Z) h_α(Z)]` of `f_p = 1_{A_p}`. -/
noncomputable def hermCoeff {k : ℕ} (p : Fin k) (α : Fin k → ℕ) : ℝ :=
  ∫ x, (argmaxRegion p).indicator (fun _ => (1 : ℝ)) x * hMulti α x ∂(gaussPi k)

/-- The level-`m` weight `W_m(f_p) = Σ_{|α|=m} f̂_p(α)²` (Eq. (4)). -/
noncomputable def levelWeight {k : ℕ} (p : Fin k) (m : ℕ) : ℝ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple k m, hermCoeff p α ^ 2

/-- The power-series coefficient `c_{k,m} = Σ_{p=1}^{k} W_m(f_p)` (Eq. (9)). -/
noncomputable def coeffC (k m : ℕ) : ℝ :=
  ∑ p : Fin k, levelWeight p m

end HermiteLaptop.MaxAgree


