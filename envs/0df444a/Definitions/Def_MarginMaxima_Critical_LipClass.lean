-- Prove2me | Definitions.Def_MarginMaxima_Critical_LipClass
-- name    : MarginMaxima_Critical_LipClass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:52.690395+00:00
-- url     : https://prove2.me/theorems/98c920f0-4d17-4b7b-8cb4-0132f85a87ca
-- title:
--   Lipschitz aggregations $x\mapsto G(\langle u_1,x\rangle,\dots,\langle u_r,x\rangle)$, the weights $w_j$, $W$, the entropy $H(p)$ and the bound $82W(1+H(p))$ of Theorem C.1
-- statement:
--   Let $G:\mathbb R^r\to\mathbb R$ and $\rho_1,\dots,\rho_r>0$. The class $\mathcal G$ consists of the functions
--   $$x\mapsto G(\langle u_1,x\rangle,\dots,\langle u_r,x\rangle)\qquad (x\in B_d),\qquad \|u_j\|\le\rho_j,$$
--   on the closed unit ball $B_d$ of $\mathbb R^d$; the affine variant uses $\langle u_j,x\rangle+b_j$ with $\|u_j\|\le R_j$ and $|b_j|\le R_j$. For $L,\gamma>0$ let $J=\{j: L\rho_j\ge\gamma\}$, $w_j=L^2\rho_j^2/\gamma^2$ for $j\in J$, $W=\sum_{j\in J}w_j$, $p_j=w_j/W$ and $H(p)=-\sum_{j\in J}p_j\ln p_j$ (Shannon entropy, natural logarithm). The bound of Theorem C.1 is $82\,W(1+H(p))$, read as $0$ when $J=\emptyset$.
--
--   These objects state the paper's entropy upper bound, which in particular gives the upper bound of Theorem 1.1(a).
--
--   **Formalization Note.** `LipClass d r G ρ` and `AffLipClass d r G R` are sets of functions on `Ball d`. `activeSet L ρ γ` is the `Finset` $J$, `weight`, `totalWeight`, `weightEntropy` are $w_j$, $W$, $H(p)$, and `entropyBound L ρ γ` is `if J = ∅ then 0 else 82 * W * (1 + H)`.
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 30, Theorem C.1; p. 3 (H the Shannon entropy)

import Mathlib
import Definitions.Def_MarginMaxima_Critical_MaxClass

namespace MarginMaxima.Critical

/-- The aggregation class `𝒢` of Theorem C.1: the functions
`x ↦ G(⟨u_1, x⟩, …, ⟨u_r, x⟩)` on the closed unit ball of `ℝ^d`, with `‖u_j‖ ≤ ρ_j`. -/
def LipClass (d r : ℕ) (G : (Fin r → ℝ) → ℝ) (ρ : Fin r → ℝ) : Set (Ball d → ℝ) :=
  {f | ∃ u : Fin r → EuclideanSpace ℝ (Fin d), (∀ j, ‖u j‖ ≤ ρ j) ∧
    f = fun x : Ball d => G (fun j => inner ℝ (u j) x.1)}

/-- The affine aggregation class of Theorem C.1: `x ↦ G(⟨u_1, x⟩ + b_1, …, ⟨u_r, x⟩ + b_r)` on the
closed unit ball of `ℝ^d`, with `‖u_j‖ ≤ R_j` and `|b_j| ≤ R_j`. -/
def AffLipClass (d r : ℕ) (G : (Fin r → ℝ) → ℝ) (R : Fin r → ℝ) : Set (Ball d → ℝ) :=
  {f | ∃ (u : Fin r → EuclideanSpace ℝ (Fin d)) (b : Fin r → ℝ), (∀ j, ‖u j‖ ≤ R j) ∧
    (∀ j, |b j| ≤ R j) ∧ f = fun x : Ball d => G (fun j => inner ℝ (u j) x.1 + b j)}

/-- `J = {j : L ρ_j ≥ γ}`. -/
noncomputable def activeSet {r : ℕ} (L : ℝ) (ρ : Fin r → ℝ) (γ : ℝ) : Finset (Fin r) :=
  Finset.univ.filter fun j => γ ≤ L * ρ j

/-- `w_j = L² ρ_j² / γ²`. -/
noncomputable def weight {r : ℕ} (L : ℝ) (ρ : Fin r → ℝ) (γ : ℝ) (j : Fin r) : ℝ :=
  L ^ 2 * ρ j ^ 2 / γ ^ 2

/-- `W = Σ_{j ∈ J} w_j`. -/
noncomputable def totalWeight {r : ℕ} (L : ℝ) (ρ : Fin r → ℝ) (γ : ℝ) : ℝ :=
  ∑ j ∈ activeSet L ρ γ, weight L ρ γ j

/-- The Shannon entropy (natural logarithm) `H(p) = -Σ_{j ∈ J} p_j ln p_j` of `p_j = w_j / W`,
`j ∈ J`. -/
noncomputable def weightEntropy {r : ℕ} (L : ℝ) (ρ : Fin r → ℝ) (γ : ℝ) : ℝ :=
  - ∑ j ∈ activeSet L ρ γ,
      (weight L ρ γ j / totalWeight L ρ γ) * Real.log (weight L ρ γ j / totalWeight L ρ γ)

/-- The bound `82 W (1 + H(p))` of Theorem C.1, read as `0` when `J = ∅`. -/
noncomputable def entropyBound {r : ℕ} (L : ℝ) (ρ : Fin r → ℝ) (γ : ℝ) : ℝ :=
  if activeSet L ρ γ = ∅ then 0
  else 82 * totalWeight L ρ γ * (1 + weightEntropy L ρ γ)

end MarginMaxima.Critical


