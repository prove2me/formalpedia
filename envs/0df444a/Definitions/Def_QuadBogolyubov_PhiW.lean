-- Prove2me | Definitions.Def_QuadBogolyubov_PhiW
-- name    : QuadBogolyubov_PhiW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:33.312632+00:00
-- url     : https://prove2.me/theorems/86cb4985-4046-4235-98b7-404d2677f09e
-- title:
--   The rooted cube average $\Phi_W$ of (35)
-- statement:
--   With $\mu_B=(|G|^2/|B|)\mathbf 1_B$ the normalized counting measure of the bilinear variety and $\mathcal V=\{0,1\}^3\setminus\{(0,0,0)\}$, for a tuple $(F_\nu)_{\nu\in\mathcal V}$ of functions on $G$,
--   $$\Phi_W((F_\nu)_{\nu\in\mathcal V})=\mathbb E_{x_1,x_2,x_3\in W}\prod_{1\le i<j\le3}\mu_B(x_i,x_j)\prod_{\nu\in\mathcal V}F_\nu(\nu_1x_1+\nu_2x_2+\nu_3x_3).$$
--   This is the local average whose control by the $U^3(W)$ norm is the core of the counting lemma.
--
--   **Formalization Note** $B$ contains $(0,0)$, so it is non-empty. The family is a function on all of `Fin 3 → ZMod 2`, and only $\nu\ne0$ enters.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), App. D.2, p.57, eq. (35)

import Mathlib
import Definitions.Def_QuadBogolyubov_IsRooted
import Definitions.Def_QuadBogolyubov_gowersU3

set_option autoImplicit false

open scoped BigOperators

namespace QuadBogolyubov

/-- The normalised counting measure `μ_B = (|G|² / |B|) 1_B` of the bilinear variety `B` of `W`,
as a function on `G × G`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), App. D.2,
p.57: "If S ⊆ Gᵏ is non-empty, write µS = (|G|ᵏ/|S|) 1S for its normalised counting measure."

**Formalization Note.** `B` always contains `(0, 0)`, so it is non-empty. -/
noncomputable def muB {n : ℕ} (W : QuadVariety n) (x y : Fin n → ZMod 2) : ℝ :=
  ((Fintype.card (Fin n → ZMod 2) : ℝ) ^ 2 / ((bilinVar W).card : ℝ)) * ind (bilinVar W) (x, y)

/-- The **rooted cube average** `Φ_W((F_ν)_{ν ∈ V})` of (35), for `V = {0,1}³ \ {(0,0,0)}`:
`Φ_W = 𝔼_{x₁,x₂,x₃ ∈ W} ∏_{1 ≤ i < j ≤ 3} μ_B(xᵢ, xⱼ) ∏_{ν ∈ V} F_ν(ν₁x₁ + ν₂x₂ + ν₃x₃)`.

App. D.2, p.57, eq. (35): "Put V = {0, 1}³ \ {(0, 0, 0)}. For a tuple (Fν)ν∈V of functions defined
on G, let ΦW((Fν)ν∈V) = E_{x1,x2,x3∈W} ∏_{1≤i<j≤3} µB(xi, xj) ∏_{ν∈V} Fν(ν1x1 + ν2x2 + ν3x3)."

**Formalization Note.** The family is `F : (Fin 3 → ZMod 2) → G → ℂ`; only `F ν` with `ν ≠ 0`
enters. The three variables are `x : Fin 3 → G`, averaged uniformly over `W³`. -/
noncomputable def PhiW {n : ℕ} (W : QuadVariety n)
    (F : (Fin 3 → ZMod 2) → (Fin n → ZMod 2) → ℂ) : ℂ :=
  𝔼 x ∈ Fintype.piFinset (fun _ : Fin 3 => W.carrier),
    ((muB W (x 0) (x 1) * muB W (x 0) (x 2) * muB W (x 1) (x 2) : ℝ) : ℂ) *
      ∏ ν ∈ Finset.univ.filter (fun ν : Fin 3 → ZMod 2 => ν ≠ 0), F ν (∑ i, ν i • x i)

end QuadBogolyubov


