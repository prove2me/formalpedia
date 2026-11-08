-- Prove2me | Definitions.Def_LearnVsOpt_Errors
-- name    : LearnVsOpt_Errors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:22.741092+00:00
-- url     : https://prove2.me/theorems/165b8713-12fe-4d2e-ac3d-a8658d23f323
-- title:
--   The joint space and the single-round error $\delta=(\delta^R,\delta^L)$
-- statement:
--   **The space.** An element is a vector $R$ of functions indexed by $(k,j_1,j_2)$ together with $L=(L^u,L^c,L^{uy},L^{cy})\in\mathbb R^{2n_L+2}$. The inner product is
--   $$
--   \langle Z,Z'\rangle=\sum_{k,j_1,j_2}\int_{-1}^{1}R_{k,j_1,j_2}(q)R'_{k,j_1,j_2}(q)\,dq+\langle L,L'\rangle ,
--   $$
--   with $\|Z\|=\sqrt{\|R\|_{L^2}^2+\|L\|_2^2}$.
--
--   **The error.** Over a dictionary $D=(uc^{(1)},uc^{(2)},\dots)$, a forecast $f$ predicts $uc(f)=\sum_k f_k uc^{(k)}=(u(f),c(f))$. For the response $\vec J(f),Q(f),y(f),\lambda(f)$ at $uc(f)$ and a realized vector $uc^{(k_t)}=(u^{(k_t)},c^{(k_t)})$,
--   $$
--   \delta^R_{k,j_1,j_2}(f,k_t)(q)=\mathbb 1_{(j_1,j_2)=\vec J(f)}\big(\mathbb 1_{k_t=k}-f_k\big)\mathbb 1_{q\le Q(f)},
--   $$
--   $$
--   \delta^{L,u}=\frac{u^{(k_t)}-u(f)}{2\sqrt{n_L}},\quad \delta^{L,c}=\frac{\rho_L\lambda(f)\big(c^{(k_t)}-c(f)\big)}{2\sqrt{n_L}},\quad \delta^{L,uy}=\frac{\big(u^{(k_t)}-u(f)\big)^\top y(f)}{2\sqrt{n_L}},\quad \delta^{L,cy}=\frac{\big(c^{(k_t)}-c(f)\big)^\top y(f)}{2\sqrt{n_L}} .
--   $$
--
--   The response-calibration part guards against manipulation and the Lagrangian part against regret.
--
--   **Formalization Note** Forecasts are functions $\mathbb N\to\mathbb R$ vanishing past the dictionary, indices start at $0$, and the outcome is given by its vector, so $\mathbb 1_{k_t=k}$ reads $D[k]=uc^{(k_t)}$. Only step-function sums occur in the integrals.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, §3, p.7; (3), p.8; (5), p.9; (10), p.12; (13), p.15

import Mathlib
import Definitions.Def_LearnVsOpt_Selection

open scoped Matrix

namespace LearnVsOpt

variable {nL : ℕ}

/-- A utility-cost vector `uc = (u, c) ∈ [0, 1]^{2n_L}` (Fikioris, Sivan & Tardos, arXiv:2611.05580,
§3, p.7). -/
abbrev UC (nL : ℕ) := (Fin nL → ℝ) × (Fin nL → ℝ)

/-- The predicted vector `uc(f) = Σ_k f_k uc^(k) = (u(f), c(f))` of a forecast `f` over a dictionary
`D = (uc^(1), uc^(2), …)` (§3, p.7).

**Formalization Note.** Forecasts are functions `ℕ → ℝ` that vanish past the dictionary ("viewed as
elements of `Δ_{n̂_O}` by setting `f_k = 0` for all unobserved `k`", p.16), and indices start at `0`. -/
noncomputable def ucOf (D : List (UC nL)) (f : ℕ → ℝ) : UC nL :=
  (fun j => ∑ k ∈ Finset.range D.length, f k * (D.getD k 0).1 j,
   fun j => ∑ k ∈ Finset.range D.length, f k * (D.getD k 0).2 j)

/-- `f` is a forecast over the first `n` indices: a point of `Δ_n`, extended by zero. -/
def IsForecast (n : ℕ) (f : ℕ → ℝ) : Prop :=
  (∀ k, 0 ≤ f k) ∧ (∀ k, n ≤ k → f k = 0) ∧ ∑ k ∈ Finset.range n, f k = 1

/-- An element of the joint space of (13), p.15: a vector `R` of functions indexed by
`(k, j₁, j₂)` and the Lagrangian vector `L = (L^u, L^c, L^{uy}, L^{cy}) ∈ ℝ^{2n_L+2}`. The same type
holds single-round errors `δ(f, k)` and the cumulative `Z_t = (R_t, L_t)`. -/
structure JointVec (nL : ℕ) where
  /-- The coordinates `(k, j₁, j₂) ↦ (q ↦ R_{k,j₁,j₂}(q))`. -/
  R : ℕ → Fin nL → Fin nL → ℝ → ℝ
  /-- `L^u`. -/
  Lu : Fin nL → ℝ
  /-- `L^c`. -/
  Lc : Fin nL → ℝ
  /-- `L^{uy}`. -/
  Luy : ℝ
  /-- `L^{cy}`. -/
  Lcy : ℝ

/-- The inner product (5), p.9, `⟨g, g̃⟩ = ∫_{−1}^{1} g(x) g̃(x) dx`, summed over the coordinates
`k < n` and `j₁, j₂ ∈ [n_L]`.

**Formalization Note.** Only step-function sums occur, which are integrable on `[−1, 1]`; (6)
(`LearnVsOpt.display_6`) evaluates the integral. `n` is the number of indices `k` in play; `R_t` and
`δ` vanish at larger indices. -/
noncomputable def JointVec.innerR (n : ℕ) (Z Z' : JointVec nL) : ℝ :=
  ∑ k ∈ Finset.range n, ∑ j₁, ∑ j₂, ∫ q in (-1 : ℝ)..1, Z.R k j₁ j₂ q * Z'.R k j₁ j₂ q

/-- The Euclidean inner product on `ℝ^{2n_L+2}`. -/
noncomputable def JointVec.innerL (Z Z' : JointVec nL) : ℝ :=
  Z.Lu ⬝ᵥ Z'.Lu + Z.Lc ⬝ᵥ Z'.Lc + Z.Luy * Z'.Luy + Z.Lcy * Z'.Lcy

/-- The inner product of (13), p.15: `⟨Z, Z′⟩ = ⟨R, R′⟩ + ⟨L, L′⟩`. -/
noncomputable def JointVec.inner (n : ℕ) (Z Z' : JointVec nL) : ℝ :=
  JointVec.innerR n Z Z' + JointVec.innerL Z Z'

/-- `‖R‖_{L²}`. -/
noncomputable def JointVec.normR (n : ℕ) (Z : JointVec nL) : ℝ := Real.sqrt (JointVec.innerR n Z Z)

/-- `‖L‖₂`. -/
noncomputable def JointVec.normL (Z : JointVec nL) : ℝ := Real.sqrt (JointVec.innerL Z Z)

/-- `‖Z‖ = √(‖R‖²_{L²} + ‖L‖²₂)`, (13), p.15. -/
noncomputable def JointVec.norm (n : ℕ) (Z : JointVec nL) : ℝ := Real.sqrt (JointVec.inner n Z Z)

open Classical in
/-- **The single-round joint error** `δ(f, k) = (δ^R(f, k), δ^L(f, k))` for the forecast `f` with
response `s`, and the realized vector `v = uc^(k)`: (3), p.8, (10), p.12, (13), p.15. That is,
`δ^R_{k',j₁,j₂}(f, k)(q) = 1_{(j₁,j₂)=J⃗(f)} (1_{k=k'} − f_{k'}) 1_{q≤Q(f)}`,
`δ^{L,u} = (u^(k) − u(f))/(2√n_L)`, `δ^{L,c} = ρ_L λ(f)(c^(k) − c(f))/(2√n_L)`,
`δ^{L,uy} = (u^(k) − u(f))⊤y(f)/(2√n_L)`, `δ^{L,cy} = (c^(k) − c(f))⊤y(f)/(2√n_L)`.

**Formalization Note.** The outcome is given by its vector `v`: `1_{k=k'}` reads `D[k'] = v`, which
for a dictionary without repeats is the same thing, and also makes sense for a vector not yet in `D`,
all of whose coordinates `k' < |D|` then carry `−f_{k'}`. `s` is the selector's response at `uc(f)`;
see `Algorithm`. -/
noncomputable def delta (ρL : ℝ) (D : List (UC nL)) (s : Selection nL) (f : ℕ → ℝ) (v : UC nL) :
    JointVec nL where
  R := fun k j₁ j₂ q =>
    (if (j₁, j₂) = (s.j₁, s.j₂) then 1 else 0) * ((if D[k]? = some v then 1 else 0) - f k) *
      (if q ≤ s.Q then 1 else 0)
  Lu := fun j => (1 / (2 * Real.sqrt nL)) * (v.1 j - (ucOf D f).1 j)
  Lc := fun j => (ρL * s.lam / (2 * Real.sqrt nL)) * (v.2 j - (ucOf D f).2 j)
  Luy := (1 / (2 * Real.sqrt nL)) * ((v.1 - (ucOf D f).1) ⬝ᵥ s.y)
  Lcy := (1 / (2 * Real.sqrt nL)) * ((v.2 - (ucOf D f).2) ⬝ᵥ s.y)

end LearnVsOpt


