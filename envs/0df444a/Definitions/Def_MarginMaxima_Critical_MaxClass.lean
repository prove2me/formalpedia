-- Prove2me | Definitions.Def_MarginMaxima_Critical_MaxClass
-- name    : MarginMaxima_Critical_MaxClass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:01:59.357799+00:00
-- url     : https://prove2.me/theorems/21213d1e-f07b-46e6-9c6f-0924e2034a1a
-- title:
--   Maxima of $r$ linear functionals on the unit ball, zero-witness shattering, $\mathrm{fat}^0_\gamma$, the suprema over all dimensions, and the constants $\gamma_c$, $g_\star$, $g_w$, $L$
-- statement:
--   For $d\ge 1$ let $B_d=\{x\in\mathbb R^d:\|x\|\le 1\}$ be the closed unit ball. For $R>0$ and a positive integer $r$, $F^{(d)}_{\max,r}(R)$ is the class of functions
--   $$x\mapsto \max_{j\le r}\langle u_j,x\rangle\qquad(x\in B_d),\qquad \|u_j\|\le R,$$
--   with exactly $r$ **heads** $u_1,\dots,u_r$ (repetitions allowed); $F^{(d)}_{\max,r}=F^{(d)}_{\max,r}(1)$. The $R$-bounded affine variant is $x\mapsto\max_j(\langle u_j,x\rangle+b_j)$ with $\|u_j\|\le R$, $|b_j|\le R$.
--
--   Points $x_1,\dots,x_m$ are **$\gamma$-shattered with witnesses** $s_1,\dots,s_m$ by a class $H$ if for every $y\in\{\pm1\}^m$ some $f\in H$ has $y_i(f(x_i)-s_i)\ge\gamma$ for all $i$ (the witnesses are fixed before the labels); this and $\mathrm{fat}_\gamma(H)$, the largest size of such a set, are the published definition `BartlettNN_Margin_FatShattering`. They are **$\gamma$-shattered at zero witnesses** if this holds with all $s_i=0$, and $\mathrm{fat}^0_\gamma(H)$ is the largest size of such a set. Both are valued in $\mathbb N\cup\{\infty\}$. Finally
--   $$\mathrm{fat}_\gamma(F_{\max,r})=\sup_{d\ge1}\mathrm{fat}_\gamma(F^{(d)}_{\max,r}),\qquad \mathrm{fat}^0_\gamma(F_{\max,r})=\sup_{d\ge1}\mathrm{fat}^0_\gamma(F^{(d)}_{\max,r}).$$
--   The constants are $\gamma_c=1/(3\sqrt3)$, $g_\star=63/449$, $g_w=17/(54\sqrt3)$, and for $\Delta\ge0$ and $r$ the factor $L=\min\{\ln(e/\Delta),\ln\ln r\}$ of Theorem 1.1, with $\ln(e/0)=\infty$, i.e. $L=\ln\ln r$ at $\Delta=0$.
--
--   These are the objects of the paper's main theorem: the margin complexity of maxima of linear functionals, with and without witnesses.
--
--   **Formalization Note.** `Ball d` is the subtype `{x : EuclideanSpace ℝ (Fin d) // ‖x‖ ≤ 1}`; `MaxClassR d r R` uses `⨆ j : Fin r`, the maximum when `r ≥ 1` (every statement assumes `1 ≤ r`). `ZeroShatters H γ x` is `∀ b : Fin m → Bool, ∃ h ∈ H, ∀ i, γ ≤ h (x i) * pm (b i)`, the body of `GammaShatters` with the witness vector `0`, and `fat0` is `⨆ m x (_ : ZeroShatters H γ x), (m : ℕ∞)` like `fat`. `fatMax r γ` and `fat0Max r γ` are `⨆ (d : ℕ) (_ : 1 ≤ d)` of these. `Lfactor Δ r` is `if Δ = 0 then log (log r) else min (log (exp 1 / Δ)) (log (log r))`, which avoids Lean's `log (e/0) = log 0 = 0`.
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 2, §1 Definitions and Theorem 1.1; p. 30, Theorem C.1 (R-bounded affine functions)

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering

open BartlettNN.Margin

namespace MarginMaxima.Critical

/-- The closed unit ball `{x : ‖x‖ ≤ 1}` of `ℝ^d`, as a type. -/
abbrev Ball (d : ℕ) : Type := {x : EuclideanSpace ℝ (Fin d) // ‖x‖ ≤ 1}

/-- `F^{(d)}_{max,r}(R)`: the functions `x ↦ max_{j<r} ⟨u_j, x⟩` on the closed unit ball of `ℝ^d`,
with exactly `r` heads `u_j` of norm at most `R` (repetitions allowed). For `r ≥ 1` the supremum
over `Fin r` is the maximum of `r` reals. -/
def MaxClassR (d r : ℕ) (R : ℝ) : Set (Ball d → ℝ) :=
  {f | ∃ u : Fin r → EuclideanSpace ℝ (Fin d), (∀ j, ‖u j‖ ≤ R) ∧
    f = fun x : Ball d => ⨆ j, inner ℝ (u j) x.1}

/-- `F^{(d)}_{max,r}`: maxima of `r` linear functionals of norm at most `1` on the unit ball. -/
def MaxClass (d r : ℕ) : Set (Ball d → ℝ) := MaxClassR d r 1

/-- The `r`-fold maxima of `R`-bounded affine functions `x ↦ max_{j<r} (⟨u_j, x⟩ + b_j)`,
`‖u_j‖ ≤ R`, `|b_j| ≤ R`, on the closed unit ball of `ℝ^d`. -/
def AffMaxClassR (d r : ℕ) (R : ℝ) : Set (Ball d → ℝ) :=
  {f | ∃ (u : Fin r → EuclideanSpace ℝ (Fin d)) (b : Fin r → ℝ), (∀ j, ‖u j‖ ≤ R) ∧
    (∀ j, |b j| ≤ R) ∧ f = fun x : Ball d => ⨆ j, (inner ℝ (u j) x.1 + b j)}

/-- Zero-witness `γ`-shattering: for every sign vector `b` some `h ∈ H` has
`y_i h(x_i) ≥ γ` for all `i` (the witnesses `s_i` of `GammaShatters` are all `0`). -/
def ZeroShatters {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) {m : ℕ} (x : Fin m → X) : Prop :=
  ∀ b : Fin m → Bool, ∃ h ∈ H, ∀ i, γ ≤ h (x i) * pm (b i)

/-- The zero-witness fat-shattering dimension `fat⁰_γ(H)`, valued in `ℕ∞`, in the same shape as
`BartlettNN.Margin.fat`. -/
noncomputable def fat0 {X : Type*} (H : Set (X → ℝ)) (γ : ℝ) : ℕ∞ :=
  ⨆ (m : ℕ) (x : Fin m → X) (_ : ZeroShatters H γ x), (m : ℕ∞)

/-- `fat_γ(F_{max,r}) = sup_{d ≥ 1} fat_γ(F^{(d)}_{max,r})` (with witnesses), in `ℕ∞`. -/
noncomputable def fatMax (r : ℕ) (γ : ℝ) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : 1 ≤ d), fat (MaxClass d r) γ

/-- `fat⁰_γ(F_{max,r}) = sup_{d ≥ 1} fat⁰_γ(F^{(d)}_{max,r})` (zero witnesses), in `ℕ∞`. -/
noncomputable def fat0Max (r : ℕ) (γ : ℝ) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : 1 ≤ d), fat0 (MaxClass d r) γ

/-- The critical margin with witnesses, `γ_c = 1/(3√3)`. -/
noncomputable def gammaC : ℝ := 1 / (3 * Real.sqrt 3)

/-- `g⋆ = 63/449`. -/
noncomputable def gStar : ℝ := 63 / 449

/-- `g_w = 17/(54√3)`. -/
noncomputable def gW : ℝ := 17 / (54 * Real.sqrt 3)

/-- The factor `L = min{ln(e/Δ), ln ln r}` of Theorem 1.1(a), with the paper's convention
`ln(e/0) = ∞`, so that `L = ln ln r` when `Δ = 0`. -/
noncomputable def Lfactor (Δ : ℝ) (r : ℕ) : ℝ :=
  if Δ = 0 then Real.log (Real.log r)
  else min (Real.log (Real.exp 1 / Δ)) (Real.log (Real.log r))

end MarginMaxima.Critical


