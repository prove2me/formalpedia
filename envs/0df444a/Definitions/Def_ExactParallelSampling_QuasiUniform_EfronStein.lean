-- Prove2me | Definitions.Def_ExactParallelSampling_QuasiUniform_EfronStein
-- name    : ExactParallelSampling_QuasiUniform_EfronStein
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:49:53.183777+00:00
-- url     : https://prove2.me/theorems/7e369a2c-50fa-4f69-aa9f-c74182e19c20
-- title:
--   Efron–Stein components of the conditional law of one coordinate; support-size queries; L_q and R_q
-- statement:
--   The objects of §5.1 (pp. 24–25) and §7 (p. 37). Fix $\mu$, a set $B$ and $x\notin B$, and let $Y$ be uniform on $\Omega_B$.
--
--   - `condVec p B Z x y` $=p_Z(y)$: the conditional law $a\mapsto\Pr[X_x=a\mid X_Z=y_Z]$ for $Z\subseteq B$ and $y\in\Omega_B$. Vectors of $\mathbb R^{\Omega_x}$ are functions on $\alpha$ vanishing off $\Omega_x$.
--   - `uniformVec p x` $=u$: the uniform distribution on $\Omega_x$.
--   - `condExpUnif p B T g y` $=\mathbb E[g(Y)\mid Y_T](y)$: the average of $g$ over the points of $\Omega_B$ that agree with $y$ on $T$.
--   - `esComponent p B x A` $=f_A=\sum_{T\subseteq A}(-1)^{|A\setminus T|}\,\mathbb E[p_B(Y)-u\mid Y_T]$. This is the Efron–Stein component [ES81] of $p_B-u$ when $\Omega_B$ is a product, that is, when $B$ is independent.
--   - `esWeight` $=w_A=\mathbb E\|f_A(Y)\|^2$; `esH` $=H=\{A\subseteq B: A\ne\emptyset,\ w_A>0\}$; `esF p x Z` $=F(Z)=1/s_Z(x)-1/s_x$.
--   - `lcmUpTo r` $=\mathrm{lcm}(1,\dots,r)$.
--   - `ssQuery p x Z z` is a **support-size query**: with a fixed pinning $z$, the number of values $a$ with $\Pr[X_Z=z_Z,X_x=a]>0$, read off at most $|\Omega_x|$ counting queries.
--   - $L_q=\mathrm{lcm}(1,\dots,q)$, $R_q=2+\lceil\log_2\log_2L_q\rceil$ and $R'_q=2+\lceil\log_2\log_2q\rceil$ (logarithms base 2).
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, §5.1 and §7, p. 24–25, 37; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-! # Efron–Stein components of the conditional law of one coordinate (§5.1, pp. 24–25)

Setting of §5.1: `μ` quasi-uniform, `B` independent, `x ∉ B`, `r = s_x`. `Y` is uniform on
`Ω_B` (a product, because `B` is independent). For `Z ⊆ B` and `y ∈ Ω_B`, `p_Z(y) ∈ ℝ^{Ω_x}` is the
conditional law of `X_x` given `X_Z = y_Z`, and `u` is the uniform distribution on `Ω_x`. Vectors in
`ℝ^{Ω_x}` are written as functions `α → ℝ` vanishing off `Ω_x`. -/

variable {E α : Type*} [Fintype E] [Fintype α]

/-- `x'` agrees with the pinning `y` of `B` on the coordinates of `Z` (`Z ⊆ B`). -/
def AgreesOn (B Z : Finset E) (y : ↥B → α) (x' : E → α) : Prop :=
  ∀ j (h : j ∈ B), j ∈ Z → x' j = y ⟨j, h⟩

/-- `p_Z(y)`: the conditional law `a ↦ Pr[X_x = a | X_Z = y_Z]` of `X_x` given `X_Z = y_Z`. -/
def condVec (p : (E → α) → ℝ) (B Z : Finset E) (x : E) (y : ↥B → α) : α → ℝ :=
  fun a =>
    (∑ x' ∈ Finset.univ.filter (fun x' : E → α => AgreesOn B Z y x' ∧ x' x = a), p x') /
      (∑ x' ∈ Finset.univ.filter (fun x' : E → α => AgreesOn B Z y x'), p x')

/-- `u`: the uniform distribution on `Ω_x`. -/
def uniformVec (p : (E → α) → ℝ) (x : E) : α → ℝ :=
  fun a => if a ∈ singleSupp p x then 1 / (s p x : ℝ) else 0

/-- `E[g(Y) | Y_T]` for `Y` uniform on `Ω_B`, evaluated at `y` (`T ⊆ B`). -/
def condExpUnif (p : (E → α) → ℝ) (B T : Finset E) (g : (↥B → α) → α → ℝ) (y : ↥B → α) :
    α → ℝ :=
  let fiber := (supp p B).filter (fun y' => ∀ j (h : j ∈ B), j ∈ T → y' ⟨j, h⟩ = y ⟨j, h⟩)
  fun a => (∑ y' ∈ fiber, g y' a) / (fiber.card : ℝ)

/-- The Efron–Stein component `f_A` of the vector-valued function `p_B − u` of `Y` uniform on
`Ω_B` [ES81]: `f_A = ∑_{T ⊆ A} (−1)^{|A ∖ T|} E[p_B(Y) − u | Y_T]` (`A ⊆ B`). -/
def esComponent (p : (E → α) → ℝ) (B : Finset E) (x : E) (A : Finset E) (y : ↥B → α) :
    α → ℝ :=
  fun a => ∑ T ∈ A.powerset, (-1 : ℝ) ^ (A \ T).card *
    condExpUnif p B T (fun y' a' => condVec p B B x y' a' - uniformVec p x a') y a

/-- The weight `w_A = E‖f_A(Y_A)‖²` for `Y` uniform on `Ω_B`. -/
def esWeight (p : (E → α) → ℝ) (B : Finset E) (x : E) (A : Finset E) : ℝ :=
  (∑ y ∈ supp p B, ∑ a, (esComponent p B x A y a) ^ 2) / ((supp p B).card : ℝ)

/-- `H = {A ⊆ B : A ≠ ∅, w_A > 0}`. -/
def esH (p : (E → α) → ℝ) (B : Finset E) (x : E) : Finset (Finset E) :=
  B.powerset.filter (fun A => A ≠ ∅ ∧ 0 < esWeight p B x A)

/-- `F(Z) = 1/s(Z) − 1/r` with `s(Z) = s_Z(x)` and `r = s_x`. -/
def esF (p : (E → α) → ℝ) (x : E) (Z : Finset E) : ℝ :=
  1 / condSize p Z x - 1 / (s p x : ℝ)

/-- `lcm(1, …, r)`. -/
def lcmUpTo (r : ℕ) : ℕ :=
  (Finset.Icc 1 r).lcm id

/-- A support-size query (§5.1, p. 24): with a fixed pinning `z` of `Z`, the number of values
`a` of `X_x` with `Pr[X_Z = z_Z, X_x = a] > 0`, i.e. the number of positive answers among the
counting queries `Pr[X_Z = z_Z, X_x = a]`. -/
def ssQuery (p : (E → α) → ℝ) (x : E) (Z : Finset E) (z : E → α) : ℕ :=
  (Finset.univ.filter (fun a => 0 < count p (insert x Z) (Function.update z x a))).card

/-- `L_q = lcm(1, …, q)` (§7, p. 37). -/
def Lq (q : ℕ) : ℕ := lcmUpTo q

/-- `R_q = 2 + ⌈log₂ log₂ L_q⌉` (§7, p. 37). -/
def Rq (q : ℕ) : ℕ := 2 + ⌈Real.logb 2 (Real.logb 2 (Lq q : ℝ))⌉₊

/-- `R'_q = 2 + ⌈log₂ log₂ q⌉` (Lemma 7.2). -/
def Rq' (q : ℕ) : ℕ := 2 + ⌈Real.logb 2 (Real.logb 2 (q : ℝ))⌉₊

end ExactParallelSampling.QuasiUniform


