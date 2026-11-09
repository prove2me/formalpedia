-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Potential
-- name    : HardCoreLocalSampling_Local_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:36.502898+00:00
-- url     : https://prove2.me/theorems/d037becd-1401-4d77-b38f-73d7dabee9fb
-- title:
--   Potential recursion, root probability, and multi-index Taylor coefficients
-- statement:
--   With $\phi(R)=\operatorname{arsinh}\sqrt R$, the message of $s=(H,v)$ is $y_s=\phi(R_H(v))$, and all true messages lie in $[0,U]$, $U=\operatorname{arsinh}\sqrt\lambda$. The constant $\bar U=2+\lambda$ is a different constant, the right end of the grid interval of Lemma 9. The recursion and the root probability are
--
--   $$
--   F_d(y)=\operatorname{arsinh}\Bigl(\sqrt\lambda\prod_{i=1}^d\operatorname{sech}y_i\Bigr),\qquad
--   P_d(y)=\frac1{1+\lambda\prod_{i=1}^d\operatorname{sech}^2y_i}.
--   $$
--
--   Their complex extensions are $\log(A+(1+A^2)^{1/2})$, $A=\sqrt\lambda\prod_i\operatorname{sech}z_i$, with principal branches, and $(1+A^2)^{-1}$.
--
--   Multi-indices are $\alpha\in\mathbb N^d$, $|\alpha|=\sum_i\alpha_i$, $\alpha!=\prod_i\alpha_i!$, and the Taylor coefficient of $f$ at $c$ is $\partial^\alpha f(c)/\alpha!$. For a parent center $c_s$ and scale $\eta$, the normalized coefficients of equations (14)–(16) are
--
--   $$
--   d_{s,0}=\frac{F_d(c_{s_1},\dots,c_{s_d})-c_s}{\eta},\qquad
--   d_{s,\alpha}=\eta^{|\alpha|-1}\frac{\partial^\alpha F_d(c_{s_1},\dots,c_{s_d})}{\alpha!}\quad(|\alpha|\ge1),
--   $$
--
--   and the root coefficients of (22) are $h_\alpha=\eta^{|\alpha|}\partial^\alpha P_d(c)/\alpha!$.
--
--   **Formalization Note** The partial derivative is the one-variable `deriv` along a coordinate, so it is meaningful where the function is differentiable; all functions here are analytic where they are used. At $\alpha=0$ the Taylor coefficient is the function value, which is how `normalizedCoeff` writes $d_{s,0}$.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §5 eqs. (1)–(2), printed p.6 (PDF p.7); §6 eq. (7), printed p.7 (PDF p.8); §7 eqs. (14)–(16), printed p.8 (PDF p.9); §9 eq. (22), printed p.10 (PDF p.11)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Deletion

namespace HardCoreLocalSampling.Local

/-! The potential coordinate and its recursion, §5 eq. (2) and §6 eq. (7), printed pp.6–7 /
PDF pp.7–8, with multi-index Taylor coefficients (§4, §7). `N^d` is `Fin d → ℕ`. -/

/-- `F_d(y) = arsinh(√λ ∏ sech y_i)`, eq. (2). -/
noncomputable def Fd {d : ℕ} (lam : ℝ) (y : Fin d → ℝ) : ℝ :=
  Real.arsinh (Real.sqrt lam * ∏ i, (Real.cosh (y i))⁻¹)

/-- `P_d(y) = 1 / (1 + λ ∏ sech² y_i)`, eq. (7): the root's unoccupied probability. -/
noncomputable def Pd {d : ℕ} (lam : ℝ) (y : Fin d → ℝ) : ℝ :=
  1 / (1 + lam * ∏ i, ((Real.cosh (y i))⁻¹) ^ 2)

/-- `A(z) = √λ ∏ sech z_i` on complex arguments. -/
noncomputable def complexA {d : ℕ} (lam : ℝ) (z : Fin d → ℂ) : ℂ :=
  (Real.sqrt lam : ℂ) * ∏ i, (Complex.cosh (z i))⁻¹

/-- The complex extension of `F_d`: `log (A + (1 + A²)^{1/2})` with principal branches,
as in the proof of Lemma 8. -/
noncomputable def FdC {d : ℕ} (lam : ℝ) (z : Fin d → ℂ) : ℂ :=
  Complex.log (complexA lam z + (1 + complexA lam z ^ 2) ^ (1 / 2 : ℂ))

/-- The complex extension of `P_d`: `(1 + λ ∏ sech² z_i)⁻¹`, eq. (7). -/
noncomputable def PdC {d : ℕ} (lam : ℝ) (z : Fin d → ℂ) : ℂ :=
  1 / (1 + (lam : ℂ) * ∏ i, ((Complex.cosh (z i))⁻¹) ^ 2)

/-- `U = arsinh √λ`, the upper bound of all true messages. Distinct from `Ubar`. -/
noncomputable def Umsg (lam : ℝ) : ℝ := Real.arsinh (Real.sqrt lam)

/-- `Ū = 2 + λ`, the right end of the grid interval of Lemma 9. -/
def Ubar (lam : ℚ) : ℚ := 2 + lam

/-- The message `y_s = arsinh √(R_{G-D}(v))` of the subproblem `s = (G - D, v)`. -/
noncomputable def message {V : Type*} [Fintype V] (G : SimpleGraph V) (lam : ℝ)
    (D : Finset V) (v : V) : ℝ :=
  Real.arsinh (Real.sqrt (deletionOdds G lam D v))

/-- The child messages `(y_{s_1}, ..., y_{s_d})` of `s = (G - D, v)` in label order. -/
noncomputable def childMessages {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (lam : ℝ) (D : Finset V) (v : V) : Fin (orderedNeighbors G D v).length → ℝ :=
  fun i => message G lam (childDeleted G D v i) ((orderedNeighbors G D v)[i.val])

section Taylor
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {d : ℕ}

/-- The partial derivative `∂_i f`, by the one-variable derivative along coordinate `i`. -/
noncomputable def partialD (i : Fin d) (f : (Fin d → 𝕜) → 𝕜) : (Fin d → 𝕜) → 𝕜 :=
  fun z => deriv (fun w => f (Function.update z i w)) (z i)

/-- The iterated partial derivative `∂^α f`. -/
noncomputable def iterPartial (α : Fin d → ℕ) (f : (Fin d → 𝕜) → 𝕜) : (Fin d → 𝕜) → 𝕜 :=
  (List.finRange d).foldr (fun i g => (partialD i)^[α i] g) f

/-- The Taylor coefficient `∂^α f(c) / α!` with `α! = ∏ α_i!`. -/
noncomputable def taylorCoeff (f : (Fin d → 𝕜) → 𝕜) (c : Fin d → 𝕜) (α : Fin d → ℕ) : 𝕜 :=
  iterPartial α f c / ((∏ i, (α i).factorial : ℕ) : 𝕜)

/-- The closed polydisc `|z_i - c_i| ≤ r`. -/
def polydisc (c : Fin d → 𝕜) (r : ℝ) : Set (Fin d → 𝕜) :=
  {z | ∀ i, ‖z i - c i‖ ≤ r}

end Taylor

/-- `|α| = ∑ α_i`. -/
def mdeg {d : ℕ} (α : Fin d → ℕ) : ℕ := ∑ i, α i

/-- The monomial `∏ x_i^{α_i}`; the empty product is one. -/
noncomputable def monomial {d : ℕ} (x : Fin d → ℝ) (α : Fin d → ℕ) : ℝ := ∏ i, x i ^ α i

/-- The normalized coefficient of eqs. (14)–(16), from the Taylor coefficients `A α` of the
parent function at the child centers: `d_0 = (A 0 - c_s)/η` and `d_α = η^{|α|-1} A α` for
`|α| ≥ 1`. (`A 0` is the function value at the child centers.) -/
noncomputable def normalizedCoeff {d : ℕ} (eta cs : ℝ) (A : (Fin d → ℕ) → ℝ)
    (α : Fin d → ℕ) : ℝ :=
  if mdeg α = 0 then (A α - cs) / eta else eta ^ (mdeg α - 1) * A α

/-- The root coefficient `h_α = η^{|α|} ∂^α P_d(c) / α!`, eq. (22). -/
noncomputable def rootCoeff {d : ℕ} (lam eta : ℝ) (c : Fin d → ℝ) (α : Fin d → ℕ) : ℝ :=
  eta ^ mdeg α * taylorCoeff (Pd lam) c α

end HardCoreLocalSampling.Local


