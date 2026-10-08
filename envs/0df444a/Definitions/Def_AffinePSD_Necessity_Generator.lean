-- Prove2me | Definitions.Def_AffinePSD_Necessity_Generator
-- name    : AffinePSD_Necessity_Generator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:20.163721+00:00
-- url     : https://prove2.me/theorems/b0e743ce-ee08-4584-82f1-66fc28598815
-- title:
--   Symmetrized partial derivatives on $S_d$ and the operator $\mathcal A^\sharp$ of (2.12)
-- statement:
--   This file defines the right-hand side of the generator formula (2.12).
--
--   Following §1.2, a function $f$ on $S_d$ is read as $g(x) = f((x + x^\top)/2)$ on $M_d$, so $\partial f/\partial x_{ij}$ is the derivative of $f$ in the direction $\tfrac12(E^{ij}+E^{ji})$; second derivatives and the gradient $\nabla f(x) = (\partial f(x)/\partial x_{ij})_{i,j}$ follow the same convention.
--
--   Given a truncation function $\chi$ and a parameter set, for $f$ in the space $\mathcal S_+$ of restrictions to $S_d^+$ of rapidly decreasing smooth functions on $S_d$ (B.1) and $x \in S_d^+$,
--   $$\begin{aligned}\mathcal A^\sharp f(x) ={}& \frac12 \sum_{i,j,k,l} A_{ijkl}(x)\, \frac{\partial^2 f(x)}{\partial x_{ij}\,\partial x_{kl}} + \sum_{i,j} \big(b_{ij} + B_{ij}(x)\big) \frac{\partial f(x)}{\partial x_{ij}} - \big(c + \langle \gamma, x\rangle\big) f(x) \\ &+ \int_{S_d^+\setminus\{0\}} \big(f(x+\xi) - f(x)\big)\, m(d\xi) \\ &+ \int_{S_d^+\setminus\{0\}} \big(f(x+\xi) - f(x) - \langle \chi(\xi), \nabla f(x)\rangle\big)\, M(x,d\xi).\end{aligned}$$
--
--   Theorem 2.4 identifies $\mathcal A^\sharp$ with the generator of an affine process on $\mathcal S_+$.
--
--   **Formalization Note.** $\mathcal S_+$ is encoded by Schwartz functions $F$ on $M_d$ restricted to the cone. Restricting a Schwartz function on $M_d$ to $S_d$ gives one on $S_d$, and $F(\mathrm{sym}\,x)\,e^{-\|x - x^\top\|^2}$ extends one from $S_d$, so the restrictions to $S_d^+$ are exactly $\mathcal S_+$. Derivatives are taken in the symmetric directions $\tfrac12(E^{ij}+E^{ji})$; the sum against $A_{ijkl}$ does not depend on the chosen symmetric extension because $A_{ijkl}$ is symmetric under $i\leftrightarrow j$ and $k \leftrightarrow l$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §1.2, p. 6 (derivative convention); (2.12), p. 9; (B.1), p. 65

import Mathlib
import Definitions.Def_AffinePSD_Necessity_Params

open MeasureTheory
open scoped SchwartzMap

namespace AffinePSD.Necessity

/-- The first partial derivative `∂f(x)/∂x_{ij}` in the paper's convention (§1.2, p. 6): a function `f`
on `S_d` is read as `g(x) = f((x + x^⊤)/2)` on `M_d`, so `∂f/∂x_{ij}` is the derivative of `F` in the
symmetric direction `(E^{ij} + E^{ji})/2`. -/
noncomputable def D1 {d : ℕ} (F : Mat d → ℝ) (x : Mat d) (i j : Fin d) : ℝ :=
  fderiv ℝ F x (symE i j)

/-- The second partial derivative `∂²f(x)/∂x_{ij}∂x_{kl}` in the convention of `D1`. -/
noncomputable def D2 {d : ℕ} (F : Mat d → ℝ) (x : Mat d) (i j k l : Fin d) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ F y (symE i j)) x (symE k l)

/-- The gradient `∇f(x) = (∂f(x)/∂x_{ij})_{i,j}` in the convention of `D1`. -/
noncomputable def grad {d : ℕ} (F : Mat d → ℝ) (x : Mat d) : Mat d := fun i j => D1 F x i j

/-- The right-hand side `A^♯ f(x)` of (2.12) (Theorem 2.4, p. 9) for `f = F|_{S_d^+}`, `F` a Schwartz
function:
`½ ∑ A_{ijkl}(x) ∂²f/∂x_{ij}∂x_{kl} + ∑ (b_{ij} + B_{ij}(x)) ∂f/∂x_{ij} − (c + ⟨γ, x⟩) f(x)
 + ∫ (f(x+ξ) − f(x)) m(dξ) + ∫ (f(x+ξ) − f(x) − ⟨χ(ξ), ∇f(x)⟩) M(x, dξ)`.

**Formalization Note.** The space `S_+` of (B.1) (p. 65) is encoded by Schwartz functions on `M_d`
restricted to the cone: restricting a Schwartz function on `M_d` to `S_d` gives one on `S_d`, and
`F(sym x)·e^{−‖x − x^⊤‖²}` extends one from `S_d`, so the restrictions to `S_d^+` are exactly `S_+`. The
derivatives are the symmetrized partials `D1`, `D2`; the sum with `A_{ijkl}` does not depend on the
symmetric extension because `A_{ijkl}` is symmetric in `i ↔ j` and in `k ↔ l`. -/
noncomputable def Asharp {d : ℕ} (χ : Trunc d) (P : Params d) (F : 𝓢(Mat d, ℝ)) (x : Cone d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l, Acoef P x i j k l * D2 F x i j k l
  + ∑ i, ∑ j, (P.b i j + Bmap P x i j) * D1 F x i j
  - (P.c + tr P.γ x) * F x
  + ∫ ξ, (F ((x : Mat d) + (ξ : Mat d)) - F x) ∂P.m
  + ∫ ξ, (F ((x : Mat d) + (ξ : Mat d)) - F x - tr (χ.χ ξ) (grad F x)) ∂(Mker P x)

end AffinePSD.Necessity


