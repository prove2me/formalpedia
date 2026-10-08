-- Prove2me | Definitions.Def_PrivLearn_MaskedParity_Oracle
-- name    : PrivLearn_MaskedParity_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:53.108132+00:00
-- url     : https://prove2.me/theorems/386817b7-d6a2-421c-bdbe-8fd5bfb178cf
-- title:
--   The decomposition f_g, C_g, the half-restrictions c^s, f^s (6) and the SQ oracle 𝒪 of §5.3.2
-- statement:
--   Use the domain $D$, the concepts $c_{r,a}$ and the inner product $\langle\cdot,\cdot\rangle$ of MASKED-PARITY. For a statistical query $g(u,y)$ (p. 29) let
--   $$f_g(u)=\frac{g(u,1)-g(u,-1)}2,\qquad C_g=\frac12\,\mathbb E\bigl[g(u,1)+g(u,-1)\bigr],$$
--   the label-dependent part and the label-independent constant of $g$. For $s\in\{0,1\}$ and a function $f$ on $D$, its restriction to the half with last bit $s$ is $f^s(x,i,b)=f(x,i,b)$ if $b=s$ and $0$ if $b\ne s$ (equation (6), p. 29, extended to every $(r,a)$ on p. 30); this gives $c^s_{r,a}$ and $f^s_g$.
--
--   The **SQ oracle** $\mathcal O=\mathcal O_{c_{r,a},\mathcal D}$ (p. 30) answers the query $(g,\tau)$ by
--   $$\mathcal O(g,\tau)=\begin{cases}C_g+\langle f^1_g,c^1_{r,a}\rangle&\text{if } |\langle f^0_g,c^0_{r,a}\rangle|<\tau,\\ \mathbb E\bigl[g(u,c_{r,a}(u))\bigr]&\text{otherwise.}\end{cases}$$
--
--   The oracle drops the only term of the true answer that depends on the mask bit $a$ whenever that term is smaller than the tolerance; it is the oracle against which the paper proves that nonadaptive learners fail.
--
--   **Formalization Note.** Expectations are averages under the uniform distribution on the domain. The restriction $f^s$ is one function `half s f`, used for both $c^s_{r,a}$ and $f^s_g$. The oracle is defined for every real-valued query and every real $\tau$; its validity as an SQ oracle is a theorem, not part of the definition.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 29 (f_g, C_g, equation (6)), p. 30 (the oracle O and the extension of c^0_{r,a})

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model

namespace PrivLearn.MaskedParity

/-- p. 29: the label-dependent part `f_g(u) = (g(u, 1) − g(u, −1))/2` of a query `g`. -/
noncomputable def fg {d : ℕ} (g : Dom d → ℝ → ℝ) : Dom d → ℝ := fun u =>
  (g u 1 - g u (-1)) / 2

/-- p. 29: the label-independent part `C_g = (1/2) E[g(u, 1) + g(u, −1)]` of a query `g`, the
expectation under the uniform distribution on the domain. -/
noncomputable def Cg {d : ℕ} (g : Dom d → ℝ → ℝ) : ℝ :=
  (Fintype.card (Dom d) : ℝ)⁻¹ * ∑ u, (g u 1 + g u (-1)) / 2

/-- (6), p. 29: the restriction `f^s(x, i, b) = f(x, i, b)` if `b = s` and `0` if `b ≠ s` of a
function to the half of the domain with last bit `s`. Applied to `c_{r,a}` it is `c^s_{r,a}`
(extended to every `(r, a)` on p. 30), applied to `f_g` it is `f^s_g`. -/
def half {d : ℕ} (s : ZMod 2) (f : Dom d → ℝ) : Dom d → ℝ := fun u =>
  if u.2.2 = s then f u else 0

/-- p. 30: the SQ oracle `𝒪 = 𝒪_{c_{r,a},𝒟}` on the target `c_{r,a}` and the uniform distribution:
`𝒪(g, τ) = C_g + ⟨f^1_g, c^1_{r,a}⟩` if `|⟨f^0_g, c^0_{r,a}⟩| < τ`, and the exact value
`E[g(u, c_{r,a}(u))]` otherwise. -/
noncomputable def oracleO {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) (g : Dom d → ℝ → ℝ) (τ : ℝ) :
    ℝ :=
  if |ip (half 0 (fg g)) (half 0 (cMP r a))| < τ then
    Cg g + ip (half 1 (fg g)) (half 1 (cMP r a))
  else qval (cMP r a) g

end PrivLearn.MaskedParity


