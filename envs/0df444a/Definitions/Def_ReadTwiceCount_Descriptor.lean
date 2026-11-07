-- Prove2me | Definitions.Def_ReadTwiceCount_Descriptor
-- name    : ReadTwiceCount_Descriptor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:48.708566+00:00
-- url     : https://prove2.me/theorems/9d9d74c7-1450-4dbd-98c6-ab2d8333bf02
-- title:
--   The descriptor $\mathcal F(y)=(1-c\prod_{I_-}\frac{y_i}{y_i+1}\prod_{I_+}\frac{1}{y_i+1})^{-1}$
-- statement:
--   An (abstract) **descriptor** has a number $t\ge0$ of free factors, giving the coefficient $c=2^{-t}$, and $n$ inputs, each labelled $\mathrm{EQ}$ or $\mathrm{NEQ}$. Write $I_-$ for the $\mathrm{NEQ}$ inputs and $I_+$ for the $\mathrm{EQ}$ inputs. At real inputs $y=(y_1,\dots,y_n)$,
--   $$Q(y)=c\prod_{i\in I_-}\frac{y_i}{y_i+1}\prod_{i\in I_+}\frac{1}{y_i+1},\qquad \mathcal F(y)=\frac{1}{1-Q(y)} .$$
--   This is display (6): substituting $p_i=1/(y_i+1)$ into the prefix product (4) and the parent coordinate (5).
--
--   The descriptor with $t=0$ and no inputs has $Q=1$; it corresponds to a zero parent marginal and is called **singular**. Every other descriptor is **nonsingular**. The partial derivative $\partial\mathcal F/\partial y_i$ is the derivative of $\mathcal F$ in its $i$-th input with the others fixed.
--
--   **Formalization Note** $\mathcal F$ is a real function; it is used at inputs $y_i\ge1$, where it is finite for every nonsingular descriptor.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §3, p.4, displays (4)–(6)

import Mathlib

namespace ReadTwiceCount

/-- The label of an incidence of a descriptor (He, *A Deterministic Approximation Scheme for
Counting Read-Twice CNF Assignments*, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §3, p.3):
`EQ` if the queried occurrence `zᵢ` and the clause literal `xᵢ` have the same sign, `NEQ` if their
signs differ. -/
inductive Label
  | EQ
  | NEQ
  deriving DecidableEq

/-- The factor of one input in the descriptor: `y/(y+1)` for `NEQ` (that is `1 − pᵢ` with
`pᵢ = 1/(yᵢ+1)`) and `1/(y+1)` for `EQ` (that is `pᵢ`). -/
noncomputable def Label.factor : Label → ℝ → ℝ
  | .NEQ, y => y / (y + 1)
  | .EQ, y => 1 / (y + 1)

/-- **An abstract descriptor**: a number `t` of free factors (coefficient `c = 2^{−t}`) and `n`
inputs, each labelled `EQ` or `NEQ`. -/
structure Descriptor where
  /-- The number of free factors; the coefficient is `c = 2^{−t}`. -/
  t : ℕ
  /-- The number of inputs. -/
  n : ℕ
  /-- The label of each input. -/
  label : Fin n → Label

namespace Descriptor

/-- `Q(y) = c ∏_{i∈I−} yᵢ/(yᵢ+1) ∏_{i∈I+} 1/(yᵢ+1)`, `c = 2^{−t}`: display (4) after substituting
`pᵢ = 1/(yᵢ+1)`. -/
noncomputable def Q (d : Descriptor) (y : Fin d.n → ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ d.t * ∏ i, (d.label i).factor (y i)

/-- **The finite descriptor `ℱ(y)`**, display (6) (He, STOC 2027 submission, manuscript sha256
7a2a9dcd…, §3, p.4): `ℱ(y) = (1 − c ∏_{i∈I−} yᵢ/(yᵢ+1) ∏_{i∈I+} 1/(yᵢ+1))^{−1}`, `c = 2^{−t}`, where
`I−` holds the `NEQ` inputs and `I+` the `EQ` inputs.

**Formalization Note** ℱ is a real function of real inputs; it is used at inputs `yᵢ ≥ 1`. -/
noncomputable def value (d : Descriptor) (y : Fin d.n → ℝ) : ℝ := 1 / (1 - d.Q y)

/-- A descriptor is **nonsingular** unless it has no factors and `c = 1` (p.4: "A descriptor with no
factors and c = 1 would have Q = 1 and a zero parent marginal; the preliminary zero test excludes this
case"). -/
def Nonsingular (d : Descriptor) : Prop := d.t ≠ 0 ∨ d.n ≠ 0

/-- The partial derivative `∂ℱ/∂yᵢ` at `y`: the derivative of `ℱ` in its `i`-th input with the
others fixed. -/
noncomputable def partialDeriv (d : Descriptor) (y : Fin d.n → ℝ) (i : Fin d.n) : ℝ :=
  deriv (fun z => d.value (Function.update y i z)) (y i)

end Descriptor

end ReadTwiceCount


