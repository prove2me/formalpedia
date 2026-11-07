-- Prove2me | Definitions.Def_ModFormPIR_Weil
-- name    : ModFormPIR_Weil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:39.385125+00:00
-- url     : https://prove2.me/theorems/a8629fc0-e9f2-49c6-8545-4a9d8eefe9a5
-- title:
--   The matrices $\rho_T,\rho_S$ and the theta function $\Theta$
-- statement:
--   Let $\zeta_q=e^{2\pi i/q}$ and $\mu\not\equiv0\pmod q$. With $\varepsilon_{\mu,q}$ determined by $\sum_{y}\zeta_q^{\mu y^2}=\varepsilon_{\mu,q}^{-1}\sqrt q$, the matrices of the Weil representation at the generators are
--   $$\rho_Te_x=\zeta_q^{\mu x^2}e_x,\qquad \rho_Se_x=\frac{\varepsilon_{\mu,q}}{\sqrt q}\sum_{y}\zeta_q^{-2\mu xy}e_y.$$
--   For $g=\begin{pmatrix}a&b\\c&d_0\end{pmatrix}\in SL_2(\mathbb Z)$ the automorphy factor is $G(g,\tau)=c\tau+d_0$. The vector-valued Jacobi theta function is
--   $$\Theta(\tau,w)=\sum_{k\in\mathbb Z}(-1)^k\exp\Big(\frac{\pi i\tau}q\big(k-\tfrac12\big)^2+2\pi i\big(k-\tfrac12\big)w\Big)e_{k+(q-1)/2\bmod q}.$$
--   §12 uses the parameter $\mu=(q+1)/2$. These are the objects whose transformation law drives the modular-forms part of the proof.
--
--   **Formalization Note** The series is a `tsum` in each coordinate; the sanity file proves it summable.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Fact 10.9, Definition 10.10, pp.40–41; Definition 10.16, p.42; Definition 12.12, p.69

import Mathlib
import Definitions.Def_ModFormPIR_Exponent

open Complex Matrix
open scoped UpperHalfPlane
open scoped BigOperators MatrixGroups Real

set_option autoImplicit false

namespace ModFormPIR

/-!
# The Weil representation and the vector-valued theta function

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Fact 10.9, Definition 10.10, pp.40–41; Definitions 10.12, 10.16, pp.41–42;
Definitions 12.10, 12.12, pp.68–69.

**Formalization Note.** `ε_{μ,q}` is defined by the printed identity `∑_y ζ_q^{μy²} = ε⁻¹√q`, that is
`ε = √q / ∑_y ζ_q^{μy²}`; the Gauss sum is nonzero, so no division by zero occurs. A vector in `ℂ^q` is a function
`ZMod q → ℂ`, and a matrix acts by `mulVec`, so the column of `x` is `ρ e_x`.
-/

variable (q : ℕ) [NeZero q]

/-- `ζ_q = e^{2πi/q}`. -/
noncomputable def zeta : ℂ := exp (2 * π * I / q)

/-- `ζ_q^t` for `t ∈ ℤ_q`. -/
noncomputable def zq (t : ZMod q) : ℂ := zeta q ^ t.val

/-- `ε_{μ,q}`, determined by `∑_y ζ_q^{μy²} = ε⁻¹√q` (Fact 10.9). -/
noncomputable def epsilonWeil (μ : ℤ) : ℂ :=
  (Real.sqrt q : ℂ) / ∑ y : ZMod q, zq q ((μ : ZMod q) * y ^ 2)

/-- `ρ_T`: diagonal, `e_x ↦ ζ_q^{μx²} e_x` (Definition 10.10). -/
noncomputable def rhoT (μ : ℤ) : Matrix (ZMod q) (ZMod q) ℂ :=
  Matrix.of fun y x => if y = x then zq q ((μ : ZMod q) * x ^ 2) else 0

/-- `ρ_S`: `e_x ↦ (ε_{μ,q}/√q) ∑_y ζ_q^{-2μxy} e_y` (Definition 10.10). -/
noncomputable def rhoS (μ : ℤ) : Matrix (ZMod q) (ZMod q) ℂ :=
  Matrix.of fun y x =>
    (epsilonWeil q μ / (Real.sqrt q : ℂ)) * zq q (-2 * (μ : ZMod q) * x * y)

/-- `ρ` takes the printed values at the generators `T` and `S` (Fact 10.11). -/
def IsWeil (μ : ℤ) (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) : Prop :=
  ρ ModularGroup.T = rhoT q μ ∧ ρ ModularGroup.S = rhoS q μ

/-- The parameter `μ = (q+1)/2` used in §12 (p.70). -/
def muHalf : ℤ := (((q + 1) / 2 : ℕ) : ℤ)

/-- `G(g,τ) = cτ + d₀` for `g = [a b; c d₀]` (Definition 10.16). -/
noncomputable def denomG (g : SL(2, ℤ)) (τ : ℍ) : ℂ := ((g 1 0 : ℤ) : ℂ) * τ + ((g 1 1 : ℤ) : ℂ)

/-- The `k`-th term of `Θ` (Definition 12.12):
`(-1)^k exp((πiτ/q)(k-1/2)² + 2πi(k-1/2)w)`. -/
noncomputable def thetaTerm (τ : ℍ) (w : ℂ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k *
    exp (π * I * τ / q * ((k : ℂ) - 1 / 2) ^ 2 + 2 * π * I * ((k : ℂ) - 1 / 2) * w)

/-- The coordinate shift `k ↦ k + (q-1)/2 mod q` of Definition 12.12. -/
def thetaIndex (k : ℤ) : ZMod q := ((k + (((q - 1) / 2 : ℕ) : ℤ) : ℤ) : ZMod q)

/-- Definition 12.12: `Θ(τ,w) = ∑_{k∈ℤ} (-1)^k exp((πiτ/q)(k-1/2)² + 2πi(k-1/2)w) e_{k+(q-1)/2 mod q}`,
coordinate by coordinate. -/
noncomputable def Theta (τ : ℍ) (w : ℂ) : ZMod q → ℂ :=
  fun r => ∑' k : ℤ, if thetaIndex q k = r then thetaTerm q τ w k else 0

end ModFormPIR


