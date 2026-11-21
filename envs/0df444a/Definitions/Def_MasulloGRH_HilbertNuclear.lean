-- Prove2me | Definitions.Def_MasulloGRH_HilbertNuclear
-- name    : MasulloGRH_HilbertNuclear
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:21:32.309115+00:00
-- url     : https://prove2.me/theorems/a9a326e0-0101-4e1f-b617-c0b71b8769cc
-- title:
--   Nuclear operators on Hilbert spaces: trace, trace norm, Hilbert–Schmidt norm
-- statement:
--   Let $H$ be a complex Hilbert space and $T$ a bounded operator on $H$.
--
--   1. $T$ is **nuclear**, or trace class, if there are sequences $(x_m)$, $(y_m)$ in $H$ with $\sum_m\|x_m\|\,\|y_m\|<\infty$ and
--   $$Tu=\sum_{m}\langle u,x_m\rangle\,y_m\qquad\text{for all }u\in H .$$
--   2. The **trace** of $T$ is
--   $$\operatorname{Trace}(T)=\sum_{\varphi\in\Sigma}\langle T\varphi,\varphi\rangle_H$$
--   for an orthonormal basis $\Sigma$ of $H$. For nuclear $T$ the sum converges absolutely and does not depend on $\Sigma$.
--   3. The absolute value is $|T|=(T^*T)^{1/2}$, and the **trace norm** is $\|T\|_{\mathrm{Tr}}=\operatorname{Trace}(|T|)$.
--   4. The **Hilbert–Schmidt norm** is $\|T\|_{S_2}=\big(\sum_{\varphi\in\Sigma}\|T\varphi\|^2\big)^{1/2}$, and $T$ is **Hilbert–Schmidt** if this is finite.
--
--   The nuclear operators form the ideal $N(H)$, normed by the trace norm; the draft computes traces of operators on Hardy–Sobolev completions of spaces of $\theta$-functions.
--
--   **Formalization Note** The sums of items 2 and 4 are taken over one fixed orthonormal basis of $H$. The inner product is linear in the second variable, so $\langle T\varphi,\varphi\rangle_H$ is written with $T\varphi$ in the second slot.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.3, Definition C.3.4.2 (pp. 697–698) and Definition C.3.6.2 (p. 704)

import Mathlib

/-!
# Nuclear operators, traces and Hilbert–Schmidt operators on Hilbert spaces

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix C, §C.3:
Definition C.3.4.2 (pp. 697–698), Definition C.3.6.2 (p. 704).
-/

namespace MasulloGRH

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `T` is a nuclear (trace-class) operator on the Hilbert space `H`: there are sequences
`(x_m)`, `(y_m)` in `H` with `∑ ‖x_m‖ ‖y_m‖ < ∞` and `T u = ∑_m ⟨u, x_m⟩ y_m` for all `u`. -/
def IsNuclearOperator (T : H →L[ℂ] H) : Prop :=
  ∃ x y : ℕ → H, Summable (fun m => ‖x m‖ * ‖y m‖) ∧
    ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)

/-- An orthonormal basis of `H`, chosen once and for all. -/
def chosenHilbertBasis (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : HilbertBasis (exists_hilbertBasis ℂ H).choose ℂ H :=
  (exists_hilbertBasis ℂ H).choose_spec.choose

/-- Definition C.3.4.2(1): the trace `∑_φ ⟨T φ, φ⟩` of an operator `T`, the sum over an
orthonormal basis of `H`.  For a nuclear operator the sum converges absolutely and does not
depend on the orthonormal basis. -/
def operatorTrace (T : H →L[ℂ] H) : ℂ :=
  ∑' i, inner ℂ (chosenHilbertBasis H i) (T (chosenHilbertBasis H i))

/-- The absolute value `|T| = (T* T)^{1/2}` of an operator. -/
def operatorAbs (T : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (star T * T)

/-- Definition C.3.4.2(2): the trace norm `‖T‖_Tr = Trace |T|`. -/
def traceNorm (T : H →L[ℂ] H) : ℝ := (operatorTrace (operatorAbs T)).re

/-- The Hilbert–Schmidt norm `‖T‖_{S₂} = (∑_φ ‖T φ‖²)^{1/2}` (Definition C.3.6.2), the sum over an
orthonormal basis of `H`. -/
def hilbertSchmidtNorm (T : H →L[ℂ] H) : ℝ :=
  Real.sqrt (∑' i, ‖T (chosenHilbertBasis H i)‖ ^ 2)

/-- `T` is a Hilbert–Schmidt operator: `∑_φ ‖T φ‖² < ∞` over an orthonormal basis. -/
def IsHilbertSchmidt (T : H →L[ℂ] H) : Prop :=
  Summable (fun i => ‖T (chosenHilbertBasis H i)‖ ^ 2)

end

end MasulloGRH


