-- Prove2me | Definitions.Def_CliffordHierTest_PauliNorm
-- name    : CliffordHierTest_PauliNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:01.089857+00:00
-- url     : https://prove2.me/theorems/7b90cbca-281a-4a43-97df-cb24e77c70cb
-- title:
--   Normalized trace inner product, Pauli derivatives $\partial_h U$ and Pauli uniformity norms $\|U\|_{P^k}$
-- statement:
--   Let $d$ be a prime and $n\ge0$. Operators on $n$ qudits, $L(d^n)$, are complex matrices indexed by $\mathbb F_d^n$. For $a=(u,v)\in\mathbb F_d^{2n}$ the **Weyl operator** is $W_a=\tau^{-(|u_1v_1|+\cdots+|u_nv_n|)}Z^uX^v$, where $X^v|x\rangle=|x+v\rangle$, $Z^u|x\rangle=\omega^{u\cdot x}|x\rangle$, $\omega=e^{2\pi i/d}$ and $\tau=(-1)^de^{i\pi/d}$.
--
--   The **normalized Hilbert–Schmidt inner product** and the **Frobenius norm** are
--   $$\langle U,V\rangle=\frac1{d^n}\operatorname{tr}[U^*V],\qquad \|U\|_2=\sqrt{\langle U,U\rangle}.$$
--   The **Pauli derivative** of $U$ in direction $h\in\mathbb F_d^{2n}$ is $\partial_hU=W_hUW_h^*U^*$, and the **$k$-th Pauli uniformity norm** is
--   $$\|U\|_{P^k}=\Big(\mathop{\mathbb E}_{h_1,\dots,h_k\in\mathbb F_d^{2n}}\frac1{d^n}\operatorname{tr}[\partial_{h_k}\cdots\partial_{h_1}U]\Big)^{1/2^k}.$$
--   The **Fourier coefficients** of $U$ are $\hat U(a)=\langle W_a,U\rangle$.
--
--   These are the analytic objects of the mission: the norms $\|\cdot\|_{P^k}$ are noncommutative analogues of the Gowers uniformity norms, and their near-extremizers are the subject of the main theorem.
--
--   **Formalization Note** The register is `ResidueRegister d n = Fin n → ZMod d`; $W_a$ is the published GNW21 operator `cyclicWeyl d n a` (its phase exponent $\sum_j|u_j||v_j|$ agrees with $\sum_j|u_jv_j|$ modulo the order $D$ of $\tau$). The expectation is the average over `Fin k → DiscretePhaseSpace d n`, with $h_1$ applied first. The averaged trace `pauliMoment k U` is a nonnegative real for every matrix; `pauliNorm k U` is the $2^k$-th root of its complex modulus.
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.1 Definition 3, p.4; §2.2 (inner product, Frobenius norm, Definitions 7, 8), p.5; Definition 15, p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

open scoped Matrix

namespace CliffordHierTest

/-!
# Inner product, Pauli derivatives and Pauli uniformity norms

Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256
610d53a6…), §2.1, p.4 (Definition 3); §2.2, p.5 (normalized Hilbert–Schmidt inner product,
Frobenius norm, Definitions 7 and 8); §3, p.7 (Definition 15).

**Formalization Note.** The `n`-qudit register is `ResidueRegister d n = Fin n → ZMod d`, so
`L(dⁿ)` is `QuditOperator d n`, the complex matrices indexed by it. Phase-space points
`a = (u, v) ∈ 𝔽_d^{2n}` are `DiscretePhaseSpace d n` (pairs, `u` the `Z`-exponent, `v` the
`X`-exponent). The Weyl operator `W_a` of Definition 3 is the published GNW21 operator
`cyclicWeyl d n a` (entry `(x, y)` equal to `τ^{-Σ|u_j||v_j|} ω^{u·x}` when `x = y + v`, else `0`),
which is `τ^{-(|u₁v₁|+⋯+|uₙvₙ|)} Z^u X^v`: the exponents agree modulo the order `D` of `τ`.
The adjoint `U*` is the conjugate transpose `Uᴴ`.

The expectation `E_{h₁,…,h_k}` of Definition 8 is the average over `Fin k → DiscretePhaseSpace d n`;
`h₁ = hs 0` is applied first (innermost): `iterDeriv hs U = ∂_{h_k} ⋯ ∂_{h₁} U`. The averaged
normalized trace `pauliMoment k U` is the complex number inside the `2^k`-th root of Definition 8;
it is a nonnegative real for every matrix (iterate (3) down to (4)), and `pauliNorm k U` takes the
`2^k`-th root of its complex modulus, which is that real number.
-/

open QAlgorithms.Papers.Independent.Extend50.P30

variable {d n : ℕ}

/-- The normalized Hilbert–Schmidt inner product `⟨U, V⟩ = d^{-n} tr[U* V]` on `L(dⁿ)` (p.5). -/
noncomputable def hsInner [NeZero d] (U V : QuditOperator d n) : ℂ :=
  ((d : ℂ) ^ n)⁻¹ * (Uᴴ * V).trace

/-- The (normalized) Frobenius norm `‖U‖₂ = √⟨U, U⟩` (p.5); `⟨U, U⟩` is a nonnegative real. -/
noncomputable def frobNorm [NeZero d] (U : QuditOperator d n) : ℝ :=
  Real.sqrt (hsInner U U).re

/-- Definition 7 (p.5): the Pauli derivative `∂_h U = W_h U W_h* U*`. -/
noncomputable def pauliDeriv [NeZero d] (h : DiscretePhaseSpace d n) (U : QuditOperator d n) :
    QuditOperator d n :=
  cyclicWeyl d n h * U * (cyclicWeyl d n h)ᴴ * Uᴴ

/-- The iterated derivative `∂_{h_k} ⋯ ∂_{h₁} U`, with `h₁ = hs 0` applied first. -/
noncomputable def iterDeriv [NeZero d] :
    (k : ℕ) → (Fin k → DiscretePhaseSpace d n) → QuditOperator d n → QuditOperator d n
  | 0, _, U => U
  | k + 1, hs, U => iterDeriv k (Fin.tail hs) (pauliDeriv (hs 0) U)

/-- The averaged normalized trace `E_{h₁,…,h_k ∈ 𝔽_d^{2n}} d^{-n} tr[∂_{h_k} ⋯ ∂_{h₁} U]`
inside the root of Definition 8 (p.5). -/
noncomputable def pauliMoment [NeZero d] (k : ℕ) (U : QuditOperator d n) : ℂ :=
  ((Fintype.card (Fin k → DiscretePhaseSpace d n) : ℂ))⁻¹ *
    ∑ hs : Fin k → DiscretePhaseSpace d n, ((d : ℂ) ^ n)⁻¹ * (iterDeriv k hs U).trace

/-- Definition 8 (p.5): the `k`-th Pauli uniformity norm
`‖U‖_{P^k} = (E_{h₁,…,h_k} d^{-n} tr[∂_{h_k} ⋯ ∂_{h₁} U])^{1/2^k}`, the `2^k`-th root taken of the
modulus of the (nonnegative real) average. -/
noncomputable def pauliNorm [NeZero d] (k : ℕ) (U : QuditOperator d n) : ℝ :=
  ‖pauliMoment k U‖ ^ (((2 : ℝ) ^ k)⁻¹)

/-- Definition 15 (p.7): the Fourier coefficient `Û(a) = ⟨W_a, U⟩`. -/
noncomputable def fourierCoeff [NeZero d] (U : QuditOperator d n) (a : DiscretePhaseSpace d n) : ℂ :=
  hsInner (cyclicWeyl d n a) U

end CliffordHierTest


