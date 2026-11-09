-- Prove2me | Definitions.Def_DepthOneQExp_IsQuantumExpanderGap
-- name    : DepthOneQExp_IsQuantumExpanderGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:19.704531+00:00
-- url     : https://prove2.me/theorems/eea698f3-17f3-48c3-bf03-37a60d5445e8
-- title:
--   Quantum expander with spectral gap at least $\Delta$
-- statement:
--   A family of $n$-qubit unitaries $U_1,\dots,U_m$ **forms a quantum expander with spectral gap $\Delta$** if the second largest singular value of
--   $$
--   M = \frac1m\sum_{i=1}^m U_i\otimes \overline{U_i}
--   $$
--   equals $1-\Delta$ (Definition 2.1); "a spectral gap of at least $\Delta$" (Theorems 2.2, 2.13) means that this singular value is at most $1-\Delta$. The predicate states
--   $$
--   \Big\| \frac1m\sum_{i=1}^m U_i\otimes \overline{U_i} - \frac{|a_1\rangle\langle a_1|}{2^n}\Big\| \le 1-\Delta ,
--   $$
--   in the operator norm, with $|a_1\rangle=\sum_x|x\rangle|x\rangle$.
--
--   For unitary $U_i$, both $M$ and $M^\dagger$ fix $|a_1\rangle$, so $\mathbb C a_1$ and its orthogonal complement reduce $M$; $M$ has singular value $1$ on $\mathbb C a_1$, and its second singular value is the norm of $M$ on $a_1^\perp$, which is the left-hand side above. Since $\mathbb E_{U\sim\mathrm{Haar}}U\otimes\overline U=|a_1\rangle\langle a_1|/2^n$ (Eq. (2.41)), this is also the form of Definition 1.1 and of Eq. (2.46).
--
--   **Formalization Note** $\overline{U_i}$ is the entrywise complex conjugate; the norm is the $L^2$ operator norm; the family is indexed (repetitions count). Unitarity is not part of the predicate and is stated separately where the paper requires it. For $\Delta\le 0$ the predicate is the plain inequality.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Definition 2.1, p.6 (with Eqs. (2.40)–(2.41), p.13)

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_maxEnt

namespace DepthOneQExp

open scoped Matrix.Norms.L2Operator Kronecker

/-- **Quantum expander with spectral gap at least `Δ`** (Anshu–Balasubramanian–Haferkamp–Harrow–Tan,
*Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Definition 2.1, p.6): a family of `n`-qubit unitaries `U_1, …, U_m` forms a
quantum expander with spectral gap `Δ` if the second largest singular value of
`M = (1/m) Σ_i U_i ⊗ Ū_i` equals `1 − Δ`; "a spectral gap of at least `Δ`" (Theorems 2.2, 2.13)
means that this singular value is at most `1 − Δ`. Here:
`‖(1/m) Σ_i U_i ⊗ Ū_i − |a_1⟩⟨a_1| / 2ⁿ‖ ≤ 1 − Δ`, in the operator norm, with
`|a_1⟩ = Σ_x |x⟩|x⟩` (`maxEnt`).

**Formalization Note** For unitary `U_i`, `(U_i ⊗ Ū_i)|a_1⟩ = |a_1⟩` and the same for the adjoint,
so `ℂ a_1` and its orthogonal complement reduce `M`; `M` has singular value `1` on `ℂ a_1` and the
second singular value is `‖M|_{a_1^⊥}‖ = ‖M − |a_1⟩⟨a_1|/2ⁿ‖`. Since
`E_{U∼Haar} U ⊗ Ū = |a_1⟩⟨a_1|/2ⁿ` (Eq. (2.41), p.13), this is also the form of Definition 1.1 and
of Eq. (2.46). The norm is the `L²` operator norm (`Matrix.Norms.L2Operator`), `Ū_i` is the entrywise
complex conjugate, and the family is indexed (repetitions count). Unitarity of the `U_i` is not part
of the predicate; it is stated separately where the paper requires it. -/
def IsQuantumExpanderGap {n m : ℕ}
    (V : Fin m → Matrix (MITMSynthesis.Q n) (MITMSynthesis.Q n) ℂ) (Δ : ℝ) : Prop :=
  ‖(1 / (m : ℂ)) • ∑ i, (V i ⊗ₖ (V i).map star) -
      (1 / (2 ^ n : ℂ)) • Matrix.vecMulVec (maxEnt n) (star (maxEnt n))‖ ≤ 1 - Δ

end DepthOneQExp


