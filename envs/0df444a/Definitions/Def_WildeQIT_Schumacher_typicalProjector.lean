-- Prove2me | Definitions.Def_WildeQIT_Schumacher_typicalProjector
-- name    : WildeQIT_Schumacher_typicalProjector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:58.993109+00:00
-- url     : https://prove2.me/theorems/565d0697-11e3-4bcd-8ec3-37bf26044f5d
-- title:
--   Typical projector $\Pi^\delta_{A^n}$ of a density operator
-- statement:
--   Let $\rho = \sum_x p_X(x)|x\rangle\langle x|$ be a spectral decomposition, with eigenvectors $|x\rangle = Ue_x$ and eigenvalue distribution $p_X$. For a sequence $x^n$ put $|x^n\rangle = |x_1\rangle\otimes\cdots\otimes|x_n\rangle$ (eq. (15.9)). The $\delta$-typical subspace $T^\delta_{A^n}$ is the span of the $|x^n\rangle$ with $x^n$ in the $\delta$-typical set $T^{X^n}_\delta$ of $p_X$ (Definition 15.1.2), and the typical projector is
--
--   $$
--   \Pi^\delta_{A^n} = \sum_{x^n \in T^{X^n}_\delta} |x^n\rangle\langle x^n|_{A^n}.
--   $$
--
--   The typical subspace measurement $\{\Pi^\delta_{A^n}, I - \Pi^\delta_{A^n}\}$ asks whether $n$ copies of the source are typical; it is the first step of Schumacher compression.
--
--   **Formalization Note** $T^{X^n}_\delta$ is the published weak typical set `WildeQIT.typicalSet` (sequences of positive probability whose sample entropy is within $\delta$ of $H(X)$, base 2), Definition 14.2.3. The book allows weak or strong typicality; this definition uses the weak one. The projector is a function of the decomposition $(U, p_X)$; theorems assume `IsSpectralDecomposition ρ U p`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definitions 15.1.2–15.1.3, eqs. (15.9)–(15.11), p. 464

import Definitions.Def_WildeQIT_typicalSet
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definitions 15.1.2
(Typical Subspace) and 15.1.3 (Typical Projector), eqs. (15.9)–(15.11), pp. 463–465.
-/

open Matrix

namespace WildeQIT.Schumacher

/-- **Typical projector** `Π^δ_{Aⁿ}` (Wilde, arXiv:1106.1445v8, Definition 15.1.3, eq. (15.11),
p. 464). Given a spectral decomposition `ρ = ∑ₓ p_X(x) |x⟩⟨x|` (eq. (15.2)) whose eigenvectors
are the columns of `U` (`|x⟩` has coordinates `U_{y,x}`) and whose eigenvalue distribution is
`p`, the projector onto the `δ`-typical subspace `T^δ_{Aⁿ} = span{|xⁿ⟩ : xⁿ ∈ T^{Xⁿ}_δ}`
(Definition 15.1.2, eq. (15.10)) is
`Π^δ_{Aⁿ} = ∑_{xⁿ ∈ T^{Xⁿ}_δ} |xⁿ⟩⟨xⁿ|`, where `|xⁿ⟩ = |x₁⟩ ⊗ ⋯ ⊗ |xₙ⟩` (eq. (15.9)) has
coordinates `yⁿ ↦ ∏ᵢ U_{yᵢ,xᵢ}`.

**Formalization Note.** The typical set `T^{Xⁿ}_δ` is the published weak typical set
`WildeQIT.typicalSet p n δ` (Definition 14.2.3, sequences of positive probability whose sample
entropy is within `δ` of `H(X)`, logarithms base 2); the book allows weak or strong typicality
(p. 464) and we take the weak notion. The projector depends on the decomposition `(U, p)`,
which the book leaves implicit ("with respect to a density operator ρ"); `U` is intended to be
unitary with `ρ = U diag(p) U†` (`IsSpectralDecomposition`), and statements assume this. -/
noncomputable def typicalProjector {a : Type} [Fintype a] (U : Matrix a a ℂ) (p : FinDist a)
    (n : ℕ) (δ : ℝ) : Matrix (Fin n → a) (Fin n → a) ℂ :=
  ∑ x ∈ typicalSet p n δ,
    Matrix.vecMulVec (fun y : Fin n → a => ∏ i, U (y i) (x i))
      (star fun y : Fin n → a => ∏ i, U (y i) (x i))

end WildeQIT.Schumacher


