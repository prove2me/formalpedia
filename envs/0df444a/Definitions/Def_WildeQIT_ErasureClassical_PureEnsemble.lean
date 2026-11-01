-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_PureEnsemble
-- name    : WildeQIT_ErasureClassical_PureEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:54.661791+00:00
-- url     : https://prove2.me/theorems/4e1b9747-0425-45ec-8cdd-3f917de0dce3
-- title:
--   Pure-state input ensemble $\{p_X(x),|\varphi^x\rangle\}$
-- statement:
--   A **pure-state input ensemble** for a channel with input system $A'$ is a probability distribution $p_X$ on a finite alphabet together with a unit vector $|\varphi^x\rangle\in\mathcal H_{A'}$ for every letter $x$. It corresponds to the classical–quantum input
--
--   $$
--   \tau_{XA'}\equiv\sum_x p_X(x)\,|x\rangle\langle x|_X\otimes|\varphi^x\rangle\langle\varphi^x|_{A'} .
--   $$
--
--   The Holevo information of a channel (20.8) is a maximum over such inputs.
--
--   **Formalization Note** The alphabet is `Fin k` with $k$ part of the data, so alphabets of every finite size are allowed. A unit vector satisfies $\langle\varphi|\varphi\rangle=1$, and its density operator is $|\varphi\rangle\langle\varphi|$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.1, (20.9), p. 561; Theorem 13.3.2, (13.105), p. 404

import Definitions.Def_WildeQIT_FinDist
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.1, p. 561, eq. (20.9)
(classical–quantum inputs `∑ₓ p_X(x)|x⟩⟨x|_X ⊗ ψˣ_{A′}` with pure `ψˣ`), and Theorem 13.3.2,
p. 404, eq. (13.105).
-/

namespace WildeQIT.ErasureClassical

/-- **Pure-state input ensemble** `τ_{XA′} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ |φˣ⟩⟨φˣ|_{A′}` (Wilde, *From
Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (20.9), p. 561, and (13.105), p. 404):
a probability distribution on a finite alphabet together with one unit vector `|φˣ⟩` of the
channel input per letter.

**Formalization Note.** The alphabet is `Fin k` with `k : ℕ` part of the data: the book does
not bound the alphabet size, every finite alphabet is in bijection with some `Fin k`, and the
Holevo information is invariant under relabeling. A vector `φ : a → ℂ` is a unit vector when
`⟨φ|φ⟩ = ∑ᵢ conj(φᵢ) φᵢ = 1`; its density operator is `|φ⟩⟨φ| = vecMulVec φ (star φ)`. -/
structure PureEnsemble (a : Type) [Fintype a] where
  /-- The size of the classical alphabet `X`. -/
  k : ℕ
  /-- The distribution `p_X`. -/
  p : FinDist (Fin k)
  /-- The pure signal states `|φˣ⟩_{A′}`. -/
  φ : Fin k → a → ℂ
  /-- Each `|φˣ⟩` is a unit vector. -/
  norm_one : ∀ x, star (φ x) ⬝ᵥ φ x = 1

/-- The density operator `|φˣ⟩⟨φˣ|` of the `x`-th signal state of a pure ensemble. -/
def PureEnsemble.state {a : Type} [Fintype a] (e : PureEnsemble a) (x : Fin e.k) :
    Matrix a a ℂ :=
  Matrix.vecMulVec (e.φ x) (star (e.φ x))

end WildeQIT.ErasureClassical


