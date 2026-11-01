-- Prove2me | Definitions.Def_WildeQIT_Degradable_CQInput
-- name    : WildeQIT_Degradable_CQInput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:16.775813+00:00
-- url     : https://prove2.me/theorems/edc82d86-c91a-4700-80e6-f5386731724c
-- title:
--   Classical–quantum input ensemble $\rho_{XA'} = \sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_{A'}$
-- statement:
--   A **classical–quantum input** to a channel with input system $A'$ is an ensemble $\{p_X(x),\rho^x_{A'}\}$: a finite alphabet $\mathcal X$, a probability distribution $p_X$ on it, and one density operator $\rho^x_{A'}$ per letter. It stands for the classical–quantum state
--
--   $$
--   \rho_{XA'} \equiv \sum_x p_X(x)\,|x\rangle\langle x|_X\otimes\rho^x_{A'} .
--   $$
--
--   These are the inputs over which the Holevo information $\chi(\mathcal N)$ (Definition 13.3.1) and the private information $P(\mathcal N)$ (Definition 13.6.1) are maximized.
--
--   **Formalization Note** The alphabet is `Fin k`, with its size `k` part of the data, so that the size is unbounded; every finite alphabet is in bijection with some `Fin k`. The distribution is the published `WildeQIT.FinDist` and each signal state satisfies the published `WildeQIT.IsDensityOperator`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eq. (13.82), p. 400, and eq. (13.178), p. 416

import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.3, p. 400, eq. (13.82), and §13.6, p. 416, eq. (13.178)
(the input ensembles `ρ_{XA′} = ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ ρˣ_{A′}`).
-/

namespace WildeQIT.Degradable

/-- **Classical–quantum input** `ρ_{XA′} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ ρˣ_{A′}` (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (13.82),
p. 400, and (13.178), p. 416): an ensemble `{p_X(x), ρˣ}` of density operators on the channel
input, indexed by a finite classical alphabet `X`.

**Formalization Note.** The book does not bound the alphabet size; the alphabet is `Fin k` with
`k : ℕ` part of the data (every finite alphabet is in bijection with some `Fin k`, and the
quantities of this chapter are invariant under relabeling). -/
structure CQInput (a : Type) [Fintype a] where
  /-- The size of the classical alphabet `X`. -/
  k : ℕ
  /-- The distribution `p_X`. -/
  p : FinDist (Fin k)
  /-- The signal states `ρˣ_{A′}`. -/
  ρ : Fin k → Matrix a a ℂ
  /-- Each signal state is a density operator. -/
  isDensity : ∀ x, IsDensityOperator (ρ x)

end WildeQIT.Degradable


