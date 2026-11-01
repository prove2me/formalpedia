-- Prove2me | Definitions.Def_WildeQIT_Degradable_PureEnsemble
-- name    : WildeQIT_Degradable_PureEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:14.562899+00:00
-- url     : https://prove2.me/theorems/4cb8240f-efb4-4777-811d-0644c5ce4452
-- title:
--   Pure-state ensemble $\tau_{XA} = \sum_x p_X(x)|x\rangle\langle x|_X\otimes|\varphi_x\rangle\langle\varphi_x|_A$
-- statement:
--   A **pure-state ensemble** on a system $A$ consists of a finite alphabet, a probability distribution $p_X$ on it, and a unit vector $|\varphi_x\rangle_A$ for each letter $x$. It stands for the classical–quantum state
--
--   $$
--   \tau_{XA} \equiv \sum_x p_X(x)\,|x\rangle\langle x|_X\otimes|\varphi_x\rangle\langle\varphi_x|_A .
--   $$
--
--   Theorem 13.3.2 shows that the Holevo information of a channel can be computed by maximizing over these ensembles alone.
--
--   **Formalization Note** The alphabet is `Fin k` with `k` part of the data; the vectors live in `EuclideanSpace ℂ a` and have norm one.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.3.2, eq. (13.105), p. 404

import Definitions.Def_WildeQIT_FinDist
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.3.2, p. 404, eq. (13.105)
(`τ_{XA} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ |φˣ⟩⟨φˣ|_A`).
-/

namespace WildeQIT.Degradable

/-- **Pure-state ensemble** `τ_{XA} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ |φˣ⟩⟨φˣ|_A` (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 404, (13.105)):
a distribution on a finite alphabet together with one unit vector `|φˣ⟩` per letter.

**Formalization Note.** The alphabet is `Fin k` with `k : ℕ` part of the data, as for
`CQInput`. -/
structure PureEnsemble (a : Type) [Fintype a] where
  /-- The size of the classical alphabet `X`. -/
  k : ℕ
  /-- The distribution `p_X`. -/
  p : FinDist (Fin k)
  /-- The pure signal states `|φˣ⟩_A`. -/
  φ : Fin k → EuclideanSpace ℂ a
  /-- Each `|φˣ⟩` is a unit vector. -/
  norm_eq_one : ∀ x, ‖φ x‖ = 1

end WildeQIT.Degradable


