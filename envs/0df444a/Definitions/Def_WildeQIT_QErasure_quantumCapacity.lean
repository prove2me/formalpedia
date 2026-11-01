-- Prove2me | Definitions.Def_WildeQIT_QErasure_quantumCapacity
-- name    : WildeQIT_QErasure_quantumCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:39:39.139784+00:00
-- url     : https://prove2.me/theorems/5884f968-c69c-4b2e-8048-d3e1058c19cb
-- title:
--   Quantum capacity $C_Q(\mathcal N)$
-- statement:
--   The **quantum capacity** $C_Q(\mathcal N)$ of a quantum channel is the supremum of all achievable rates of quantum communication over $\mathcal N$:
--
--   $$
--   C_Q(\mathcal N)=\sup\{Q\in\mathbb R : Q\text{ is achievable for }\mathcal N\}.
--   $$
--
--   **Formalization Note** The supremum is taken in the extended reals `EReal`, so it is the genuine least upper bound in every case ($\bot$ for an empty set, $\top$ for an unbounded one), never a junk real value.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.1, p. 659

import Definitions.Def_WildeQIT_QErasure_IsAchievableRate
import Mathlib.Data.EReal.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.1, p. 659
(the quantum capacity `C_Q(N)`).
-/

namespace WildeQIT.QErasure

/-- **Quantum capacity `C_Q(N)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, §24.1, p. 659): "The quantum capacity `C_Q(N)` is defined as the supremum of all
achievable rates for `N`."

**Formalization Note.** The supremum is taken in the extended reals `EReal`, so that it is the true
least upper bound in every case: an empty set of achievable rates gives `⊥` and an unbounded one `⊤`,
never a junk real value. -/
noncomputable def quantumCapacity {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : EReal :=
  sSup ((fun Q : ℝ => (Q : EReal)) '' {Q | IsAchievableRate N Q})

end WildeQIT.QErasure


