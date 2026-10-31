-- Prove2me | Definitions.Def_KallMayerSLP_KKT_RC1
-- name    : KallMayerSLP_KKT_RC1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:31.86999+00:00
-- url     : https://prove2.me/theorems/704b1c73-2c6f-4218-bf6b-8118036baf85
-- title:
--   Slater condition RC 1
-- statement:
--   The program (3.1) satisfies the **Slater condition RC 1** if there is a feasible point $\tilde x$ at which every constraint holds strictly:
--   $$
--   \exists\,\tilde x\in\mathcal B:\qquad g_i(\tilde x)<0\quad\forall i .
--   $$
--
--   It is the hypothesis of Proposition 3.4 (KKT conditions); for convex problems it implies RC 0.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3, p.63 (PDF 74), RC 1

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_feasibleSet

namespace KallMayerSLP.KKT

/-- **Slater condition `RC 1`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3, p.63 (PDF 74):
"`RC 1` For (3.1) there exists a feasible point `x̃` such that `gᵢ(x̃) < 0 ∀i`."

**Formalization Note.** A point with `gᵢ(x̃) < 0` for all `i` is automatically feasible; the
feasibility clause is kept to mirror the text. -/
def RC1 {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ x ∈ feasibleSet g, ∀ i, g i x < 0

end KallMayerSLP.KKT


