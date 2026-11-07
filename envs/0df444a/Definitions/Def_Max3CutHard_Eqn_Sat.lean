-- Prove2me | Definitions.Def_Max3CutHard_Eqn_Sat
-- name    : Max3CutHard_Eqn_Sat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:21.584322+00:00
-- url     : https://prove2.me/theorems/80248ba1-49a1-4599-8f75-5ac437ac76da
-- title:
--   An assignment satisfies an equation
-- statement:
--   An assignment $\sigma:U\cup W\to\mathbb Z_3$ **satisfies** the equation $e$ if
--
--   $$\sigma(u_e)+\sigma(w_e)+\sigma(w'_e)=t_e.$$
--
--   **Formalization Note** The assignment is given as the pair of its restrictions to $U$ and to $W$; satisfaction is decidable.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_Eqn

namespace Max3CutHard

/-- **An assignment satisfies an equation.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations, p.4: an
assignment `σ : U ∪ W → ℤ₃` satisfies `e` iff `σ(u_e) + σ(w_e) + σ(w′_e) = t_e`.

**Formalization Note.** The assignment is a pair `(σU, σW)` of maps `U → ℤ₃`, `W → ℤ₃`. -/
def Eqn.Sat {U W : Type} (σU : U → ZMod 3) (σW : W → ZMod 3) (e : Eqn U W) : Prop :=
  σU e.u + σW e.w + σW e.w' = e.t

instance Eqn.instDecidableSat {U W : Type} (σU : U → ZMod 3) (σW : W → ZMod 3) (e : Eqn U W) :
    Decidable (e.Sat σU σW) := by
  unfold Eqn.Sat; infer_instance

end Max3CutHard


