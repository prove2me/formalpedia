-- Prove2me | Definitions.Def_NadlerCLS_COInstance
-- name    : NadlerCLS_COInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:57:13.712066+00:00
-- url     : https://prove2.me/theorems/4b561272-93d2-456a-9a8a-75d316ab3f97
-- title:
--   Instances of Continuous-LocalOpt and $\beta$-Hölder-LocalOpt
-- statement:
--   An instance on $[0,1]^n$ consists of well-behaved arithmetic circuits $f:[0,1]^n\to[0,1]^n$ and $p:[0,1]^n\to[0,1]$ together with positive rational parameters $\delta$ and $\lambda$. Continuous-LocalOpt (Definition 2) and $\beta$-Hölder-LocalOpt (Definition 5) share this instance format.
--
--   **Formalization Note** The circuit outputs are clipped to the ranges $[0,1]^n$ and $[0,1]$ (`fC`, `pC`). The paper prints both problems on $[0,1]^3$ and uses $[0,1]^n$ in Appendix C; $n$ is a parameter. `encCO` is the binary code of an instance.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Definition 2, p.11; Definition 5, p.31

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_Circ

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- An **instance of Continuous-LocalOpt or β-Hölder-LocalOpt** on `[0, 1]ⁿ`
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485, Definition 2,
p.11, and Definition 5, p.31: "An instance consists of well-behaved arithmetic circuits
f : [0, 1]3 → [0, 1]3 and p : [0, 1]3 → [0, 1], together with positive rational parameters δ and
λ"). `f` has `n` inputs and `n` outputs, `p` has `n` inputs and one output; `lam` is λ.

**Formalization Note** The two problems share this instance type and differ only in their answers
(`coSearch`, `holderSearch`). The paper prints both on `[0, 1]³` and uses `[0, 1]ⁿ` in Appendix C
(p.34: "we assume both … are in the polynomial dimensional box [0, 1]n for generality"); `n` is a
parameter of the problem. -/
structure COInstance (n : ℕ) where
  f : Circ
  p : Circ
  δ : ℚ
  lam : ℚ

variable {n : ℕ}

/-- The input format: both circuits well-behaved of the right arities, `δ > 0`, `λ > 0`. -/
def COInstance.Valid (I : COInstance n) : Prop :=
  I.f.Valid n n ∧ I.p.Valid n 1 ∧ 0 < I.δ ∧ 0 < I.lam

/-- The update `f(x)`, clipped coordinatewise to `[0, 1]` (the range `f : [0,1]ⁿ → [0,1]ⁿ`). -/
noncomputable def COInstance.fC (I : COInstance n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => clip (I.f.eval x i)

/-- The potential `p(x)`, clipped to `[0, 1]` (the range `p : [0,1]ⁿ → [0, 1]`). -/
noncomputable def COInstance.pC (I : COInstance n) (x : Fin n → ℝ) : ℝ :=
  clip (I.p.eval x (0 : Fin 1))

/-- The binary code of an instance. -/
def encCO (I : COInstance n) : List Bool :=
  encCirc I.f ++ encCirc I.p ++ encRat I.δ ++ encRat I.lam

end NadlerCLS


