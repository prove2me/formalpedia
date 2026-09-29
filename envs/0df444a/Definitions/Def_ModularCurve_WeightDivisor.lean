-- Prove2me | Definitions.Def_ModularCurve_WeightDivisor
-- name    : ModularCurve_WeightDivisor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/1612171e-c4d9-5655-8a57-af15b927dd6f
-- title:
--   Weight floor divisor on the modular function field
-- statement:
--   Fix a field $K$ and an integer $N\ge 1$, and let $F=$ [`ModularCurve.modularFunctionFieldC K N`](../def/ModularCurve_JqCoeff.html#L61) be the intermediate field of $K$-Laurent series generated over $K$ by the $j$-series $\bar\jmath=$ `jqModC K` $=q^{-1}(1+\cdots)$ (the integral $j$-expansion with coefficients pushed into $K$) and by its $N$-fold $q$-rescaling `jqNModC K N`. Places of $F/K$ are taken in the sense of the project's [`AlgebraicCurve.Place`](../def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring $A\subsetneq F$ containing $\operatorname{im}(K\to F)$ and a principal ideal ring, so a discrete valuation ring, with $\operatorname{ord}_w$ the associated normalised integer valuation; divisors are finitely supported $\mathbb{Z}$-valued functions on places.
--
--   For $m\in\mathbb{N}$ and a place $w$, `weightFloor K N m w` is the integer given by a three-branch expression: the quotient $(2m\cdot\operatorname{ord}_w\bar\jmath)/3$ when $\operatorname{ord}_w\bar\jmath>0$ and $0$ otherwise; plus the quotient $(m\cdot\operatorname{ord}_w(\bar\jmath-1728))/2$ when $\operatorname{ord}_w(\bar\jmath-1728)>0$ and $0$ otherwise; plus $m\cdot\operatorname{ord}_w\bar\jmath$ when $\operatorname{ord}_w\bar\jmath<0$ and $0$ otherwise. Here $1728$ means the image of $1728\in K$ in $F$, and in each guarded branch the numerator is non-negative, so the quotient is the integer floor.
--
--   `weightDivisor K N m` is then defined by cases: if some finitely supported divisor $D$ on the places of $F/K$ satisfies $D(w)=\,$`weightFloor K N m w` for every $w$, it is such a divisor; otherwise it is the zero divisor. The accompanying lemma `weightDivisor_apply` records that, under exactly that existence hypothesis, `weightDivisor K N m` takes the value `weightFloor K N m w` at every place $w$; without the hypothesis nothing is claimed, since the floor expression need not have finite support.
--
--   **Relation to Mathlib.** Mathlib has no notion of places or divisors of a function field in this shape; `Place`, `Divisor` and the Picard groups used here are the project's own, and the weight floor divisor is specific to this development.
--
--   **Where it is used.** The divisor is the algebraic shadow of the weight-$2m$ structure: its Riemann–Roch space plays the role of the space of holomorphic weight-$2m$ modular functions of level $N$ (zeros of prescribed order at the elliptic points above $j=0$ and $j=1728$, poles of order at most $m$ times the width at the cusps), and is used in the dimension counts for such spaces on the modular curve of level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeightDivisor.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def weightFloor (m : ℕ) (w : Place K ↥(modularFunctionFieldC K N)) : ℤ :=
  (if 0 < w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N))
      then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N))) / 3 else 0)
  + (if 0 < w.ord ((⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) - algebraMap K _ 1728)
      then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) - algebraMap K _ 1728)) / 2
      else 0)
  + (if w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) < 0
      then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem K N⟩ : ↥(modularFunctionFieldC K N)) else 0)

open scoped Classical in

def weightDivisor (m : ℕ) : Divisor K ↥(modularFunctionFieldC K N) :=
  if h : ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w, D w = weightFloor K N m w then h.choose else 0

theorem weightDivisor_apply (m : ℕ)
    (h : ∃ D : Divisor K ↥(modularFunctionFieldC K N), ∀ w, D w = weightFloor K N m w)
    (w : Place K ↥(modularFunctionFieldC K N)) :
    weightDivisor K N m w = weightFloor K N m w := by
  classical
  rw [weightDivisor, dif_pos h]
  exact h.choose_spec w

end ModularCurve

end


