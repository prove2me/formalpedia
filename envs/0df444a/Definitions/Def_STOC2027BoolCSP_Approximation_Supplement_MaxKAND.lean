-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_MaxKAND
-- name    : STOC2027BoolCSP_Approximation_Supplement_MaxKAND
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:32:44.147954+00:00
-- url     : https://prove2.me/theorems/76b32fbf-ccc0-40e0-ac7c-4371291e452d
-- title:
--   Unweighted Max-$k$-AND gap problem and $\mathrm P\ne\mathrm{NP}$
-- statement:
--   A **Max-$k$-AND instance** is a list of $M$ clauses, each a signed conjunction $x_i=\sigma_{C,i}$ ($i\in C$) on exactly $k$ distinct Boolean variables. It is **unweighted** when every clause has weight one; repeated clauses are allowed. Following Section 10, its **value** is a fraction of the total constraint weight:
--   $$\mathrm{val}(I)=\frac{\mathrm{OPT}(I)}{M}=\max_x\frac{\#\{C:\ x\ \text{satisfies}\ C\}}{M}.$$
--
--   For thresholds $s$, the YES instances of the gap problem are the unweighted instances with $M\ge1$ and $\mathrm{val}\ge s$, and the NO instances are the unweighted instances with $M\ge 1$ and $\mathrm{val}\le s$.
--
--   $\mathrm P\ne\mathrm{NP}$ means that some NP language over a finite nonempty alphabet is not in P, in Cook's Turing machine model.
--
--   These objects state Theorem 1.4.
--
--   **Formalization Note** Instances are the live mission's `ConjInstance k` (injective variable maps, so exactly $k$ distinct variables per clause) with every weight equal to $1$. `P` and `NP` are those of the published `CookPvsNP_defs`.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 2, 3, 21 (PDF 5, 6, 24), Theorem 1.4, §1.1 and Section 10

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_ConjOpt

namespace STOC2027BoolCSP.Approximation.Supplement

open STOC2027BoolCSP.Approximation

/-- An unweighted Max-`k`-AND instance: every clause (a signed conjunction on exactly `k`
distinct variables) has weight one; repeated clauses are allowed. -/
def IsUnweighted {k : ℕ} (C : ConjInstance k) : Prop := ∀ c, C.w c = 1

/-- The value of a Max-`k`-AND instance as a fraction of the total constraint weight (Section 10):
for an unweighted instance, the largest number of simultaneously satisfied clauses divided by the
number `M` of clauses. -/
noncomputable def andValue {k : ℕ} (C : ConjInstance k) : ℝ := conjOpt C / C.M

/-- YES instances of the gap problem: unweighted, at least one clause, value at least `s`. -/
def AndYes (k : ℕ) (s : ℝ) (C : ConjInstance k) : Prop :=
  IsUnweighted C ∧ 0 < C.M ∧ s ≤ andValue C

/-- NO instances of the gap problem: unweighted, at least one clause, value at most `s`. -/
def AndNo (k : ℕ) (s : ℝ) (C : ConjInstance k) : Prop :=
  IsUnweighted C ∧ 0 < C.M ∧ andValue C ≤ s

/-- `P ≠ NP`: some `NP` language over a finite nonempty alphabet is not in `P` (Cook's model). -/
def PneNP : Prop :=
  ∃ (Sym : Type) (_ : Fintype Sym) (_ : Nonempty Sym), ¬ (CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym)

end STOC2027BoolCSP.Approximation.Supplement


