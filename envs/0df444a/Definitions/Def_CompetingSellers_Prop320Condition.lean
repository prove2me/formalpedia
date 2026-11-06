-- Prove2me | Definitions.Def_CompetingSellers_Prop320Condition
-- name    : CompetingSellers_Prop320Condition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:23.123207+00:00
-- url     : https://prove2.me/theorems/75dd0b79-20f1-482c-9fe9-3dec2a68cb1c
-- title:
--   The characterizing condition of Proposition 3.20 (and the optimal equalizers of Definition 3.19)
-- statement:
--   The **optimal equalizers** (Definition 3.19): for $a<b$, $A^*_{LB}=A^{LB}_{R^*}$ with $R^*\in(\Delta,b]$ maximizing Alice's revenue (against Bob's selected best response) within the Large-Bob family; for $a\ge b$, $A^*_{LA}=A^{LA}_{R^*}$ with $R^*\in[0,b]$ maximizing it within the Large-Alice family.
--
--   A mechanism $A$ satisfies the **condition of Proposition 3.20** (for a constant $C$) if:
--
--   1. when $a<b$: its allocation rule is monotone, $\mathrm{util}_A=\mathrm{util}_{A^*_{LB}}$ on $[s^*,a]$, and $z^+_A(v)\in\Big[\frac{v-R^*+\Delta}{v+\alpha^*(v-\mathrm{util}_A(v))},\frac{\mathrm{util}_{A^*_{LB}}(a)}{b}\Big]$ for $v\in(0,s^*]$, where $u^*=\mathrm{util}_{A^*_{LB}}(a)/b$, $\alpha^*=\frac{\Delta}{a-bu^*}$, $s^*=(R^*-\Delta)\frac{a-\Delta u^*}{a-(2b-a)u^*}$;
--   2. when $b\le a<Cb$: its allocation rule is monotone, $\mathrm{util}_A=\mathrm{util}_{A^*_{LA}}$ on $\{\Delta\}\cup[s^*,a]$, and $z^+_A(v)\in\Big[1-\frac{R^*}{v-\Delta},\frac{\mathrm{util}_{A^*_{LA}}(a)}{b}\Big]$ for $v\in(\Delta,s^*]$, where $s^*=\Delta+\frac{bR^*}{b-\mathrm{util}_{A^*_{LA}}(a)}$;
--   3. when $Cb\le a$: $A$ is a posted price of $a-b$.
--
--   **Formalization Note** The optimal equalizer is given with its parameter $R^*$ (Bob's best-response revenue against it, by Lemmas 3.13 and 3.18). Item 3 is up to essential equivalence: $A$ is essentially equivalent to a mechanism realizing $\mathrm{FP}(a-b)$.
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Definition 3.19 and Proposition 3.20, p.30 (PDF 33)

import Mathlib
import Definitions.Def_CompetingSellers_IsStackelbergEq
import Definitions.Def_CompetingSellers_EssEquiv
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_IsLargeAliceEq
import Definitions.Def_CompetingSellers_IsLargeBobEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

variable {S : Type} [MeasurableSpace S] {null : S}

/-- **Optimal Large-Bob equalizer** (Definition 3.19 item 1, p.30): `A = A^{LB}_R` with
`R ∈ (Δ, b]` maximizing Alice's revenue (against Bob's selected best response) within the
Large-Bob-equalizer family. -/
def IsOptimalLargeBobEq (a b R u : ℝ) (A : Mech S null) : Prop :=
  IsLargeBobEq a b R u A ∧ (∃ B : Mech S null, IsBobChoice a b A B) ∧
    ∀ (R' u' : ℝ) (A' B' B : Mech S null), IsLargeBobEq a b R' u' A' →
      IsBobChoice a b A' B' → IsBobChoice a b A B →
        revenue a b A' B' Seller.alice ≤ revenue a b A B Seller.alice

/-- **Optimal Large-Alice equalizer** (Definition 3.19 item 2, p.30): `A = A^{LA}_R` with
`R ∈ [0, b]` maximizing Alice's revenue within the Large-Alice-equalizer family. -/
def IsOptimalLargeAliceEq (a b R s : ℝ) (A : Mech S null) : Prop :=
  IsLargeAliceEq a b R s A ∧ (∃ B : Mech S null, IsBobChoice a b A B) ∧
    ∀ (R' s' : ℝ) (A' B' B : Mech S null), IsLargeAliceEq a b R' s' A' →
      IsBobChoice a b A' B' → IsBobChoice a b A B →
        revenue a b A' B' Seller.alice ≤ revenue a b A B Seller.alice

/-- **The condition of Proposition 3.20** (p.30).
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Proposition 3.20, p.30 (PDF 33): "A mechanism `A` is optimal for
Alice if and only if the following condition holds, depending on the relation between `a` and
`b`:
1. When `0 < a < b`, its allocation rule is monotone and satisfies:
`util_A(v) = util_{A*_LB}(v)` ∀ `v ∈ [s*, a]`,
`z⁺_A(v) ∈ [(v − R*_LB + ∆)/(v + α*(v − util_A(v))), util_{A*_LB}(a)/b]` ∀ `v ∈ (0, s*]`,
where `A*_LB` is the optimal Large-Bob-Equalizer of Definition 3.19, `R*_LB` is the revenue of Bob
when best-responding to it, `u* = util_{A*_LB}(a)/b`, `α* = ∆/(a − b · u*)`, and
`s* = (R*_LB − ∆) · (a − ∆ · u*)/(a − (2b − a) · u*)`.
2. When `b ≤ a < C · b`, where `C ∈ (3.146, 3.147)` satisfies `C − ln C = 2`, its allocation rule
is monotone and satisfies: `util_A(v) = util_{A*_LA}(v)` ∀ `v ∈ {∆} ∪ [s*, a]`,
`z⁺_A(v) ∈ [1 − R*_LA/(v − ∆), util_{A*_LA}(a)/b]` ∀ `v ∈ (∆, s*]`, where `A*_LA` is the optimal
Large-Alice-Equalizer of Definition 3.19, `R*_LA` is the revenue of Bob when best-responding to
it, and `s* = ∆ + b·R*_LA/(b − util_{A*_LA}(a))`.
3. When `C · b ≤ a`, `A` is a posted price of `a − b`."

**Formalization Note.** `C` is a parameter (the theorems assume `C − ln C = 2` and
`C ∈ (3.146, 3.147)`). In items 1–2 the optimal equalizer is given by its parameter `R*` (which is
Bob's best-response revenue against it, Lemmas 3.13, 3.18); "its allocation rule is monotone" is
monotonicity of `z⁺_A` on `[0, ∞)`. Item 3 is up to essential equivalence (footnote 3, p.3):
`A` is essentially equivalent to a mechanism realizing `FP(a − b)`. -/
def Prop320Condition (a b C : ℝ) (A : Mech S null) : Prop :=
  (a < b → ∃ (R u : ℝ) (As : Mech S null), IsOptimalLargeBobEq a b R u As ∧
      MonotoneOn (mZPlus a A) (Set.Ici 0) ∧
      (∀ v ∈ Set.Icc ((R - |a - b|) * (a - |a - b| * (mUtil a As a / b)) /
            (a - (2 * b - a) * (mUtil a As a / b))) a, mUtil a A v = mUtil a As v) ∧
      ∀ v ∈ Set.Ioc 0 ((R - |a - b|) * (a - |a - b| * (mUtil a As a / b)) /
            (a - (2 * b - a) * (mUtil a As a / b))),
        mZPlus a A v ∈ Set.Icc
          ((v - R + |a - b|) /
            (v + |a - b| / (a - b * (mUtil a As a / b)) * (v - mUtil a A v)))
          (mUtil a As a / b)) ∧
  (b ≤ a → a < C * b → ∃ (R s : ℝ) (As : Mech S null), IsOptimalLargeAliceEq a b R s As ∧
      MonotoneOn (mZPlus a A) (Set.Ici 0) ∧
      (∀ v, (v = |a - b| ∨ v ∈ Set.Icc (|a - b| + b * R / (b - mUtil a As a)) a) →
        mUtil a A v = mUtil a As v) ∧
      ∀ v ∈ Set.Ioc |a - b| (|a - b| + b * R / (b - mUtil a As a)),
        mZPlus a A v ∈ Set.Icc (1 - R / (v - |a - b|)) (mUtil a As a / b)) ∧
  (C * b ≤ a → ∃ P : Mech S null, IsPricingMech (fp (a - b)) P ∧ EssEquiv a b Seller.alice A P)

end CompetingSellers


