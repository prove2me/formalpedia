-- Prove2me | Definitions.Def_TaoCake_Impossibility_Model
-- name    : TaoCake_Impossibility_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:05:56.891518+00:00
-- url     : https://prove2.me/theorems/84a4d9a7-272e-4f38-ad10-c7babcd9d3c5
-- title:
--   §2 — cake [0,1], piecewise-constant hungry densities, utility, two-agent mechanisms, allocations, truthfulness and proportionality
-- statement:
--   The model of Section 2 (pp. 3–4) for two agents.
--
--   1. **Cake** $C = [0,1]$.
--   2. **Piecewise-constant density** (p. 3): $f : \mathbb R \to \mathbb R$ such that $[0,1]$ is partitioned into finitely many intervals $I_1, \dots, I_n$ (any kind: open, closed, half-open, singleton or empty; arbitrary real endpoints; $n$ unbounded) with $f$ constant on each $I_k$.
--   3. **Hungry** (p. 3): $f(x) > 0$ for every $x \in [0,1]$, endpoints included. A density is **admissible** if it is piecewise-constant and hungry. No normalization and no rationality is imposed.
--   4. **Utility** (p. 3): $v_f(X) = \int_{X \cap [0,1]} f(x)\,dx$ (Lebesgue integral).
--   5. **Profiles and mechanisms** (p. 4): a profile is $F = (f_1, f_2)$; a deterministic mechanism maps every profile to two sets, $M(F) = (M_1(F), M_2(F))$.
--   6. **Allocation** (p. 3): $(A_1, A_2)$ with $A_1, A_2 \subseteq [0,1]$, $A_1 \cap A_2 = \emptyset$ (the published predicate `EnvyFreeCake104.Divide.IsPartialAlloc`), each Lebesgue measurable. Entireness $A_1 \cup A_2 = [0,1]$ is not required. $M$ is **feasible** if $M(F)$ is an allocation at every admissible profile.
--   7. **Proportional** (pp. 3–4): for every admissible $F$ and $i \in \{1,2\}$, $v_{f_i}(M_i(F)) \ge \tfrac12 v_{f_i}([0,1])$.
--   8. **Truthful** (p. 4): for every admissible $F$, agent $i$ and admissible $g$,
--
--   $$v_{f_i}(M_i(F)) \ge v_{f_i}\big(M_i(F[i \leftarrow g])\big),$$
--
--   where $F[i \leftarrow g]$ replaces agent $i$'s report by $g$ and both sides use the true density $f_i$.
--
--   **Formalization Note** Agents are `Fin 2`; Lean agent `0` is the paper's agent 1. A `Mechanism` is a raw function on all pairs of real functions; feasibility, truthfulness and proportionality constrain it only at admissible profiles (and over admissible misreports), so it is the paper's mechanism extended arbitrarily off its domain. Allowing every Lebesgue-measurable output set (rather than sets with a Riemann utility) enlarges the class of mechanisms; the utility integrates over $X \cap [0,1]$, matching the published `Valuation.value` convention. A separate unbundled integral is used because the reports built in Section 3 need not be integrable `Valuation`s. Utility is total: it is zero on a nonintegrable restricted integrand. Admissible densities are bounded finite interval step functions, hence integrable on the cake and its measurable subsets; this default never substitutes for an undefined utility in the behavioral axioms. Raw constructed reports need not have this property. The raw mechanism may depend on off-cake values, although utility cannot; equivalence for the goal is equivalence of existence, obtained by restricting to reports with a fixed off-cake extension.
-- source:
--   Biaoshuai Tao, On Existence of Truthful Fair Cake Cutting Mechanisms, arXiv:2104.07387v1, pp. 3–4 (PDF 3–4), Section 2

import Mathlib
import Definitions.Def_EnvyFreeCake104_Divide_Model

open MeasureTheory

namespace TaoCake.Impossibility

/-! # The two-agent cake-cutting model of Tao, *On Existence of Truthful Fair Cake Cutting
Mechanisms* (arXiv:2104.07387v1, §2, pp. 3–4)

Agents are indexed by `Fin 2`: Lean agent `0` is the paper's agent 1 and Lean agent `1` is the
paper's agent 2. -/

/-- The cake `C = [0, 1]` (p. 3). -/
def cake : Set ℝ := Set.Icc 0 1

/-- A value density `f` is piecewise-constant (p. 3) if `[0, 1]` can be partitioned into
finitely many intervals and `f` is constant on each of these intervals. The intervals are
arbitrary order-connected subsets of `ℝ` (open, closed, half-open, degenerate or empty), with
arbitrary real endpoints; their number `n` is unbounded. -/
def IsPiecewiseConstant (f : ℝ → ℝ) : Prop :=
  ∃ (n : ℕ) (I : Fin n → Set ℝ),
    (∀ k, (I k).OrdConnected) ∧
    (∀ k l, k ≠ l → Disjoint (I k) (I l)) ∧
    (⋃ k, I k) = cake ∧
    ∀ k, ∀ x ∈ I k, ∀ y ∈ I k, f x = f y

/-- Agent with density `f` is hungry (p. 3): `f x > 0` for every `x ∈ [0, 1]`, endpoints
included. -/
def IsHungry (f : ℝ → ℝ) : Prop :=
  ∀ x ∈ cake, 0 < f x

/-- The type space of Theorem 3.1 (p. 4): piecewise-constant hungry value densities. Values
outside `[0, 1]` are irrelevant (every utility integrates over a subset of the cake). -/
def IsAdmissible (f : ℝ → ℝ) : Prop :=
  IsPiecewiseConstant f ∧ IsHungry f

/-- Utility `v_f(X) = ∫_X f(x) dx` (p. 3) of the set `X`, restricted to the cake, for the
density `f`; Lebesgue (Bochner) integral against Lebesgue measure. -/
noncomputable def utility (f : ℝ → ℝ) (X : Set ℝ) : ℝ :=
  ∫ x in X ∩ cake, f x

/-- A reported profile `F = (f₁, f₂)` of two value density functions, as raw real functions. -/
abbrev Profile := Fin 2 → ℝ → ℝ

/-- A deterministic direct-revelation mechanism (p. 4): a map from reported profiles to the
two agents' shares, `M F i = M_i(F)`. It is a raw function on all profiles; every requirement
below constrains it only on admissible profiles. -/
abbrev Mechanism := Profile → Fin 2 → Set ℝ

/-- Every density of the profile is admissible (piecewise-constant and hungry). -/
def IsAdmissibleProfile (F : Profile) : Prop :=
  ∀ i : Fin 2, IsAdmissible (F i)

/-- An allocation `(A₁, A₂)` (p. 3): mutually disjoint subsets of `[0, 1]` (the published
`IsPartialAlloc` with both agents participating), each Lebesgue measurable. Entireness
(`A₁ ∪ A₂ = [0, 1]`) is **not** required. -/
def IsAllocation (A : Fin 2 → Set ℝ) : Prop :=
  EnvyFreeCake104.Divide.IsPartialAlloc Finset.univ cake A ∧
    ∀ i : Fin 2, NullMeasurableSet (A i) volume

/-- `M` outputs an allocation at every admissible profile. -/
def IsFeasible (M : Mechanism) : Prop :=
  ∀ F : Profile, IsAdmissibleProfile F → IsAllocation (M F)

/-- Proportionality for two agents (p. 3–4): at every admissible profile `F`, each agent `i`
receives `v_i(M_i(F)) ≥ (1/2) · v_i([0, 1])`, valued with the reported density `F i`. -/
def IsProportional (M : Mechanism) : Prop :=
  ∀ F : Profile, IsAdmissibleProfile F → ∀ i : Fin 2,
    (1 / 2 : ℝ) * utility (F i) cake ≤ utility (F i) (M F i)

/-- Dominant-strategy truthfulness (p. 4): for every agent `i`, every admissible profile `F`
and every admissible misreport `g` of agent `i`,
`v_i(M_i(F)) ≥ v_i(M_i(f₁, …, g, …, f_n))`, both sides valued with the true density `F i`. -/
def IsTruthful (M : Mechanism) : Prop :=
  ∀ F : Profile, IsAdmissibleProfile F → ∀ i : Fin 2, ∀ g : ℝ → ℝ, IsAdmissible g →
    utility (F i) (M (Function.update F i g) i) ≤ utility (F i) (M F i)

end TaoCake.Impossibility


