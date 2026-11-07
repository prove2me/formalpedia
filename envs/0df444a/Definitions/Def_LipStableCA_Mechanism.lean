-- Prove2me | Definitions.Def_LipStableCA_Mechanism
-- name    : LipStableCA_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:07.71621+00:00
-- url     : https://prove2.me/theorems/6199bdc3-b3b7-4095-ac7a-3c05f969f541
-- title:
--   Randomized mechanisms over a seed space: truthfulness, UT, TIE, ex-post IR
-- statement:
--   A deterministic mechanism $(S,p)$ is truthful if for all $i$, $v_i$, $v_i'$ and $v_{-i}$,
--   $$v_i(S(v)_i)-p_i(v)\ge v_i(S(v_i',v_{-i})_i)-p_i(v_i',v_{-i}).$$
--   A randomized mechanism draws a seed $\omega$ independently of the reports and runs the deterministic mechanism $(S(\cdot;\omega),p(\cdot;\omega))$. It is universally truthful if it is a distribution over truthful deterministic mechanisms, truthful in expectation if the inequality holds in expectation over the seed, and ex-post individually rational if, for every fixed profile, a truthful bidder's realized utility is nonnegative with probability one. Its allocation law at $v$ is the distribution of $S(v;\omega)$. The module also defines the mixture of a family of mechanisms used in Observation 2.11.
--
--   **Formalization Note.** Measurability of $\omega\mapsto S(v;\omega)$ is a predicate, used as a hypothesis or a conclusion, since the paper names no σ-algebra. Universal truthfulness is an almost-everywhere statement, because the set of truthful seeds need not be measurable. Truthfulness in expectation includes integrable payments, without which $\mathbb E[p_i]$ is undefined.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Def. 2.1, p.7; §2, p.7; §5, p.21

import Definitions.Def_LipStableCA_emd

open MeasureTheory

namespace LipStableCA

variable {n m : ℕ}

/-- A deterministic mechanism `(S, p)` is truthful, Definition 2.1, p.7: for all `i`, `vᵢ`, `v′ᵢ` and
`v₋ᵢ`, `vᵢ(S(v)ᵢ) − pᵢ(v) ≥ vᵢ(S(v′ᵢ, v₋ᵢ)ᵢ) − pᵢ(v′ᵢ, v₋ᵢ)`. **Formalization Note.** Reports and
deviations range over the valuation class `V` only. -/
def IsTruthful (S : Profile n m → Alloc n m) (p : Profile n m → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (v : Profile n m) (u : Finset (Fin m) → ℝ), IsProfile v → IsValuation u →
    v i ((S (Function.update v i u)).1 i) - p (Function.update v i u) i ≤ v i ((S v).1 i) - p v i

/-- A randomized mechanism over a seed space `Ω`, §2, p.7 ("first draws a random seed, independently of
the reports"): a family of deterministic mechanisms `(S(· ; ω), p(· ; ω))`, §5, p.21. **Formalization
Note.** No proof fields. Measurability is the separate predicate `Mechanism.Measurable`, a hypothesis
or a conclusion of each statement that uses `Mechanism.law`. -/
structure Mechanism (n m : ℕ) (Ω : Type*) where
  /-- The allocation `S(v; ω)`. -/
  alloc : Profile n m → Ω → Alloc n m
  /-- The payments `p(v; ω)`. -/
  pay : Profile n m → Ω → Fin n → ℝ

namespace Mechanism

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `ω ↦ S(v; ω)` is measurable at every valid report, which is what makes the allocation law
meaningful. The paper leaves the σ-algebra implicit. -/
def Measurable (M : Mechanism n m Ω) : Prop :=
  ∀ v : Profile n m, IsProfile v → _root_.Measurable (M.alloc v)

/-- `ω ↦ pᵢ(v; ω)` is measurable at every valid report. -/
def PayMeasurable (M : Mechanism n m Ω) : Prop :=
  ∀ v : Profile n m, IsProfile v → ∀ i, _root_.Measurable (fun ω => M.pay v ω i)

/-- The allocation law `P_v`, Definition 2.2, p.7, as a mass function. -/
noncomputable def law (M : Mechanism n m Ω) (μ : Measure Ω) (v : Profile n m) (T : Alloc n m) : ℝ :=
  μ.real {ω | M.alloc v ω = T}

/-- Universally truthful, Definition 2.1, p.7: a distribution over truthful deterministic mechanisms.
**Formalization Note.** Stated as `∀ᵐ`; the set of truthful seeds quantifies over uncountably many
reports and need not be measurable, and `∀ᵐ` says that its complement has outer measure `0`. -/
def IsUT (M : Mechanism n m Ω) (μ : Measure Ω) : Prop :=
  ∀ᵐ ω ∂μ, IsTruthful (fun v => M.alloc v ω) (fun v => M.pay v ω)

/-- Truthful in expectation, Definition 2.1, p.7: the truthfulness inequality in expectation over the
seed. **Formalization Note.** Integrable payments are part of the definition: otherwise `E[pᵢ]` is
undefined and the Bochner integral would return `0`. -/
def IsTIE (M : Mechanism n m Ω) (μ : Measure Ω) : Prop :=
  (∀ v : Profile n m, IsProfile v → ∀ i, Integrable (fun ω => M.pay v ω i) μ) ∧
  ∀ (i : Fin n) (v : Profile n m) (u : Finset (Fin m) → ℝ), IsProfile v → IsValuation u →
    ∫ ω, (v i ((M.alloc (Function.update v i u) ω).1 i) - M.pay (Function.update v i u) ω i) ∂μ ≤
      ∫ ω, (v i ((M.alloc v ω).1 i) - M.pay v ω i) ∂μ

/-- Ex-post individually rational, Definition 2.1, p.7: for every fixed profile, a truthful bidder's
realized utility is nonnegative with probability one. -/
def IsExPostIR (M : Mechanism n m Ω) (μ : Measure Ω) : Prop :=
  ∀ v : Profile n m, IsProfile v → ∀ i, ∀ᵐ ω ∂μ, 0 ≤ v i ((M.alloc v ω).1 i) - M.pay v ω i

/-- The mixture of Observation 2.11, p.9: on seed `(ξ, ω)`, run the mechanism `M ξ` with internal coins `ω`.
**Formalization Note.** The coins of the family share one type; their law may depend on `ξ` (a kernel). -/
def mixture {Ξ : Type*} (M : Ξ → Mechanism n m Ω) : Mechanism n m (Ξ × Ω) where
  alloc v ω := (M ω.1).alloc v ω.2
  pay v ω := (M ω.1).pay v ω.2

end Mechanism

end LipStableCA


