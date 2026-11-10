-- Prove2me | Definitions.Def_SFLOracleLowerBound_Hardness_Allocation
-- name    : SFLOracleLowerBound_Hardness_Allocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:25:57.6964+00:00
-- url     : https://prove2.me/theorems/ce96abd9-841e-4a2f-a9ca-b897fdd63d59
-- title:
--   Public allocation data, cost, optimum and SFL
-- statement:
--   Let $\mathcal C$ and $\mathcal F$ be finite nonempty client and facility sets. Public connection costs $D(c,f)$ take values in $[0,\infty]$. An assignment $\sigma:\mathcal C\to\mathcal F$ is feasible when every used connection cost is finite. Its cluster at $f$ is $C_f=\sigma^{-1}(f)$, and
--   $$
--   \operatorname{cost}(\sigma)=\sum_f\left(g(C_f)+\sum_{c\in C_f}D(c,f)\right),\qquad
--   \mathrm{OPT}=\min_{\sigma\text{ feasible}}\operatorname{cost}(\sigma).
--   $$
--   The optimum of an infeasible instance is $+\infty$. SFL means that $D$ extends to a finite-valued pseudometric on the disjoint union $\mathcal C\sqcup\mathcal F$. Distinct points may have distance zero. The rational-encoding predicate requires a rational pseudometric extension whose full matrix has polynomial total binary description length; it is used only for Proposition 26's witnesses.
--
--   These definitions keep public data separate from the hidden facility cost. **Formalization Note** Nonnegative costs are `ENNReal`; facility costs have separate nonnegativity hypotheses. A rational entry uses $4+\lfloor\log_2|a|\rfloor+\lfloor\log_2 b\rfloor$ bits, with the logarithm at zero set to zero, for numerator $a$ and denominator $b$. This allows the usual sign and separator headers; the existential polynomial absorbs encoding conventions.
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Definitions 4–5, p.6; Proposition 26, pp.25–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_SetFunctions

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

abbrev PublicData (C F : Type) := C → F → ℝ≥0∞

/-- Definition 5: a finite-valued pseudometric on a disjoint sum. -/
def IsSFL {C F : Type} (D : PublicData C F) : Prop :=
  ∃ δ : Sum C F → Sum C F → ℝ,
    (∀ x y, 0 ≤ δ x y) ∧ (∀ x, δ x x = 0) ∧
    (∀ x y, δ x y = δ y x) ∧ (∀ x y z, δ x z ≤ δ x y + δ y z) ∧
    ∀ c f, D c f = ENNReal.ofReal (δ (Sum.inl c) (Sum.inr f))

def cluster {C F : Type} [Fintype C] [DecidableEq F] (σ : C → F) (f : F) : Finset C :=
  univ.filter (fun c => σ c = f)

def Feasible {C F : Type} (D : PublicData C F) (σ : C → F) : Prop := ∀ c, D c (σ c) < ⊤

/-- Definition 4, p.6: the objective is extended nonnegative, including infeasibility. -/
def allocationCost {C F : Type} [Fintype C] [Fintype F] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) (σ : C → F) : ℝ≥0∞ :=
  ∑ f : F, (ENNReal.ofReal (g (cluster σ f)) + ∑ c ∈ cluster σ f, D c f)

/-- A finite assignment family; sInf ∅ = +∞ if no feasible assignment exists. -/
def optimum {C F : Type} [Fintype C] [Fintype F] [DecidableEq F]
    (D : PublicData C F) (g : Finset C → ℝ) : ℝ≥0∞ :=
  ⨅ σ : {σ : C → F // Feasible D σ}, allocationCost D g σ.val

/-- Binary length of a signed numerator and positive denominator; harmless fixed headers. -/
def rationalBits (q : ℚ) : ℕ :=
  4 + Nat.log2 q.num.natAbs + Nat.log2 q.den

def RationalEncoding {n m : ℕ} (D : PublicData (Fin n) (Fin m)) (P : Polynomial ℕ) : Prop :=
  ∃ δ : Sum (Fin n) (Fin m) → Sum (Fin n) (Fin m) → ℚ,
    (∀ x y, 0 ≤ δ x y) ∧ (∀ x, δ x x = 0) ∧
    (∀ x y, δ x y = δ y x) ∧ (∀ x y z, δ x z ≤ δ x y + δ y z) ∧
    (∀ c f, D c f = ENNReal.ofReal (δ (Sum.inl c) (Sum.inr f))) ∧
    (∑ x, ∑ y, rationalBits (δ x y)) ≤ P.eval n

end SFLOracleLowerBound.Hardness


