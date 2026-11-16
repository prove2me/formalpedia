-- Prove2me | Definitions.Def_KTaxi_Competitive_Supplement_Memoryless
-- name    : KTaxi_Competitive_Supplement_Memoryless
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:30:28.094194+00:00
-- url     : https://prove2.me/theorems/33171624-3067-43b0-b4d1-5b825d5f6931
-- title:
--   §6 / Appendix C — lazy memoryless policies, oblivious cost and oriented discrepancy
-- statement:
--   A lazy memoryless policy on the full real line assigns to each unordered multiset $X$ of two taxi locations and each current request $(r,s)$ a probability law on serving locations. Its support is contained in $X$, and if $r$ is present the law is concentrated at $r$. The conditional law is independent of every other aspect of the past; it may depend on destination, orientation and absolute position. Coincident taxis are included.
--
--   For a fixed finite request list $\sigma$, expected hard cost is the sum over serving locations of the pickup distance plus the remaining expected cost. Passenger travel is free. An offline schedule chooses one of the two labelled taxis per request; $\operatorname{OPT}_{x_0}(\sigma)$ is the minimum of the finitely many resulting costs. Oblivious competitiveness from a common start $x_0$ means that one finite $\beta\ge0$ bounds every fixed finite list by $\rho\operatorname{OPT}_{x_0}(\sigma)+\beta$.
--
--   Let $\mathrm{free}(\{x,y\})$ be the finite lists with an actual zero-cost offline schedule from $\{x,y\}$. With the online algorithm starting at $\{x,x\}$, define
--   $$F_A(x,y)=\sup_{\sigma\in\mathrm{free}(\{x,y\})}\mathbb E[A(\sigma)]\in[0,\infty].$$
--   The empty list is allowed, and the orientation of $(x,y)$ is retained. The final predicates express both distance bounds and both comparisons of Appendix C for an arbitrary finite nonnegative function, with a single common probability for each distinct triple. This layer supplies the objects for Lemmas C.1–C.3 and Theorem 1.3 without any regularity or symmetry assumption.
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §6, PDF p. 15 (printed p. 14); Appendix C, PDF pp. 23–24 (printed pp. 22–23)

import Mathlib
import Definitions.Def_KTaxi_Competitive_Model

open scoped ENNReal NNReal

namespace KTaxi.Competitive.Supplement

/-! §6 and Appendix C, PDF pp. 15, 23–24. A policy specifies the conditional law of
serving LOCATIONS, so neither taxi labels nor irrelevant private state can encode memory.
No regularity, reflection invariance, translation invariance or destination independence
is imposed. A PMF suffices because its support has at most two locations. -/
structure MemorylessPolicy where
  law : Multiset ℝ → (ℝ × ℝ) → PMF ℝ
  supported : ∀ X q a, X.card = 2 → law X q a ≠ 0 → a ∈ X
  lazy : ∀ X q, X.card = 2 → q.1 ∈ X → law X q = PMF.pure q.1

/-- Expected hard cost of a fixed finite request list. The multiset removes only ONE copy
of the serving location, including when both taxis coincide. -/
noncomputable def memorylessCost (A : MemorylessPolicy) :
    Multiset ℝ → List (ℝ × ℝ) → ℝ≥0∞
  | _, [] => 0
  | X, q :: qs => ∑' a : ℝ, A.law X q a *
      (edist a q.1 + memorylessCost A ((X.erase a).cons q.2) qs)

/-- Labelled configurations are converted to unordered multisets only for the policy. -/
def locations (x : Fin 2 → ℝ) : Multiset ℝ := (List.ofFn x : Multiset ℝ)

/-- Cost of a deterministic offline serving schedule, encoded as one label per request. -/
noncomputable def scheduleCost : (Fin 2 → ℝ) → List ((ℝ × ℝ) × Fin 2) → ℝ≥0∞
  | _, [] => 0
  | x, (q, i) :: rest => edist (x i) q.1 + scheduleCost (Function.update x i q.2) rest

/-- The infimum is a MINIMUM: for a finite list there are finitely many schedules, at
least one, and each has finite cost. No boundedness of the real line is assumed. -/
noncomputable def optCost (x : Fin 2 → ℝ) (qs : List (ℝ × ℝ)) : ℝ≥0∞ :=
  ⨅ a : Fin qs.length → Fin 2, scheduleCost x (qs.zip (List.ofFn a))

/-- Oblivious competitiveness from the fixed common start x₀. β is finite and precedes
ALL request lists; no adaptive or offline-randomness-dependent request list is allowed. -/
def ObliviousCompetitive (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ρ β : ℝ≥0) : Prop :=
  ∀ qs : List (ℝ × ℝ), memorylessCost A (locations x₀) qs ≤
    (ρ : ℝ≥0∞) * optCost x₀ qs + (β : ℝ≥0∞)

/-- free({x,y}), including the empty list, is defined by an actual zero-cost schedule. -/
def Free (x y : ℝ) (qs : List (ℝ × ℝ)) : Prop :=
  ∃ a : Fin qs.length → Fin 2,
    scheduleCost (fun i => if i = 0 then x else y) (qs.zip (List.ofFn a)) = 0

/-- The actual oriented discrepancy supremum, BEFORE any finiteness assertion. -/
noncomputable def discrepancy (A : MemorylessPolicy) (x y : ℝ) : ℝ≥0∞ :=
  ⨆ qs : {qs : List (ℝ × ℝ) // Free x y qs},
    memorylessCost A (locations (fun _ => x)) qs.val

/-- Both C.1 bounds for an arbitrary finite nonnegative oriented function. -/
def Bounds (F : ℝ → ℝ → ℝ≥0) (ρ : ℝ≥0) : Prop :=
  ∀ x y, |x - y| ≤ (F x y : ℝ) ∧ (F x y : ℝ) ≤ (ρ : ℝ) * |x - y|

/-- The SAME probability must satisfy both inequalities, at every distinct triple.
No symmetry, measurability, continuity or algorithm-realizability is required of F. -/
def Comparisons (F : ℝ → ℝ → ℝ≥0) : Prop :=
  ∀ x y z : ℝ, x ≠ y → x ≠ z → y ≠ z → ∃ p : ℝ,
    0 ≤ p ∧ p ≤ 1 ∧
    p * |x - y| + (1 - p) * (|z - y| + (F x z : ℝ)) ≤ (F x y : ℝ) ∧
    (1 - p) * |z - y| + p * (|x - y| + (F z x : ℝ)) ≤ (F z y : ℝ)

end KTaxi.Competitive.Supplement


