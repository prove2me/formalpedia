-- Prove2me | Definitions.Def_TwoConnSS_IsContractionStage
-- name    : TwoConnSS_IsContractionStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:49:26.174112+00:00
-- url     : https://prove2.me/theorems/a7e386fb-dd6a-4fe4-8ce7-5871e83d36b6
-- title:
--   Algorithm A at its contraction stage, with $L$ and $R$
-- statement:
--   At the contraction stage of Algorithm A, the **large components** are the 2EC components that are not cycles of length $4$ to $8$; $L$ is their total number of edges and $R$ the total number of edges of the remaining 5–8-cycle components.
--
--   `IsContractionStage G q S₀ S M` says that $(S, M)$ is reached by Algorithm A from the initial cover $S_0$ and has finished its loops:
--
--   1. some $(S_1, M_1)$ with the output properties of Lemma 8.11 ($S_1 \subseteq S_0$, canonical for A, 4-cycles primitive, $\mathrm{cost}_A(S_1, M_1) \le K_A$) reaches $(S, M)$ by a finite chain of successful exchanges of Algorithm A;
--   2. $S$ is bridgeless and canonical for A;
--   3. no two distinct 4-cycle components lie in one 2VC block of $\hat G_S$;
--   4. $\hat G_S$ has no cycle through $q$ or more parts.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.2.3, p.55; Algorithm A (full version), p.56

import Mathlib
import Definitions.Def_TwoConnSS_SuccA
import Definitions.Def_TwoConnSS_KA
import Definitions.Def_TwoConnSS_partGraph

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- The ordinary large 2EC components at the contraction stage (p.55): "all ordinary 2EC components
other than the cycle components of lengths four through eight". -/
noncomputable def largeComps (S : Finset (Sym2 V)) : Finset (Finset V) :=
  (comps S).filter fun C => IsTwoECComp S C ∧ ¬ ∃ t, 4 ≤ t ∧ t ≤ 8 ∧ IsCycleComp S C t

/-- `L := Σ_i |E(C_i)|` over the ordinary large 2EC components (p.55). -/
noncomputable def Lsum (S : Finset (Sym2 V)) : ℕ :=
  ∑ C ∈ largeComps S, (edgesIn S C).card

/-- `R`: the number of edges in the remaining 5–8-cycle components (p.55). -/
noncomputable def Rsum (S : Finset (Sym2 V)) : ℕ :=
  ∑ C ∈ (comps S).filter (fun C => ∃ t, 5 ≤ t ∧ t ≤ 8 ∧ IsCycleComp S C t), (edgesIn S C).card

/-- **`(S, M)` is reached by Algorithm A from `S₀` and is at its contraction stage, for the cycle
threshold `q`.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Algorithm A (full version), p.56:
"1 Transform S into a canonical weak 2-edge-cover using Lemma 8.11; 2 while S contains a bridge do
3 Find a successful exchange by applying Theorem 8.22 under assignment A; 4 while two 4-cycles lie
in one 2VC block of Ĝ_S do 5 Find a successful exchange by applying Lemma 8.26; 6 while Ĝ_S
contains a long cycle do 7 Find a successful exchange using the component-cycle construction of
Claim 8.28; 8 return the exact completion of Theorem 8.29."

The clauses: some `(S₁, M₁)` with the output properties of Lemma 8.11 (`S₁ ⊆ S₀`, canonical for A,
4-cycles primitive, `cost_A(S₁, M₁) ≤ K_A`) reaches `(S, M)` by a finite chain of successful
A-exchanges; `S` is bridgeless and canonical for A; no two distinct 4-cycle components lie in one
2VC block of `Ĝ_S`; and `Ĝ_S` has no cycle through `q` or more parts.

Also defined here: the large components, `L` and `R` of §8.2.3.

**Formalization Note.** This is the run of Algorithm A described by its loop conditions; the
exchanges are recorded only through their defining properties (`SuccA`). Theorem 8.29 is stated
for an algorithm that outputs such an `(S, M)`, see its docstring. -/
def IsContractionStage (G : SimpleGraph V) (q : ℕ) (S₀ S M : Finset (Sym2 V)) : Prop :=
  (∃ S₁ M₁, S₁ ⊆ S₀ ∧ IsCanonA G S₁ M₁ ∧ Primitive S₀ S₁ ∧ costA S₁ M₁ ≤ KA S₀ ∧
    Relation.ReflTransGen (SuccA G S₀) (S₁, M₁) (S, M)) ∧
  br S = 0 ∧ IsCanonA G S M ∧
  (∀ C C', IsCycleComp S C 4 → IsCycleComp S C' 4 → C ≠ C' → ¬ SharePartBlock G S M C C') ∧
  ¬ HasLongPartCycle G S M q

end TwoConnSS


