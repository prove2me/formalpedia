-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Norm
-- name    : OAI_Analysis_ForestSpace_Norm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:52:02.064972+00:00
-- url     : https://prove2.me/theorems/5e80aea0-20dc-4669-9c5a-d64dbf92fefb
-- title:
--   Basic properties of the disjoint-segment norm and its comparison with coordinates and $\ell_1$
-- statement:
--   Let $(V,\le)$ be a partially ordered set. A *segment* is a finite order-convex chain $S\subseteq V$, possibly empty, and $\Sigma_S u=\sum_{v\in S}u(v)$. For $u:V\to\mathbb{R}$, the *test values* of $u$ are the numbers $\sum_{i=1}^m(\Sigma_{S_i}u)^2$, where $S_1,\dots,S_m$ ranges over finite families of pairwise disjoint segments ($m=0$ allowed). Let $\Theta(u)$ be the supremum of the test values. The function $u$ *satisfies the test bound with constant $C$* if all its test values are at most $C$, and $u$ is *test-bounded* if it satisfies the test bound with some constant. The disjoint-segment norm and, for finitely supported $u$, the $\ell_1$-size are
--
--   $$
--   \rho(u)=\sqrt{\Theta(u)},\qquad \Theta(u)=\sup\Bigl\{\sum_{i=1}^m\bigl(\Sigma_{S_i}u\bigr)^2:\ S_1,\dots,S_m\ \text{pairwise disjoint segments}\Bigr\},\qquad \|u\|_1=\sum_{v\in\operatorname{supp}u}|u(v)|.
--   $$
--
--   The file records the following properties.
--
--   1. **Supremum of the test values.** $0$ is a test value of every $u$. If $u$ satisfies the test bound with constant $C$, then the set of test values is bounded above and $\Theta(u)\le C$. If $u$ is test-bounded, then $u$ satisfies the test bound with constant $\Theta(u)$, and $\Theta(u)\ge0$.
--   2. **The square of the norm.** $\rho(u)\ge0$ for every $u$. If $u$ is test-bounded, then $\rho(u)^2=\Theta(u)$ and $u$ satisfies the test bound with constant $\rho(u)^2$.
--   3. **Norm bounds versus test bounds.** If $C\ge0$ and $u$ satisfies the test bound with constant $C^2$, then $\rho(u)\le C$. Conversely, if $u$ is test-bounded and $\rho(u)\le C$ for a real $C$, then $u$ satisfies the test bound with constant $C^2$.
--   4. **Coordinates.** If $u$ is test-bounded, then $|u(v)|\le\rho(u)$ for every $v\in V$.
--   5. **Comparison with $\ell_1$.** Let $u$ be finitely supported. Then $\|u\|_1\ge0$, and $\sum_{v\in S}|u(v)|\le\|u\|_1$ for every finite $S\subseteq V$. Moreover, $u$ satisfies the test bound with constant $\|u\|_1^2$, so every finitely supported $u$ is test-bounded, and $\rho(u)\le\|u\|_1$.
--
--   In particular, for every finitely supported $u$ and every $v\in V$,
--
--   $$
--   |u(v)|\le\rho(u)\le\|u\|_1 .
--   $$
--
--   These facts connect the norm $\rho$ with the combinatorial test bounds used in all later estimates. To prove $\rho(u)\le C$ it suffices to bound each family of disjoint segments separately. The two-sided comparison shows that $\rho$ is finite and positive-definite on finitely supported vectors, which is why it is a norm there. Its completion is the space $J(V)$.
--
--   **Formalization Note** $\Theta(u)$ is `squareSup u`, the `sSup` of the set `testValues u`, and $\rho$ is `rho u = Real.sqrt (squareSup u)`. In Lean, `sSup` of a set of reals that is not bounded above is $0$, so a vector that is not test-bounded gets $\rho(u)=0$. For this reason, the statements that identify $\Theta(u)$ with the true supremum carry the hypothesis `∃ C, TestBound u C`. The $\ell_1$-size is `l1size u`, a sum over `u.support` for `u : V →₀ ℝ`. The lemmas are `zero_mem_testValues`, `TestBound.bddAbove`, `TestBound.squareSup_le`, `testBound_squareSup`, `squareSup_nonneg`, `rho_nonneg`, `rho_sq`, `testBound_rho_sq`, `rho_le_of_testBound`, `testBound_of_rho_le`, `coordinate_le_rho`, `l1size_nonneg`, `finset_abs_sum_le_l1size`, `testBound_l1size`, `finsupp_has_testBound` and `rho_le_l1size`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Norm.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Norm.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section SegmentNorm
variable {V : Type} [PartialOrder V]

 theorem zero_mem_testValues (u : V → ℝ) : 0 ∈ testValues u := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, by simp, by simp [Pairwise], ?_⟩
  simp

 theorem TestBound.bddAbove {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
    BddAbove (testValues u) := by
  refine ⟨C, ?_⟩
  rintro r ⟨ι, inst, S, hs, hd, rfl⟩
  exact h ι inst S hs hd

 theorem TestBound.squareSup_le {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
    squareSup u ≤ C := by
  apply csSup_le ⟨0, zero_mem_testValues u⟩
  rintro r ⟨ι, inst, S, hs, hd, rfl⟩
  exact h ι inst S hs hd

 theorem testBound_squareSup {u : V → ℝ} (hu : ∃ C, TestBound u C) :
    TestBound u (squareSup u) := by
  intro ι inst S hs hd
  exact le_csSup hu.choose_spec.bddAbove ⟨ι, inst, S, hs, hd, rfl⟩

 theorem squareSup_nonneg {u : V → ℝ} (hu : ∃ C, TestBound u C) : 0 ≤ squareSup u :=
  (testBound_squareSup hu).nonneg

 theorem rho_nonneg (u : V → ℝ) : 0 ≤ rho u := Real.sqrt_nonneg _

 theorem rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : rho u ^ 2 = squareSup u :=
  Real.sq_sqrt (squareSup_nonneg hu)

 theorem testBound_rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : TestBound u (rho u ^ 2) := by
  rw [rho_sq hu]
  exact testBound_squareSup hu

 theorem rho_le_of_testBound {u : V → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : TestBound u (C ^ 2)) : rho u ≤ C :=
  Real.sqrt_le_iff.mpr ⟨hC, hu.squareSup_le⟩

 theorem testBound_of_rho_le {u : V → ℝ} (hu : ∃ C, TestBound u C)
    {C : ℝ} (h : rho u ≤ C) : TestBound u (C ^ 2) :=
  (testBound_rho_sq hu).mono (by nlinarith [rho_nonneg u])

 theorem coordinate_le_rho {u : V → ℝ} (hu : ∃ C, TestBound u C) (v : V) :
    |u v| ≤ rho u := by
  have hh := (testBound_rho_sq hu).single (isSegment_singleton v)
  simp only [segSum, sum_singleton] at hh
  exact (sq_le_sq₀ (abs_nonneg _) (rho_nonneg _)).mp (by simpa only [sq_abs] using hh)

omit [PartialOrder V] in
 theorem l1size_nonneg [PartialOrder V] (u : V →₀ ℝ) : 0 ≤ l1size u :=
  sum_nonneg (fun vertex _ => abs_nonneg (u vertex))

omit [PartialOrder V] in
 theorem finset_abs_sum_le_l1size [PartialOrder V] (u : V →₀ ℝ) (S : Finset V) :
    ∑ v ∈ S, |u v| ≤ l1size u := by
  have he : (∑ v ∈ S ∪ u.support, |u v|) = l1size u := by
    symm
    apply sum_subset subset_union_right
    intro v hv hn
    rw [Finsupp.notMem_support_iff.mp hn, abs_zero]
  rw [← he]
  exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun v hv hn => abs_nonneg _)

 theorem testBound_l1size (u : V →₀ ℝ) : TestBound u (l1size u ^ 2) := by
  intro ι inst S hS hd
  have habs : (∑ i, |segSum u (S i)|) ≤ l1size u := by
    calc
      (∑ i, |segSum u (S i)|) ≤ ∑ i, ∑ v ∈ S i, |u v| :=
        sum_le_sum fun i hi => abs_sum_le_sum_abs _ _
      _ = ∑ v ∈ univ.biUnion S, |u v| :=
        (sum_biUnion (by intro i hi j hj hij; exact hd hij)).symm
      _ ≤ l1size u := finset_abs_sum_le_l1size u _
  have hsq := sum_sq_le_sq_sum_of_nonneg
    (s := (univ : Finset ι)) (f := fun i => |segSum u (S i)|) (fun i hi => abs_nonneg _)
  simp only [sq_abs] at hsq
  have hnonneg : 0 ≤ ∑ i, |segSum u (S i)| := sum_nonneg (fun i hi => abs_nonneg _)
  nlinarith [l1size_nonneg u]

 theorem finsupp_has_testBound (u : V →₀ ℝ) : ∃ C, TestBound u C := ⟨_, testBound_l1size u⟩

 theorem rho_le_l1size (u : V →₀ ℝ) : rho u ≤ l1size u :=
  rho_le_of_testBound (l1size_nonneg u) (testBound_l1size u)

end SegmentNorm

section SourceNormFidelity
variable {V : Type} [PartialOrder V]

end SourceNormFidelity

end

end ForestSpace

end OAI


