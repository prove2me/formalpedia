-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Aharoni
-- name    : OAI_Analysis_C0Absorption_Aharoni
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:54:02.333718+00:00
-- url     : https://prove2.me/theorems/479db1fb-40cc-4fd7-a0d0-94e326191e2b
-- title:
--   Metric bumps and an Aharoni-type embedding into c0
-- statement:
--   Let $M$ be a separable metric space with a dense sequence $(q_n)$.
--
--   1. **Earlier cut.** $\mathrm{cut}_0=r$ and $\mathrm{cut}_{n+1}(x)=\min\bigl(\mathrm{cut}_n(x),d(x,q_n)-r/4\bigr)$, so $\mathrm{cut}_n(x)\le d(x,q_j)-r/4$ for $j<n$.
--   2. **Metric bumps.**
--   $$
--   \beta_{r,n}(x)=\max\Bigl(0,\ \min\bigl(r-d(x,q_n),\ d(x,q_0)-r,\ \mathrm{cut}_n(x)\bigr)\Bigr)\in[0,r].
--   $$
--   It vanishes when $d(x,q_0)\le r$, and for fixed $x$ and $r>0$ it vanishes for all large $n$, since some earlier $q_j$ is close to $x$.
--   3. **Dyadic family.** For $(k,n)\in\mathbb Z\times\mathbb N$ put $\beta_{(k,n)}=\beta_{2^k,n}$. For fixed $x$, only finitely many values exceed any $\varepsilon>0$, so $(\beta_p(x))_p\in C_0(\mathbb Z\times\mathbb N)$.
--   4. **Embedding.** Enumerating $\mathbb Z\times\mathbb N$ by $\mathbb N$ gives $\mathrm{aharoniEmbedding}:M\to c_0$, the classical bi-Lipschitz embedding of a separable metric space into $c_0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Aharoni.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Aharoni.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift
import Definitions.Def_OAI_Analysis_C0Absorption_Onto
import Definitions.Def_OAI_Analysis_C0Absorption_Absorption

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section Aharoni
variable {M : Type*} [MetricSpace M]

def earlierCut (q : ℕ → M) (r : ℝ) : ℕ → M → ℝ
  | 0, _ => r
  | n+1, x => min (earlierCut q r n x) (dist x (q n)-r/4)

theorem earlierCut_le_point (q : ℕ → M) (r : ℝ) {n j : ℕ} (hj : j< n) (x : M) :
    earlierCut q r n x≤ dist x (q j)-r/4 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j=n
    · subst j; exact min_le_right _ _
    · exact (min_le_left _ _).trans (ih (by omega))

def metricBump (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : ℝ :=
  max 0 (min (r-dist x (q n)) (min (dist x (q 0)-r) (earlierCut q r n x)))

theorem metricBump_nonneg (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : 0≤ metricBump q r n x := le_max_left _ _

theorem metricBump_le_scale (q : ℕ → M) {r : ℝ} (hr : 0≤ r) (n : ℕ) (x : M) : metricBump q r n x≤ r :=
  max_le hr ((min_le_left _ _).trans (sub_le_self _ dist_nonneg))

theorem metricBump_zero_of_base (q : ℕ → M) {r : ℝ} (n : ℕ) (x : M) (h : dist x (q 0)≤ r) :
    metricBump q r n x=0 :=
  max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (sub_nonpos.mpr h)))

theorem metricBump_eventually_zero (q : ℕ → M) (hq : DenseRange q) {r : ℝ} (hr : 0< r) (x : M) :
    ∃ N : ℕ, ∀ n, N≤ n → metricBump q r n x=0 := by
  obtain ⟨j,hj⟩ := hq.exists_dist_lt x (show 0< r/4 by positivity)
  refine ⟨j+1,fun n hn => ?_⟩
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_right _ _).trans
    ((earlierCut_le_point q r (n := n) (j := j) (by omega) x).trans (by linarith)))

def dyadicBump (q : ℕ → M) (p : ℤ × ℕ) (x : M) : ℝ := metricBump q ((2 : ℝ)^p.1) p.2 x

theorem dyadicBump_finite_large (q : ℕ → M) (hq : DenseRange q) (x : M) {ε : ℝ} (hε : 0<ε) :
    {p : ℤ × ℕ | ε≤ dyadicBump q p x}.Finite := by
  classical
  obtain ⟨L,hL,hL'⟩ := exists_mem_Ico_zpow hε (show (1 : ℝ)<2 by norm_num)
  obtain ⟨U,hU,hU'⟩ := exists_mem_Ico_zpow (show 0< max 1 (dist x (q 0)) by positivity)
    (show (1 : ℝ)<2 by norm_num)
  choose N hN using fun k : ℤ => metricBump_eventually_zero q hq (zpow_pos (by norm_num : (0 : ℝ)<2) k) x
  have hfinite : (⋃ k∈Set.Icc L U, ({k} : Set ℤ) ×ˢ Set.Iio (N k)).Finite :=
    (Set.finite_Icc L U).biUnion (fun k hk => (Set.finite_singleton k).prod (Set.finite_Iio _))
  apply hfinite.subset
  rintro ⟨k,n⟩ hp
  have hnonzero : dyadicBump q (k,n) x≠0 := ne_of_gt (hε.trans_le hp)
  have hkL : L≤ k := by
    by_contra hh
    have hr := zpow_lt_zpow_right₀ (a := (2 : ℝ)) (by norm_num) (lt_of_not_ge hh)
    have hb := metricBump_le_scale q (zpow_pos (by norm_num : (0 : ℝ)<2) k).le n x
    change metricBump q ((2 : ℝ)^k) n x≥ε at hp
    linarith
  have hkU : k≤ U := by
    by_contra hh
    have hk : U+1≤ k := by omega
    have hr := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hk
    apply hnonzero
    exact metricBump_zero_of_base q n x ((le_max_right _ _).trans (hU'.le.trans hr))
  have hn : n< N k := by
    by_contra hh
    exact hnonzero (hN k n (le_of_not_gt hh))
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨⟨hkL,hkU⟩,⟨rfl,hn⟩⟩⟩

theorem dyadicBump_tendsto (q : ℕ → M) (hq : DenseRange q) (x : M) :
    Tendsto (fun p => dyadicBump q p x) cofinite (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply Filter.eventually_cofinite.mpr
  simpa only [Real.dist_eq,sub_zero,dyadicBump,abs_of_nonneg (metricBump_nonneg q _ _ x),not_lt]
    using dyadicBump_finite_large q hq x hε

def dyadicC0 (q : ℕ → M) (hq : DenseRange q) (x : M) : C₀(ℤ × ℕ,ℝ) :=
  cfunOfTendsto (fun p => dyadicBump q p x) (dyadicBump_tendsto q hq x)

@[simp] theorem dyadicC0_apply (q : ℕ → M) (hq : DenseRange q) (x : M) (p : ℤ × ℕ) :
    dyadicC0 q hq x p=dyadicBump q p x := rfl

end Aharoni
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section AharoniLower
variable {M : Type*} [MetricSpace M]

end AharoniLower

section C0Reindex
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]

end C0Reindex

section AharoniEmbedding
variable {M : Type*} [MetricSpace M]

def dyadicEnumeration : (ℤ × ℕ) ≃ ℕ := Denumerable.eqv _

def aharoniEmbedding (q : ℕ → M) (hq : DenseRange q) (x : M) : C0 :=
  cfunPull dyadicEnumeration.symm dyadicEnumeration.symm.injective.tendsto_cofinite (dyadicC0 q hq x)

end AharoniEmbedding

end
end C0Absorption

end OAI


