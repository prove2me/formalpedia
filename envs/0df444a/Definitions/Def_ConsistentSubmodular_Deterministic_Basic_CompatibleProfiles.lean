-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
-- name    : ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:58.026906+00:00
-- url     : https://prove2.me/theorems/1d634fbd-8488-4a64-ab55-84286bae9b3c
-- title:
--   Compatible profiles on types, contracted objectives, finite maximum, and safe polygonal paths
-- statement:
--   Types are indexed by `Fin d`. For an `Objective n` $f$ (nonnegative, monotone, submodular) and a point in the simplex, the following abstract time-indexed data is used.
--
--   - `Objective.onTypes f cores Q`: the objective on $d$ types, $I\mapsto f\big(Q\cup\bigcup_{i\in I}\mathrm{cores}(i)\big)$, for a buffer $Q$ and physical cores $\mathrm{cores}(i)\subseteq[n]$ (cores may overlap or coincide). It is again nonnegative, monotone, submodular.
--   - `CompatibleProfile d`: a family of objectives $f_t$ on $d$ types indexed by time $t\in\mathbb N$ such that values increase with time, $f_s(I)\le f_t(I)$ for $s\le t$, and marginals decrease with time, $f_t(J)-f_t(I)\le f_s(J)-f_s(I)$ for $s\le t$, $I\subseteq J$.
--   - `CompatibleProfile.fromPhysical f cores Q hQ`: the profile $t\mapsto f.\mathrm{onTypes}(\mathrm{cores},Q_t)$ for a monotone buffer sequence $Q_t$ (a growing set of arrivals).
--   - For a profile $P$: `baseline t` $=f_t(\emptyset)$; `residualOn t I` $=f_t(I)-f_t(\emptyset)$; `residual t i` $=f_t(\{i\})-f_t(\emptyset)$; `loss t i` $=\mathrm{residual}_t(i)-\mathrm{residual}_{t+1}(i)$.
--   - `finiteMaximum I g`: $\max_{i\in I}g(i)$ for a finite set $I$, and $0$ for $I=\emptyset$ (used only with nonnegative $g$).
--   - `poolValue t I` $=\max_{i\in I}\mathrm{loss}_t(i)$; `terminalValue m I` $=\max_{i\in I}\mathrm{residual}_m(i)$.
--   - For a profile on $m+1$ types, `multilinearValue t p` $=\mathbb E\,f_t(I(p))$ with $I(p)$ the independent random set of types with marginals $p\in$ `Point m`; `SafePath t level γ`: every node of the polygonal path $\gamma$ and every point of every segment lies in the simplex and has `multilinearValue t` at least `level`.
--
--   The file also proves that residuals are nonnegative and nonincreasing in $t$, that losses are nonnegative, and basic properties (upper bound, nonnegativity, singleton value) of `finiteMaximum`.
--
--   These definitions abstract the window instances of Section 3.2 into time-indexed profiles on types, and `SafePath` is the profile-level form of the safe paths of clairvoyant certificates (Definition 3.1).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/CompatibleProfiles.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace Objective

variable {n d : ℕ} (f : Objective n)

/-- Contract a buffer and replace each type by its physical core. Core overlap
and repeated identical cores are both allowed. -/
def onTypes (cores : Fin d → Finset (Fin n)) (Q : Finset (Fin n)) : Objective d where
  value I := f.value (Q ∪ I.biUnion cores)
  nonnegative I := f.nonnegative _
  monotone I J hIJ := f.monotone _ _
    (Finset.union_subset_union_right (Finset.biUnion_subset_biUnion_of_subset_left cores hIJ))
  submodular I J := by
    have hs := f.submodular (Q ∪ I.biUnion cores) (Q ∪ J.biUnion cores)
    have hsub : Q ∪ (I ∩ J).biUnion cores ⊆
        (Q ∪ I.biUnion cores) ∩ (Q ∪ J.biUnion cores) := by
      apply Finset.subset_inter
      · exact Finset.union_subset_union_right
          (Finset.biUnion_subset_biUnion_of_subset_left cores Finset.inter_subset_left)
      · exact Finset.union_subset_union_right
          (Finset.biUnion_subset_biUnion_of_subset_left cores Finset.inter_subset_right)
    have hm := f.monotone _ _ hsub
    have hu : (Q ∪ I.biUnion cores) ∪ (Q ∪ J.biUnion cores) =
        Q ∪ (I ∪ J).biUnion cores := by
      rw [Finset.union_biUnion]
      ext e
      simp only [Finset.mem_union]
      tauto
    rw [hu] at hs
    linarith

@[simp] theorem onTypes_empty (cores : Fin d → Finset (Fin n)) (Q : Finset (Fin n)) :
    (f.onTypes cores Q).value ∅ = f.value Q := by simp [onTypes]

@[simp] theorem onTypes_singleton (cores : Fin d → Finset (Fin n))
    (Q : Finset (Fin n)) (i : Fin d) :
    (f.onTypes cores Q).value {i} = f.value (Q ∪ cores i) := by simp [onTypes]

end Objective

/-- Time increases values and decreases every fixed-context type marginal. -/
structure CompatibleProfile (d : ℕ) where
  objective : ℕ → Objective d
  values_increase : ∀ s t, s ≤ t → ∀ I, (objective s).value I ≤ (objective t).value I
  marginals_decrease : ∀ s t, s ≤ t → ∀ I J, I ⊆ J →
    (objective t).value J - (objective t).value I ≤
      (objective s).value J - (objective s).value I

namespace CompatibleProfile

variable {n d : ℕ}

def fromPhysical (f : Objective n) (cores : Fin d → Finset (Fin n))
    (Q : ℕ → Finset (Fin n)) (hQ : Monotone Q) : CompatibleProfile d where
  objective t := f.onTypes cores (Q t)
  values_increase s t hst I := f.monotone _ _ (Finset.union_subset_union_left (hQ hst))
  marginals_decrease s t hst I J hIJ := by
    have hcore := Finset.biUnion_subset_biUnion_of_subset_left cores hIJ
    have h := f.diminishing_returns (A := Q s ∪ I.biUnion cores)
      (B := Q t ∪ I.biUnion cores) (Finset.union_subset_union_left (hQ hst))
      (J.biUnion cores)
    have hu (u : ℕ) : (Q u ∪ I.biUnion cores) ∪ J.biUnion cores = Q u ∪ J.biUnion cores := by
      rw [Finset.union_assoc, Finset.union_eq_right.mpr hcore]
    simpa only [Objective.onTypes, hu] using h

variable (P : CompatibleProfile d)

def baseline (t : ℕ) : ℝ := (P.objective t).value ∅

def residualOn (t : ℕ) (I : Finset (Fin d)) : ℝ :=
  (P.objective t).value I - P.baseline t

def residual (t : ℕ) (i : Fin d) : ℝ := P.residualOn t {i}

def loss (t : ℕ) (i : Fin d) : ℝ := P.residual t i - P.residual (t + 1) i

theorem residualOn_nonnegative (t : ℕ) (I : Finset (Fin d)) : 0 ≤ P.residualOn t I := by
  exact sub_nonneg.mpr ((P.objective t).monotone ∅ I (Finset.empty_subset _))

theorem residualOn_antitone {s t : ℕ} (hst : s ≤ t) (I : Finset (Fin d)) :
    P.residualOn t I ≤ P.residualOn s I :=
  P.marginals_decrease s t hst ∅ I (Finset.empty_subset _)

theorem loss_nonnegative (t : ℕ) (i : Fin d) : 0 ≤ P.loss t i :=
  sub_nonneg.mpr (P.residualOn_antitone (Nat.le_succ t) {i})

end CompatibleProfile

/-- The finite maximum, with zero for the empty family. All uses below have
nonnegative entries, so adjoining the empty maximum causes no ambiguity. -/
def finiteMaximum {ι : Type*} (I : Finset ι) (g : ι → ℝ) : ℝ :=
  if h : I.Nonempty then g (Classical.choose (I.exists_max_image g h)) else 0

theorem finiteMaximum_le {ι : Type*} {I : Finset ι} {g : ι → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i ∈ I, g i ≤ a) : finiteMaximum I g ≤ a := by
  classical
  by_cases hI : I.Nonempty
  · rw [finiteMaximum, dif_pos hI]
    exact h _ (Classical.choose_spec (I.exists_max_image g hI)).1
  · simp [finiteMaximum, hI, ha]

theorem le_finiteMaximum {ι : Type*} {I : Finset ι} {g : ι → ℝ}
    {i : ι} (hi : i ∈ I) : g i ≤ finiteMaximum I g := by
  classical
  have hI : I.Nonempty := ⟨i, hi⟩
  rw [finiteMaximum, dif_pos hI]
  exact (Classical.choose_spec (I.exists_max_image g hI)).2 i hi

theorem finiteMaximum_nonnegative {ι : Type*} {I : Finset ι} {g : ι → ℝ}
    (h : ∀ i ∈ I, 0 ≤ g i) : 0 ≤ finiteMaximum I g := by
  classical
  by_cases hI : I.Nonempty
  · rw [finiteMaximum, dif_pos hI]
    exact h _ (Classical.choose_spec (I.exists_max_image g hI)).1
  · simp [finiteMaximum, hI]

@[simp] theorem finiteMaximum_singleton {ι : Type*} (i : ι) (g : ι → ℝ)
    (hg : 0 ≤ g i) : finiteMaximum {i} g = g i := by
  classical
  exact le_antisymm (finiteMaximum_le hg (by simp)) (le_finiteMaximum (Finset.mem_singleton_self i))

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

def poolValue (t : ℕ) (I : Finset (Fin d)) : ℝ := finiteMaximum I (P.loss t)

def terminalValue (m : ℕ) (I : Finset (Fin d)) : ℝ := finiteMaximum I (P.residual m)

end CompatibleProfile

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

/-- The value of a type mixture at stage `t`: the expectation of the profile's
objective under independent type samples. -/
def multilinearValue (t : ℕ) (p : Point m) : ℝ := finiteExpectation p (P.objective t).value

/-- Safety of a polygonal path at stage `t` and level `level`: every point lies in
the simplex and has multilinear value at least `level`. -/
def SafePath (t : ℕ) (level : ℝ) (γ : PolygonalPath m) : Prop :=
  (∀ j, IsSimplex (γ.node j) ∧ level ≤ P.multilinearValue t (γ.node j)) ∧
  ∀ (j : Fin γ.pieces) (x : ℝ), 0 ≤ x → x ≤ 1 →
    IsSimplex (mix (γ.node j.castSucc) (γ.node j.succ) x) ∧
    level ≤ P.multilinearValue t (mix (γ.node j.castSucc) (γ.node j.succ) x)

end CompatibleProfile

end ConsistentSubmodular

end


