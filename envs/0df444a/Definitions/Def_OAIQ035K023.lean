-- Prove2me | Definitions.Def_OAIQ035K023
-- name    : OAIQ035K023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:57:06.103048+00:00
-- url     : https://prove2.me/theorems/4a214ec9-4e74-4d8b-b298-a8d441522141
-- title:
--   Definitions bundle OAIQ035K023 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 13 definitions and 14 theorems. The definitions and types are `OAI.MetricKMedian.Instance.restrictFacilities`, `OAI.MetricKMedian.LPBinary.Repair.opening`, `OAI.MetricKMedian.LPBinary.Truncated.row`, `OAI.MetricKMedian.Preparation.RationalBundles.bundle`, `OAI.MetricKMedian.Preparation.RationalBundles.geometry`, `OAI.MetricKMedian.Preparation.RationalBundles.missing`, `OAI.MetricKMedian.Preparation.RationalBundles.next`, `OAI.MetricKMedian.Preparation.RationalBundles.suppliers`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.representatives`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.select`, `OAI.MetricKMedian.Preparation.RationalUnitInput.V`, `OAI.MetricKMedian.Preparation.RationalUnitInput.representatives`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ridx`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_RationalBundleGeometry`, `KMedian_Geometry_RationalGeometryScan`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Instance`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_RationalArgmin`, `KMedian_Optimization_TruncatedListOperations`, `KMedian_Preparation_RationalRepresentatives`, `KMedian_Reduction_BudgetReduction`, `KMedian_Sparse_SparseBernoulliSubsets`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K005`, `OAIQ035K008`, `OAIQ035K009` and `OAIQ035K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K034`, `OAIQ035K035` and `OAIQ035K044`; the statement `OAI_MetricKMedian_RationalPhysicalKernel_histories_completed_expectation`; the proofs of `OAI_MetricKMedian_RationalPhysicalKernel_histories_completed_expectation`, `OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices`, `OAI.MetricKMedian.Reduction.Serving.bad_count`, `OAI.MetricKMedian.Reduction.completion_branch_exists` and `OAI.MetricKMedian.Reduction.sparse_branch_exists`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K009
import Definitions.Def_OAIQ035K010

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalBundleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset
variable {n m : ℕ}

def next (d : Fin n → Fin n → ℚ) (t : Fin n) : Fin n :=
  if h : (univ.erase t).Nonempty then firstNearest (univ.erase t) (d t) h else t

def bundle (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ)
    (F : Fin n → Finset (Fin m)) (δ : ℚ) (t : Fin n) : Finset (Fin m) :=
  if next d t=t then F t else (F t).filter (fun a => di t a ≤ δ*d t (next d t))

def missing (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ)
    (F : Fin n → Finset (Fin m)) (δ : ℚ) (t : Fin n) : Finset (Fin m) :=
  F t \ bundle d di F δ t

theorem next_self (d : Fin n → Fin n → ℚ) (t : Fin n) (h : next d t=t) : ∀ u, u=t := by
  intro u
  by_contra hu
  have hn : (univ.erase t).Nonempty := ⟨u, mem_erase.mpr ⟨hu,mem_univ _⟩⟩
  have hm := (firstNearest_spec (univ.erase t) (d t) hn).1
  simp only [next, dite_eq_left hn] at h
  rw [h] at hm
  exact notMem_erase _ _ hm

theorem next_min (d : Fin n → Fin n → ℚ) (t u : Fin n) (htu : t≠u) :
    d t (next d t) ≤ d t u := by
  have hn : (univ.erase t).Nonempty := ⟨u,mem_erase.mpr ⟨htu.symm,mem_univ _⟩⟩
  simp only [next,dite_eq_left hn]
  exact (firstNearest_spec _ _ hn).2 u (mem_erase.mpr ⟨htu.symm,mem_univ _⟩)

theorem bundle_sub (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ)
    (F : Fin n → Finset (Fin m)) (δ : ℚ) (t : Fin n) : bundle d di F δ t ⊆ F t := by
  unfold bundle
  split_ifs
  · exact Subset.rfl
  · exact filter_subset _ _

noncomputable def geometry {X : Type} [PseudoMetricSpace X]
    (F : Fin n → Finset (Fin m)) (y : Fin m → ℚ) (s : Fin n → X) (i : Fin m → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin m → ℚ) (V : Fin n → ℚ) (M δ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) :
    BundleGeometry F (fun a => (y a:ℝ)) s i (fun t => (V t:ℝ)) (M:ℝ) (δ:ℝ) := by
  let P := bundle d di F δ
  let A := missing d di F δ
  let p := mass y P
  let c := mass y A
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hδ' : (0:ℝ) < δ := by exact_mod_cast hδ
  have hy' : ∀ a, (0:ℝ) < y a := by intro a; exact_mod_cast hy a
  have hu' : ∀ t, ∑ a ∈ F t, (y a:ℝ)=1 := by intro t; exact_mod_cast hu t
  have hv' : ∀ t, ∑ a ∈ F t, (y a:ℝ)*dist (s t) (i a)=(V t:ℝ) := by
    intro t
    simp only [hdi]
    exact_mod_cast hv t
  have hV : ∀ t, (0:ℝ) ≤ V t := fun t => (hv' t) ▸
    sum_nonneg (fun a _ => mul_nonneg (hy' a).le dist_nonneg)
  have hsub : ∀ t, P t ⊆ F t := bundle_sub d di F δ
  have hcm : ∀ t, (c t:ℝ)=∑ a ∈ A t, (y a:ℝ) := by intro t; simp only [c,mass,Rat.cast_sum]
  have hpm : ∀ t, (p t:ℝ)=∑ a ∈ P t, (y a:ℝ) := by intro t; simp only [p,mass,Rat.cast_sum]
  have hunit : ∀ t, (p t:ℝ)+(c t:ℝ)=1 := by
    intro t
    rw [hpm,hcm]
    change (∑ a ∈ P t, (y a:ℝ))+(∑ a ∈ F t \ P t, (y a:ℝ))=1
    rw [add_comm,sum_sdiff (hsub t),hu']
  have hc : ∀ t, (0:ℝ) ≤ c t := by intro t; rw [hcm]; exact sum_nonneg (fun a _ => (hy' a).le)
  have hzero : ∀ t, next d t=t → c t=0 := by
    intro t ht
    simp [c,mass,A,missing,bundle,ht]
  have hL : ∀ t, next d t≠t → M*V t < d t (next d t) := by
    intro t ht
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hM.le).trans_lt
      (hs t (next d t) ht.symm)
  have hcharge : ∀ t, (δ:ℝ)*dist (s t) (s (next d t))*(c t:ℝ) ≤ (V t:ℝ) := by
    intro t
    by_cases ht : next d t=t
    · rw [hzero t ht,Rat.cast_zero,mul_zero]
      exact hV t
    · have he : A t=(F t).filter (fun a => (δ:ℝ)*dist (s t) (s (next d t))<dist (s t) (i a)) := by
        ext a
        simp only [A,missing,bundle,ite_eq_right ht,mem_sdiff,mem_filter,not_and,hd,hdi]
        have hcast : ((δ*d t (next d t):ℚ):ℝ)= (δ:ℝ)*(d t (next d t):ℝ) := by push_cast; rfl
        rw [← hcast, Rat.cast_lt]
        constructor
        · rintro ⟨ha,hb⟩
          exact ⟨ha,lt_of_not_ge (hb ha)⟩
        · rintro ⟨ha,hb⟩
          exact ⟨ha,fun _ => not_le.mpr hb⟩
      rw [hcm,he]
      exact (outside_mass_bound (F t) (fun a => (y a:ℝ)) (fun a => dist (s t) (i a))
        (fun a _ => (hy' a).le) (fun _ _ => dist_nonneg)).trans_eq (hv' t)
  have hsmall : ∀ t, (c t:ℝ) ≤ 1/((M:ℝ)*(δ:ℝ)) := by
    intro t
    by_cases ht : next d t=t
    · rw [hzero t ht,Rat.cast_zero]
      positivity
    · have hVL : (M:ℝ)*(V t:ℝ)<dist (s t) (s (next d t)) := by
        rw [hd]
        exact_mod_cast hL t ht
      have hLp : 0 < dist (s t) (s (next d t)) :=
        (mul_nonneg hM'.le (hV t)).trans_lt hVL
      exact deficit_small hM' hδ' hLp (hcharge t) hVL.le
  refine {
    P := P
    A := A
    p := fun t => (p t:ℝ)
    c := fun t => (c t:ℝ)
    L := fun t => dist (s t) (s (next d t))
    next := next d
    sub := hsub
    missing := fun _ => rfl
    mass := fun t => (hpm t).symm
    deficit_mass := fun t => (hcm t).symm
    unit := hunit
    nonneg := hc
    small := hsmall
    large := fun t => by linarith only [hunit t,hsmall t]
    disjoint := ?_
    next_distance := fun _ => rfl
    closest := ?_
    radius := ?_
    outside_radius := ?_
    self_singleton := next_self d
    self_zero := by intro t ht; rw [hzero t ht,Rat.cast_zero]
    zero_full := ?_
    charge := hcharge }
  · intro t u htu
    apply disjoint_left.mpr
    intro a ha hb
    have ht : next d t≠t := fun hh => htu ((next_self d t hh u).symm)
    have hu : next d u≠u := fun hh => htu (next_self d u hh t)
    have hdist : 0 < dist (s t) (s u) := by
      rw [hd]
      have hh : (M:ℝ)*max (V t:ℝ) (V u:ℝ) < (d t u:ℝ) := by exact_mod_cast hs t u htu
      exact (mul_nonneg hM'.le ((hV t).trans (le_max_left _ _))).trans_lt hh
    have hta : (di t a:ℝ) ≤ (δ:ℝ)*(d t (next d t):ℝ) := by
      have h := (mem_filter.mp (show a ∈ (F t).filter (fun b => di t b ≤ δ*d t (next d t)) by
        simpa only [P,bundle,ite_eq_right ht] using ha)).2
      exact_mod_cast h
    have hua : (di u a:ℝ) ≤ (δ:ℝ)*(d u (next d u):ℝ) := by
      have h := (mem_filter.mp (show a ∈ (F u).filter (fun b => di u b ≤ δ*d u (next d u)) by
        simpa only [P,bundle,ite_eq_right hu] using hb)).2
      exact_mod_cast h
    exact bundle_disjoint_geometry (s t) (s u) (i a)
      (Ls := dist (s t) (s (next d t))) (Lt := dist (s u) (s (next d u))) hδ'.le hδ1 hdist
      (by rw [hd,hd]; exact_mod_cast next_min d t u htu)
      (by rw [dist_comm (s t) (s u),hd,hd]; exact_mod_cast next_min d u t htu.symm)
      (by rwa [hdi,hd]) (by rwa [hdi,hd])
  · intro t u htu
    rw [hd,hd]
    exact_mod_cast next_min d t u htu
  · intro t ht a ha
    have h := (mem_filter.mp (show a ∈ (F t).filter (fun b => di t b ≤ δ*d t (next d t)) by
      simpa only [P,bundle,ite_eq_right ht] using ha)).2
    rw [hdi,hd]
    exact_mod_cast h
  · intro t ht a ha
    have h := mem_sdiff.mp ha
    have hh : ¬ di t a ≤ δ*d t (next d t) := by
      intro hh
      apply h.2
      simp only [bundle,ite_eq_right ht,mem_filter]
      exact ⟨h.1,hh⟩
    rw [hdi,hd]
    exact_mod_cast lt_of_not_ge hh
  · intro t ht
    apply Subset.antisymm (hsub t)
    intro a ha
    by_contra hpa
    have hle : (y a:ℝ) ≤ (c t:ℝ) := by
      rw [hcm]
      exact single_le_sum (fun b _ => (hy' b).le) (mem_sdiff.mpr ⟨ha,hpa⟩)
    rw [ht] at hle
    exact not_lt_of_ge hle (hy' a)

end MetricKMedian.Preparation.RationalBundles
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem used_tuple (S : Finset (Fin n)) (hS : S.card ≤ d) : used (tuple (d := d) S)=S := by
  ext x
  simp only [used,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,ha⟩
    dsimp only [tuple] at ha
    split_ifs at ha with h
    · have he : S.orderEmbOfFin rfl ⟨a.val,h⟩=x := Fin.ext ha
      rw [← he]
      exact orderEmbOfFin_mem _ _ _
    · exact False.elim ((Nat.ne_of_gt x.isLt) ha)
  · intro hx
    let a : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x,hx⟩
    have ha : a.val < d := lt_of_lt_of_le a.isLt hS
    refine ⟨⟨a.val,ha⟩,?_⟩
    dsimp only [tuple]
    rw [dite_eq_left a.isLt]
    change (S.orderEmbOfFin rfl a).val=x.val
    have he := (S.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩
    exact congrArg (fun z : S => (z.val:Fin n).val) he

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Instance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem feasible_nonempty (I : Instance) : (feasibleSets I).Nonempty := by
  obtain ⟨i,hi⟩ := I.facilities_nonempty
  refine ⟨{i},mem_filter.mpr ⟨mem_powerset.mpr ?_,singleton_nonempty _,?_⟩⟩
  · exact singleton_subset_iff.mpr hi
  · simpa only [card_singleton] using I.k_pos

theorem mem_feasible (I : Instance) (S : Finset (Fin I.n)) :
    S ∈ feasibleSets I ↔ S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k := by
  simp only [feasibleSets,mem_filter,mem_powerset]

theorem nearest_nonneg (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) :
    0 ≤ nearest I j S := by
  unfold nearest
  split_ifs with hS
  · apply le_min'
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact_mod_cast I.distance_nonneg j i
  · exact le_rfl

theorem nearest_attained (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n))
    (hS : S.Nonempty) : ∃ i ∈ S, nearest I j S=(I.distance j i:ℝ) := by
  have hm := min'_mem (S.image (fun i => (I.distance j i:ℝ))) (hS.image _)
  obtain ⟨i,hi,he⟩ := mem_image.mp hm
  exact ⟨i,hi,by rw [nearest,dite_eq_left hS]; exact he.symm⟩

theorem cost_nonneg (I : Instance) (S : Finset (Fin I.n)) : 0 ≤ cost I S :=
  sum_nonneg (fun j _ => I.nearest_nonneg j S)

theorem optimum_attained (I : Instance) :
    ∃ S, S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S=optimum I := by
  have hS := I.feasible_nonempty
  have hm := min'_mem ((feasibleSets I).image (cost I)) (hS.image _)
  obtain ⟨S,hSf,he⟩ := mem_image.mp hm
  obtain ⟨hsub,hne,hcard⟩ := (I.mem_feasible S).mp hSf
  exact ⟨S,hsub,hne,hcard,by rw [optimum,dite_eq_left hS]; exact he⟩

theorem optimum_nonneg (I : Instance) : 0 ≤ optimum I := by
  obtain ⟨S,_,_,_,he⟩ := I.optimum_attained
  rw [← he]
  exact I.cost_nonneg S

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalGeometryScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset SupplierStars RationalSuppliers
variable {f n j : ℕ} {X : Type} [PseudoMetricSpace X]

 theorem valid (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ) (V : Fin n → ℚ) (M δ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) :
    let P := bundle d di F δ;
    let A := missing d di F δ;
    (∀ t, 0 < mass y P t) ∧ Pairwise (fun t u => Disjoint (P t) (P u)) ∧
    (∀ t, 0 ≤ mass y A t) ∧ (∀ t, mass y A t ≤ 1/8) ∧
    (∀ t, mass y P t+mass y A t=1) := by
  intro P A
  let G := geometry F y s i d di V M δ hd hdi hy hM hδ hδ1 hu hv hs
  have hc : ∀ t, (mass y A t:ℝ) ≤ 1/8 := fun t => (G.small t).trans hθ
  have hu' : ∀ t, (mass y P t:ℝ)+(mass y A t:ℝ)=1 := G.unit
  refine ⟨?_,G.disjoint,?_,?_,?_⟩
  · intro t
    have h := hc t
    have h' := hu' t
    have hp : (0:ℝ) < mass y P t := by linarith only [h,h']
    exact_mod_cast hp
  · intro t
    have h := G.nonneg t
    change (0:ℝ) ≤ (mass y A t:ℝ) at h
    exact_mod_cast h
  · intro t
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hc t
  · intro t
    exact_mod_cast hu' t

def suppliers (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ) (V : Fin n → ℚ) (M δ γ : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hy : ∀ a, 0 < y a) (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) < 1/2)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1)
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u) : RationalSuppliers.Data f n :=
  let h := valid F y s i d di V M δ hd hdi hy hM hδ hδ1 hθ hu hv hs
  {y:=y, P:=bundle d di F δ, A:=missing d di F δ,
   p:=mass y (bundle d di F δ), c:=mass y (missing d di F δ), γ:=γ,
   hy:=fun a => (hy a).le, hp:=h.1, hP:=h.2.1, hm:=fun _ => rfl, hc:=fun _ => rfl,
   hc0:=h.2.2.1, hc1:=h.2.2.2.1, hunit:=h.2.2.2.2,hγ:=hγ,hγ1:=hγ1}

end MetricKMedian.Preparation.RationalBundles
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation.RationalRepresentatives
open Finset
variable {n : ℕ}

def select (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ) :
    ℕ → Finset (Fin n) → Finset (Fin n)
  | 0, _ => ∅
  | k+1, U => if hU : U.Nonempty then
      let s := firstNearest U V hU
      insert s (select d V M k (U.filter (fun j => M*V j < d j s)))
    else ∅

def representatives (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ) : Finset (Fin n) :=
  select d V M n univ

end MetricKMedian.Preparation.RationalRepresentatives
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalUnitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

def V (c : Fin j) : ℚ := ∑ a ∈ U.F c, U.y a*U.dc c a

theorem V_nonneg (c : Fin j) : 0≤U.V c :=
  sum_nonneg (fun a _ => mul_nonneg (U.hy a).le (U.hdc c a))

def representatives (M : ℚ) := RationalRepresentatives.representatives U.dd U.V M

def ridx (M : ℚ) : Fin (U.representatives M).card → Fin j :=
  (U.representatives M).orderEmbOfFin rfl

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.LPBinary
open Finset

namespace Truncated

def row (ds : Row) (H : ℚ) : Row := ds.map (fun d => if d≤1 then d else H)
end Truncated
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair

def opening (ys : Row) (ρ : ℚ) : Row := ys.map (fun y => min 1 (y/(1-ρ)))
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_RationalArgmin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

theorem rationalArgmin_spec (A : Finset ℚ) (f : ℚ → ℚ) (hA : A.Nonempty) :
    rationalArgmin A f ∈ A ∧ ∀ t ∈ A, f (rationalArgmin A f) ≤ f t := by
  let v := (A.image f).min' (hA.image f)
  let B := A.filter (fun t => f t=v)
  have hB : B.Nonempty := by
    obtain ⟨t,ht,he⟩ := mem_image.mp (min'_mem (A.image f) (hA.image f))
    exact ⟨t,mem_filter.mpr ⟨ht,he⟩⟩
  have heq : rationalArgmin A f=B.min' hB := by
    simp only [rationalArgmin,dite_eq_left hA]
    change (if h : B.Nonempty then B.min' h else 0)=_
    rw [dite_eq_left hB]
  rw [heq]
  obtain ⟨h1,h2⟩ := mem_filter.mp (min'_mem B hB)
  refine ⟨h1,?_⟩
  intro t ht
  rw [h2]
  exact min'_le (A.image f) _ (mem_image_of_mem f ht)

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_BudgetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

def restrictFacilities (I : Instance) (F : Finset (Fin I.n)) (hF : I.k ≤ F.card) : Instance :=
  { I with facilities := F, k_le := hF }

end Instance

end MetricKMedian
end
end

end OAI
end


