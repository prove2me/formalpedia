-- Prove2me | Definitions.Def_OAIQ053K031
-- name    : OAIQ053K031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:59:41.627959+00:00
-- url     : https://prove2.me/theorems/24942020-8e6b-4319-9962-1b0612ba977f
-- title:
--   Definitions bundle OAIQ053K031 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 18 definitions, 1 inductive type or structure and 19 theorems. The definitions and types are `OAI.MetricKMedian.IntegerLaw.prod`, `OAI.MetricKMedian.Preparation.RationalBundles.bundle`, `OAI.MetricKMedian.Preparation.RationalBundles.geometry`, `OAI.MetricKMedian.Preparation.RationalBundles.missing`, `OAI.MetricKMedian.Preparation.RationalSuppliers.counts`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input`, `OAI.MetricKMedian.Preparation.RationalUnitInput.representatives`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ridx`, `OAI.MetricKMedian.RationalLaw.sigma`, `OAI.MetricKMedian.RationalPhysicalKernel.enumeration`, `OAI.MetricKMedian.RationalPhysicalKernel.updateEvent`, `OAI.MetricKMedian.SparseHistories.branch`, `OAI.MetricKMedian.SparseHistories.tree`, `OAI.MetricKMedian.SparseIntegerLaw.bindIndexed`, `OAI.MetricKMedian.SparseIntegerLaw.fair`, `OAI.MetricKMedian.SparseIntegerLaw.mix`, `OAI.MetricKMedian.SparseIntegerLaw.prod`, `OAI.MetricKMedian.SparseOuterLaw.outsideCount`, `OAI.MetricKMedian.SparseSelect.choose`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Geometry_ComputedRationalCompression`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_RationalBundleGeometry`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseHistories`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseMixture`, `KMedian_Sparse_SparseMomentAlgebra`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseProduct`, `KMedian_Sparse_SparseSelect`, `KMedian_Sparse_SparseSupplierSupport`, `KMedian_Sparse_SparseSupport`.
--
--   **Imports.** It imports the bundles `OAIQ053K015`, `OAIQ053K016`, `OAIQ053K017` and `OAIQ053K018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K039`, `OAIQ053K040`, `OAIQ053K041`, `OAIQ053K042` and `OAIQ053K043`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016
import Definitions.Def_OAIQ053K017
import Definitions.Def_OAIQ053K018

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_ComputedRationalCompression
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset

theorem scaledFeatures_bound {n d : ℕ} (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    ∀ i j, |scaledFeatures v i j| ≤ (2:ℤ)^(L*(n+1)) := by
  intro i j
  rw [scaledFeatures_eq]
  simpa only [Fintype.card_fin] using RationalScaling.numerator_bound (fun i => v i j) L
    (fun i => hnum i j) (fun i => hden i j) i

end MetricKMedian.RationalLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_IntegerBranching
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.eliminateAt_numerator _root_.OAI.MetricKMedian.IntegerLaw.mem_support _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight _root_.OAI.MetricKMedian.RationalLaw.integer_numerator_zero _root_.OAI.MetricKMedian.RationalLaw.integer_weight _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.RationalLaw.scaledFeatures_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerBranching
open Finset
variable {n : ℕ}

theorem branch_moment (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (f : Fin n → Fin 2 → ℚ) :
    (∑ a, (branch μ p hp).rational.weight a*f a.1 a.2)=
      ∑ i, μ.rational.weight i*(p i*f i 0+(1-p i)*f i 1) := by
  have hD : (RationalScaling.denominator p:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos p).ne'
  have hM : (μ.denominator:ℚ) ≠ 0 := by exact_mod_cast μ.denominator_pos.ne'
  simp only [IntegerLaw.rational,branch,Vector.getElem_ofFn,Fin.eta]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,branchNumerator]
  norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
  simp only [Int.cast_mul,Int.cast_sub,RationalScaling.numerator_cast]
  apply sum_congr rfl
  intro i _
  field_simp

end MetricKMedian.IntegerBranching

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalBundleGeometry
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset
variable {n m : ℕ}

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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitInput
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliFeatures
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem target_succ (p : Fin n → ℚ) (t : ℕ) (ht : t<n) (f : Fin d → Fin (n+1)) :
    target p (t+1) f=
      if (⟨t,ht⟩ : Fin n) ∈ used f then p ⟨t,ht⟩*target p t (without f ⟨t,ht⟩)
      else target p t f := by
  let i : Fin n := ⟨t,ht⟩
  have val_ne : ∀ x : Fin n, x ≠ i → x.val ≠ t := fun x h he => h (Fin.ext he)
  by_cases hi : i ∈ used f
  · rw [ite_eq_left hi]
    unfold target
    rw [used_without,← mul_prod_erase (used f) (fun x => if x.val<t+1 then p x else 0) hi]
    simp only [i,show t<t+1 by omega,ite_eq_left]
    congr 1
    apply prod_congr rfl
    intro x hx
    have hn := val_ne x (mem_erase.mp hx).1
    have he : x.val<t+1 ↔ x.val<t := by omega
    simp only [he]
  · rw [ite_eq_right hi]
    unfold target
    apply prod_congr rfl
    intro x hx
    have hn := val_ne x (fun (he : x=i) => hi (he ▸ hx))
    have he : x.val<t+1 ↔ x.val<t := by omega
    simp only [he]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseAlgorithm
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem branch_moment (μ : SparseIntegerLaw α) (p : α → ℚ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) (f : α → ℚ) :
    (μ.branch p hp next).moment f=
      μ.moment (fun a => p a*f (next a 0)+(1-p a)*f (next a 1)) := by
  let ρ := IntegerBranching.branch μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val])
  have h := ρ.reindex_moment finProdFinEquiv
    (fun a => f (next μ.states[a.1.val] a.2))
  have h' := IntegerBranching.branch_moment μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val]) (fun i b => f (next μ.states[i.val] b))
  unfold moment branch
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1
  all_goals try with_reducible_and_instances rfl

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMarginalTools
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 theorem moment_congr (μ : SparseIntegerLaw α) (f g : α → ℚ)
    (h : ∀ i : Fin μ.length, f μ.states[i.val]=g μ.states[i.val]) :
    μ.moment f=μ.moment g := by
  apply sum_congr rfl
  intro i _
  rw [h i]

 theorem dirac_moment (a : α) (f : α → ℚ) : (dirac a).moment f=f a := by
  change (∑ _i : Fin 1, ((1:ℤ):ℚ)/1*f a)=f a
  simp

 theorem dirac_states (a : α) (i : Fin (dirac a).length) : (dirac a).states[i.val]=a := by
  simp [dirac]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMomentAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem moment_mul (μ : SparseIntegerLaw α) (c : ℚ) (f : α → ℚ) :
    μ.moment (fun a => c*f a)=c*μ.moment f := by
  simp only [moment,mul_left_comm,mul_sum]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBind
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset
variable {α : Type} {β : α → Type} [Fintype α] [∀ a, Fintype (β a)]

def sigma (μ : RationalLaw α) (κ : ∀ a, RationalLaw (β a)) : RationalLaw (Sigma β) where
  weight z := μ.weight z.1*(κ z.1).weight z.2
  nonneg z := mul_nonneg (μ.nonneg _) ((κ _).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp only [← mul_sum]
    calc
      _ = ∑ a, μ.weight a := sum_congr rfl (fun a _ => by rw [(κ a).total,mul_one])
      _ = 1 := μ.total

theorem sigma_moment (μ : RationalLaw α) (κ : ∀ a, RationalLaw (β a)) (f : Sigma β → ℚ) :
    (∑ z, (μ.sigma κ).weight z*f z)=
      ∑ a, μ.weight a*∑ b, (κ a).weight b*f ⟨a,b⟩ := by
  rw [Fintype.sum_sigma]
  simp only [sigma,mul_sum,mul_assoc]

end MetricKMedian.RationalLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) :
    SparseIntegerLaw β where
  length := ∑ a, (κ a).length
  states := Vector.ofFn (fun i => let z := finSigmaFinEquiv.symm i;
    (κ z.1).states[z.2.val])
  law := (μ.law.rational.sigma (fun a => (κ a).law.rational)).integer.reindex finSigmaFinEquiv

theorem bindIndexed_moment (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (f : β → ℚ) :
    (μ.bindIndexed κ).moment f=∑ a, μ.law.rational.weight a*(κ a).moment f := by
  let ρ := μ.law.rational.sigma (fun a => (κ a).law.rational)
  have h := ρ.integer.reindex_moment finSigmaFinEquiv
    (fun z => f (κ z.1).states[z.2.val])
  have h' := μ.law.rational.sigma_moment (fun a => (κ a).law.rational)
    (fun z => f (κ z.1).states[z.2.val])
  simp only [RationalLaw.integer_weight] at h
  unfold moment bindIndexed
  simp only [Vector.getElem_ofFn]
  convert h.trans h' using 1
  all_goals try with_reducible_and_instances rfl

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMixture
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def fair : SparseIntegerLaw (Fin 2) where
  length := 2
  states := Vector.ofFn id
  law := {
    denominator := 2
    denominator_pos := by norm_num
    numerator := fun _ => 1
    numerator_nonneg := fun _ => by norm_num
    total := by simp }

def mix (μ ν : SparseIntegerLaw α) : SparseIntegerLaw α :=
  fair.bindIndexed (fun a => if a.val=0 then μ else ν)

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseProduct
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.IntegerLaw
open Finset
variable {α β : Type} [Fintype α] [Fintype β]

def prod (μ : IntegerLaw α) (ν : IntegerLaw β) : IntegerLaw (α × β) where
  denominator := μ.denominator*ν.denominator
  denominator_pos := mul_pos μ.denominator_pos ν.denominator_pos
  numerator := fun a => μ.numerator a.1*ν.numerator a.2
  numerator_nonneg a := mul_nonneg (μ.numerator_nonneg _) (ν.numerator_nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp only [← mul_sum,ν.total,← sum_mul,μ.total]

@[simp] theorem prod_weight (μ : IntegerLaw α) (ν : IntegerLaw β) (a : α) (b : β) :
    (μ.prod ν).rational.weight (a,b)=μ.rational.weight a*ν.rational.weight b := by
  simp only [prod,rational,Int.cast_mul]
  exact mul_div_mul_comm _ _ _ _

end MetricKMedian.IntegerLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

def prod (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β) (f : α → β → γ) : SparseIntegerLaw γ where
  length := μ.length*ν.length
  states := Vector.ofFn (fun i => f μ.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).1.val]
    ν.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).2.val])
  law := (μ.law.prod ν.law).reindex (finProdFinEquiv (m := μ.length) (n := ν.length))

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSupport
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.prod_weight _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem zero_indicator (μ : SparseIntegerLaw α) (P : α → Prop) [DecidablePred P]
    (hz : μ.moment (fun x => if P x then 1 else 0)=0)
    (a : Fin μ.length) (ha : 0 < μ.law.rational.weight a) : ¬P μ.states[a.val] := by
  intro hpa
  have hs := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*(if P μ.states[i.val] then 1 else 0))
    (fun i _ => mul_nonneg (μ.law.rational.nonneg _) (by split_ifs <;> norm_num)) (mem_univ a)
  change _ ≤ μ.moment (fun x => if P x then 1 else 0) at hs
  rw [hz,ite_eq_left hpa,mul_one] at hs
  exact (not_lt_of_ge hs) ha

theorem one_indicator (μ : SparseIntegerLaw α) (P : α → Prop) [DecidablePred P]
    (hz : μ.moment (fun x => if P x then 1 else 0)=1)
    (a : Fin μ.length) (ha : 0 < μ.law.rational.weight a) : P μ.states[a.val] := by
  by_contra hn
  have hs := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1))
    (fun i _ => mul_nonneg (μ.law.rational.nonneg _) (by split_ifs <;> norm_num)) (mem_univ a)
  have hsum : (∑ i : Fin μ.length, μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1))=0 := by
    have hh : ∀ i : Fin μ.length,
        μ.law.rational.weight i*(if P μ.states[i.val] then 0 else 1)=
          μ.law.rational.weight i-μ.law.rational.weight i*(if P μ.states[i.val] then 1 else 0) := by
      intro i
      split_ifs <;> ring
    simp_rw [hh]
    rw [sum_sub_distrib,μ.law.rational.total]
    change 1-μ.moment (fun x => if P x then 1 else 0)=0
    rw [hz,sub_self]
  rw [hsum,ite_eq_right hn,mul_one] at hs
  exact (not_lt_of_ge hs) ha

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

def branch (κ : α → SparseIntegerLaw α) (h : History α) : SparseIntegerLaw (History α) :=
  (κ h.1).map (extend h)

def tree (κ : ℕ → α → SparseIntegerLaw α) (a : α) : ℕ → SparseIntegerLaw (History α)
  | 0 => .dirac (a,[])
  | t+1 => (tree κ a t).bindIndexed (fun i => branch (κ t) (tree κ a t).states[i.val])

end MetricKMedian.SparseHistories
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalKernel
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy
def enumeration (A : Finset (CopyState.Copy (F := F) Δ)) : Fin A.card ≃ A :=
  (Fintype.orderIsoFinOfCardEq A (Fintype.card_coe A)).toEquiv

def updateEvent (g β : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (e : RationalBatchData.Event A g β) : State F Δ g β := by
  obtain ⟨G,Z⟩ := e
  exact (RationalBatchData.transition A G
    (RationalBatchData.heavySet (RationalBatchData.graphMass G g) β) Z,
    some ⟨A,⟨G,Z⟩⟩)

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

def choose (μ : SparseIntegerLaw α) (P : α → Bool) (cost : α → ℚ) : Option α :=
  best P cost μ.states.toList

end MetricKMedian.SparseSelect
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedTerminal
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial _root_.OAI.MetricKMedian.SparseWeightedPartial.features_pair _root_.OAI.MetricKMedian.SparseWeightedPartial.features_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

theorem state_spec (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (hpair : ¬Active u p)
    (ω : Fin n → Bool)
    (hfixed : ∀ i, i∉fractional p → SparseBernoulli.flag ω i=point p i) :
    (∀ i, 0 ≤ point (state u p ω) i ∧ point (state u p ω) i ≤ 1) ∧
    (fractional (state u p ω)).card ≤ 1 ∧
    (∑ i, u i*point (state u p ω) i) ≤ (∑ i, u i*point p i)+1 := by
  let P := (fractional p).filter (fun i => 0 < u i)
  let N := (fractional p).filter (fun i => u i < 0)
  have hP : P.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact inactive u p hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have hN : N.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact inactive u p hpair i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij
      (mul_pos_of_neg_of_neg (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  have hq : ∀ i, 0 ≤ point (state u p ω) i ∧ point (state u p ω) i ≤ 1 := by
    intro i
    rw [point_state]
    split_ifs
    · exact hp i
    · cases hω : ω i <;> simp [SparseBernoulli.flag,hω]
  refine ⟨hq,?_,?_⟩
  · apply le_trans (card_le_card (show fractional (state u p ω) ⊆ N from ?_)) hN
    intro i hi
    have hneg : u i<0 := by
      by_contra hn
      have hh := (mem_filter.mp hi).2
      simp only [point_state,ite_eq_right hn] at hh
      cases hω : ω i <;> simp [SparseBernoulli.flag,hω] at hh
    exact mem_filter.mpr ⟨by
      simpa only [fractional,mem_filter,mem_univ,true_and,point_state,ite_eq_left hneg] using hi,hneg⟩
  · have hz : ∀ i, i ∉ P → u i*(point (state u p ω) i-point p i)=0 := by
      intro i hi
      by_cases hn : u i<0
      · simp only [point_state,ite_eq_left hn,sub_self,mul_zero]
      by_cases he : u i=0
      · rw [he,zero_mul]
      have hp' : 0 < u i := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
      have hnf : i ∉ fractional p := fun hf => hi (mem_filter.mpr ⟨hf,hp'⟩)
      simp only [point_state,ite_eq_right hn,hfixed i hnf,sub_self,mul_zero]
    have ht : ∀ i ∈ P, u i*(point (state u p ω) i-point p i) ≤ 1 := by
      intro i hi
      have hui := (mem_filter.mp hi).2
      calc
        _ ≤ u i*1 := mul_le_mul_of_nonneg_left (by linarith only [(hq i).2,(hp i).1]) hui.le
        _ ≤ 1 := by simpa only [mul_one] using hu i hui
    have hsum : (∑ i, u i*(point (state u p ω) i-point p i)) ≤ 1 := by
      rw [← sum_subset (subset_univ P) (fun i _ hi => hz i hi)]
      calc
        _ ≤ ∑ _i ∈ P, (1:ℚ) := sum_le_sum ht
        _ = (P.card:ℚ) := by simp only [sum_const,nsmul_eq_mul,mul_one]
        _ ≤ 1 := by exact_mod_cast hP
    simp only [mul_sub,sum_sub_distrib] at hsum
    linarith only [hsum]

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

def outsideCount (q : Fin m → ℚ) (z : State n m) (e : Fin m) : ℕ :=
  base q e+if 0 < point z.1 e then 1 else 0

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSupplierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

def counts (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ g : ℚ) (zG : SparseSignedPreparation.State n (size f n) × SparseCounts.Table f n)
    (a : Fin (f+n*f)) : ℕ :=
  Sum.elim (fun i => SparseOuterLaw.outsideCount (q y P A c γ g) zG.1 (index.symm (.inl i)))
    (fun ti => zG.2 ti.1 ti.2) (physicalIndex a)

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace FixedParameters
theorem positive {τ : ℝ} (qR : FixedBatch.RationalParameters τ) : 0<qR.g := by exact_mod_cast qR.gpos
end FixedParameters

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView indices)
open Program
structure Input where
  f : ℕ
  j : ℕ
  m : ℕ
  U : RationalUnitInput f j
  metric : PseudoMetricSpace (Fin m)
  R : @Realization f j U (Fin m) metric
  B : ℚ
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end


