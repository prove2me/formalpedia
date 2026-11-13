-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
-- name    : OddOrder_Peterfalvi_S09_FrobeniusConjIndex
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:21:07.938624+00:00
-- url     : https://prove2.me/theorems/3c9f69a7-8720-40a8-989a-1bf6fd77b1b4
-- title:
--   The conjugate family index for a Frobenius member (Peterfalvi (7.9))
-- statement:
--   Discharges the residual conjugate-index inputs of the (7.9) cross-orthogonality at the Frobenius level. The distinguished $\zeta=\zeta_0=\mathrm{Ind}_K^L\theta_0$ has complex conjugate $\bar\zeta=\mathrm{Ind}_K^L\theta_0^*$.
--
--   Main results: `hypothesis78_sourceSet_eq` (the (7.8) coherent source set equals the Sibley family $S$), `hypothesis78_isCoherent_sourceSet` (the Frobenius coherence as an `IsCoherent` over the (7.8) source set) and `hypothesis78_betaDecomp` (the (7.8.a) `BetaDecomp` for the $i$-th Frobenius member).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusConjIndex.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis79
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusEstimate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordDecomposition

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The distinguished `ζ` is irreducible** (Frobenius-kernel induction).  `ζ_0 = Ind_K(θ_0)` with
`θ_0 ≠ 1_K`, so it is irreducible by `isIrreducibleCharacter_induce_of_frobeniusGroup`. -/
theorem hypothesis78_zeta_irreducible [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    IsIrreducibleCharacter ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
      (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct) := by
  classical
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hθ0_ne : pf.θ 0 ≠ trivialIrreducibleCharacter _ := by
    intro h
    refine pf.ind1H_ne_zero (pf.inj ?_).symm
    simp only [h, pf.triv]
  have hzd : (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 := rfl
  rw [hzd, congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) 0]
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hFrob (pf.θ 0) hθ0_ne

open OddOrder.Peterfalvi.S09.Cert in
/-- **The `(7.8)` coherent source set equals the Sibley family `S`.**  Both `sourceSet =
{ζ_i | i ≠ ind1H} = {Ind θ_i | θ_i ≠ 1_K}` and `S = {Ind θ | θ ≠ 1_K}` coincide: `⊆` since
`θ_i ≠ 1_K` for `i ≠ ind1H`; `⊇` since every `Ind θ` is `Ind θ_j` (`cover`) with `j ≠ ind1H`
(else `Ind θ = Ind 1_K`, contra `induce_ne_trivialChar_induce`).
Lets `F.coherence` (an `IsCoherent` over `S`) be transported to the `sourceSet` the (7.9) machinery
expects. -/
theorem hypothesis78_sourceSet_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).sourceSet
      = (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
  classical
  have hθ_ne : ∀ j, j ≠ (F.sibleyPlacedFamily i hodd hnilp C hFrob).ind1H →
      (F.sibleyPlacedFamily i hodd hnilp C hFrob).θ j ≠ trivialIrreducibleCharacter _ := by
    intro j hj h
    refine hj ((F.sibleyPlacedFamily i hodd hnilp C hFrob).inj ?_)
    simp only [h, (F.sibleyPlacedFamily i hodd hnilp C hFrob).triv]
  ext φ
  constructor
  · rintro ⟨idx, hidx, rfl⟩
    rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) idx]
    exact ⟨(F.sibleyPlacedFamily i hodd hnilp C hFrob).θ idx, hθ_ne idx hidx, rfl⟩
  · rintro ⟨θ', hθ'_ne, rfl⟩
    obtain ⟨j, hj⟩ := (F.sibleyPlacedFamily i hodd hnilp C hFrob).cover θ'
    have hj' : ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        ((F.sibleyPlacedFamily i hodd hnilp C hFrob).θ j : ClassFunction _ ℂ)
      = ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ' : ClassFunction _ ℂ) := hj
    refine ⟨j, ?_, ?_⟩
    · intro hjind
      apply induce_ne_trivialChar_induce ((F.H i).subgroupOf (F.L i)) θ' hθ'_ne
      rw [← hj', show j = (F.sibleyPlacedFamily i hodd hnilp C hFrob).ind1H from hjind,
        (F.sibleyPlacedFamily i hodd hnilp C hFrob).triv]
    · rw [congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) j]; exact hj'

/-- **`F.coherence` as an `IsCoherent` over the `(7.8)` `sourceSet`.**  Transports the Sibley
coherence (over `S`) to `sourceSet = S` (`hypothesis78_sourceSet_eq`), keeping the same
`extension = ν` — so `hnu` stays `hypothesis78_nu_eq`.  The `hcoh` input of
`zetaImage_cross_eq_zero_of_conjIndex`. -/
noncomputable def hypothesis78_isCoherent_sourceSet [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau
      (F.hypothesis78 i hodd hnilp C hFrob).sourceSet
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i)) := by
  have hS := F.hypothesis78_sourceSet_eq i hodd hnilp C hFrob
  exact
    { nonzero := hS.symm ▸ (F.coherence i hodd hnilp C hFrob).nonzero
      extension := (F.coherence i hodd hnilp C hFrob).extension
      extension_inner_eq := fun φ ψ hφ hψ =>
        (F.coherence i hodd hnilp C hFrob).extension_inner_eq φ ψ (hS ▸ hφ) (hS ▸ hψ)
      extends_on_supported := fun φ hφ =>
        (F.coherence i hodd hnilp C hFrob).extends_on_supported φ (hS ▸ hφ)
      extension_mem_ZIrr := fun φ hφ =>
        (F.coherence i hodd hnilp C hFrob).extension_mem_ZIrr φ (hS ▸ hφ) }

open OddOrder.Peterfalvi.S09.Cert in
/-- **The (7.8.a) `BetaDecomp` for the `i`-th Frobenius member.**  Built via the abstract
`betaDecompOfFacts`, discharging its facts from the induced family `ζ_j = Ind_K θ_j`
(`hypothesis78_hyp76_zeta_eq` projection): orthogonality (`induce_family_orthogonal_of_injective`),
norms (`induce_norm_ne_zero`), degree reality (`induce_apply_one_star`), the Dade agreement
(`coherence_hagree_dadeMap`), `⟨ζ_0^ν, 1_G⟩ = 0` (`F.hzeta0nu`), `⟨ζ_i, 1_L⟩ = 0` for `i ≠ ind1H`
(`inner_induce_constOne_eq_zero`), and `⟨β, 1_G⟩ = 1`.  The `hBD` input of the (7.9) conclusion. -/
noncomputable def hypothesis78_betaDecomp [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).BetaDecomp := by
  classical
  set pf := F.sibleyPlacedFamily i hodd hnilp C hFrob with hpf
  -- Family projection `ζ_a = Ind_K θ_a`, and `θ_j ≠ 1_K` for `j ≠ ind1H`.
  have hzeta : ∀ a, (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta a
      = ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (pf.θ a : ClassFunction _ ℂ) :=
    fun a => congrFun (F.hypothesis78_hyp76_zeta_eq i hodd hnilp C hFrob) a
  have hθ_ne : ∀ j, j ≠ pf.ind1H →
      pf.θ j ≠ trivialIrreducibleCharacter _ := by
    intro j hj h
    refine hj (pf.inj ?_)
    simp only [h, pf.triv]
  -- `hz0`, `hζ0norm`, `hindZ`, and `a`/`ha`.
  have hz0 : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0 (1 : ↥(F.L i)) ≠ 0 := by
    rw [hzeta 0]; exact induce_apply_one_ne_zero ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
  have hζ0norm : ClassFunction.inner
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0)
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0) = 1 := by
    have := (F.hypothesis78_zeta_irreducible i hodd hnilp C hFrob)
    rw [show (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct = 0 from rfl] at this
    exact IsIrreducibleCharacter.inner_self_eq_one this
  have hindZ : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).ind1H
      - (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct ∈ ZIrr ↥(F.L i) := by
    rw [hzeta, hzeta]
    exact Submodule.sub_mem _
      (ClassFunction.induce_mem_ZIrr _ (pf.θ _).property.mem_ZIrr)
      (ClassFunction.induce_mem_ZIrr _ (pf.θ _).property.mem_ZIrr)
  have hζ0nuZ : (F.hypothesis78 i hodd hnilp C hFrob).nu
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
        (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct) ∈ ZIrr G :=
    (F.hypothesis78 i hodd hnilp C hFrob).nu_zetaDistinct_mem_ZIrr_of_isCoherent
      (F.hypothesis78_isCoherent_sourceSet i hodd hnilp C hFrob)
      (F.hypothesis78_nu_eq i hodd hnilp C hFrob)
  refine betaDecompOfFacts (F.hypothesis78 i hodd hnilp C hFrob) rfl ?_ ?_ hz0 ?_ ?_ ?_ ?_ ?_
    hζ0norm
    (Classical.choose (exists_betaDecomp_a (F.hypothesis78 i hodd hnilp C hFrob) hindZ hζ0nuZ))
    (Classical.choose_spec (exists_betaDecomp_a (F.hypothesis78 i hodd hnilp C hFrob) hindZ hζ0nuZ))
  · -- horth: distinct induced irreducibles are orthogonal.
    intro a b hab
    rw [hzeta a, hzeta b]
    exact induce_family_orthogonal_of_injective ((F.H i).subgroupOf (F.L i)) pf.θ
      pf.inj a b hab
  · -- hN
    intro j; rw [hzeta j]
    exact induce_norm_ne_zero ((F.H i).subgroupOf (F.L i)) (pf.θ j)
  · -- hP_real
    intro j; rw [hzeta j]
    exact induce_apply_one_star ((F.H i).subgroupOf (F.L i)) (pf.θ j)
  · -- hagree: coherence extension agrees with τ on the equal-degree difference.
    intro j hj0 hjind
    have hSj : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j
        ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S :=
      ⟨pf.θ j, hθ_ne j hjind, hzeta j⟩
    have hS0 : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0
        ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S :=
      ⟨pf.θ 0,
        hθ_ne 0 (Ne.symm pf.ind1H_ne_zero), hzeta 0⟩
    obtain ⟨deg_j, -, hdegj⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (pf.θ j)
    obtain ⟨deg_0, hdeg0_pos, hdeg0⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (pf.θ
        (0 : Fin ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.n + 1)))
    have hdeg0_ne : (deg_0 : ℂ) ≠ 0 := by exact_mod_cast hdeg0_pos.ne'
    have hidxC : (((F.H i).subgroupOf (F.L i)).index : ℂ) ≠ 0 := by
      exact_mod_cast Subgroup.index_ne_zero_of_finite
    have hzj1 : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta j (1 : ↥(F.L i))
        = (((F.H i).subgroupOf (F.L i)).index : ℂ) * (deg_j : ℂ) := by
      rw [hzeta j, ClassFunction.induce_apply_one, hdegj]
    have hz01 : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta 0 (1 : ↥(F.L i))
        = (((F.H i).subgroupOf (F.L i)).index : ℂ) * (deg_0 : ℂ) := by
      rw [hzeta 0, ClassFunction.induce_apply_one, hdeg0]
    have hd : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.d j = (deg_j : ℂ) / (deg_0 : ℂ) := by
      have h1 := (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta_one_eq_d_mul j
      rw [hzj1, hz01] at h1
      rw [eq_div_iff hdeg0_ne]
      apply mul_left_cancel₀ hidxC
      linear_combination -h1
    have hres := coherence_hagree_dadeMap
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
      (F.coherence i hodd hnilp C hFrob) hSj hS0 (m0 := deg_0) (mi := deg_j) hdeg0_ne hd
      ((F.hypothesis78 i hodd hnilp C hFrob).hyp76.psi_support j)
    rw [F.hypothesis78_nu_eq i hodd hnilp C hFrob]
    exact hres
  · -- hzeta0nu
    rw [F.hypothesis78_nu_eq i hodd hnilp C hFrob, hzeta 0]
    exact F.hzeta0nu i hodd hnilp C hFrob (pf.θ 0)
      (hθ_ne 0 (Ne.symm pf.ind1H_ne_zero))
  · -- hzeta_orth_one
    intro j hj; rw [hzeta j]
    exact inner_induce_constOne_eq_zero ((F.H i).subgroupOf (F.L i)) (pf.θ j)
      (hθ_ne j hj)
  · -- hβ1
    have hz_ind : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).ind1H
        = ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) : ClassFunction _ ℂ) := by
      rw [hzeta, show (F.hypothesis78 i hodd hnilp C hFrob).ind1H
          = pf.ind1H from rfl,
        pf.triv]
    have hz_zd : (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
          (F.hypothesis78 i hodd hnilp C hFrob).zetaDistinct
        = ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (pf.θ 0 : ClassFunction _ ℂ) := hzeta _
    rw [(F.hypothesis78 i hodd hnilp C hFrob).beta_def, inner_tau_supported_constOne,
      ClassFunction.inner_sub_left, hz_ind, hz_zd, inner_induce_trivialChar_constOne_eq_one,
      inner_induce_constOne_eq_zero ((F.H i).subgroupOf (F.L i)) (pf.θ 0)
        (hθ_ne 0 (Ne.symm pf.ind1H_ne_zero)), sub_zero]

end FrobeniusFamily

end OddOrder.Peterfalvi.S09


