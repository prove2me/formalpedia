-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusEstimate
-- name    : OddOrder_Peterfalvi_S09_FrobeniusEstimate
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:18:55.19821+00:00
-- url     : https://prove2.me/theorems/fab2f944-fd5d-419e-8102-cabeecdc4c8c
-- title:
--   Peterfalvi (7.8.b) for a Frobenius family: the $\zeta$-norm estimate
-- statement:
--   Downstream of the per-member Hypothesis78: the (7.8.b) norm bound $1-e_i/h_i\le$ `zetaNuRhoNormSq` for each Frobenius family member, on the way to the lower bound on $|G_0|$ in the (7.10) character estimate.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusEstimate.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusEstimate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis78
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09.Cert

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **Peterfalvi (7.8.a) for the `i`-th Frobenius member: `⟨ζ_0^ν, 1_G⟩ = 0`** (`hzeta0nu`, the last
`zetaNuRhoNormSqGeOfDade` input).  The abstract `IsCoherent` does not carry orthogonality to `1_G`,
but it is recovered from the **complex conjugate** `ζ̄_0 = Ind θ̄_0 ∈ S` — a second member of the
*same degree*, distinct from `ζ_0` because `L_i` has odd order (no nontrivial real irreducible), so
`⟨ζ_0, ζ̄_0⟩ = 0` (`inner_induce_conj_eq_zero_of_frobenius_of_odd`).
`coherence_extension_orthogonal_constOne` then forces `⟨ν ζ_0, 1_G⟩ = 0`.  Mirrors
`S14.witness_L_hzeta0nu`; holds for **any** nontrivial `θ_0`. -/
theorem hzeta0nu [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)
    (θ0 : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)))
    (hθ0 : θ0 ≠ trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i))) :
    ClassFunction.inner
        ((F.coherence i hodd hnilp C hFrob).extension
          (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ)))
        (Hypothesis71.constOne G) = 0 := by
  classical
  have hoddL : Odd (Nat.card ↥(F.L i)) :=
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
  have hKnorm : ((F.H i).subgroupOf (F.L i)).Normal := hFrob.isNormal
  -- Introduce `θ̄_0` **opaquely** (via `obtain`, not `let`) carrying only `↑θ̄_0 = (↑θ_0)‾`, so its
  -- coercion is not re-unfolded inside every `induce` coset sum (whnf-budget protection).
  obtain ⟨θ0', hθ0'coe⟩ :
      ∃ t : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)),
        (t : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)
          = (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ).conj :=
    ⟨⟨(θ0 : ClassFunction _ ℂ).conj, θ0.isIrreducible.conj⟩, rfl⟩
  have hθ0' : θ0' ≠ trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) := by
    intro h
    apply hθ0
    have hcoe : (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ).conj
        = trivialClassFunction ↥((F.H i).subgroupOf (F.L i)) := by
      rw [← hθ0'coe]
      have h2 := congrArg
        (fun c : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) =>
          (c : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)) h
      simpa using h2
    apply Subtype.ext
    change (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)
      = trivialClassFunction ↥((F.H i).subgroupOf (F.L i))
    rw [← ClassFunction.conj_conj (θ0 : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ), hcoe]
    exact trivialClassFunction_isReal
  -- The two members `ζ_0 = Ind θ_0`, `ζ̄_0 = Ind θ̄_0 ∈ S`.
  have hmem0 : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ)
      ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := ⟨θ0, hθ0, rfl⟩
  have hmem0' : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)
      ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := ⟨θ0', hθ0', rfl⟩
  -- Norms `= 1` (Frobenius), orthogonality to `1_L`.
  have hnorm0 := inner_self_induce_eq_one_of_frobeniusGroup hFrob θ0 hθ0
  have hnorm0' := inner_self_induce_eq_one_of_frobeniusGroup hFrob θ0' hθ0'
  have h1_0 := inner_induce_constOne_eq_zero ((F.H i).subgroupOf (F.L i)) θ0 hθ0
  have h1_0' := inner_induce_constOne_eq_zero ((F.H i).subgroupOf (F.L i)) θ0' hθ0'
  -- `⟨ζ_0, ζ̄_0⟩ = 0` (odd-order Frobenius: `ζ_0` non-real), via the general helper.
  have horth : ClassFunction.inner
      (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ))
      (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)) = 0 := by
    rw [hθ0'coe]
    exact inner_induce_conj_eq_zero_of_frobenius_of_odd hoddL hFrob θ0 hθ0
  -- The type-I support `A(L_i) = H_i^#`.
  have hAH : OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))
      = (F.H i : Set G) \ {1} := F.sharpImage_subgroupOf_eq i
  -- The equal-degree difference `ζ̄_0 − ζ_0` is `H_i^#`-supported.
  have hdeg' : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)
        (1 : ↥(F.L i))
      = 1 * ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0 : ClassFunction _ ℂ)
        (1 : ↥(F.L i)) := by
    rw [one_mul, ClassFunction.induce_apply_one, ClassFunction.induce_apply_one]
    congr 1
    rw [hθ0'coe, ClassFunction.conj_apply]
    obtain ⟨m, -, hm⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ0
    rw [hm, star_natCast]
  have hsupp : (ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ0' : ClassFunction _ ℂ)
      - ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
    have hds := induce_diff_support (K := (F.H i).subgroupOf (F.L i)) θ0' θ0 1 hdeg'
    rw [one_smul] at hds
    intro x hx
    have hxd := hds hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hxd
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff (F.H i) hAH x).mpr ⟨hxd.1, hxd.2⟩
  -- The Dade `⊥ 1_G` transport and `ℂ`-linearity of `τ = sib.tau`.
  have htau1 : ∀ φ : ClassFunction ↥(F.L i) ℂ,
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) →
      ClassFunction.inner
          ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau φ)
          (Hypothesis71.constOne G)
        = ClassFunction.inner φ (Hypothesis71.constOne ↥(F.L i)) := by
    intro φ hφ
    rw [show (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau φ
        = (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade.dadeMap
          ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ from
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
        (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
        ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade.fullDadeIsometryData) hφ]
    exact inner_tau_supported_constOne (F.sibleyToHypothesis71 i hodd hnilp C hFrob)
      ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥(F.L i) ℂ),
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau (c • x)
        = c • (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).tau x :=
    dadeIntegralCharacterMap_smul_complex
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
      ((F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade.fullDadeIsometryData)
  exact coherence_extension_orthogonal_constOne (F.coherence i hodd hnilp C hFrob) hτ_smul htau1
    hmem0 hmem0' hnorm0 hnorm0' horth hsupp h1_0 h1_0'

end FrobeniusFamily

end OddOrder.Peterfalvi.S09


