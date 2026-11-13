-- Prove2me | Definitions.Def_OddOrder_FeitThompsonCharacterData
-- name    : OddOrder_FeitThompsonCharacterData
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T18:00:19.551255+00:00
-- url     : https://prove2.me/theorems/a2e51c87-8f78-4d1d-8b8e-a09decec8f42
-- title:
--   Feit–Thompson Section 16: character data
-- statement:
--   Formalizes the genuine Dade $\sigma$-integral on $W$, the aligned $\omega/\mu$ character grid, and the API consumed by the canonical Section 16 character-data producer (Peterfalvi §§3-13, pp. 5-68).
--
--   Main declarations: `tiCyclicW` (G-internal TI-cyclic structure (3.1)); `tiCyclicWDadeApp` (The full §4 Dade application for `tiCyclicW` (all local subgroups `H(a) = ⊥`, so…); `tau3W` (The (3.2) Dade σ-integral on `W = tp.W`); `omegaSChar` (The underlying linear character of `omegaS i j`, as a monoid hom of `↥tp.W`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonCharacterData.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/FeitThompsonCharacterData.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_FeitThompsonNuGrid
import Definitions.Def_OddOrder_Peterfalvi_S13_TypeDetermination
import Definitions.Def_OddOrder_FeitThompsonSetup
import Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

namespace Section16CharacterData

variable {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G)

variable (tp : Section16TypePStructure mp)

variable [NeZero (Nat.card ↥(mp.certainTypeS hG).W1)]

variable [NeZero (Nat.card ↥(mp.certainTypeT hG).W1)]

/-- The **G-internal TI-cyclic structure (3.1)** on `W = S ∩ T = mp.K ⊔ mp.Kstar`, supported on
the regular set `Ẑ = W ∖ (W₁ ∪ W₂)` (`= S14.zTilde mp.K mp.Kstar`); the TI-set fact is the proven
BG §14 `typeP_duality` (Theorem 14.7).  Extracted from `tau3W`'s local `let` as a top-level
definition so the (3.2) σ-isometry property package (`tau3W_isometry` etc., the issue-3002 grid
property supply) can be read off the `S05` lemmas. -/
noncomputable def tiCyclicW : OddOrder.Peterfalvi.S05.TICyclicHypothesis G :=
  { W := tp.W
    W1 := tp.W1
    W2 := tp.W2
    W1_le_W := by rw [tp.W_eq_join]; exact le_sup_left
    W2_le_W := by rw [tp.W_eq_join]; exact le_sup_right
    W1_nontrivial := by
      rw [tp.W1_eq_K hG]
      exact fun h => BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
        (Subgroup.card_eq_one.mpr h)
    W2_nontrivial := by
      rw [tp.W2_eq_Kstar hG]
      exact fun h => BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
        (Subgroup.card_eq_one.mpr h)
    W_sup := tp.W_eq_join.symm
    W_disjoint := disjoint_iff.mpr tp.W1_inf_W2_eq_bot
    W_card_coprime := by
      rw [← tp.q_eq_card_W1, ← tp.p_eq_card_W2]
      exact (Nat.coprime_primes tp.q_prime tp.p_prime).mpr (ne_of_lt tp.q_lt_p)
    W_card_odd := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card tp.W)
    W_cyclic := tp.W_cyclic
    V := (tp.W : Set G) \ ((tp.W1 : Set G) ∪ (tp.W2 : Set G))
    V_subset_sharp := by
      rintro x hx
      rw [Set.mem_sdiff] at hx
      obtain ⟨_, hxni⟩ := hx
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hxni
      change x ∈ Set.univ \ ({1} : Set G)
      refine ⟨Set.mem_univ x, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact fun h => hxni.1 (h ▸ one_mem tp.W1)
    V_subset_W := Set.sdiff_subset
    W_normalizes_V := by
      intro w v hv
      have hvW : v ∈ tp.W := hv.1
      have := tp.W_cyclic
      let : CommGroup ↥tp.W := IsCyclic.commGroup
      have hcg : (w : G) * v = v * (w : G) := by
        have h := mul_comm w (⟨v, hvW⟩ : ↥tp.W)
        have := congrArg (Subgroup.subtype tp.W) h
        simpa using this
      have heq : (w : G) * v * (w : G)⁻¹ = v := by rw [hcg]; group
      rw [heq]; exact hv
    V_ti := by
      -- The `Ẑ = zTilde` TI-set fact for the canonical pair (BG Theorem 14.7).
      have hZti : OddOrder.GroupTheory.IsTISubset (BG.Ch4.S14.zTilde mp.K mp.Kstar)
          (mp.K ⊔ mp.Kstar) := by
        obtain ⟨Mst, hMstP⟩ :=
          (BG.Ch4.S14.typeP_duality hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
            mp.Kstar_eq).2.2.exists
        exact hMstP.2.2.2.2.2.1
      rw [tp.W_eq_kappa_join hG, tp.W1_eq_K hG, tp.W2_eq_Kstar hG]
      exact hZti }

/-- The full §4 Dade application for `tiCyclicW` (all local subgroups `H(a) = ⊥`, so
`HConjInvariant` is automatic). -/
noncomputable def tiCyclicWDadeApp :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G)
      (tiCyclicW hG mp tp) :=
  OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication.mk
    (tiCyclicW hG mp tp).toDadeHypothesis.fullDadeIsometryData

/-- **The (3.2) Dade σ-integral on `W = tp.W`** (see the section header above): the σ-isometry of
`tiCyclicW`, re-viewed as an integral character map. -/
noncomputable def tau3W : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥tp.W G :=
  (tiCyclicW hG mp tp).sigmaIntegral rfl (tiCyclicWDadeApp hG mp tp)

/-- The underlying linear character of `omegaS i j`, as a monoid hom of `↥tp.W`. -/
noncomputable def omegaSChar (i : Fin tp.q) (j : Fin tp.p) : ↥tp.W →* ℂˣ :=
  ((mp.certainTypeS hG).sdiffTICyclicHypothesis.omegaProdChar
    ((mp.certainTypeS hG).w1CharEquiv (eqQ hG mp tp i)) (chi2enum hG mp tp j)).comp
    (gridEquivE hG mp tp).toMonoidHom

end Section16CharacterData

end

end OddOrder


