-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_NonGaloisExclusion
-- name    : OddOrder_Peterfalvi_S13_NonGaloisExclusion
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:36:43.611725+00:00
-- url     : https://prove2.me/theorems/d4ffd89f-bc71-4add-86e3-c4b752da9434
-- title:
--   Peterfalvi (11.9.c): the non-Galois $u=a$ pin
-- statement:
--   Formalizes (11.9.c) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §11, pp. 66-67): under Hypothesis (11.2), in Clifford case (a) of (9.7) (the non-Galois case), $u=a$.
--
--   Main declarations: `Hypothesis.muColumnChar_zero` (The trivial μ-grid column has the trivial `W₂`-dual); `Hypothesis.exists_muColumnChar_inv` (The inverse of a nontrivial μ-column dual is again a μ-column dual, at a nonzero index); `caseA_u_eq_a_of_residual_not_orthogonal` (Peterfalvi (11.9.c), the non-Galois `u = a` pin); `not_cliffordCaseA_of_hypothesis` (Peterfalvi (11.9.c), the non-Galois exclusion).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_NonGaloisExclusion.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_NonGaloisExclusion.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_TypeIIIGalois
import Definitions.Def_OddOrder_Peterfalvi_S13_TypeDetermination
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_GroupTheory_NilpotentAbelianization

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The trivial μ-grid column has the trivial `W₂`-dual**: `muColumnChar 0 = 1`.  The
Pontryagin reindex `finCardEquivCharacterGroup` is normalized to send `0` to the trivial
character (`finCardEquivCharacterGroup_zero`); companion of `muColumnChar_ne_one`. -/
theorem Hypothesis.muColumnChar_zero [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    hyp.muColumnChar hG hodd (0 : Fin hyp.w2) = 1 := by
  have := hyp.finiteG
  classical
  set h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis with hhdef
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hchar : hyp.muColumnChar hG hodd (0 : Fin hyp.w2)
      = finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) := by
    unfold Hypothesis.muColumnChar
    rfl
  rw [hchar, show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from Fin.ext (by simp),
    finCardEquivCharacterGroup_zero]
  rfl

open scoped FiniteInduce in
/-- **The inverse of a nontrivial μ-column dual is again a μ-column dual, at a nonzero index**:
`(muColumnChar j)⁻¹ = muColumnChar j'` for some `j' ≠ 0`.  The Pontryagin reindex
`finCardEquivCharacterGroup ∘ finCongr` is a bijection onto the `W₂`-dual group, so the inverse
character is hit; it is nontrivial (`j ≠ 0`, `muColumnChar_ne_one`), so `j' ≠ 0` by the
column-`0` normalization (`muColumnChar_zero`).  This lets the conjugate half of the
`R(μ_j)`-family (built on the inverse column `χ₂⁻¹`) be read through the σ-grid world-bridge
`certainTypeOmegaSigma_muColumnChar_eq_aligned` at the column index `j'`. -/
theorem Hypothesis.exists_muColumnChar_inv [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {j : Fin hyp.w2} (hj : j ≠ 0) :
    ∃ j' : Fin hyp.w2, j' ≠ 0 ∧
      hyp.muColumnChar hG hodd j' = (hyp.muColumnChar hG hodd j)⁻¹ := by
  have := hyp.finiteG
  classical
  -- the surjectivity core, with the reindex-equivalence instances confined to this block
  obtain ⟨j', hj'⟩ : ∃ j' : Fin hyp.w2,
      hyp.muColumnChar hG hodd j' = (hyp.muColumnChar hG hodd j)⁻¹ := by
    set h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis with hhdef
    have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
    let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
    have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
    have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
    have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
    -- the whole reindex `Fin w₂ ≃ Ŵ₂`
    set e : Fin hyp.w2 ≃ ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
      (finCongr hcardW2sub.symm).trans (finCardEquivCharacterGroup _) with hedef
    have hchar : ∀ j'' : Fin hyp.w2, hyp.muColumnChar hG hodd j'' = e j'' := by
      intro j''
      unfold Hypothesis.muColumnChar
      rfl
    refine ⟨e.symm ((e j)⁻¹), ?_⟩
    rw [hchar, hchar, Equiv.apply_symm_apply]
    rfl
  refine ⟨j', ?_, hj'⟩
  -- nonzero index: else `1 = muColumnChar 0 = (muColumnChar j)⁻¹`, contradicting `j ≠ 0`
  intro h0
  rw [h0, hyp.muColumnChar_zero hG hodd] at hj'
  apply hyp.muColumnChar_ne_one hG hodd hj
  ext x
  have hx := congrArg (fun f : (_ →* ℂˣ) => f x) hj'
  simp only [MonoidHom.one_apply, MonoidHom.inv_apply] at hx
  have hx1 : hyp.muColumnChar hG hodd j x = 1 := inv_eq_one.mp hx.symm
  simp [hx1]

end OddOrder.Peterfalvi.S12

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

set_option maxHeartbeats 1600000 in
-- the (5.5)/conj-involution assembly elaborates a large grid case analysis in one declaration
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9.c), the non-Galois `u = a` pin** (issue 1024): under Hypothesis (11.2)
(type III/IV) with the (11.8) refuter `h118`, the Clifford case (a) forces `u = a`.

Proof (`by_contra u ≠ a`, so `u = a·m` with `m ≥ 2` by `caseA_a_dvd_u`):

1. `λ` = the (9.8.d) degree-`qa` irreducible of `𝒮(H₀U') = 𝒮(H₀C)`
   (`caseA_exists_irreducible_qa`; `C = U'` is (11.6) `core_structure`), and
   `μ` = the reducible μ-column at `j = 1` (degree `qu`,
   `caseA_character_counts` (b)).
2. (5.5) expands `c(μ) = ∑_{α ∈ E} α` over `E ⊆ R(μ)` (`certainTypeR`, the signed σ-grid
   family on the columns `χ₂, χ₂⁻¹`); the (5.2.d) image equation gives the complementarity
   `⟨c(μ), R p⟩ − ⟨c(μ̄), R p⟩ = 1` for every `p`.
3. The degree-`0` combination `qa·μ − qu·λ` is `A₀`-supported, so `c` agrees with the
   pointwise Dade `τ` there and conjugation commutes (`tau_mapRingEquiv_comm`):
   `qa·(conj(c μ) − c μ̄) = qu·(conj(c λ) − c λ̄)`.  The left side has `R`-grid coefficients
   in `{−1, 0, 1}` (steps 2 and `conj(R q) = −R(J q)`, `certainTypeRImage_conj`), the right
   side is `m ≥ 2` times an integer per grid vector — so every coefficient vanishes:
   `[R(J p) ∈ E] + [R p ∈ E] = 1`.
4. At `p = (false, 0)`: `J p = (true, 0)` (`rowInv_zero`), so **exactly one** of the two
   row-`0` members of `R(μ)` lies in `E`.  The (11.9.a) row-`0` projection evaluates
   `⟨φ^τ, R(false, i)⟩ = δ·[i = 0]`, `⟨φ^τ, R(true, i)⟩ = −δ·[i = 0]` (through the σ-grid
   world-bridge at the columns `k` and `k'` with `muColumnChar k' = (muColumnChar k)⁻¹`),
   hence `t = ⟨φ^τ, c(μ)⟩ = ±δ = ±1`.
5. `ψ = μ − m·λ` has degree `0`, so `0 = ⟨φ, ψ⟩ = ⟨φ^τ, ψ^τ⟩ = t − m·⟨φ^τ, c(λ)⟩`; with
   `t = ±1` and `⟨φ^τ, c(λ)⟩ ∈ ℤ` this gives `m ∣ 1`, contradicting `m ≥ 2`. -/
theorem caseA_u_eq_a_of_residual_not_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief))
    {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.base.w1 : ℂ))
    (h118 : ¬ ∀ (i : Fin hyp.base.w1) (j : Fin hyp.base.w2),
      ClassFunction.inner
        ((hyp.base.tau ((∑ r : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd r 0) - ζ))
          - ∑ r : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd r 0)
        (hyp.base.alignedOmegaSigmaGrid hG hG.odd i j) = 0) :
    (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u = caseA.a := by
  have := hyp.base.finiteG
  classical
  by_contra hne
  -- ### 0. arithmetic frame: `u = a·m`, `m ≥ 2`
  obtain ⟨m, hm⟩ := OddOrder.Peterfalvi.S11.caseA_a_dvd_u caseA
  have hw1ge : 3 ≤ hyp.base.w1 := by
    have hodd : Odd hyp.base.w1 :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.W1)
    have hgt : 1 < hyp.base.w1 :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.base.typeP.W1_nontrivial
    obtain ⟨k, hk⟩ := hodd; omega
  have hqe : hyp.s11Setup.q = hyp.base.w1 := hyp.s11Setup_q_eq
  -- ### 1. the μ-column and the (9.8.d) irreducible λ
  have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
  have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro heq; have := congrArg Fin.val heq; simp at this
  set μ : ClassFunction ↥M ℂ := ∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩
    with hμdef
  have hμmem : μ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C := by
    rw [hμdef, hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd ⟨1, hw2⟩]
    exact columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp ⟨1, hw2⟩ hk1
      (S_H0C_not_coherent_unconditional hG hyp) hyp.type_alt
  have hμc : μ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
    OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hμmem
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  have hμμ : ClassFunction.inner μ μ = (hyp.base.w1 : ℂ) :=
    hyp.base.muGrid_column_sum_inner_self hG hG.odd ⟨1, hw2⟩
  have hμred : ¬ IsIrreducibleCharacter μ := by
    intro hirr
    have h1 := hirr.inner_self_eq_one
    rw [hμμ] at h1
    have h2 : (hyp.base.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  -- degree `μ(1) = qu` (`caseA_character_counts` (b))
  have hμH0 : μ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.chief.H0 :=
    OddOrder.Peterfalvi.S11.sOf_antitone hyp.s11Setup le_sup_left hμmem
  obtain ⟨-, hb, -, -⟩ := OddOrder.Peterfalvi.S11.caseA_character_counts hG
    (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) caseA
  obtain ⟨hμdeg, -⟩ := hb μ hμH0 hμred
  -- λ: the (9.8.d) degree-`qa` irreducible, transported into `𝒮(H₀C)` via (11.6) `C = U'`
  obtain ⟨lam, hlamU', hlamirr, hlamdeg⟩ :=
    OddOrder.Peterfalvi.S11.caseA_exists_irreducible_qa hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) caseA
  have hCU : hyp.C = OddOrder.Peterfalvi.S11.uprimeSub hyp.s11Setup := by
    rw [(core_structure hG hyp (S_H0C_not_coherent_unconditional hG hyp)
      hyp.type_alt).2.2.2, hyp.Uprime_eq]
    change derivedInG hyp.base.typeP.U = derivedInG hyp.s11Setup.typeP.U
    rw [hyp.setup_typeP_eq]
  have hlammem : lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C := by
    change lam ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup (hyp.chief.H0 ⊔ hyp.C)
    rw [hCU]
    exact hlamU'
  have hlamc : lam.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
    OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hlammem
  -- `u ≠ 0` (else `μ(1) = 0`), hence `m ≥ 2`
  have humpos : (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u ≠ 0 := by
    intro h0
    apply inducedKernelFamily_mem_apply_one_ne_zero (hIKF hμmem)
    rw [hμdeg, h0, Nat.mul_zero, Nat.cast_zero]
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m'
    · exact absurd (by rw [hm, Nat.mul_zero]) humpos
    · exact absurd (by rw [hm, Nat.mul_one]) hne
    · omega
  -- ### 2. the (5.5) expansion and the `R(μ)`-family
  have hTsub : OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C ⊆
      OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime := hyp.sOf_H0C_subset_sOf_H0Cprime
  obtain ⟨c⟩ := coherent_sOf_H0C hG hyp (S_H0C_not_coherent_unconditional hG hyp)
    hyp.type_alt
  obtain ⟨E, hEsub, hEeq⟩ :=
    coherent_extension_eq_sum_memberRFamily hG hyp hTsub c hμmem hμc
  obtain ⟨k, hk0, hμcol, himg⟩ :=
    sOf_H0Cprime_memberRFamily_imageSet_of_col hG hyp (hTsub hμmem) hμred
  set h46 := hyp.base.toHypothesis46 hG hG.odd with hh46def
  set χ₂ := hyp.base.muColumnChar hG hG.odd k with hχ₂def
  set R := OddOrder.Peterfalvi.S06.certainTypeRImage h46 χ₂ χ₂⁻¹ with hRdef
  have hχ₂ne1 : χ₂ ≠ 1 := hyp.base.muColumnChar_ne_one hG hG.odd hk0
  have hne' : χ₂ ≠ χ₂⁻¹ := (OddOrder.Peterfalvi.S06.column_inv_ne_self h46 hχ₂ne1).symm
  have hRinj : Function.Injective R := by
    rw [hRdef]
    exact OddOrder.Peterfalvi.S06.certainTypeRImage_injective h46 hne'
  have hRinner : ∀ p q, ClassFunction.inner (R p) (R q) = if p = q then (1 : ℂ) else 0 := by
    intro p q
    rw [hRdef]
    exact OddOrder.Peterfalvi.S06.certainTypeRImage_inner h46 hne' p q
  have hRimg : (sOf_H0Cprime_memberRFamily hG hyp (hTsub hμmem)).imageSet
      = Finset.univ.image R := by
    rw [himg, hRdef]
    rfl
  -- the half-swap/row-inversion `J` is an involution, and conjugation acts as `−J` on `R`
  have hJJ : ∀ r : Bool × Fin (Nat.card ↥h46.W1),
      ((!(!r.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis r.2).1,
        OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis
          (!r.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis r.2).2) :
        Bool × Fin (Nat.card ↥h46.W1)) = r := by
    intro r
    simp [OddOrder.Peterfalvi.S06.rowInv_rowInv]
  have hRconj : ∀ q : Bool × Fin (Nat.card ↥h46.W1),
      ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (R q)
      = -R (!q.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis q.2) := by
    intro q
    rw [hRdef]
    exact OddOrder.Peterfalvi.S06.certainTypeRImage_conj h46 χ₂ q
  -- `⟨c(μ), R p⟩ = [R p ∈ E]`
  have hE : ∀ p, ClassFunction.inner (c.extension μ) (R p)
      = if R p ∈ E then (1 : ℂ) else 0 := by
    intro p
    rw [hEeq, OddOrder.RepresentationTheory.inner_sum_left,
      Finset.sum_congr rfl (fun α hα => ?_), Finset.sum_ite_eq' E (R p) (fun _ => (1 : ℂ))]
    have h1 := hEsub hα
    rw [hRimg, Finset.mem_image] at h1
    obtain ⟨q, -, rfl⟩ := h1
    rw [hRinner q p]
    by_cases hpq : q = p
    · rw [if_pos hpq, if_pos (by rw [hpq])]
    · rw [if_neg hpq, if_neg (fun he => hpq (hRinj he))]
  -- ### 3. complementarity `⟨c(μ), R p⟩ − ⟨c(μ̄), R p⟩ = 1`
  have hdiffsupp : ((μ - μ.conj : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    rw [show (μ - μ.conj : ClassFunction ↥M ℂ) = -(μ.conj - μ) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hμmem)
  have hcdiff : c.extension (μ - μ.conj) = hyp.base.tau (μ - μ.conj) :=
    c.extends_on_supported _ ⟨Submodule.sub_mem _ (Submodule.subset_span hμmem)
      (Submodule.subset_span hμc), hdiffsupp⟩
  have hsum_all : ∀ p, ClassFunction.inner (hyp.base.tau (μ - μ.conj)) (R p) = 1 := by
    intro p
    rw [(sOf_H0Cprime_memberRFamily hG hyp (hTsub hμmem)).image_eq, hRimg,
      Finset.sum_image (fun p _ q _ hpq => hRinj hpq),
      OddOrder.RepresentationTheory.inner_sum_left,
      Finset.sum_congr rfl (fun q _ => hRinner q p),
      Finset.sum_ite_eq' Finset.univ p (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ p)]
  have hcompl : ∀ p, ClassFunction.inner (c.extension μ.conj) (R p)
      = ClassFunction.inner (c.extension μ) (R p) - 1 := by
    intro p
    have h1 : ClassFunction.inner (c.extension μ - c.extension μ.conj) (R p) = 1 := by
      rw [← map_sub, hcdiff]
      exact hsum_all p
    rw [ClassFunction.inner_sub_left] at h1
    linear_combination -h1
  -- ### 4. the difference trick: `qa·(conj(c μ) − c μ̄) = qu·(conj(c λ) − c λ̄)`
  set nlam : ℤ := ((hyp.s11Setup.q * caseA.a : ℕ) : ℤ) with hnlamdef
  set nmu : ℤ :=
    ((hyp.s11Setup.q * (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u : ℕ) : ℤ)
    with hnmudef
  set ζd : ClassFunction ↥M ℂ := nlam • μ - nmu • lam with hζddef
  have hζdspan : ζd ∈ Submodule.span ℤ
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ nlam (Submodule.subset_span hμmem))
      (Submodule.smul_mem _ nmu (Submodule.subset_span hlammem))
  have hζd1 : ζd 1 = 0 := by
    rw [hζddef, hnlamdef, hnmudef]
    simp only [ClassFunction.sub_apply, ClassFunction.zsmul_apply, hμdeg, hlamdeg,
      zsmul_eq_mul]
    push_cast
    ring
  have hζdsupp : ζd.support ⊆ hyp.base.A0 :=
    inducedKernelFamily_zSpan_support_of_apply_one_eq_zero hyp.base.mderivSharp_subset_A0
      (Submodule.span_mono (fun x hx => hIKF hx) hζdspan) hζd1
  have hζdconj : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζd
      = nlam • μ.conj - nmu • lam.conj := by
    rw [hζddef, ClassFunction.mapRingEquiv_sub, ClassFunction.mapRingEquiv_zsmul,
      ClassFunction.mapRingEquiv_zsmul, ← ClassFunction.conj_eq_mapRingEquiv_conjAe,
      ← ClassFunction.conj_eq_mapRingEquiv_conjAe]
  have hζdconjspan : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζd
      ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) := by
    rw [hζdconj]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ nlam (Submodule.subset_span hμc))
      (Submodule.smul_mem _ nmu (Submodule.subset_span hlamc))
  have hζdconjsupp : (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζd).support
      ⊆ hyp.base.A0 := by
    rw [ClassFunction.support_mapRingEquiv]
    exact hζdsupp
  have hcomm : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension ζd)
      = c.extension (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζd) := by
    rw [c.extends_on_supported ζd ⟨hζdspan, hζdsupp⟩,
      ← hyp.base.tau_mapRingEquiv_comm Complex.conjAe.toRingEquiv hζdsupp,
      c.extends_on_supported _ ⟨hζdconjspan, hζdconjsupp⟩]
  have hLHS : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension ζd)
      = nlam • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension μ)
        - nmu • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension lam) := by
    rw [hζddef, map_sub, map_zsmul, map_zsmul, ClassFunction.mapRingEquiv_sub,
      ClassFunction.mapRingEquiv_zsmul, ClassFunction.mapRingEquiv_zsmul]
  have hRHS : c.extension (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζd)
      = nlam • c.extension μ.conj - nmu • c.extension lam.conj := by
    rw [hζdconj, map_sub, map_zsmul, map_zsmul]
  have hD : nlam • (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension μ)
        - c.extension μ.conj)
      = nmu • (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension lam)
        - c.extension lam.conj) := by
    have h1 : nlam • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension μ)
          - nmu • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension lam)
        = nlam • c.extension μ.conj - nmu • c.extension lam.conj := by
      rw [← hLHS, ← hRHS]
      exact hcomm
    have h2 : nlam • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension μ)
          - nlam • c.extension μ.conj
          - (nmu • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension lam)
            - nmu • c.extension lam.conj)
        = (nlam • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension μ)
            - nmu • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension lam))
          - (nlam • c.extension μ.conj - nmu • c.extension lam.conj) := by
      abel
    rw [h1, sub_self] at h2
    rw [smul_sub, smul_sub]
    exact sub_eq_zero.mp h2
  -- ### 5. per-grid-vector integrality kills every coefficient: exactly-one on the row-`0` pair
  -- `⟨conj(c μ), R p⟩ = −[R(J p) ∈ E]` for the half-swap/row-inversion `J`
  have hconjE : ∀ p : Bool × Fin (Nat.card ↥h46.W1),
      ClassFunction.inner
        (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension μ)) (R p)
      = -(if R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2) ∈ E
          then (1 : ℂ) else 0) := by
    intro p
    rw [hEeq, ← ClassFunction.mapRingEquivLinear_apply, map_sum,
      OddOrder.RepresentationTheory.inner_sum_left,
      Finset.sum_congr rfl (fun α hα => ?_),
      Finset.sum_ite_eq' E
        (R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2)) (fun _ => (-1 : ℂ))]
    · by_cases hmem : R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2) ∈ E
      · rw [if_pos hmem, if_pos hmem]
      · rw [if_neg hmem, if_neg hmem, neg_zero]
    · have h1 := hEsub hα
      rw [hRimg, Finset.mem_image] at h1
      obtain ⟨q, -, rfl⟩ := h1
      rw [ClassFunction.mapRingEquivLinear_apply, hRconj q,
        ClassFunction.inner_neg_left,
        hRinner (!q.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis q.2) p]
      -- `J q = p ↔ q = J p` (both `!` and `rowInv` are involutions)
      by_cases hqp : (!q.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis q.2) = p
      · rw [if_pos hqp, if_pos (show R q
            = R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2) from by
          rw [← hqp, hJJ q])]
      · rw [if_neg hqp, if_neg (show ¬ R q
            = R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2) from by
          intro he
          exact hqp (by rw [hRinj he, hJJ p]))]
        norm_num
  -- the R-members and the λ-difference are virtual characters
  have hclamZ : c.extension lam ∈ ZIrr G :=
    c.extension_mem_ZIrr lam (Submodule.subset_span hlammem)
  have hclamcZ : c.extension lam.conj ∈ ZIrr G :=
    c.extension_mem_ZIrr lam.conj (Submodule.subset_span hlamc)
  have hDlamZ : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension lam)
      - c.extension lam.conj ∈ ZIrr G :=
    Submodule.sub_mem _ (ClassFunction.mapRingEquiv_mem_ZIrr _ hclamZ) hclamcZ
  have hRZ : ∀ p, R p ∈ ZIrr G := by
    intro p
    have h1 : R p ∈ (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ne1
        (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).imageSet := by
      rw [show (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ne1
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).imageSet
          = Finset.univ.image R from by rw [hRdef]; rfl]
      exact Finset.mem_image_of_mem R (Finset.mem_univ p)
    exact (OddOrder.Peterfalvi.S06.certainTypeR h46 hχ₂ne1
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46 χ₂).symm).mem_ZIrr _ h1
  have hnlamne : (0 : ℤ) < nlam := by
    rw [hnlamdef]
    have hq3 : 3 ≤ hyp.s11Setup.q := by omega
    have := caseA.a_pos
    positivity
  -- exactly-one, in indicator form: `[R(J p) ∈ E] + [R p ∈ E] = 1`
  have hkey : ∀ p : Bool × Fin (Nat.card ↥h46.W1),
      ((if R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2) ∈ E
          then (1 : ℤ) else 0)
        + (if R p ∈ E then (1 : ℤ) else 0)) = 1 := by
    intro p
    obtain ⟨y, hy⟩ := ClassFunction.inner_mem_ZIrr_int hDlamZ (hRZ p)
    have hy' : ClassFunction.inner
          (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (c.extension lam)) (R p)
        - ClassFunction.inner (c.extension lam.conj) (R p) = ((y : ℤ) : ℂ) := by
      rw [← ClassFunction.inner_sub_left]
      exact hy
    have h1 := congrArg (fun x : ClassFunction G ℂ => ClassFunction.inner x (R p)) hD
    rw [← Int.cast_smul_eq_zsmul ℂ nlam, ← Int.cast_smul_eq_zsmul ℂ nmu,
      ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_left,
      hconjE p, hcompl p, hE p, hy'] at h1
    -- pass to `ℤ`
    set eJ : ℤ := if R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2) ∈ E
      then (1 : ℤ) else 0 with heJdef
    set ep : ℤ := if R p ∈ E then (1 : ℤ) else 0 with hepdef
    have hcastJ : (if R (!p.1, OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis p.2) ∈ E
        then (1 : ℂ) else 0) = ((eJ : ℤ) : ℂ) := by
      rw [heJdef]; split <;> simp
    have hcastp : (if R p ∈ E then (1 : ℂ) else 0) = ((ep : ℤ) : ℂ) := by
      rw [hepdef]; split <;> simp
    rw [hcastJ, hcastp] at h1
    have h2 : ((nlam * (-eJ - (ep - 1)) : ℤ) : ℂ) = ((nmu * y : ℤ) : ℂ) := by
      push_cast
      linear_combination h1
    have h3 : nlam * (-eJ - (ep - 1)) = nmu * y := Int.cast_injective h2
    -- `nmu = nlam · m`
    have hnm : nmu = nlam * (m : ℤ) := by
      rw [hnlamdef, hnmudef, hm]
      push_cast
      ring
    rw [hnm, mul_assoc] at h3
    have h4 : -eJ - (ep - 1) = (m : ℤ) * y := mul_left_cancel₀ hnlamne.ne' h3
    have heJ01 : eJ = 0 ∨ eJ = 1 := by rw [heJdef]; split <;> simp
    have hep01 : ep = 0 ∨ ep = 1 := by rw [hepdef]; split <;> simp
    -- `|LHS| ≤ 1 < 2 ≤ m·|y|` unless `y = 0`
    have hy0 : y = 0 := by
      by_contra hyne
      have h1abs : 1 ≤ |y| := Int.one_le_abs (by simpa using hyne)
      have hm2' : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm2
      have h5 : (2 : ℤ) ≤ (m : ℤ) * |y| := by
        calc (2 : ℤ) = 2 * 1 := by ring
          _ ≤ (m : ℤ) * |y| :=
            mul_le_mul hm2' h1abs (by norm_num) (by omega)
      have h6 : |(m : ℤ) * y| = (m : ℤ) * |y| := by
        rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ (m : ℤ))]
      have h7 : |-eJ - (ep - 1)| ≤ 1 := by
        rcases heJ01 with h | h <;> rcases hep01 with h' | h' <;> rw [h, h'] <;> norm_num
      rw [h4, h6] at h7
      omega
    rw [hy0, mul_zero] at h4
    omega
  -- ### 6. the (11.9.a) row-`0` values of `φ^τ` on the `R`-members
  have hrow0 := hyp.base.inner_tau_muColumnZero_sub_zeta_rowZero_of_residual_not_orthogonal
    hG hyp.type_alt (hyp.base.SHC_isCoherent hG) hζS hζirr hζ1 h118
  set τφ : ClassFunction G ℂ :=
    hyp.base.tau ((∑ r : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd r 0) - ζ) with hτφdef
  have hcw1 : Nat.card ↥h46.W1 = hyp.base.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.base.typeP.W1_le).toEquiv
  have hfc : ∀ i' : Fin (Nat.card ↥h46.W1), finCongr hcw1.symm (finCongr hcw1 i') = i' := by
    intro i'
    ext
    simp
  have hfc0 : ∀ i' : Fin (Nat.card ↥h46.W1), finCongr hcw1 i' = 0 ↔ i' = 0 := by
    intro i'
    constructor <;> intro h <;> ext <;> simpa using congrArg Fin.val h
  obtain ⟨kinv, hkinv0, hkinveq⟩ := hyp.base.exists_muColumnChar_inv hG hG.odd hk0
  -- `⟨φ^τ, ω^σ_{χ₂, i'}⟩ = [i' = 0]` (the `k`-column through the world-bridge)
  have hctval : ∀ i' : Fin (Nat.card ↥h46.W1),
      ClassFunction.inner τφ (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i')
      = if i' = 0 then (1 : ℂ) else 0 := by
    intro i'
    conv_lhs => rw [← hfc i']
    rw [hχ₂def, certainTypeOmegaSigma_muColumnChar_eq_aligned hG hyp.base hcw1
      (finCongr hcw1 i') k, hτφdef, hrow0 (finCongr hcw1 i') k]
    by_cases h0 : i' = 0
    · rw [if_pos ((hfc0 i').mpr h0), if_pos h0]
    · rw [if_neg (fun h => h0 ((hfc0 i').mp h)), if_neg h0]
  -- same for the inverse column `χ₂⁻¹ = muColumnChar kinv`
  have hctvalinv : ∀ i' : Fin (Nat.card ↥h46.W1),
      ClassFunction.inner τφ (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂⁻¹ i')
      = if i' = 0 then (1 : ℂ) else 0 := by
    intro i'
    rw [hχ₂def, ← hkinveq]
    conv_lhs => rw [← hfc i']
    rw [certainTypeOmegaSigma_muColumnChar_eq_aligned hG hyp.base hcw1
      (finCongr hcw1 i') kinv, hτφdef, hrow0 (finCongr hcw1 i') kinv]
    by_cases h0 : i' = 0
    · rw [if_pos ((hfc0 i').mpr h0), if_pos h0]
    · rw [if_neg (fun h => h0 ((hfc0 i').mp h)), if_neg h0]
  -- the signed member values
  set δ : ℤ := (h46.columnFamily χ₂).sign with hδdef
  have hδpm : δ = 1 ∨ δ = -1 := (h46.columnFamily χ₂).sign_eq
  have hRfalse : ∀ i', R (false, i')
      = ((δ : ℤ) : ℂ) • OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i' := by
    intro i'
    rw [hRdef, hδdef]
    rfl
  have hRtrue : ∀ i', R (true, i')
      = (-((δ : ℤ) : ℂ)) • OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂⁻¹ i' := by
    intro i'
    rw [hRdef, hδdef]
    rfl
  have hvalfalse : ∀ i', ClassFunction.inner τφ (R (false, i'))
      = if i' = 0 then ((δ : ℤ) : ℂ) else 0 := by
    intro i'
    rw [hRfalse i', OddOrder.RepresentationTheory.inner_smul_right, star_intCast, hctval i']
    split <;> ring
  have hvaltrue : ∀ i', ClassFunction.inner τφ (R (true, i'))
      = if i' = 0 then (-((δ : ℤ) : ℂ)) else 0 := by
    intro i'
    rw [hRtrue i', OddOrder.RepresentationTheory.inner_smul_right, star_neg, star_intCast,
      hctvalinv i']
    split <;> ring
  -- ### 7. `t = ⟨φ^τ, c(μ)⟩ = ±1` from exactly-one on the row-`0` pair
  have hone := hkey (false, (0 : Fin (Nat.card ↥h46.W1)))
  rw [show ((!(false, (0 : Fin (Nat.card ↥h46.W1))).1,
      OddOrder.Peterfalvi.S06.rowInv h46.toHypothesis
        (false, (0 : Fin (Nat.card ↥h46.W1))).2) : Bool × Fin (Nat.card ↥h46.W1))
      = (true, 0) from by simp] at hone
  have hft : R (false, (0 : Fin (Nat.card ↥h46.W1)))
      ≠ R (true, (0 : Fin (Nat.card ↥h46.W1))) := by
    intro he
    have h1 := hRinj he
    simp at h1
  have hval : ∀ α ∈ E, ClassFunction.inner τφ α
      = (if α = R (false, (0 : Fin (Nat.card ↥h46.W1))) then ((δ : ℤ) : ℂ) else 0)
        + (if α = R (true, (0 : Fin (Nat.card ↥h46.W1))) then (-((δ : ℤ) : ℂ)) else 0) := by
    intro α hα
    have h1 := hEsub hα
    rw [hRimg, Finset.mem_image] at h1
    obtain ⟨⟨b, i'⟩, -, rfl⟩ := h1
    cases b
    · rw [hvalfalse i']
      by_cases h0 : i' = 0
      · subst h0
        rw [if_pos rfl, if_pos rfl, if_neg hft, add_zero]
      · rw [if_neg h0,
          if_neg (fun he => h0 (by simpa using congrArg Prod.snd (hRinj he))),
          if_neg (fun he => by simpa using congrArg Prod.fst (hRinj he)), add_zero]
    · rw [hvaltrue i']
      by_cases h0 : i' = 0
      · subst h0
        rw [if_pos rfl, if_neg hft.symm, if_pos rfl, zero_add]
      · rw [if_neg h0,
          if_neg (fun he => by simpa using congrArg Prod.fst (hRinj he)),
          if_neg (fun he => h0 (by simpa using congrArg Prod.snd (hRinj he))), add_zero]
  have htval : ClassFunction.inner τφ (c.extension μ)
      = (if R (false, (0 : Fin (Nat.card ↥h46.W1))) ∈ E then ((δ : ℤ) : ℂ) else 0)
        + (if R (true, (0 : Fin (Nat.card ↥h46.W1))) ∈ E then (-((δ : ℤ) : ℂ)) else 0) := by
    rw [hEeq, OddOrder.RepresentationTheory.inner_sum_right, Finset.sum_congr rfl hval,
      Finset.sum_add_distrib,
      Finset.sum_ite_eq' E (R (false, (0 : Fin (Nat.card ↥h46.W1))))
        (fun _ => ((δ : ℤ) : ℂ)),
      Finset.sum_ite_eq' E (R (true, (0 : Fin (Nat.card ↥h46.W1))))
        (fun _ => (-((δ : ℤ) : ℂ)))]
  -- ### 8. the pin equation `0 = t − m·s` closes the contradiction
  -- `ψ = μ − m·λ`: degree `0`, `A₀`-supported, `c`-extended by `τ`
  set ψp : ClassFunction ↥M ℂ := μ - ((m : ℤ) : ℂ) • lam with hψpdef
  have hψspan : ψp ∈ Submodule.span ℤ
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) := by
    rw [hψpdef, Int.cast_smul_eq_zsmul]
    exact Submodule.sub_mem _ (Submodule.subset_span hμmem)
      (Submodule.smul_mem _ _ (Submodule.subset_span hlammem))
  have hψ1 : ψp 1 = 0 := by
    rw [hψpdef, ClassFunction.sub_apply, ClassFunction.smul_apply, hμdeg, hlamdeg, hm]
    push_cast
    ring
  have hψsupp : ψp.support ⊆ hyp.base.A0 :=
    inducedKernelFamily_zSpan_support_of_apply_one_eq_zero hyp.base.mderivSharp_subset_A0
      (Submodule.span_mono (fun x hx => hIKF hx) hψspan) hψ1
  have hτψ : hyp.base.tau ψp
      = c.extension μ - ((m : ℤ) : ℂ) • c.extension lam := by
    rw [← c.extends_on_supported ψp ⟨hψspan, hψsupp⟩, hψpdef, Int.cast_smul_eq_zsmul,
      map_sub, map_zsmul, Int.cast_smul_eq_zsmul]
  -- source-side orthogonality `⟨φ, ψ⟩ = 0`
  have hζHC : ζ ∈ hyp.SOf hyp.HC := by
    rw [← secondDerived_eq_HC_of_noncoherent hG hyp
      (S_H0C_not_coherent_unconditional hG hyp) hyp.type_alt, hyp.SOf_secondDerived_eq hG]
    exact ⟨hζS, hζirr, hζ1⟩
  have hζμ : ClassFunction.inner ζ μ = 0 :=
    SOf_HC_inner_sOf_H0C_eq_zero hyp hζHC hμmem
  have hζlam : ClassFunction.inner ζ lam = 0 :=
    SOf_HC_inner_sOf_H0C_eq_zero hyp hζHC hlammem
  have hμ0μ : ClassFunction.inner
      (∑ r : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd r 0) μ = 0 := by
    rw [hμdef, hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd 0,
      hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd ⟨1, hw2⟩,
      OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnSum_def,
      OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_neg ?_]
    rw [hyp.base.muColumnChar_zero hG hG.odd]
    intro h
    exact hyp.base.muColumnChar_ne_one hG hG.odd hk1 h.symm
  have hμ0lam : ClassFunction.inner
      (∑ r : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd r 0) lam = 0 := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [irr_cf_inner
      (mem_irreducibleCharacters.mpr (hyp.base.muGrid_isIrreducible hG hG.odd r 0))
      (mem_irreducibleCharacters.mpr hlamirr), if_neg ?_]
    intro heq
    have h1 : hyp.base.muGrid hG hG.odd r 0 1 = lam 1 := by rw [heq]
    rw [hyp.base.muGrid_zero_column_apply_one hG hG.odd r, hlamdeg] at h1
    have h2 : (hyp.s11Setup.q * caseA.a : ℕ) = 1 := by exact_mod_cast h1.symm
    have hq1 : hyp.s11Setup.q = 1 := Nat.dvd_one.mp ⟨caseA.a, h2.symm⟩
    omega
  have hφψ : ClassFunction.inner
      ((∑ r : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd r 0) - ζ) ψp = 0 := by
    rw [hψpdef, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_smul_right, hμ0μ, hμ0lam, hζμ, hζlam]
    ring
  -- the Dade pairing
  have hφsupp : (((∑ r : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd r 0) - ζ :
      ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 :=
    hyp.base.muColumnZero_sub_zeta_support hG hG.odd hζS hζ1
  have hpair : ClassFunction.inner τφ (hyp.base.tau ψp) = 0 := by
    rw [hτφdef, hyp.base.tau_inner_eq_of_supported hφsupp hψsupp]
    exact hφψ
  -- extract the integer `s = ⟨φ^τ, c(λ)⟩` and conclude
  have hμ0Z : (∑ r : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd r 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun r _ => (hyp.base.muGrid_isIrreducible hG hG.odd r 0).mem_ZIrr)
  have hτφZ : τφ ∈ ZIrr G := by
    rw [hτφdef]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.base.dadeData.dade hφsupp
      (Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr)
  obtain ⟨s, hs⟩ := ClassFunction.inner_mem_ZIrr_int hτφZ hclamZ
  have hteq : ClassFunction.inner τφ (c.extension μ) = ((m : ℤ) : ℂ) * ((s : ℤ) : ℂ) := by
    have h1 := hpair
    rw [hτψ, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast, hs] at h1
    linear_combination h1
  -- `t = ±δ` from exactly-one; `t = m·s` forces `m ∣ 1`, contradicting `m ≥ 2`
  have htpm : ClassFunction.inner τφ (c.extension μ) = ((δ : ℤ) : ℂ)
      ∨ ClassFunction.inner τφ (c.extension μ) = -((δ : ℤ) : ℂ) := by
    rw [htval]
    by_cases hf : R (false, (0 : Fin (Nat.card ↥h46.W1))) ∈ E
    · have ht : R (true, (0 : Fin (Nat.card ↥h46.W1))) ∉ E := by
        rw [if_pos hf] at hone
        intro hcon
        rw [if_pos hcon] at hone
        omega
      left
      rw [if_pos hf, if_neg ht, add_zero]
    · have ht : R (true, (0 : Fin (Nat.card ↥h46.W1))) ∈ E := by
        rw [if_neg hf] at hone
        by_contra hcon
        rw [if_neg hcon] at hone
        omega
      right
      rw [if_neg hf, if_pos ht, zero_add]
  have hmsδ : (m : ℤ) * s = δ ∨ (m : ℤ) * s = -δ := by
    rcases htpm with h | h
    · left
      have h1 : (((m : ℤ) * s : ℤ) : ℂ) = ((δ : ℤ) : ℂ) := by
        push_cast
        linear_combination hteq.symm.trans h
      exact_mod_cast h1
    · right
      have h1 : (((m : ℤ) * s : ℤ) : ℂ) = ((-δ : ℤ) : ℂ) := by
        push_cast
        linear_combination hteq.symm.trans h
      exact_mod_cast h1
  have hdvd : (m : ℤ) ∣ 1 := by
    rcases hmsδ with h | h <;> rcases hδpm with h' | h' <;> rw [h'] at h
    · exact ⟨s, h.symm⟩
    · exact ⟨-s, by rw [mul_neg, h, neg_neg]⟩
    · exact ⟨-s, by rw [mul_neg, h]; norm_num⟩
    · exact ⟨s, by rw [h, neg_neg]⟩
  have hm1 : (m : ℤ) = 1 ∨ (m : ℤ) = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
  omega

end OddOrder.Peterfalvi.S13

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9.c), the non-Galois exclusion** (issue 1024 P3): under Hypothesis (11.2)
(type III/IV), the Clifford case (a) of (9.7) is impossible.

The (11.8) refuter core (`exists_zeta_residual_not_orthogonal_H0C_of_refuter`, instantiated at
the unconditional (11.3) `S_H0C_not_coherent_unconditional`) supplies `ζ` with the grid
non-orthogonality `h118`; the keystone `caseA_u_eq_a_of_residual_not_orthogonal` then pins
`u = a`.  The arithmetic closes both branches:

* `u = 1`: the `U`-action image on the chief factor `H̄` is trivial, so `U` centralizes `H̄`,
  contradicting `ChiefFactorData.U_noncentral_on_quotient`.
* `u ≥ 2`: the Frobenius congruence `u ≡ 1 (mod q)` (`mkSection11CharacterData_u_modEq_one`)
  gives `q ≤ u − 1`; with `u = a ∣ p − 1` (`caseA.a_dvd_p_sub_one`) this forces
  `q ≤ p − 2 < p`, contradicting (11.9.b) `p < q`
  (`w2_lt_w1_of_hypothesis_H0C_unconditional`). -/
theorem not_cliffordCaseA_of_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] :
    ¬ Nonempty (OddOrder.Peterfalvi.S11.CliffordCaseAData
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)) := by
  rintro ⟨caseA⟩
  -- (11.5)/(11.7) structural inputs for the refuter core
  have hM2 : secondDerivedInAmbient M
      = hyp.base.typeP.H
        ⊔ (hyp.base.typeP.U ⊓ Subgroup.centralizer (hyp.base.typeP.H : Set G)) :=
    secondDerived_eq_fitting_of_base hG hyp.base hyp.type_alt
      (fun s13 => S_H0C_not_coherent_unconditional hG s13)
  have hHcard : Nat.card ↥hyp.base.typeP.H = hyp.base.w2 ^ hyp.base.w1 :=
    card_H_eq_of_base hG hyp.base hyp.type_alt
      (fun s13 => S_H0C_not_coherent_unconditional hG s13)
  -- (11.8): `ζ` and the grid non-orthogonality, via the unconditional (11.3)
  obtain ⟨ζ, hζS, hζirr, hζ1, h118⟩ :=
    exists_zeta_residual_not_orthogonal_H0C_of_refuter hG hyp.base hyp.type_alt hM2 hHcard
      (fun s13hyp => S_H0C_not_coherent_unconditional hG s13hyp)
  -- the keystone pin `u = a`
  have hua := caseA_u_eq_a_of_residual_not_orthogonal hG hyp caseA hζS hζirr hζ1 h118
  set u : ℕ := (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u with hudef
  -- the Frobenius congruence `u ≡ 1 (mod w₁)`
  have hU : hyp.s11Setup.typeP.U ≠ ⊥ := hyp.s11Setup.nontrivial.1
  have hmod : u ≡ 1 [MOD hyp.base.w1] := by
    have h := hyp.base.mkSection11CharacterData_u_modEq_one hyp.s11Setup hyp.chief hU
    rwa [show Nat.card ↥hyp.s11Setup.typeP.W1 = hyp.base.w1 from hyp.s11Setup_q_eq] at h
  -- `a ∣ p − 1` with `p = w₂`
  have hpeq : hyp.chief.p = hyp.base.w2 := by
    have h := hyp.chief.typeIII_IV_p_eq_W2 hyp.type_alt
    rw [← h]
    change Nat.card ↥hyp.s11Setup.typeP.W2 = hyp.base.w2
    rw [hyp.setup_typeP_eq]
    rfl
  have hadvd : caseA.a ∣ hyp.base.w2 - 1 := hpeq ▸ caseA.a_dvd_p_sub_one
  -- (11.9.b) `w₂ < w₁`, and `w₂ ≥ 3`
  have hlt : hyp.base.w2 < hyp.base.w1 :=
    w2_lt_w1_of_hypothesis_H0C_unconditional hG hyp.base hyp.type_alt hM2 hHcard
  have hw2three : 3 ≤ hyp.base.w2 := by
    have hodd : Odd hyp.base.w2 :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.W2)
    have hgt : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
    obtain ⟨k, hk⟩ := hodd; omega
  have hapos := caseA.a_pos
  rcases Nat.lt_or_ge u 2 with hu1 | hu2
  · -- `u = 1`: the `U`-action image is trivial, contradicting `U_noncentral_on_quotient`
    have hu_eq1 : u = 1 := by omega
    have hcard1 : Nat.card
        ↥(OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief).range = 1 := by
      have h := (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).u_eq_card_quotient
      rw [← hudef] at h
      rw [← hu_eq1]
      exact h.symm
    have hbot : (OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief).range = ⊥ :=
      Subgroup.card_eq_one.mp hcard1
    apply hyp.chief.U_noncentral_on_quotient
    rw [eq_top_iff]
    intro x _ l hl
    have h1 : OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief ⟨l, hl⟩ = 1 := by
      have hmem : OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief ⟨l, hl⟩
          ∈ (OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief).range := ⟨⟨l, hl⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    change (OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief ⟨l, hl⟩) x = x
    rw [h1]
    rfl
  · -- `u ≥ 2`: `q ≤ u − 1 = a − 1 ≤ p − 2 < p`, contradicting `p < q`
    have hdvd : hyp.base.w1 ∣ u - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
    have hle : hyp.base.w1 ≤ u - 1 := Nat.le_of_dvd (by omega) hdvd
    have hale : caseA.a ≤ hyp.base.w2 - 1 := Nat.le_of_dvd (by omega) hadvd
    omega

end OddOrder.Peterfalvi.S13

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9.c), `U` is cyclic** (issue 1024 P3): under Hypothesis (11.2)
(type III/IV), `U` is cyclic.

The non-Galois exclusion (`not_cliffordCaseA_of_hypothesis`) leaves the Galois case (b) of the
(9.7) dichotomy, whose Singer field model makes the chief-factor image `Ū = U/C_U(H̄)` cyclic
(`CliffordCaseBData.Ubar_cyclic`).  The kernel of the restriction `↥U →* Ū` is the action
kernel `C_U(H̄) = cSub`, which is `C = U ⊓ C_G(H)` (`C_eq_cSub`, via (11.7) `H₀ = ⊥`) and hence
`U' = [U,U]` ((11.6) `core_structure`); `U` is nilpotent (`TypePData.U_nilpotent`), and a
nilpotent group with a cyclic quotient by a subgroup of its commutator is cyclic
(`isCyclic_of_isNilpotent_of_ker_le_commutator`, issue 9086). -/
theorem U_isCyclic_of_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] :
    IsCyclic ↥hyp.base.typeP.U := by
  classical
  rw [← hyp.setup_typeP_eq]
  have hnil : Group.IsNilpotent ↥hyp.s11Setup.typeP.U := hyp.s11Setup.typeP.U_nilpotent
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) with hA | hB
  · exact absurd hA (not_cliffordCaseA_of_hypothesis hG hyp)
  obtain ⟨caseB⟩ := hB
  have hcyc : IsCyclic ↥(OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief).range :=
    caseB.Ubar_cyclic
  -- the restriction `↥U →* Ū`, kernel inside `U'`
  set e : ↥hyp.s11Setup.typeP.U
      ≃* ↥(hyp.s11Setup.typeP.U.subgroupOf (hyp.s11Setup.typeP.U ⊔ hyp.s11Setup.typeP.W1)) :=
    (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : hyp.s11Setup.typeP.U ≤ hyp.s11Setup.typeP.U ⊔ hyp.s11Setup.typeP.W1)).symm
    with hedef
  refine OddOrder.GroupTheory.isCyclic_of_isNilpotent_of_ker_le_commutator
    ((OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief).rangeRestrict.comp
      e.toMonoidHom) ?_
  intro x hx
  have hone : OddOrder.Peterfalvi.S11.uActionHom hyp.s11Setup hyp.chief (e x) = 1 := by
    have h1 := MonoidHom.mem_ker.mp hx
    exact congrArg Subtype.val h1
  -- `↑x ∈ cSub = C = U'` ((11.6)/(11.7))
  have hxC : (x : G) ∈ hyp.C := by
    rw [C_eq_cSub_of_noncoherent hG hyp (S_H0C_not_coherent_unconditional hG hyp)
      hyp.type_alt]
    exact Subgroup.mem_map.mpr
      ⟨(hyp.s11Setup.typeP.U.subgroupOf
          (hyp.s11Setup.typeP.U ⊔ hyp.s11Setup.typeP.W1)).subtype (e x),
        Subgroup.mem_map.mpr ⟨e x, MonoidHom.mem_ker.mpr hone, rfl⟩, rfl⟩
  have hCU' : hyp.C = derivedInG hyp.s11Setup.typeP.U := by
    rw [(core_structure hG hyp (S_H0C_not_coherent_unconditional hG hyp)
      hyp.type_alt).2.2.2, hyp.Uprime_eq]
    rw [hyp.setup_typeP_eq]
  rw [hCU'] at hxC
  -- pull back through the injective `U.subtype`: `derivedInG U = (commutator ↥U).map U.subtype`
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxC
  rwa [show y = x from Subtype.ext hyx] at hy

end OddOrder.Peterfalvi.S13

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **`U`-commutativity is independent of the type-`P` witness** (the `M`-side analog of the
`S16` transfer `isMulCommutative_typePData_U_of_V`): any two `TypePData` on the same maximal `M`
have their `U`-factors conjugate in `M' = [M,M]` — both complement the normal Hall subgroup
`H = M_F` in `M'` (`derived_complement`, `H_eq`), so Schur–Zassenhaus conjugacy
(`IsComplement'.exists_conj_of_coprime`, with `M_F` solvable as a proper subgroup of the minimal
simple `G`) transports `IsMulCommutative` between them.  This is what lets the (11.9.c)
commutativity of `hyp.base.typeP.U` refute an *arbitrary* `TypeIVData` witness. -/
theorem isMulCommutative_typePData_U_of_typePData_U [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (d₁ d₂ : TypePData M)
    (h : IsMulCommutative ↥d₁.U) : IsMulCommutative ↥d₂.U := by
  classical
  -- both `U`s complement `H = M_F` in `M'`
  have hH12 : d₁.H = d₂.H := by rw [d₁.H_eq, d₂.H_eq]
  have hH_le : d₁.H ≤ derivedInG M := d₁.H_le
  have hM'_le_M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hH_le_M : d₁.H ≤ M := hH_le.trans hM'_le_M
  have hM_le_NH : M ≤ Subgroup.normalizer (d₁.H : Set G) := by
    rw [d₁.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M
  have hHnormal : (d₁.H.subgroupOf (derivedInG M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH_le).mpr (hM'_le_M.trans hM_le_NH)
  have hcompl₁ : (d₁.H.subgroupOf (derivedInG M)).IsComplement'
      (d₁.U.subgroupOf (derivedInG M)) := d₁.derived_complement
  have hcompl₂ : (d₁.H.subgroupOf (derivedInG M)).IsComplement'
      (d₂.U.subgroupOf (derivedInG M)) := by
    rw [hH12]
    exact d₂.derived_complement
  -- `|H|` (Hall in `M`) is coprime to `[M' : H]` (which divides `[M : H]`)
  have hcop : Nat.Coprime (Nat.card ↥(d₁.H.subgroupOf (derivedInG M)))
      ((d₁.H.subgroupOf (derivedInG M)).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall M
    rw [← d₁.H_eq] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le_M).toEquiv] at h0
    have hcard : Nat.card ↥(d₁.H.subgroupOf (derivedInG M)) = Nat.card ↥d₁.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le).toEquiv
    have hdvd : (d₁.H.subgroupOf (derivedInG M)).index
        ∣ (d₁.H.subgroupOf M).index := by
      have htower : d₁.H.relIndex (derivedInG M) * (derivedInG M).relIndex M
          = d₁.H.relIndex M :=
        Subgroup.relIndex_mul_relIndex d₁.H (derivedInG M) M hH_le hM'_le_M
      exact ⟨(derivedInG M).relIndex M, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  -- `H = M_F` is solvable (a proper subgroup of the minimal simple `G`)
  have hH_lt_top : d₁.H < ⊤ :=
    lt_of_le_of_lt hH_le_M (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1)
  have hHsolv : Group.IsSolvable ↥d₁.H := hG.isSolvable_of_lt_top d₁.H hH_lt_top
  have hsolv : Group.IsSolvable ↥(d₁.H.subgroupOf (derivedInG M))
      ∨ Group.IsSolvable (↥(derivedInG M) ⧸ d₁.H.subgroupOf (derivedInG M)) :=
    Or.inl (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hH_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hH_le).injective)
  -- Schur–Zassenhaus conjugacy, then push the commutativity across
  obtain ⟨n, _hn, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hcompl₁ hcompl₂
  have hUsub : IsMulCommutative ↥(d₁.U.subgroupOf (derivedInG M)) :=
    isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe d₁.U_le).symm h
  have hmapped : IsMulCommutative
      ↥((d₁.U.subgroupOf (derivedInG M)).map (MulAut.conj n).toMonoidHom) :=
    isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective) hUsub
  rw [hn] at hmapped
  exact isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe d₂.U_le) hmapped

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9.c), `U` is abelian**: the `IsMulCommutative` form of
`U_isCyclic_of_hypothesis` — the shape the type-III/IV discriminator consumes. -/
theorem U_isMulCommutative_of_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] :
    IsMulCommutative ↥hyp.base.typeP.U :=
  OddOrder.GroupTheory.isMulCommutative_of_isCyclic (U_isCyclic_of_hypothesis hG hyp)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9.c), the Type-IV exclusion**: no type-III/IV maximal subgroup carrying
Hypothesis (11.2) is of Type IV — any `TypeIVData` witness has its `U`-factor conjugate to the
abelian `hyp.base.typeP.U` (`isMulCommutative_typePData_U_of_typePData_U`), contradicting
`U_not_commutative`. -/
theorem not_isTypeIV_of_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)] :
    ¬ IsTypeIV M := by
  rintro ⟨d⟩
  exact d.U_not_commutative
    (isMulCommutative_typePData_U_of_typePData_U hG hyp.s11Setup.maximal hyp.base.typeP d.typeP
      (U_isMulCommutative_of_hypothesis hG hyp))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.9.c), the universal Type-IV exclusion, per-subgroup form**: no maximal
subgroup of a minimal simple odd group is of Type IV.  A Type-IV `M` carries the §10 hypothesis
(`exists_hypothesis_of_typeIIIorIVorV`), hence the §13 Hypothesis (11.2)
(`exists_hypothesis_of_isTypeIIIorIV`), and `not_isTypeIV_of_hypothesis` refutes the witness.

This is the consumer signature for the T-side (14.9) type determination: the `hVcomm` residual
of `S16` `T_not_isTypeIV_of_isTypeP1` discharges as
`not_isTypeIV_of_mem_maximalSubgroups hG hyp.base.T_maximal`. -/
theorem not_isTypeIV_of_mem_maximalSubgroups {G : Type*} [Group G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) : ¬ IsTypeIV M := by
  intro hMIV
  obtain ⟨hyp12⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG hM
    (Or.inr (Or.inl hMIV))
  obtain ⟨s13, -⟩ := exists_hypothesis_of_isTypeIIIorIV hG hyp12 (Or.inr hMIV)
  have : NeZero (Nat.card (s13.base.toHypothesis46 hG hG.odd).W1) := ⟨Nat.card_pos.ne'⟩
  exact not_isTypeIV_of_hypothesis hG s13 hMIV

/-- **Peterfalvi (13.2.a), the per-subgroup type determination**: every non-type-I maximal
subgroup of a minimal simple odd group is of Type II or Type III.  The BG type dictionary
(`proposition_type_classification`) sends the type-`P` structure (`isTypeP_of_isTypeNonI`) to
II--V; Type V is excluded universally by the unconditional Theorem (10.10)
(`no_typeV_maximal_unconditional`), Type IV by the (11.9.c) universal exclusion above.

This is the honest per-`M` content of (13.2.a)'s "`S` is of Type II or Type III" — symmetric
in the (13.1) pair (both `S` and `T` qualify, via `S_nonI`/`T_nonI`), matching Coq
`PFsection13`'s `FTtype ∈ {2,3,4}` section context narrowed by the type-IV exclusion.  The
κ-ordered refinement "if `q < p` then `S` is of Type II" is the separate
`isTypeP2_of_typeP_kappaHall_lt` (`S13_TypeDetermination`). -/
theorem isTypeII_or_isTypeIII_of_isTypeNonI {G : Type*} [Group G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hnonI : IsTypeNonI M) :
    IsTypeII M ∨ IsTypeIII M := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hM hnonI
  obtain ⟨-, hbII, hcIII_IV, hdV, -, -⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hM
  rcases OddOrder.BG.Ch4.S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
  · -- type `P₁`: type V is excluded by (10.10), so `M_F ≠ M_σ` and `M` is III or IV;
    -- type IV is excluded by (11.9.c).
    have hMF : OddOrder.BG.Ch4.S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M := fun h =>
      OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG ⟨M, hM, hdV.mpr ⟨hP1, h⟩⟩
    exact Or.inr ((hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right
      (not_isTypeIV_of_mem_maximalSubgroups hG hM))
  · exact Or.inl (hbII.mpr hP2)

/-- **BG Theorem 15.7(a)/(b) for the non-type-I maximals — `F(M)` is TI**: the Fitting subgroup
of a non-type-I maximal subgroup of a minimal simple odd group is a TI-subgroup of `G`.  On the
Type-II branch this is the type-`P₂` clause (`fittingIsTI_of_isTypeP2`); on the Type-III branch
the classification gives `M_F ≠ M_σ` and Theorem 15.7(a)'s contrapositive
(`fitting_isTI_of_mf_ne_msigma`) concludes.

This is the (13.2.e) `TI`-input in the symmetric form the (13.1) pair needs: the
`IsTypeP2`-only summon (`fittingIsTI_of_isTypeP2` at the carrier `S_typeP2`) is not available
at the swapped `T`-side instance, whereas `T_nonI` is a (13.1) field. -/
theorem fittingIsTI_of_isTypeNonI {G : Type*} [Group G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hnonI : IsTypeNonI M) :
    OddOrder.BG.Ch4.S15.FittingIsTI M := by
  obtain ⟨-, hbII, hcIII_IV, -, -, -⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hM
  rcases isTypeII_or_isTypeIII_of_isTypeNonI hG hM hnonI with hII | hIII
  · exact OddOrder.BG.Ch4.S15.fittingIsTI_of_isTypeP2 hG hM (hbII.mp hII)
  · exact OddOrder.BG.Ch4.S15.fitting_isTI_of_mf_ne_msigma hG hM
      (hcIII_IV.mp (Or.inl hIII)).2

end OddOrder.Peterfalvi.S13


