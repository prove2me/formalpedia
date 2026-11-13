-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_CoreStructure_KernelBounds
-- name    : OddOrder_Peterfalvi_S13_CoreStructure_KernelBounds
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:53:46.379649+00:00
-- url     : https://prove2.me/theorems/e48eea12-e41e-4b55-bf09-2fef681954ae
-- title:
--   Peterfalvi §13: kernel bounds for the core structure (11.6)
-- statement:
--   Formalizes the kernel part of Peterfalvi (11.6) (Peterfalvi, *Character Theory for the Odd Order Theorem*, Section 13, pp. 64-66), developing the $p$-complement and the kernel $K_0 = O_p(H)\cdot[R,R]$.
--
--   Main declarations: `pComplementCore` (The `p`-complement `O_{p'}(H)` of the nilpotent `H` — the join of the `q'`-cores over the…); `pComplement` (The ambient `p`-complement `R = O_{p'}(H) ≤ G`); `pKernel` (The (11.6) kernel `K₀ = O_p(H)·⁅R,R⁆` (ambient), with `R` the `p`-complement); `hKernel` (The (11.6) `H₀`-kernel `K₁ = ⁅H, M'⁆` (ambient)).
--
--   The bundle also proves 20 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_CoreStructure/KernelBounds.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_CoreStructure/KernelBounds.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_MaximalIII_IV
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_Peterfalvi_S07_PivotCoherence

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **Commutator product decomposition under cross-commutation**: if `c₁, c₂` commute with
`h₁, h₂` (four swaps), then `⁅h₁c₁, h₂c₂⁆ = ⁅h₁,h₂⁆ · ⁅c₁,c₂⁆` (explicit products; crib of the
`commutator_HC_mem_H0C` computation). -/
theorem commutator_mul_of_commute {Q : Type*} [Group Q] {h₁ c₁ h₂ c₂ : Q}
    (hsw12 : Commute c₁ h₂) (hsw11 : Commute c₁ h₁) (hsw21 : Commute c₂ h₁)
    (hsw22 : Commute c₂ h₂) :
    h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹
      = (h₁ * h₂ * h₁⁻¹ * h₂⁻¹) * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
  have e12 : c₁ * h₂ = h₂ * c₁ := hsw12
  calc h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹
      = h₁ * (c₁ * h₂) * c₂ * (c₁⁻¹ * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by group
    _ = h₁ * (h₂ * c₁) * c₂ * (c₁⁻¹ * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by rw [e12]
    _ = h₁ * h₂ * (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ * (c₂⁻¹ * h₂⁻¹) := by group
    _ = h₁ * h₂ * h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) * (c₂⁻¹ * h₂⁻¹) := by
        have hcomm3 : (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ = h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) := by
          have a1 : Commute (c₁ * c₂ * c₁⁻¹) h₁⁻¹ :=
            ((hsw11.mul_left hsw21).mul_left hsw11.inv_left).inv_right
          exact a1
        rw [show h₁ * h₂ * (c₁ * c₂ * c₁⁻¹) * h₁⁻¹ * (c₂⁻¹ * h₂⁻¹)
            = h₁ * h₂ * ((c₁ * c₂ * c₁⁻¹) * h₁⁻¹) * (c₂⁻¹ * h₂⁻¹) from by group,
          hcomm3]
        group
    _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
        have hcomm4 : (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * h₂⁻¹ = h₂⁻¹ * (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) := by
          have a1 : Commute (c₁ * c₂ * c₁⁻¹ * c₂⁻¹) h₂⁻¹ :=
            (((hsw12.mul_left hsw22).mul_left hsw12.inv_left).mul_left
              hsw22.inv_left).inv_right
          exact a1
        rw [show h₁ * h₂ * h₁⁻¹ * (c₁ * c₂ * c₁⁻¹) * (c₂⁻¹ * h₂⁻¹)
            = h₁ * h₂ * h₁⁻¹ * ((c₁ * c₂ * c₁⁻¹ * c₂⁻¹) * h₂⁻¹) from by group,
          hcomm4]
        group

namespace Hypothesis

/-- **Peterfalvi (9.3) at the §13 hypothesis**: `p = |W₂|` is prime and
`|H| = p^q · |C_H(U)|` (types III/IV; type V is excluded by (10.10)). -/
theorem p_prime_and_card_H_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.p.Prime ∧
      Nat.card ↥hyp.H
        = hyp.p ^ hyp.q
          * Nat.card ↥(hyp.H ⊓ Subgroup.centralizer (hyp.U : Set G)) := by
  obtain ⟨p', hp', hW2, _hUW1, hcard⟩ :=
    (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG hyp.s11Setup).2
      hyp.type_alt
  have hpp : p' = hyp.p := by rw [← hW2, hyp.s11Setup_card_W2_eq]
  refine ⟨hpp ▸ hp', ?_⟩
  rw [← hyp.s11Setup_H_eq, ← hyp.s11Setup_U_eq, ← hyp.s11Setup_q_eq, ← hpp]
  exact hcard

/-- `H` is nilpotent (`H = M_F`, the maximal normal nilpotent Hall subgroup). -/
theorem H_isNilpotent [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Group.IsNilpotent ↥hyp.H := by
  change Group.IsNilpotent ↥hyp.base.typeP.H
  rw [hyp.base.typeP.H_eq]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M

/-- **(11.6), first step**: for a prime `q' ≠ p`, the `q'`-core of the nilpotent `H` lies in
`C_H(U)`.  By (9.3) `|H : C_H(U)| = p^q`, so `C_H(U)` contains a full Sylow `q'`-subgroup of
`H`; Sylow subgroups of the nilpotent `H` are normal and unique (`= O_{q'}(H)`). -/
theorem opCore_map_le_centralizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) {q' : ℕ} (hq' : q'.Prime) (hne : q' ≠ hyp.p) :
    (OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H).map hyp.H.subtype
      ≤ Subgroup.centralizer (hyp.U : Set G) := by
  classical
  have : Fact q'.Prime := ⟨hq'⟩
  have hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  obtain ⟨hp_prime, hcard⟩ := hyp.p_prime_and_card_H_eq hG
  set CUa := hyp.H ⊓ Subgroup.centralizer (hyp.U : Set G) with hCUa
  have hKle : CUa ≤ hyp.H := inf_le_left
  set K := CUa.subgroupOf hyp.H with hK
  -- `q'`-parts of `|H|` and `|K|` agree (the index is the `p`-power `p^q`)
  have hcardK : Nat.card ↥K = Nat.card ↥CUa :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv
  have hfact : (Nat.card ↥hyp.H).factorization q'
      = (Nat.card ↥K).factorization q' := by
    rw [hcardK, hcard, Nat.factorization_mul (pow_ne_zero _ hp_prime.pos.ne') Nat.card_pos.ne',
      Finsupp.add_apply, hp_prime.factorization_pow,
      Finsupp.single_apply, if_neg (fun h => hne h.symm), zero_add]
  -- a Sylow `q'` of `K`, lifted to `H`, is a full Sylow `q'` of `H`
  obtain ⟨S'⟩ : Nonempty (Sylow q' ↥K) := inferInstance
  set P' := (S' : Subgroup ↥K).map K.subtype with hP'
  have hP'card : Nat.card ↥P' = q' ^ ((Nat.card ↥hyp.H).factorization q') := by
    rw [hfact]
    have : Nat.card ↥P' = Nat.card ↥(S' : Subgroup ↥K) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm.toEquiv
    rw [this, S'.card_eq_multiplicity]
  have hP'p : IsPGroup q' ↥P' := S'.isPGroup'.map _
  obtain ⟨T, hT⟩ := hP'p.exists_le_sylow
  have hP'eq : P' = ↑T := by
    refine Subgroup.eq_of_le_of_card_ge hT ?_
    rw [hP'card, T.card_eq_multiplicity]
  have hTnorm : (↑T : Subgroup ↥hyp.H).Normal :=
    OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent T
  have hTeq : (↑T : Subgroup ↥hyp.H) = OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H :=
    OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal T hTnorm
  rw [← hTeq, ← hP'eq]
  -- `P' ≤ K`, and `K` maps into `CUa ≤ C_G(U)`
  have hP'K : P' ≤ K := by
    rw [hP']
    rintro x ⟨y, _, rfl⟩
    exact y.2
  refine le_trans (Subgroup.map_mono hP'K) ?_
  rw [hK, Subgroup.subgroupOf_map_subtype]
  exact inf_le_left.trans inf_le_right

/-- The `p`-complement `O_{p'}(H)` of the nilpotent `H` — the join of the `q'`-cores over
the primes `q' ≠ p` of `|H|` — as a subgroup of `↥H`. -/
noncomputable def pComplementCore [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Subgroup ↥hyp.H :=
  ⨆ (j : (Nat.card ↥hyp.H).primeFactors) (_ : (j : ℕ) ≠ hyp.p),
    OddOrder.Isaacs.Ch01.opCore (j : ℕ) ↥hyp.H

/-- The ambient `p`-complement `R = O_{p'}(H) ≤ G`. -/
noncomputable def pComplement [Finite G] {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.pComplementCore.map hyp.H.subtype

theorem pComplement_le_H [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplement ≤ hyp.H :=
  Subgroup.map_subtype_le _

/-- The `p`-complement is characteristic in `H` (join of the characteristic `q'`-cores). -/
theorem pComplementCore_characteristic [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplementCore.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [pComplementCore]
  simp_rw [Subgroup.map_iSup]
  exact iSup_congr fun j => iSup_congr fun _ =>
    Subgroup.characteristic_iff_map_eq.mp
      (OddOrder.Isaacs.Ch01.opCore.characteristic (j : ℕ) ↥hyp.H) φ

/-- **`U` centralizes the `p`-complement** — each `q'`-core lies in `C_G(U)`
(`opCore_map_le_centralizer`), hence so does the join. -/
theorem pComplement_le_centralizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pComplement ≤ Subgroup.centralizer (hyp.U : Set G) := by
  rw [pComplement, pComplementCore]
  simp_rw [Subgroup.map_iSup]
  refine iSup_le fun j => iSup_le fun hj => ?_
  exact hyp.opCore_map_le_centralizer hG (Nat.prime_of_mem_primeFactors j.2) hj

/-- The `p`-core and the `p`-complement intersect trivially (independence of the cores). -/
theorem disjoint_opCore_pComplementCore [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) (_hp_prime : hyp.p.Prime)
    (hp_mem : hyp.p ∈ (Nat.card ↥hyp.H).primeFactors) :
    Disjoint (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H) hyp.pComplementCore := by
  classical
  set O : (Nat.card ↥hyp.H).primeFactors → Subgroup ↥hyp.H :=
    fun q => OddOrder.Isaacs.Ch01.opCore (q : ℕ) ↥hyp.H with hO
  have hindep : iSupIndep O := by
    apply OddOrder.Isaacs.Ch01.iSupIndep_of_coprime_card_of_normal O
    intro i j hij
    have : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    have : Fact (j : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors j.2⟩
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    exact IsPGroup.coprime_card_of_ne (i : ℕ) (j : ℕ) hne _ _
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (i : ℕ) ↥hyp.H)
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (j : ℕ) ↥hyp.H)
  set i₀ : (Nat.card ↥hyp.H).primeFactors := ⟨hyp.p, hp_mem⟩ with hi₀
  have hdisj : Disjoint (O i₀) (⨆ (j) (_ : j ≠ i₀), O j) := (iSupIndep_def.mp hindep) i₀
  have hjoin : hyp.pComplementCore = ⨆ (j) (_ : j ≠ i₀), O j := by
    rw [pComplementCore]
    exact iSup_congr fun j => iSup_congr_Prop
      ⟨fun h heq => h (congrArg Subtype.val heq), fun h heq => h (Subtype.ext heq)⟩
      (fun _ => rfl)
  rw [hjoin]
  exact hdisj

/-- **(11.6) endgame form**: if the `p`-complement is trivial, `H` is a `p`-group. -/
theorem isPGroup_of_pComplementCore_eq_bot [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) (hbot : hyp.pComplementCore = ⊥) :
    IsPGroup hyp.p ↥hyp.H := by
  classical
  have hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  -- every prime factor `q' ≠ p` has trivial core, hence trivial Sylow — impossible
  have hsub : (Nat.card ↥hyp.H).primeFactors ⊆ {hyp.p} := by
    intro q' hq'
    rw [Finset.mem_singleton]
    by_contra hne
    have : Fact q'.Prime := ⟨Nat.prime_of_mem_primeFactors hq'⟩
    have hcore : OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [← hbot, pComplementCore]
      exact le_iSup₂ (f := fun (j : (Nat.card ↥hyp.H).primeFactors)
        (_ : (j : ℕ) ≠ hyp.p) => OddOrder.Isaacs.Ch01.opCore (j : ℕ) ↥hyp.H) ⟨q', hq'⟩ hne
    obtain ⟨T⟩ : Nonempty (Sylow q' ↥hyp.H) := inferInstance
    have hTeq : (↑T : Subgroup ↥hyp.H) = OddOrder.Isaacs.Ch01.opCore q' ↥hyp.H :=
      OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal T
        (OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent T)
    have hTbot : (↑T : Subgroup ↥hyp.H) = ⊥ := hTeq.trans hcore
    have hcard := T.card_eq_multiplicity
    rw [hTbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card ↥hyp.H).factorization q' :=
      Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hq')
        Nat.card_pos.ne' (Nat.dvd_of_mem_primeFactors hq')
    have : 2 ≤ q' ^ (Nat.card ↥hyp.H).factorization q' :=
      le_trans (Nat.prime_of_mem_primeFactors hq').two_le
        (Nat.le_self_pow hpos.ne' _)
    omega
  refine IsPGroup.of_card (n := (Nat.card ↥hyp.H).factorization hyp.p) ?_
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (Nat.card_pos (α := ↥hyp.H)).ne']
  rw [Finsupp.prod_of_support_subset _ (Nat.support_factorization _ ▸ hsub) _
    (fun i _ => pow_zero i), Finset.prod_singleton]

/-- `p ∈ primeFactors |H|`: `p` is prime and `p^q ∣ |H|` with `q = |W₁| ≥ 1` ((9.3)). -/
theorem p_mem_primeFactors [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.p ∈ (Nat.card ↥hyp.H).primeFactors := by
  obtain ⟨hp_prime, hcard⟩ := hyp.p_prime_and_card_H_eq hG
  have hq : hyp.q ≠ 0 := by
    change Nat.card ↥hyp.base.typeP.W1 ≠ 0
    exact Nat.card_pos.ne'
  refine Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, Nat.card_pos.ne'⟩
  rw [hcard]
  exact dvd_mul_of_dvd_left (dvd_pow_self _ hq) _

/-- The `p`-core and the `p`-complement jointly generate `H` (nilpotent: Sylows generate). -/
theorem opCore_sup_pComplementCore_eq_top [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H ⊔ hyp.pComplementCore = ⊤ := by
  classical
  have hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  have htop : (⨆ q : (Nat.card ↥hyp.H).primeFactors,
      OddOrder.Isaacs.Ch01.opCore (q : ℕ) ↥hyp.H) = ⊤ := by
    have hrw : (⨆ q : (Nat.card ↥hyp.H).primeFactors,
        OddOrder.Isaacs.Ch01.opCore (q : ℕ) ↥hyp.H)
        = ⨆ q : (Nat.card ↥hyp.H).primeFactors,
            ((default : Sylow (q : ℕ) ↥hyp.H) : Subgroup ↥hyp.H) :=
      iSup_congr fun q => by
        have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
        exact (OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal default
          (OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent default)).symm
    rw [hrw]
    exact OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥hyp.H
  refine le_antisymm le_top ?_
  rw [← htop]
  refine iSup_le fun j => ?_
  by_cases hj : (j : ℕ) = hyp.p
  · refine le_sup_of_le_left ?_
    rw [hj]
  · refine le_sup_of_le_right ?_
    rw [pComplementCore]
    exact le_iSup₂ (f := fun (j : (Nat.card ↥hyp.H).primeFactors)
      (_ : (j : ℕ) ≠ hyp.p) => OddOrder.Isaacs.Ch01.opCore (j : ℕ) ↥hyp.H) j hj

/-- The (11.6) kernel `K₀ = O_p(H)·⁅R,R⁆` (ambient), with `R` the `p`-complement. -/
noncomputable def pKernel [Finite G] {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype
    ⊔ ⁅hyp.pComplement, hyp.pComplement⁆

theorem pKernel_le_H [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.pKernel ≤ hyp.H := by
  refine sup_le (Subgroup.map_subtype_le _) ?_
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hyp.pComplement_le_H hg₁) (hyp.pComplement_le_H hg₂))
      (Subgroup.inv_mem _ (hyp.pComplement_le_H hg₁)))
    (Subgroup.inv_mem _ (hyp.pComplement_le_H hg₂))

/-- `M` normalizes the kernel `K₀` (it is the image of a characteristic subgroup of `H`). -/
theorem pKernel_normalized_by_M [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer (hyp.pKernel : Set G) := by
  classical
  set N₀ : Subgroup ↥hyp.H :=
    OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H ⊔ ⁅hyp.pComplementCore, hyp.pComplementCore⁆
    with hN₀
  have hchar : N₀.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    rw [hN₀, Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.characteristic_iff_map_eq.mp
        (OddOrder.Isaacs.Ch01.opCore.characteristic hyp.p ↥hyp.H) φ,
      Subgroup.characteristic_iff_map_eq.mp hyp.pComplementCore_characteristic φ]
  have hnorm : N₀.Normal := @Subgroup.normal_of_characteristic _ _ N₀ hchar
  have hmap : hyp.pKernel = N₀.map hyp.H.subtype := by
    rw [hN₀, Subgroup.map_sup, Subgroup.map_commutator, pKernel, pComplement]
  rw [hmap]
  exact OddOrder.Peterfalvi.S11.typeP_aInvariantNormal_le_normalizer hyp.base.typeP
    (hNn := hnorm)
    (@OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic _ _ _ _ _ N₀ hchar)

/-- **(11.6) key bound**: `M'' ≤ K₀ ⊔ U'` where `K₀ = O_p(H)·⁅R,R⁆`.  Commutator
generators `⁅a,b⁆` of `M''` decompose as `a = o·r·u` (`M' = H·U` along the normal `H`,
then `H = O_p·R` by the nilpotent splitting); mod `K₀` the `o`-parts die, the `r`-images
are central (`⁅R,R⁆ ≤ K₀` and `[R,U] = 1`), so `⁅a,b⁆ ≡ ⁅u_a,u_b⁆ (mod K₀)`. -/
theorem secondDerived_le_pKernel_sup_derivedU [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M ≤ hyp.pKernel ⊔ derivedInG hyp.base.typeP.U := by
  classical
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hUle : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  have hKle : hyp.pKernel ≤ M := hyp.pKernel_le_H.trans hHle
  have hRle : hyp.pComplement ≤ M := hyp.pComplement_le_H.trans hHle
  have hM'eq : derivedInG M = hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
    rw [hyp.base.typeP.derivedInG_eq_fitting_sup_U, hyp.base.typeP.H_eq]
  have hKn : (hyp.pKernel.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr hyp.pKernel_normalized_by_M
  -- `H`-elements split as `o·r` along `O_p ⊔ R = ⊤` (`O_p` is normal in `↥H`)
  have : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).Characteristic :=
    OddOrder.Isaacs.Ch01.opCore.characteristic hyp.p ↥hyp.H
  have hHsplit : ∀ h ∈ hyp.H, ∃ o ∈ (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map
      hyp.H.subtype, ∃ r ∈ hyp.pComplement, h = o * r := by
    intro h hh
    have hmem : (⟨h, hh⟩ : ↥hyp.H)
        ∈ OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H ⊔ hyp.pComplementCore := by
      rw [hyp.opCore_sup_pComplementCore_eq_top hG]
      trivial
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
    obtain ⟨o, ho, r, hr, hor⟩ := hmem
    refine ⟨(o : G), Subgroup.mem_map_of_mem _ (SetLike.mem_coe.mp ho),
      (r : G), Subgroup.mem_map_of_mem _ (SetLike.mem_coe.mp hr), ?_⟩
    have := congrArg (fun z : ↥hyp.H => (z : G)) hor
    simpa using this.symm
  -- `R` centralizes `U`
  have hcommRU : ∀ u ∈ hyp.base.typeP.U, ∀ r' ∈ hyp.pComplement, u * r' = r' * u :=
    fun u hu r' hr' =>
      Subgroup.mem_centralizer_iff.mp (hyp.pComplement_le_centralizer hG hr') u hu
  set φ := QuotientGroup.mk' (hyp.pKernel.subgroupOf M) with hφ
  rintro x hx
  rw [secondDerivedInAmbient, derivedInG] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [commutator_eq_closure] at hc
  induction hc using Subgroup.closure_induction with
  | one =>
      simp
  | mul y z _ _ hy hz =>
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
      rw [map_inv]
      exact Subgroup.inv_mem _ hy
  | mem cel hcel =>
      obtain ⟨a, b, hab⟩ := hcel
      have hcel_eq : cel = a * b * a⁻¹ * b⁻¹ := hab.symm
      have haM' : ((a : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact a.2
      have hbM' : ((b : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact b.2
      obtain ⟨ha', hha', ua, hua, haeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M haM'
      obtain ⟨hb', hhb', ub, hub, hbeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M hbM'
      obtain ⟨oa, hoa, ra, hra, haeq2⟩ := hHsplit ha' hha'
      obtain ⟨ob, hob, rb, hrb, hbeq2⟩ := hHsplit hb' hhb'
      have hoaK : oa ∈ hyp.pKernel := Subgroup.mem_sup_left hoa
      have hobK : ob ∈ hyp.pKernel := Subgroup.mem_sup_left hob
      have haMm : ((a : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) a.2
      have hbMm : ((b : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) b.2
      set A : ↥M := ⟨((a : ↥(derivedInG M)) : G), haMm⟩ with hA
      set B : ↥M := ⟨((b : ↥(derivedInG M)) : G), hbMm⟩ with hB
      set RA : ↥M := ⟨ra, hRle hra⟩ with hRA
      set RB : ↥M := ⟨rb, hRle hrb⟩ with hRB
      set UA : ↥M := ⟨ua, hUle hua⟩ with hUA
      set UB : ↥M := ⟨ub, hUle hub⟩ with hUB
      -- the `o`-parts die under `φ`
      have hφA : φ A = φ RA * φ UA := by
        have h1 : A = ⟨oa, hKle hoaK⟩ * RA * UA := by
          ext
          rw [haeq, haeq2]
          rfl
        rw [h1, map_mul, map_mul]
        have h2 : φ ⟨oa, hKle hoaK⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hoaK
        rw [h2, one_mul]
      have hφB : φ B = φ RB * φ UB := by
        have h1 : B = ⟨ob, hKle hobK⟩ * RB * UB := by
          ext
          rw [hbeq, hbeq2]
          rfl
        rw [h1, map_mul, map_mul]
        have h2 : φ ⟨ob, hKle hobK⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact Subgroup.mem_subgroupOf.mpr hobK
        rw [h2, one_mul]
      -- the `r`-images commute with each other and with the `u`-images
      have hswM : ∀ (u r' : ↥M), (u : G) ∈ hyp.base.typeP.U → (r' : G) ∈ hyp.pComplement →
          Commute (φ u) (φ r') := by
        intro u r' hu hr'
        refine Commute.map ?_ φ
        exact Subtype.ext (hcommRU _ hu _ hr')
      have hswRR : Commute (φ RA) (φ RB) := by
        have hcomm : (RA * RB * RA⁻¹ * RB⁻¹ : ↥M) ∈ hyp.pKernel.subgroupOf M := by
          refine Subgroup.mem_subgroupOf.mpr ?_
          refine Subgroup.mem_sup_right ?_
          exact Subgroup.commutator_mem_commutator hra hrb
        have h1 : φ (RA * RB * RA⁻¹ * RB⁻¹) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hcomm
        have h2 : φ RA * φ RB * (φ RA)⁻¹ * (φ RB)⁻¹ = 1 := by
          rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          exact h1
        have h3 : φ RA * φ RB = φ RB * φ RA := by
          have := congrArg (· * (φ RB * φ RA)) h2
          simpa [mul_assoc] using this
        exact h3
      -- key collapse: `⁅φA, φB⁆ = ⁅φUA, φUB⁆`
      have hkey : φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹
          = φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹ := by
        rw [hφA, hφB]
        rw [commutator_mul_of_commute
          (hswM UA RB (by exact hua) (by exact hrb))
          (hswM UA RA (by exact hua) (by exact hra))
          (hswM UB RA (by exact hub) (by exact hra))
          (hswM UB RB (by exact hub) (by exact hrb))]
        have hRR1 : φ RA * φ RB * (φ RA)⁻¹ * (φ RB)⁻¹ = 1 := by
          rw [hswRR.eq]
          group
        rw [hRR1, one_mul]
      have hratio : (A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹
          ∈ hyp.pKernel.subgroupOf M := by
        have hmapped : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹)
            = (φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹)
              * (φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹)⁻¹ := by
          simp only [map_mul, map_inv]
        have h1 : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹) = 1 := by
          rw [hmapped, hkey]
          group
        exact (QuotientGroup.eq_one_iff
          (N := hyp.pKernel.subgroupOf M) _).mp h1
      have hcomm_coe : (((derivedInG M).subtype) cel : G)
          = ((A * B * A⁻¹ * B⁻¹ : ↥M) : G) := by
        rw [hcel_eq]; exact rfl
      have hsplit : ((A * B * A⁻¹ * B⁻¹ : ↥M) : G)
          = (((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹ : ↥M) : G)
            * ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) := by
        push_cast
        group
      rw [hcomm_coe, hsplit]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact Subgroup.mem_subgroupOf.mp hratio
      · have hUcomm : ua * ub * ua⁻¹ * ub⁻¹ ∈ derivedInG hyp.base.typeP.U := by
          rw [show derivedInG hyp.base.typeP.U
              = ⁅hyp.base.typeP.U, hyp.base.typeP.U⁆
            from Subgroup.map_subtype_commutator hyp.base.typeP.U]
          exact Subgroup.commutator_mem_commutator hua hub
        have hcoe : ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) = ua * ub * ua⁻¹ * ub⁻¹ := by
          push_cast
          rfl
        rw [hcoe]
        exact hUcomm

/-- `H` normalizes the ambient image of the `p`-core (a normal subgroup of `↥H`). -/
theorem H_le_normalizer_opCore_map [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.H ≤ Subgroup.normalizer
      (((OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype : Subgroup G) : Set G) := by
  have : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).Characteristic :=
    OddOrder.Isaacs.Ch01.opCore.characteristic hyp.p ↥hyp.H
  have h := Subgroup.le_normalizer_map
    (H := OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H) hyp.H.subtype
  rwa [Subgroup.normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

/-- **(11.6) trap**: the `p`-complement is trivial.  `R ≤ H ≤ HC = M'' ≤ K₀ ⊔ U'`
((11.5) + the key bound); splitting an `r ∈ R` along the two sups leaves `r ∈ ⁅R,R⁆`
(the `U'`-part dies in `H ⊓ U = ⊥`, the `O_p`-part in `O_p ⊓ R = ⊥`), so `R` is
perfect — but `R` is nilpotent, hence trivial. -/
theorem pComplementCore_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    hyp.pComplementCore = ⊥ := by
  classical
  obtain ⟨hp_prime, -⟩ := hyp.p_prime_and_card_H_eq hG
  have hp_mem := hyp.p_mem_primeFactors hG
  have hHleM : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hcommleR : ⁅hyp.pComplement, hyp.pComplement⁆ ≤ hyp.pComplement := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
      (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)
  -- Step 1: `R ≤ ⁅R,R⁆` (ambient)
  have hRle' : hyp.pComplement ≤ ⁅hyp.pComplement, hyp.pComplement⁆ := by
    intro r hr
    have hrM'' : r ∈ secondDerivedInAmbient M := by
      rw [secondDerived_eq_HC_of_noncoherent hG hyp hnc htype]
      exact Subgroup.mem_sup_left (hyp.pComplement_le_H hr)
    have hrKU : r ∈ hyp.pKernel ⊔ derivedInG hyp.base.typeP.U :=
      hyp.secondDerived_le_pKernel_sup_derivedU hG hrM''
    -- split off the `U'`-part
    have hKleM : hyp.pKernel ≤ M := hyp.pKernel_le_H.trans hHleM
    have hU'leM : derivedInG hyp.base.typeP.U ≤ M :=
      (Subgroup.map_subtype_le _).trans (hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _))
    obtain ⟨k, hk, u', hu', hru⟩ := exists_mul_of_mem_sup_of_normalized hKleM hU'leM
      hyp.pKernel_normalized_by_M hrKU
    have hu'H : u' ∈ hyp.base.typeP.H := by
      have : u' = k⁻¹ * r := by rw [hru]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hyp.pKernel_le_H hk))
        (hyp.pComplement_le_H hr)
    have hu'U : u' ∈ hyp.base.typeP.U := (Subgroup.map_subtype_le _) hu'
    have hu'1 : u' = 1 := by
      have := hyp.H_inf_U_eq_bot.le ⟨hu'H, hu'U⟩
      rwa [Subgroup.mem_bot] at this
    have hrk : r = k := by rw [hru, hu'1, mul_one]
    -- split off the `O_p`-part
    have hkK : r ∈ (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype
        ⊔ ⁅hyp.pComplement, hyp.pComplement⁆ := by
      rw [← pKernel]; exact hrk ▸ hk
    have hOle : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype ≤ hyp.H :=
      Subgroup.map_subtype_le _
    have hCle : ⁅hyp.pComplement, hyp.pComplement⁆ ≤ hyp.H :=
      hcommleR.trans hyp.pComplement_le_H
    obtain ⟨o, ho, r'', hr'', hor⟩ := exists_mul_of_mem_sup_of_normalized hOle hCle
      hyp.H_le_normalizer_opCore_map hkK
    have hoR : o ∈ hyp.pComplement := by
      have : o = r * r''⁻¹ := by rw [hor]; group
      rw [this]
      exact Subgroup.mul_mem _ hr (Subgroup.inv_mem _ (hcommleR hr''))
    have ho1 : o = 1 := by
      have hinf : (OddOrder.Isaacs.Ch01.opCore hyp.p ↥hyp.H).map hyp.H.subtype
          ⊓ hyp.pComplement = ⊥ := by
        rw [pComplement, ← Subgroup.map_inf _ _ hyp.H.subtype hyp.H.subtype_injective,
          (hyp.disjoint_opCore_pComplementCore hp_prime hp_mem).eq_bot, Subgroup.map_bot]
      have := hinf.le ⟨ho, hoR⟩
      rwa [Subgroup.mem_bot] at this
    rw [hor, ho1, one_mul]
    exact hr''
  -- Step 2: `pComplementCore` is perfect
  have hCCeq : hyp.pComplementCore = ⁅hyp.pComplementCore, hyp.pComplementCore⁆ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hximg : ((x : ↥hyp.H) : G) ∈ ⁅hyp.pComplement, hyp.pComplement⁆ :=
        hRle' (Subgroup.mem_map_of_mem _ hx)
      rw [pComplement, ← Subgroup.map_commutator] at hximg
      obtain ⟨y, hy, hyx⟩ := hximg
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
        (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)
  -- Step 3: perfect + nilpotent ⇒ trivial
  have hHnil : Group.IsNilpotent ↥hyp.H := hyp.H_isNilpotent
  have hAnil : Group.IsNilpotent ↥hyp.pComplementCore := Subgroup.isNilpotent _
  have hcommtop : _root_.commutator ↥hyp.pComplementCore = ⊤ := by
    have h1 : (⁅hyp.pComplementCore, hyp.pComplementCore⁆).subgroupOf hyp.pComplementCore
        = _root_.commutator ↥hyp.pComplementCore :=
      OddOrder.Peterfalvi.S08.commutator_subgroupOf_self hyp.pComplementCore
    rw [← h1, ← hCCeq, Subgroup.subgroupOf_self]
  have hlcs : ∀ n, (⊤ : Subgroup ↥hyp.pComplementCore).lowerCentralSeries n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ, ih]
        exact hcommtop
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hAnil
  have hbot_top : (⊥ : Subgroup ↥hyp.pComplementCore) = ⊤ := by rw [← hn, hlcs n]
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥hyp.pComplementCore) ∈ (⊥ : Subgroup ↥hyp.pComplementCore) := by
    rw [hbot_top]; trivial
  rw [Subgroup.mem_bot] at hmem
  have := congrArg (fun z : ↥hyp.pComplementCore => (z : ↥hyp.H)) hmem
  simpa using this

/-- **Peterfalvi (11.6), `H` is a `p`-group.** -/
theorem H_isPGroup [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    IsPGroup hyp.p ↥hyp.H :=
  hyp.isPGroup_of_pComplementCore_eq_bot (hyp.pComplementCore_eq_bot hG hnc htype)

/-- The (11.6) `H₀`-kernel `K₁ = ⁅H, M'⁆` (ambient).  It contains `H' = ⁅H,H⁆` and
`⁅H,U⁆`, and `M'' ≤ K₁ ⊔ U'` by the mod-`K₁` collapse. -/
noncomputable def hKernel {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  ⁅hyp.base.typeP.H, derivedInG M⁆

theorem hKernel_le_H [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.hKernel ≤ hyp.base.typeP.H := by
  rw [hKernel, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₂M : g₂ ∈ M := (Subgroup.map_subtype_le _) hg₂
  have hconj : g₂ * g₁⁻¹ * g₂⁻¹ ∈ hyp.base.typeP.H := by
    have := (Subgroup.mem_set_normalizer_iff.mp (hyp.H_normalized_by_M hg₂M)) g₁⁻¹
    exact this.mp (Subgroup.inv_mem _ hg₁)
  have : g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) ∈ hyp.base.typeP.H := Subgroup.mul_mem _ hg₁ hconj
  convert this using 1
  group

theorem hKernel_normalized_by_M [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer (hyp.hKernel : Set G) := by
  intro m hm
  rw [← OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer, hKernel,
    Subgroup.map_commutator]
  have h1 : (hyp.base.typeP.H).map (MulAut.conj m).toMonoidHom = hyp.base.typeP.H :=
    OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mpr (hyp.H_normalized_by_M hm)
  have h2 : (derivedInG M).map (MulAut.conj m).toMonoidHom = derivedInG M := by
    rw [show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M,
      Subgroup.map_commutator,
      OddOrder.BG.AppB.map_conj_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hm)]
  rw [h1, h2]

/-- **(11.6) `H₀`-side bound**: `M'' ≤ ⁅H,M'⁆ ⊔ U'`.  Mod `K₁ = ⁅H,M'⁆` every
`H`-image is central in `M'/K₁`, so commutator generators collapse to their `U`-parts. -/
theorem secondDerived_le_hKernel_sup_derivedU [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) :
    secondDerivedInAmbient M ≤ hyp.hKernel ⊔ derivedInG hyp.base.typeP.U := by
  classical
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hUle : hyp.base.typeP.U ≤ M := hyp.base.typeP.U_le.trans (Subgroup.map_subtype_le _)
  have hKle : hyp.hKernel ≤ M := hyp.hKernel_le_H.trans hHle
  have hM'eq : derivedInG M = hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
    rw [hyp.base.typeP.derivedInG_eq_fitting_sup_U, hyp.base.typeP.H_eq]
  have hKn : (hyp.hKernel.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr hyp.hKernel_normalized_by_M
  set φ := QuotientGroup.mk' (hyp.hKernel.subgroupOf M) with hφ
  -- mod-`K₁` commutation from ambient commutator membership
  have hswK : ∀ x y : ↥M, ((x * y * x⁻¹ * y⁻¹ : ↥M) : G) ∈ hyp.hKernel →
      Commute (φ x) (φ y) := by
    intro x y hxy
    have h1 : φ (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hxy
    have h2 : φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    have := congrArg (· * (φ y * φ x)) h2
    simpa [commute_iff_eq, mul_assoc] using this
  rintro x hx
  rw [secondDerivedInAmbient, derivedInG] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [commutator_eq_closure] at hc
  induction hc using Subgroup.closure_induction with
  | one =>
      simp
  | mul y z _ _ hy hz =>
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
      rw [map_inv]
      exact Subgroup.inv_mem _ hy
  | mem cel hcel =>
      obtain ⟨a, b, hab⟩ := hcel
      have hcel_eq : cel = a * b * a⁻¹ * b⁻¹ := hab.symm
      have haM' : ((a : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact a.2
      have hbM' : ((b : ↥(derivedInG M)) : G) ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U := by
        rw [← hM'eq]; exact b.2
      obtain ⟨ha', hha', ua, hua, haeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M haM'
      obtain ⟨hb', hhb', ub, hub, hbeq⟩ :=
        exists_mul_of_mem_sup_of_normalized hHle hUle hyp.H_normalized_by_M hbM'
      have haMm : ((a : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) a.2
      have hbMm : ((b : ↥(derivedInG M)) : G) ∈ M := (Subgroup.map_subtype_le _) b.2
      set A : ↥M := ⟨((a : ↥(derivedInG M)) : G), haMm⟩ with hA
      set B : ↥M := ⟨((b : ↥(derivedInG M)) : G), hbMm⟩ with hB
      set HA : ↥M := ⟨ha', hHle hha'⟩ with hHA
      set HB : ↥M := ⟨hb', hHle hhb'⟩ with hHB
      set UA : ↥M := ⟨ua, hUle hua⟩ with hUA
      set UB : ↥M := ⟨ub, hUle hub⟩ with hUB
      have hAeq : A = HA * UA := by
        ext; rw [haeq]; rfl
      have hBeq : B = HB * UB := by
        ext; rw [hbeq]; rfl
      -- `H`-parts are mod-`K₁` central among `M'`-images
      have hmemM' : ∀ g ∈ hyp.base.typeP.H ⊔ hyp.base.typeP.U, g ∈ derivedInG M := by
        intro g hg; rwa [hM'eq]
      have hswHU : ∀ (h u : ↥M), (h : G) ∈ hyp.base.typeP.H → (u : G) ∈ derivedInG M →
          Commute (φ u) (φ h) := by
        intro h u hh hu
        refine (hswK h u ?_).symm
        rw [hKernel]
        exact Subgroup.commutator_mem_commutator hh hu
      have hkey : φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹
          = φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹ := by
        rw [hAeq, hBeq, map_mul, map_mul]
        rw [commutator_mul_of_commute
          (hswHU HB UA (by exact hhb') (hmemM' _ (Subgroup.mem_sup_right hua)))
          (hswHU HA UA (by exact hha') (hmemM' _ (Subgroup.mem_sup_right hua)))
          (hswHU HA UB (by exact hha') (hmemM' _ (Subgroup.mem_sup_right hub)))
          (hswHU HB UB (by exact hhb') (hmemM' _ (Subgroup.mem_sup_right hub)))]
        have hHH1 : φ HA * φ HB * (φ HA)⁻¹ * (φ HB)⁻¹ = 1 := by
          have hsw : Commute (φ HA) (φ HB) := by
            refine hswK HA HB ?_
            rw [hKernel]
            refine Subgroup.commutator_mem_commutator (by exact hha') ?_
            exact hyp.base.typeP.H_le hhb'
          rw [hsw.eq]
          group
        rw [hHH1, one_mul]
      have hratio : (A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹
          ∈ hyp.hKernel.subgroupOf M := by
        have hmapped : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹)
            = (φ A * φ B * (φ A)⁻¹ * (φ B)⁻¹)
              * (φ UA * φ UB * (φ UA)⁻¹ * (φ UB)⁻¹)⁻¹ := by
          simp only [map_mul, map_inv]
        have h1 : φ ((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹) = 1 := by
          rw [hmapped, hkey]
          group
        exact (QuotientGroup.eq_one_iff
          (N := hyp.hKernel.subgroupOf M) _).mp h1
      have hcomm_coe : (((derivedInG M).subtype) cel : G)
          = ((A * B * A⁻¹ * B⁻¹ : ↥M) : G) := by
        rw [hcel_eq]; exact rfl
      have hsplit : ((A * B * A⁻¹ * B⁻¹ : ↥M) : G)
          = (((A * B * A⁻¹ * B⁻¹) * (UA * UB * UA⁻¹ * UB⁻¹)⁻¹ : ↥M) : G)
            * ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) := by
        push_cast
        group
      rw [hcomm_coe, hsplit]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact Subgroup.mem_subgroupOf.mp hratio
      · have hUcomm : ua * ub * ua⁻¹ * ub⁻¹ ∈ derivedInG hyp.base.typeP.U := by
          rw [show derivedInG hyp.base.typeP.U
              = ⁅hyp.base.typeP.U, hyp.base.typeP.U⁆
            from Subgroup.map_subtype_commutator hyp.base.typeP.U]
          exact Subgroup.commutator_mem_commutator hua hub
        have hcoe : ((UA * UB * UA⁻¹ * UB⁻¹ : ↥M) : G) = ua * ub * ua⁻¹ * ub⁻¹ := by
          push_cast
          rfl
        rw [hcoe]
        exact hUcomm

end Hypothesis

end OddOrder.Peterfalvi.S13


