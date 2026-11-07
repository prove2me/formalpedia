-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:33:07.042229+00:00
-- url     : https://prove2.me/theorems/28919c7c-ce68-4c82-80e8-04f336c3ffab
-- title:
--   Index Selection
-- statement:
--   Definitions and structural lemmas for Index Selection, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexSelection.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_residueExponent_ne_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
namespace IndexSelection
variable (F L : Type*) [Field F] [Field L] [Fintype F] [Fintype L]
  [Algebra F L] [FiniteDimensional F L]
abbrev dthPowerUnits (d : Nat) : Subgroup Lˣ :=
  (powMonoidHom d : Lˣ →* Lˣ).range
abbrev PowerClass (d : Nat) :=
  Lˣ ⧸ dthPowerUnits L d
theorem natCard_powerClass (d : Nat) :
    Nat.card (PowerClass L d) = (Fintype.card L - 1).gcd d := by
  rw [← Subgroup.index_eq_card,
    IsCyclic.index_powMonoidHom_range, Nat.card_units,
    Nat.card_eq_fintype_card]
noncomputable def unitGenerator : Lˣ :=
  Classical.choose (IsCyclic.exists_generator (α := Lˣ))
theorem unitGenerator_generates (u : Lˣ) :
    u ∈ Subgroup.zpowers (unitGenerator L) :=
  Classical.choose_spec (IsCyclic.exists_generator (α := Lˣ)) u
theorem powerClassGenerator_generates (d : Nat)
    (c : PowerClass L d) :
    c ∈ Subgroup.zpowers
      (QuotientGroup.mk (unitGenerator L) : PowerClass L d) := by
  refine Quotient.inductionOn c ?_
  intro u
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (unitGenerator_generates L u)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  change (QuotientGroup.mk' (dthPowerUnits L d)) (unitGenerator L) ^ k =
    (QuotientGroup.mk' (dthPowerUnits L d)) u
  simpa only [map_zpow] using
    congrArg (QuotientGroup.mk' (dthPowerUnits L d)) hk
theorem orderOf_powerClassGenerator (d : Nat) :
    orderOf (QuotientGroup.mk (unitGenerator L) : PowerClass L d) =
      (Fintype.card L - 1).gcd d := by
  rw [orderOf_eq_card_of_forall_mem_zpowers
    (powerClassGenerator_generates L d), natCard_powerClass L d]
def mobius (u : Lˣ) : L :=
  (u : L) / (1 - (u : L))
omit [Fintype L] in
theorem mobius_injOn :
    Set.InjOn (mobius L) {u : Lˣ | u ≠ 1} := by
  intro u hu v hv huv
  have hdu : 1 - (u : L) ≠ 0 := by
    intro h
    apply hu
    apply Units.ext
    simpa using (sub_eq_zero.mp h).symm
  have hdv : 1 - (v : L) ≠ 0 := by
    intro h
    apply hv
    apply Units.ext
    simpa using (sub_eq_zero.mp h).symm
  have hcross : (u : L) * (1 - (v : L)) =
      (v : L) * (1 - (u : L)) :=
    (div_eq_div_iff hdu hdv).mp huv
  apply Units.ext
  calc
    (u : L) = (u : L) * (1 - (v : L)) + (u : L) * (v : L) := by ring
    _ = (v : L) * (1 - (u : L)) + (u : L) * (v : L) := by rw [hcross]
    _ = (v : L) := by ring
def generatorFiber (d : Nat) : Set Lˣ :=
  QuotientGroup.mk ⁻¹'
    ({(QuotientGroup.mk (unitGenerator L) : PowerClass L d)} :
      Set (PowerClass L d))
theorem ncard_generatorFiber (d : Nat) :
    Set.ncard (generatorFiber L d) =
      Nat.card (dthPowerUnits L d) := by
  let H := dthPowerUnits L d
  let t : Set (Lˣ ⧸ H) :=
    {(QuotientGroup.mk (unitGenerator L) : Lˣ ⧸ H)}
  change Set.ncard (QuotientGroup.mk ⁻¹' t) = Nat.card H
  change Nat.card (QuotientGroup.mk ⁻¹' t) = Nat.card H
  rw [Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H t),
    Nat.card_prod]
  simp [t]
theorem generatorFiber_ne_one {d : Nat}
    (hg : 1 < (Fintype.card L - 1).gcd d)
    {u : Lˣ} (hu : u ∈ generatorFiber L d) : u ≠ 1 := by
  intro huone
  have hclass :
      (QuotientGroup.mk (unitGenerator L) : PowerClass L d) = 1 := by
    subst u
    change (1 : PowerClass L d) =
      (QuotientGroup.mk (unitGenerator L) : PowerClass L d) at hu
    exact hu.symm
  have horder := orderOf_powerClassGenerator L d
  rw [hclass, orderOf_one] at horder
  omega
theorem exists_generatorClass_mobius_adjoin_eq_top
    (d e : Nat) (hq : 5 ≤ Fintype.card F) (hdpos : 0 < d) (hd : d ≤ 4)
    (hfinrank : Module.finrank F L = e) (he : 3 ≤ e)
    (hg : 1 < (Fintype.card L - 1).gcd d) :
    ∃ u : Lˣ, u ∈ generatorFiber L d ∧
      F⟮mobius L u⟯ = ⊤ := by
  classical
  let q := Fintype.card F
  let Q := Fintype.card L
  let g := (Q - 1).gcd d
  let B := q ^ (e / 2 + 1)
  let candidates : Set Lˣ := generatorFiber L d
  let bad : Set L := {x | F⟮x⟯ ≠ ⊤}
  have hqpos : 0 < q := Fintype.card_pos
  have hBpos : 0 < B := pow_pos hqpos _
  have hhalf : e / 2 + 2 ≤ e := by omega
  have hQL : Q = q ^ e := by
    dsimp [Q, q]
    rw [← hfinrank, ← Module.card_eq_pow_finrank]
  have hqfour : 4 < q := lt_of_lt_of_le (by omega) hq
  have hpowle : q * B ≤ Q := by
    calc
      q * B = q ^ (e / 2 + 2) := by
        simp [B, pow_succ, mul_comm]
      _ ≤ q ^ e := pow_le_pow_right' (by omega) hhalf
      _ = Q := hQL.symm
  have hfourB : 4 * B ≤ Q - 1 := by
    have hlt : 4 * B < Q :=
      ((Nat.mul_lt_mul_right hBpos).2 hqfour).trans_le hpowle
    omega
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right _ hdpos
  have hgle : g ≤ 4 := by
    calc
      g ≤ d := Nat.gcd_le_right _ hdpos
      _ ≤ 4 := hd
  have hB_le_rangeCard :
      B ≤ Nat.card (dthPowerUnits L d) := by
    have hrange :
        Nat.card (dthPowerUnits L d) = (Q - 1) / g := by
      simpa [Q, g, dthPowerUnits, Nat.card_units,
        Nat.card_eq_fintype_card, Fintype.card_units] using
        (IsCyclic.card_powMonoidHom_range (G := Lˣ) d)
    rw [hrange, Nat.le_div_iff_mul_le hgpos]
    calc
      B * g ≤ B * 4 := Nat.mul_le_mul_left B hgle
      _ = 4 * B := Nat.mul_comm _ _
      _ ≤ Q - 1 := hfourB
  have hbad : Set.ncard bad < B := by
    dsimp [bad, B, q]
    simpa [hfinrank] using
      (ResidueSelection.ncard_nonGenerators_lt F L)
  have hcandidates : B ≤ Set.ncard candidates := by
    dsimp [candidates]
    rw [ncard_generatorFiber L d]
    exact hB_le_rangeCard
  by_contra hnone
  have hmaps : ∀ u ∈ candidates, mobius L u ∈ bad := by
    intro u hu
    show F⟮mobius L u⟯ ≠ ⊤
    intro htop
    apply hnone
    exact ⟨u, hu, htop⟩
  have hsubset : candidates ⊆ {u : Lˣ | u ≠ 1} := by
    intro u hu
    exact generatorFiber_ne_one L hg hu
  have hinj : Set.InjOn (mobius L) candidates :=
    (mobius_injOn L).mono hsubset
  have hcardle : Set.ncard candidates ≤ Set.ncard bad :=
    Set.ncard_le_ncard_of_injOn (mobius L) hmaps hinj (Set.toFinite bad)
  exact (Nat.not_le_of_lt (hbad.trans_le hcandidates)) hcardle
theorem exists_fullOrder_mobius_adjoin_eq_top
    (d e : Nat) (hq : 5 ≤ Fintype.card F) (hdpos : 0 < d) (hd : d ≤ 4)
    (hfinrank : Module.finrank F L = e) (he : 3 ≤ e) :
    ∃ u : Lˣ, F⟮mobius L u⟯ = ⊤ ∧
      orderOf (QuotientGroup.mk u : PowerClass L d) =
        (Fintype.card L - 1).gcd d := by
  classical
  let g := (Fintype.card L - 1).gcd d
  by_cases hg : 1 < g
  · obtain ⟨u, hu, htop⟩ :=
      exists_generatorClass_mobius_adjoin_eq_top F L d e hq hdpos hd
        hfinrank he hg
    refine ⟨u, htop, ?_⟩
    have hu' :
        (QuotientGroup.mk u : PowerClass L d) =
          (QuotientGroup.mk (unitGenerator L) : PowerClass L d) := hu
    rw [hu', orderOf_powerClassGenerator L d]
  · have hgpos : 0 < g := by
      dsimp [g]
      exact Nat.gcd_pos_of_pos_right _ hdpos
    have hgone : g = 1 := by omega
    obtain ⟨y, hy⟩ := Field.exists_primitive_element F L
    have hydegree : ResidueSelection.elementDegree F L y = e := by
      rw [← hfinrank]
      exact (ResidueSelection.adjoin_eq_top_iff_elementDegree_eq F L y).mp hy
    have hynotmem : y ∉ (algebraMap F L).range := by
      intro hymem
      have hdegreeOne : (minpoly F y).natDegree = 1 :=
        minpoly.natDegree_eq_one_iff.mpr hymem
      change (minpoly F y).natDegree = e at hydegree
      rw [hdegreeOne] at hydegree
      omega
    have hyzero : y ≠ 0 := by
      intro h
      apply hynotmem
      refine ⟨0, ?_⟩
      simp [h]
    have hyone : 1 + y ≠ 0 := by
      intro h
      apply hynotmem
      refine ⟨-1, ?_⟩
      have hyneg : y = -1 := eq_neg_of_add_eq_zero_right h
      simp [hyneg]
    let u : Lˣ := Units.mk0 (y / (1 + y))
      (div_ne_zero hyzero hyone)
    have hmobius : mobius L u = y := by
      dsimp [mobius, u]
      field_simp [hyone]
      ring
    refine ⟨u, ?_, ?_⟩
    · simpa [hmobius] using hy
    · have hdvd :
          orderOf (QuotientGroup.mk u : PowerClass L d) ∣
            Nat.card (PowerClass L d) := orderOf_dvd_natCard _
      rw [natCard_powerClass L d, ← show g =
        (Fintype.card L - 1).gcd d from rfl, hgone] at hdvd
      have hordone := Nat.dvd_one.mp hdvd
      change orderOf (QuotientGroup.mk u : PowerClass L d) = g
      exact hordone.trans hgone.symm
end IndexSelection
open IndexSelection
abbrev ResiduePowerClass (P : BasePrime) (r : Rank) (level : Nat) :=
  PowerClass (ResidueField P r level) (Fintype.card (Fin r.matrixRank))
theorem exists_indexRatioUnit (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ u : (ResidueField P r level)ˣ,
      (BaseField P)⟮mobius (ResidueField P r level) u⟯ = ⊤ ∧
      orderOf (QuotientGroup.mk u : ResiduePowerClass P r level) =
        (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank := by
  simpa only [Fintype.card_fin] using
    (exists_fullOrder_mobius_adjoin_eq_top
      (BaseField P) (ResidueField P r level)
      (Fintype.card (Fin r.matrixRank)) (r.residueExponent level)
      (by simpa [BaseField, ZMod.card] using P.five_le)
      (by cases r <;> norm_num [Rank.matrixRank, Fintype.card_fin])
      (by cases r <;> norm_num [Rank.matrixRank, Fintype.card_fin])
      (GaloisField.finrank P.q (Rank.residueExponent_ne_zero r level))
      (by cases r <;>
        simp [Rank.residueExponent, Rank.matrixRank] <;> omega))
noncomputable def indexRatioUnit (P : BasePrime) (r : Rank) (level : Nat) :
    (ResidueField P r level)ˣ :=
  Classical.choose (exists_indexRatioUnit P r level)
noncomputable def indexPlaceY (P : BasePrime) (r : Rank) (level : Nat) :
    ResidueField P r level :=
  mobius (ResidueField P r level) (indexRatioUnit P r level)
noncomputable def indexPlacePolynomial
    (P : BasePrime) (r : Rank) (level : Nat) :
    Polynomial (BaseField P) :=
  minpoly (BaseField P) (indexPlaceY P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


