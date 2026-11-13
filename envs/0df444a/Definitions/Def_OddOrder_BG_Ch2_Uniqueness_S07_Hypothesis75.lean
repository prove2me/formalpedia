-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Hypothesis75
-- name    : OddOrder_BG_Ch2_Uniqueness_S07_Hypothesis75
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:32.240556+00:00
-- url     : https://prove2.me/theorems/84af1f4f-40cb-4d07-9829-8767caba5300
-- title:
--   BG §7: Hypothesis 7.5
-- statement:
--   Part of the Bender–Glauberman §7 transitivity development, concerning Hypothesis 7.5. The bundle consists of lemmas only.
--
--   The bundle also proves 25 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S07_Hypothesis75.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S07_Hypothesis75.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_SolvablePrimeIndex
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.BG.Ch2.S07

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch06 (actionFixedBy mem_actionFixedBy nontrivialActionFixedByClosure
  nontrivialActionFixedByClosure_le_iff)

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **subnormal proper ⟹ 真の正規 overgroup** (Thm 7.4 還元 R1 step1): `A'` が `Q` で subnormal
かつ `A' < ⊤` なら `∃ B ⊴ Q`, `A' ≤ B < ⊤`。subnormal 系列の頂点直下を `IsSubnormal` 帰納で。 -/
private theorem exists_normal_lt_top_of_isSubnormal {Q : Type*} [Group Q] {A' : Subgroup Q}
    (hA' : A'.IsSubnormal) (hlt : A' < ⊤) :
    ∃ B : Subgroup Q, A' ≤ B ∧ B < ⊤ ∧ B.Normal := by
  revert hlt
  induction hA' with
  | top => intro hlt; exact absurd rfl hlt.ne
  | step H K hle hSubn hN ih =>
    intro hlt
    rcases eq_or_lt_of_le (le_top : K ≤ ⊤) with hKtop | hKlt
    · refine ⟨H, le_refl _, hlt, ?_⟩
      subst hKtop
      exact Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN))
    · obtain ⟨B, hKB, hBlt, hBnorm⟩ := ih hKlt
      exact ⟨B, hle.trans hKB, hBlt, hBnorm⟩

/-- **Theorem 7.4 composition-series 還元** (R1, mmd L2206-2216): `A < P` subnormal, `P` 可解
(`hG`+`P<⊤`) ⟹ `∃ B`, `A ≤ B < P`, `B ⊴ P`, `|P:B|` 素数。subnormal 系列頂点直下
(`exists_normal_lt_top_of_isSubnormal`) を素数指数化 (`exists_normal_index_prime_of_isSolvable`
@`↥P⧸B̄`) し pull back + `↥P`→`G` translate。「`A` subnormal in `B`」は R3 で別途。 -/
private theorem tp_reduction [Finite G] (hG : IsMinimalSimpleOdd G) {A P : Subgroup G}
    (hAP : A ≤ P) (hAlt : A < P) (hPlt : P < ⊤) (hAsub : (A.subgroupOf P).IsSubnormal) :
    ∃ B : Subgroup G, A ≤ B ∧ B < P ∧ (B.subgroupOf P).Normal ∧ (B.subgroupOf P).index.Prime := by
  have : Group.IsSolvable ↥P := hG.isSolvable_of_lt_top P hPlt
  have hA'lt : A.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hAlt.not_ge h
  obtain ⟨Bbar, hABbar, hBbarlt, hBbarnorm⟩ := exists_normal_lt_top_of_isSubnormal hAsub hA'lt
  have := hBbarnorm
  have hnt : Nontrivial (↥P ⧸ Bbar) := by
    obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt hBbarlt
    exact ⟨QuotientGroup.mk x, 1, by rw [Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  obtain ⟨Nbar, hNbarnorm, hNbarprime⟩ :=
    OddOrder.GroupTheory.exists_normal_index_prime_of_isSolvable hnt
  set C : Subgroup ↥P := Nbar.comap (QuotientGroup.mk' Bbar) with hC
  have : C.Normal := hNbarnorm.comap _
  have hBbarC : Bbar ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_comap,
      show (QuotientGroup.mk' Bbar) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hCindex : C.index = Nbar.index :=
    Nbar.index_comap_of_surjective (QuotientGroup.mk'_surjective Bbar)
  have hCeq : (C.map P.subtype).subgroupOf P = C :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective C
  refine ⟨C.map P.subtype, ?_, ?_, ?_, ?_⟩
  · have hAC : A.subgroupOf P ≤ C := hABbar.trans hBbarC
    have hA_eq : (A.subgroupOf P).map P.subtype = A := by
      rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hAP
    rw [← hA_eq]; exact Subgroup.map_mono hAC
  · refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
    intro hBP
    have : C = ⊤ := by rw [← hCeq, hBP, Subgroup.subgroupOf_self]
    rw [this, Subgroup.index_top] at hCindex
    exact hNbarprime.ne_one hCindex.symm
  · rw [hCeq]; infer_instance
  · rw [hCeq, hCindex]; exact hNbarprime

/-- **Theorem 7.4(a)** (mmd L2204): `C_G(P) ⊓ K = O_{π'}(C_G(P))`。`A ≤ P` ⟹ `C_G(P) ⊆ C_G(A)`,
`K = O_{π'}(C_G(A)) ⊴ C_G(A)` ゆえ `C_G(P)⊓K` は `C_G(P)` の正規 `π'`-部分群 (⊆ O_{π'});
逆は O_{π'}(C_G(P)) の各元が `C_G(A)` の `π'`-元 ⟹ §7 Note で `K` 入り。 -/
private theorem tp_centralizer_eq [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {P : Subgroup G} (hAP : A ≤ P) :
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) := by
  set π' : Set ℕ := (primesOf A)ᶜ
  set CP : Subgroup G := Subgroup.centralizer (P : Set G) with hCP
  have hCPCA : CP ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    exact fun y hy => hx y (hAP hy)
  have hCPnK : CP ≤ Subgroup.normalizer (kSubgroup A) :=
    hCPCA.trans (le_normalizer_opiCoreInG _ _)
  apply le_antisymm
  · refine le_opiCoreInG_of_normal_of_isPiSubgroup inf_le_left ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) h
      have h2 := Subgroup.mem_normalizer_iff.mp (hCPnK hx) h
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨h1.mp ha, h2.mp hb⟩
      · rintro ⟨ha, hb⟩; exact ⟨h1.mpr ha, h2.mpr hb⟩
    · intro r hr
      have hdvd : Nat.card ↥(CP ⊓ kSubgroup A) ∣ Nat.card ↥(kSubgroup A) :=
        Subgroup.card_dvd_of_le inf_le_right
      refine isPiSubgroup_kSubgroup A r ?_
      rw [Nat.mem_primeFactors] at hr ⊢
      exact ⟨hr.1, hr.2.1.trans hdvd, Nat.card_pos.ne'⟩
  · refine le_inf (opiCoreInG_le _ _) ?_
    intro c hc
    refine mem_kSubgroup_of_piPrime_mem_centralizer hG hA (hCPCA (opiCoreInG_le _ _ hc)) ?_
    have hzle : Subgroup.zpowers c ≤ opiCoreInG π' CP := Subgroup.zpowers_le.mpr hc
    intro r hr
    refine isPiSubgroup_opiCoreInG π' CP r ?_
    have hdvd : Nat.card ↥(Subgroup.zpowers c) ∣ Nat.card ↥(opiCoreInG π' CP) :=
      Subgroup.card_dvd_of_le hzle
    rw [Nat.mem_primeFactors] at hr ⊢
    exact ⟨hr.1, hr.2.1.trans hdvd, Nat.card_pos.ne'⟩

/-- `A ≤ B ≤ P` で `P` が `π(A)`-群なら `π(B) = π(A)` (`A≤B` で `⊆`、`B≤P` で `⊇`)。
Thm 7.4 帰納で `B` を `A` の役に据えるとき `π` 不変を保証。 -/
private theorem primesOf_eq_of_le_of_isPiSubgroup [Finite G] {A B P : Subgroup G}
    (hAB : A ≤ B) (hBP : B ≤ P) (hP : Subgroup.IsPiSubgroup (primesOf A) P) :
    primesOf B = primesOf A := by
  have hAB_card : Nat.card ↥A ∣ Nat.card ↥B := Subgroup.card_dvd_of_le hAB
  have hBP_card : Nat.card ↥B ∣ Nat.card ↥P := Subgroup.card_dvd_of_le hBP
  ext r
  constructor
  · intro hr
    have hrB : r ∈ (Nat.card ↥B).primeFactors := hr
    rw [Nat.mem_primeFactors] at hrB
    exact hP r (Nat.mem_primeFactors.mpr ⟨hrB.1, hrB.2.1.trans hBP_card, Nat.card_pos.ne'⟩)
  · intro hr
    have hrA : r ∈ (Nat.card ↥A).primeFactors := hr
    rw [Nat.mem_primeFactors] at hrA
    exact Nat.mem_primeFactors.mpr ⟨hrA.1, hrA.2.1.trans hAB_card, Nat.card_pos.ne'⟩

/-- **Hypothesis 7.1 の単調性** (mmd L2212 "Hypothesis 7.1 is satisfied with `B`"): `A ≤ B`,
`π(B) = π(A)`, `B ≠ 1`, `B < ⊤` なら `Hypothesis71 B`。`generated_eq` は
`ℋ_X(B;π') ⊆ ℋ_X(A;π')` と `O_{π'}(X) ∈ ℋ_X(B;π')` から。 -/
private theorem tp_hyp71_of_le [Finite G] {A B : Subgroup G} (hA : Hypothesis71 A)
    (hAB : A ≤ B) (hprimes : primesOf B = primesOf A) (hBne : B ≠ ⊥) (hBlt : B < ⊤) :
    Hypothesis71 B := by
  refine ⟨hBne, hBlt, ?_⟩
  intro X hBX hXlt
  rw [hprimes]
  have hAX : A ≤ X := hAB.trans hBX
  have hA_eq := hA.generated_eq X hAX hXlt
  refine le_antisymm ?_ ?_
  · rw [← hA_eq]
    refine sSup_le_sSup ?_
    intro Y hY
    exact ⟨hY.1, hAB.trans hY.2.1, hY.2.2⟩
  · exact le_sSup ⟨opiCoreInG_le _ _, hBX.trans (le_normalizer_opiCoreInG _ _),
      isPiSubgroup_opiCoreInG _ _⟩

/-- **(c) の `q`-群正規化条件 finish** (mmd L2230-2232): `Q ≤ Q₁` (`Q₁` `q`-群) かつ
`Q₁ ⊓ N_G(Q) ≤ Q` なら `Q = Q₁` (`q`-群で自己正規化部分群は全体)。 -/
private theorem eq_of_inf_normalizer_le [Finite G] {q : ℕ} [Fact q.Prime] {Q Q₁ : Subgroup G}
    (hQ₁ : IsPGroup q ↥Q₁) (hQQ₁ : Q ≤ Q₁) (hself : Q₁ ⊓ Subgroup.normalizer Q ≤ Q) :
    Q = Q₁ := by
  rcases eq_or_lt_of_le hQQ₁ with h | h
  · exact h
  · have hlt := lt_normalizer_inf_of_pgroup_lt hQ₁ h
    have heq : Q₁ ⊓ Subgroup.normalizer Q = Q :=
      le_antisymm hself (le_inf hQQ₁ Subgroup.le_normalizer)
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl Q)

/-- **(c) の `Q ≤ O_{π'}(N_G(Q))`**: `π`-部分群 `Q` は自身の正規化群の `O_π` に入る
(`Q ⊴ N_G(Q)` + `Q` は `π`-群; `le_opiCoreInG_of_normal_of_isPiSubgroup`)。 -/
private theorem le_opiCoreInG_normalizer_self [Finite G] {π : Set ℕ} {Q : Subgroup G}
    (hQpi : Subgroup.IsPiSubgroup π Q) :
    Q ≤ opiCoreInG π (Subgroup.normalizer Q) :=
  le_opiCoreInG_of_normal_of_isPiSubgroup Subgroup.le_normalizer
    Subgroup.normal_in_normalizer hQpi

/-- **`opiCoreInG` is `MulAut`-equivariant**: `φ • O_π(H) = O_π(φ • H)`. The `π`-core
`oPiCore π ↥H` is characteristic, so the iso `↥H ≃* ↥(φ•H)` induced by `φ` carries it onto
`oPiCore π ↥(φ•H)` (`oPiCore.map_eq_of_mulEquiv`); mapping back along the subtypes agrees with
applying `φ`. -/
private theorem conj_smul_opiCoreInG [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  -- `φ` restricts to an isomorphism `↥H ≃* ↥(φ • H)`.
  have hHmap : H.map (φ : G →* G) = φ • H := (mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := mulAut_smul_eq_map φ _
    _ = ((Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥H).map ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map (φ • H).subtype := by
        rw [← Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [Ch03.oPiCore.map_eq_of_mulEquiv]
    _ = opiCoreInG π (φ • H) := rfl

/-- **Conjugation by a normalizing element fixes the centralizer**: if `conj x • A = A`
then `conj x • C_G(A) = C_G(A)`. -/
private theorem conj_smul_centralizer_eq {A : Subgroup G} {x : G}
    (hAeq : MulAut.conj x • A = A) :
    MulAut.conj x • Subgroup.centralizer (A : Set G) = Subgroup.centralizer (A : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  have hAeq' : MulAut.conj x⁻¹ • A = A := by
    conv_lhs => rw [← hAeq]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hconj : ((MulAut.conj x)⁻¹ • y) = x⁻¹ * y * x := by
    rw [← map_inv]
    simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv]
  constructor
  · intro hy a ha
    have haxA : x⁻¹ * a * x ∈ A := by
      have hmem : MulAut.conj x⁻¹ a ∈ MulAut.conj x⁻¹ • A :=
        Subgroup.smul_mem_pointwise_smul_iff.mpr ha
      rw [hAeq'] at hmem
      simpa only [MulAut.conj_apply, inv_inv] using hmem
    have hc := hy (x⁻¹ * a * x) haxA
    rw [hconj] at hc
    have hkey : x⁻¹ * (a * y) * x = x⁻¹ * (y * a) * x := by
      calc x⁻¹ * (a * y) * x = (x⁻¹ * a * x) * (x⁻¹ * y * x) := by group
        _ = (x⁻¹ * y * x) * (x⁻¹ * a * x) := hc
        _ = x⁻¹ * (y * a) * x := by group
    exact mul_left_cancel (mul_right_cancel hkey)
  · intro hy a ha
    rw [hconj]
    have haxA : x * a * x⁻¹ ∈ A := by
      have hmem : MulAut.conj x a ∈ MulAut.conj x • A :=
        Subgroup.smul_mem_pointwise_smul_iff.mpr ha
      rw [hAeq] at hmem
      simpa only [MulAut.conj_apply] using hmem
    have hc := hy (x * a * x⁻¹) haxA
    calc a * (x⁻¹ * y * x) = x⁻¹ * ((x * a * x⁻¹) * y) * x := by group
      _ = x⁻¹ * (y * (x * a * x⁻¹)) * x := by rw [hc]
      _ = x⁻¹ * y * x * a := by group

/-- **`N_G(A)` normalizes `K = O_{π'}(C_G(A))`**: for `x ∈ N_G(A)`, conjugation fixes `C_G(A)`
(centralizer of the normalized `A`) and hence (by equivariance) its `π'`-core `K`. -/
private theorem conj_smul_kSubgroup_eq [Finite G] {A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer A) :
    MulAut.conj x • kSubgroup A = kSubgroup A := by
  rw [kSubgroup, conj_smul_opiCoreInG,
    conj_smul_centralizer_eq (conj_smul_eq_self_of_mem_normalizer hx)]

/-- **`N_G(P)` normalizes `O_{π'}(C_G(P))`**: same equivariance, for any subgroup `P`. -/
private theorem conj_smul_opiCore_centralizer_eq [Finite G] {π : Set ℕ} {P : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) :
    MulAut.conj x • opiCoreInG π (Subgroup.centralizer (P : Set G))
      = opiCoreInG π (Subgroup.centralizer (P : Set G)) := by
  rw [conj_smul_opiCoreInG,
    conj_smul_centralizer_eq (conj_smul_eq_self_of_mem_normalizer hx)]

/-- **Conjugation transports normalization**: `S ≤ N(Q) ⟹ conj g • S ≤ N(conj g • Q)`. -/
private theorem conj_smul_le_normalizer_of_le_normalizer {S Q : Subgroup G} {g : G}
    (hS : S ≤ Subgroup.normalizer Q) :
    MulAut.conj g • S ≤ Subgroup.normalizer (MulAut.conj g • Q) := by
  intro y hy
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
  have hyN : (MulAut.conj g)⁻¹ • y ∈ Subgroup.normalizer Q := hS hy
  -- `y = conj g • ((conj g)⁻¹ • y)` normalizes `conj g • Q`.
  apply mem_normalizer_of_conj_smul_eq_self
  have hcval : ((MulAut.conj g)⁻¹ • y) = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
  have hyeq : MulAut.conj y • (MulAut.conj g • Q)
      = MulAut.conj g • (MulAut.conj ((MulAut.conj g)⁻¹ • y) • Q) := by
    rw [hcval, smul_smul, smul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [hyeq, conj_smul_eq_self_of_mem_normalizer hyN]

/-- **Conjugation commutes with the normalizer** (equality form): `conj g • N(Q) = N(conj g • Q)`.
-/
private theorem conj_smul_normalizer_eq (g : G) (Q : Subgroup G) :
    MulAut.conj g • Subgroup.normalizer (Q : Set G)
      = Subgroup.normalizer ((MulAut.conj g • Q : Subgroup G) : Set G) := by
  refine le_antisymm (conj_smul_le_normalizer_of_le_normalizer (le_refl _)) ?_
  have hback := conj_smul_le_normalizer_of_le_normalizer
    (S := Subgroup.normalizer ((MulAut.conj g • Q : Subgroup G) : Set G))
    (Q := MulAut.conj g • Q) (g := g⁻¹) (le_refl _)
  have hQ' : MulAut.conj g⁻¹ • (MulAut.conj g • Q) = Q := by
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [hQ'] at hback
  intro y hy
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  have hmem : MulAut.conj g⁻¹ • y
      ∈ MulAut.conj g⁻¹ • Subgroup.normalizer ((MulAut.conj g • Q : Subgroup G) : Set G) :=
    Subgroup.smul_mem_pointwise_smul_iff.mpr hy
  exact hback hmem

/-- **A `K`-element normalizing `P` centralizes `P`** (`N_K(P) = C_K(P)`, mmd L2242): if
`A ⊴ P` (so `P ≤ N_G(A)`, whence `P` normalizes `K = O_{π'}(C_G(A))`) and `P ⊓ K = 1`
(coprime orders), then `c ∈ K` normalizing `P` lies in `C_G(P)`. For `x ∈ P`,
`⁅x, c⁆ ∈ P` (as `c ∈ N(P)`) and `⁅x, c⁆ ∈ K` (as `P ≤ N(K)`, `c ∈ K`), so `⁅x,c⁆ ∈ P⊓K = 1`. -/
private theorem mem_centralizer_of_mem_kSubgroup_normalizer [Finite G] {A P : Subgroup G}
    (hPnA : P ≤ Subgroup.normalizer A) (hPK : P ⊓ kSubgroup A = ⊥)
    {c : G} (hcK : c ∈ kSubgroup A) (hcN : c ∈ Subgroup.normalizer P) :
    c ∈ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  -- `⁅x, c⁆ = x c x⁻¹ c⁻¹ ∈ P ⊓ K = 1`.
  have hxcx : x * c * x⁻¹ ∈ kSubgroup A := by
    have h := conj_smul_kSubgroup_eq (hPnA hx)
    have hmem : MulAut.conj x c ∈ MulAut.conj x • kSubgroup A :=
      Subgroup.smul_mem_pointwise_smul_iff.mpr hcK
    rw [h] at hmem
    simpa only [MulAut.conj_apply] using hmem
  have hcomm_K : x * c * x⁻¹ * c⁻¹ ∈ kSubgroup A :=
    (kSubgroup A).mul_mem hxcx ((kSubgroup A).inv_mem hcK)
  have hcomm_P : x * c * x⁻¹ * c⁻¹ ∈ P := by
    have hcxc : c * x⁻¹ * c⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hcN x⁻¹).mp (P.inv_mem hx)
    have : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [this]; exact P.mul_mem hx hcxc
  have hcomm_one : x * c * x⁻¹ * c⁻¹ = 1 := by
    have : x * c * x⁻¹ * c⁻¹ ∈ P ⊓ kSubgroup A := Subgroup.mem_inf.mpr ⟨hcomm_P, hcomm_K⟩
    rw [hPK, Subgroup.mem_bot] at this
    exact this
  -- `x c x⁻¹ c⁻¹ = 1 ⟹ x * c = c * x`.
  have : x * c = c * x := by
    have h2 : x * c * x⁻¹ = c := mul_inv_eq_one.mp hcomm_one
    calc x * c = (x * c * x⁻¹) * x := by group
      _ = c * x := by rw [h2]
  exact this

/-- **`ℋ_⊤(A;π)` は `N_G(A)`-共役で安定** (C_G(A) 版 `conj_smul_mem_hInvariant_top` の N_G(A) 拡張)。
`g` が `A` を (conj 作用で) 不変にすれば `conj g • Q` も `A`-不変。 -/
private theorem conj_smul_mem_hInvariant_of_normalizer {A : Subgroup G} {π : Set ℕ}
    {Q : Subgroup G} (hQ : Q ∈ hInvariant ⊤ A π) {g : G} (hgA : MulAut.conj g • A = A) :
    MulAut.conj g • Q ∈ hInvariant ⊤ A π := by
  obtain ⟨-, hQnorm, hQpi⟩ := hQ
  have hgA' : MulAut.conj g⁻¹ • A = A := by
    conv_lhs => rw [← hgA]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨le_top, ?_, ?_⟩
  · intro a ha
    apply mem_normalizer_of_conj_smul_eq_self
    have ha' : g⁻¹ * a * g ∈ A := by
      have hmem : MulAut.conj g⁻¹ a ∈ MulAut.conj g⁻¹ • A :=
        Subgroup.smul_mem_pointwise_smul_iff.mpr ha
      rw [hgA'] at hmem
      simpa only [MulAut.conj_apply, inv_inv] using hmem
    calc MulAut.conj a • MulAut.conj g • Q
        = MulAut.conj (a * g) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj (g * (g⁻¹ * a * g)) • Q := by group
      _ = MulAut.conj g • MulAut.conj (g⁻¹ * a * g) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj g • Q := by
          rw [conj_smul_eq_self_of_mem_normalizer (hQnorm ha')]
  · have hcard : Nat.card ↥(MulAut.conj g • Q) = Nat.card ↥Q :=
      (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Q).toEquiv).symm
    intro r hr
    rw [hcard] at hr
    exact hQpi r hr

/-- **`ℋ_⊤*(A;π)` は `N_G(A)`-共役で安定**: 極大性は順序同型 `Q ↦ Q^g` で移送。 -/
private theorem conj_smul_mem_hInvariantStar_of_normalizer {A : Subgroup G} {π : Set ℕ}
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ A π) {g : G} (hgA : MulAut.conj g • A = A) :
    MulAut.conj g • Q ∈ hInvariantStar ⊤ A π := by
  obtain ⟨hQmem, hQmax⟩ := hQ
  have hgA' : MulAut.conj g⁻¹ • A = A := by
    conv_lhs => rw [← hgA]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨conj_smul_mem_hInvariant_of_normalizer hQmem hgA, ?_⟩
  intro Q' hQ' hle
  have h1 : MulAut.conj g⁻¹ • Q' ∈ hInvariant ⊤ A π :=
    conj_smul_mem_hInvariant_of_normalizer hQ' hgA'
  have h2 : Q ≤ MulAut.conj g⁻¹ • Q' := by
    calc Q = MulAut.conj g⁻¹ • MulAut.conj g • Q := by
          rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ ≤ MulAut.conj g⁻¹ • Q' := by
          rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]; exact hle
  have h3 : MulAut.conj g⁻¹ • Q' = Q := hQmax _ h1 h2
  calc Q' = MulAut.conj g • MulAut.conj g⁻¹ • Q' := by
        rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    _ = MulAut.conj g • Q := by rw [h3]

/-- **Theorem 7.4(c) 主要 case** (mmd L2224-2232): `Q ∈ ℋ*(P;q)` 非自明 ⟹ `Q ∈ ℋ*(A;q)`。
`Q ⊆ Q₁ ∈ ℋ*(A;q)`; `M := O_{π'}(N_G(Q))`; Prop 1.5(b) で `Q ⊆` P-不変 Sylow-q `R₂` of `M`,
`Q ∈ ℋ*(P;q)` 極大で `Q = R₂`; Hyp 7.1 で `Q₁⊓N(Q) ⊆ M`; 位数 `|Q|=|R₂|=|M|_q ≥ |Q₁⊓N(Q)| ≥ |Q|`
⟹ `Q = Q₁⊓N(Q)`, `eq_of_inf_normalizer_le` で `Q = Q₁`。`commonConstruction` の relativize を踏襲。 -/
private theorem tp_c_main [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ P {q}) (hQne : Q ≠ ⊥) :
    Q ∈ hInvariantStar ⊤ A {q} := by
  classical
  set π' : Set ℕ := (primesOf A)ᶜ with hπ'
  have hPnQ : P ≤ Subgroup.normalizer Q := hInvariantStar_le_normalizer hQ
  have hQpi : Subgroup.IsPiSubgroup {q} Q := hInvariantStar_isPiSubgroup hQ
  have hQpi' : Subgroup.IsPiSubgroup π' Q := hQpi.mono (Set.singleton_subset_iff.mpr hq)
  have hAnQ : A ≤ Subgroup.normalizer Q := hAP.trans hPnQ
  obtain ⟨Q₁, hQ₁star, hQQ₁⟩ :=
    exists_le_hInvariantStar (H := ⊤) (A := A) (π := {q}) ⟨le_top, hAnQ, hQpi⟩
  suffices hQeqQ₁ : Q = Q₁ by rw [hQeqQ₁]; exact hQ₁star
  have hQlt : Q < ⊤ := lt_top_of_mem_hInvariantStar hG hQ
  have hNQ_lt : Subgroup.normalizer (Q : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal Q inferInstance with h | h
    · exact hQne h
    · exact (ne_of_lt hQlt) h
  set NQ : Subgroup G := Subgroup.normalizer Q with hNQ
  set M : Subgroup G := opiCoreInG π' NQ with hMdef
  have hM_le : M ≤ NQ := opiCoreInG_le _ _
  have hM_lt : M < ⊤ := lt_of_le_of_lt hM_le hNQ_lt
  have hM_solv : Group.IsSolvable ↥M := hG.isSolvable_of_lt_top M hM_lt
  have hPnM : P ≤ Subgroup.normalizer M := hPnQ.trans (le_normalizer_opiCoreInG π' NQ)
  have hM_inv : Ch03.IsAInvariant (conjAction P) M := isAInvariant_conjAction_iff.mpr hPnM
  have hCop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥M) := by
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => hP_pi p hp) (fun p hp => ?_)
    exact isPiSubgroup_opiCoreInG π' NQ p hp
  have hQM : Q ≤ M := le_opiCoreInG_normalizer_self hQpi'
  have hQ_inv : Ch03.IsAInvariant (conjAction P) Q := isAInvariant_conjAction_iff.mpr hPnQ
  have hQM_pi : Ch03.Subgroup.IsPiGroup {q} (Q.subgroupOf M) := by
    intro p hp
    exact hQpi p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv] at hp)
  have hQM_inv : Ch03.IsAInvariant hM_inv.restrict (Q.subgroupOf M) :=
    isAInvariant_subgroupOf_restrict hM_inv hQ_inv
  obtain ⟨R, hR_hall, hR_inv, hR_ge⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥M) (A := ↥P) (φ := hM_inv.restrict) hCop hQM_pi hQM_inv
  set R₂ : Subgroup G := R.map M.subtype with hR₂def
  have hR₂_pi : Subgroup.IsPiSubgroup {q} R₂ := by
    intro p hp
    rw [hR₂def, ← Nat.card_congr (Subgroup.equivMapOfInjective R M.subtype
      M.subtype_injective).toEquiv] at hp
    exact hR_hall.1 p hp
  have hR₂_inv : P ≤ Subgroup.normalizer R₂ :=
    isAInvariant_conjAction_iff.mp (isAInvariant_map_subtype_of_restrict hM_inv hR_inv)
  have hQR₂ : Q ≤ R₂ := by
    rw [hR₂def]
    calc Q = (Q.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hQM).symm
      _ ≤ R.map M.subtype := Subgroup.map_mono hR_ge
  have hQeqR₂ : R₂ = Q := hInvariantStar_eq_of_le hQ ⟨le_top, hR₂_inv, hR₂_pi⟩ hQR₂
  -- `Q₁ ⊓ NQ ≤ M` via Hypothesis 7.1.
  have hnorm : A ≤ Subgroup.normalizer (Q₁ ⊓ NQ) := by
    intro a ha
    apply mem_normalizer_of_conj_smul_eq_self (Q := Q₁ ⊓ NQ)
    rw [Subgroup.smul_inf,
      conj_smul_eq_self_of_mem_normalizer (hInvariantStar_le_normalizer hQ₁star ha),
      conj_smul_eq_self_of_mem_normalizer ((hAnQ.trans Subgroup.le_normalizer) ha)]
  have hQ₁NQ_pi' : Subgroup.IsPiSubgroup π' (Q₁ ⊓ NQ) := by
    intro p hp
    have hpq : p = q := Set.mem_singleton_iff.mp ((hInvariantStar_isPiSubgroup hQ₁star) p
      (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
        (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_dvd_of_le inf_le_left),
        Nat.card_pos.ne'⟩))
    rw [hpq]; exact hq
  have hNQ₁_le_M : Q₁ ⊓ NQ ≤ M := by
    have h1 := le_sSup (s := hInvariant NQ A π') (a := Q₁ ⊓ NQ)
      ⟨inf_le_right, hnorm, hQ₁NQ_pi'⟩
    rwa [hA.generated_eq NQ hAnQ hNQ_lt] at h1
  -- Order: `|Q₁ ⊓ NQ| ∣ |R| = |R₂| = |Q|`.
  have h1 : Ch03.Subgroup.IsPiGroup {q} ((Q₁ ⊓ NQ).subgroupOf M) := by
    intro p hp
    have hp' : p ∈ (Nat.card ↥(Q₁ ⊓ NQ)).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNQ₁_le_M).toEquiv] at hp
    exact (hInvariantStar_isPiSubgroup hQ₁star) p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp').1, (Nat.mem_primeFactors.mp hp').2.1.trans
        (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
  have hcard_dvd : Nat.card ↥(Q₁ ⊓ NQ) ∣ Nat.card ↥R := by
    have hd := hR_hall.card_dvd_of_isPiGroup h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNQ₁_le_M).toEquiv] at hd
  have hcardR_eq : Nat.card ↥R = Nat.card ↥Q := by
    rw [← hQeqR₂, hR₂def,
      Nat.card_congr (Subgroup.equivMapOfInjective R M.subtype M.subtype_injective).toEquiv]
  have hle1 : Nat.card ↥(Q₁ ⊓ NQ) ≤ Nat.card ↥Q := by
    rw [← hcardR_eq]; exact Nat.le_of_dvd Nat.card_pos hcard_dvd
  have hQ_le_NQ₁ : Q ≤ Q₁ ⊓ NQ := le_inf hQQ₁ Subgroup.le_normalizer
  have heq : Q = Q₁ ⊓ NQ := Subgroup.eq_of_le_of_card_ge hQ_le_NQ₁ hle1
  exact eq_of_inf_normalizer_le
    (isPGroup_of_isPiSubgroup_singleton (hInvariantStar_isPiSubgroup hQ₁star)) hQQ₁
    (le_of_eq heq.symm)

/-- **BG Theorem 7.4 (7.3)** (mmd L2218-2220): `P` が `A` を (conj 作用で) 不変にし `g ∈ P`,
`g^p ∈ A`, `A ⊔ ⟨g⟩ = P` かつ `p ∤ |ℋ*(A;q)|` なら `P` は `ℋ*(A;q)` のある元を正規化する。
`P/A` は位数 `1` か `p` の `p`-群として `Ω = ℋ*(A;q)` に作用 (`A` は各元を固定) ⟹ 不動点
(`card_modEq_card_fixedPoints` + `p ∤ |Ω|`)。証明では生成元 `g` の誘導 perm `σ` の `zpowers σ`
を使う (`σ^p = 1` since `g^p ∈ A`)。 -/
private theorem tp_exists_normalized [Finite G] {A P : Subgroup G} {q : ℕ} [Fact q.Prime]
    {p : ℕ} [Fact p.Prime] (hPnA : ∀ x ∈ P, MulAut.conj x • A = A) {g : G} (hgP : g ∈ P)
    (hgpA : g ^ p ∈ A) (hsup : A ⊔ Subgroup.zpowers g = P)
    (hpdvd : ¬ p ∣ Nat.card ↥(hInvariantStar ⊤ A {q})) :
    ∃ Q ∈ hInvariantStar ⊤ A {q}, P ≤ Subgroup.normalizer Q := by
  classical
  set S : Set (Subgroup G) := hInvariantStar ⊤ A {q} with hS_def
  -- `↥P` acts on `↥S` by conjugation; `conj_smul_mem_hInvariantStar_of_normalizer` keeps us in `S`.
  let smulFn : ↥P → ↥S → ↥S := fun x Q => ⟨MulAut.conj (x : G) • (Q : Subgroup G),
      conj_smul_mem_hInvariantStar_of_normalizer Q.2 (hPnA (x : G) x.2)⟩
  let act : MulAction ↥P ↥S :=
    { smul := smulFn
      one_smul := fun Q => by
        apply Subtype.ext
        change MulAut.conj ((1 : ↥P) : G) • (Q : Subgroup G) = (Q : Subgroup G)
        rw [Subgroup.coe_one, map_one, one_smul]
      mul_smul := fun x y Q => by
        apply Subtype.ext
        change MulAut.conj (((x * y : ↥P)) : G) • (Q : Subgroup G)
          = MulAut.conj ((x : G)) • MulAut.conj ((y : G)) • (Q : Subgroup G)
        rw [Subgroup.coe_mul, map_mul, mul_smul] }
  have hsmul_coe : ∀ (x : ↥P) (Q : ↥S),
      ((x • Q : ↥S) : Subgroup G) = MulAut.conj (x : G) • (Q : Subgroup G) := fun _ _ => rfl
  -- The induced permutation of the generator `g`.
  set σ : Equiv.Perm ↥S := MulAction.toPermHom ↥P ↥S ⟨g, hgP⟩ with hσ_def
  -- `σ ^ p = 1` because `g ^ p ∈ A` acts trivially (every `Q ∈ S` is `A`-invariant).
  have hσp : σ ^ p = 1 := by
    rw [hσ_def, ← map_pow]
    apply Equiv.ext
    intro Q
    rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply]
    apply Subtype.ext
    rw [hsmul_coe, Subgroup.coe_pow]
    change MulAut.conj (g ^ p) • (Q : Subgroup G) = (Q : Subgroup G)
    exact conj_smul_eq_self_of_mem_normalizer
      ((hInvariantStar_le_normalizer Q.2) hgpA)
  -- `zpowers σ` is a `p`-group: its order `= orderOf σ ∣ p`.
  have hPgroup : IsPGroup p ↥(Subgroup.zpowers σ) := by
    rcases (Nat.dvd_prime (Fact.out (p := p.Prime))).mp
      (orderOf_dvd_of_pow_eq_one hσp) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  -- `p ∤ |S|` ⟹ fixed points are nonempty (`card_modEq_card_fixedPoints`).
  have hmod := hPgroup.card_modEq_card_fixedPoints (α := ↥S)
  have hcard_ne : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers σ) ↥S) ≠ 0 := by
    intro hzero
    apply hpdvd
    have hSeq : Nat.card ↥S = Nat.card ↥(hInvariantStar ⊤ A {q}) := by rw [hS_def]
    rw [hzero] at hmod
    rw [← hSeq]
    exact (Nat.modEq_zero_iff_dvd).mp hmod
  have hne : Nonempty (MulAction.fixedPoints ↥(Subgroup.zpowers σ) ↥S) :=
    (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hcard_ne)).1
  obtain ⟨Q, hQfix⟩ := hne.some
  -- Unfold the fixed-point property: `σ` fixes `Q`, i.e. `conj g • Q.1 = Q.1`.
  have hσQ : (⟨σ, Subgroup.mem_zpowers σ⟩ : ↥(Subgroup.zpowers σ)) • Q = Q :=
    hQfix ⟨σ, Subgroup.mem_zpowers σ⟩
  -- The subgroup action of `⟨σ,_⟩` is `σ Q`, and `σ Q = ⟨g,hgP⟩ • Q` (`toPermHom`).
  have hσval : σ Q = Q := by
    rw [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] at hσQ
    exact hσQ
  have h1 : (⟨g, hgP⟩ : ↥P) • Q = Q := by
    have hstep : (⟨g, hgP⟩ : ↥P) • Q = σ Q := by
      rw [hσ_def, MulAction.toPermHom_apply, MulAction.toPerm_apply]
    rw [hstep, hσval]
  have hgN : MulAut.conj g • (Q : Subgroup G) = (Q : Subgroup G) := by
    have h2 := congrArg (Subtype.val : ↥S → Subgroup G) h1
    rwa [hsmul_coe] at h2
  refine ⟨(Q : Subgroup G), Q.2, ?_⟩
  -- `P = A ⊔ ⟨g⟩ ≤ N(Q)`: `A` normalizes `Q` (membership of `S`), `g ∈ N(Q)` by `hgN`.
  rw [← hsup, sup_le_iff]
  refine ⟨hInvariantStar_le_normalizer Q.2, ?_⟩
  rw [Subgroup.zpowers_le]
  exact mem_normalizer_of_conj_smul_eq_self hgN

/-- **(7.3) for prime index** (mmd L2218-2220): if `A ⊴ P` with `|P:A| = p` prime and
`p ∤ |ℋ*(A;q)|`, then `P` normalizes some element of `ℋ*(A;q)`. Extract a generator `g` of
the cyclic prime-order quotient `↥P ⧸ A` and apply `tp_exists_normalized`. -/
private theorem tp_exists_normalized_of_prime_index [Finite G] {A P : Subgroup G} {q : ℕ}
    [Fact q.Prime] [hAnormal : (A.subgroupOf P).Normal] (hAP : A ≤ P) {p : ℕ} (hp : p.Prime)
    (hindex : (A.subgroupOf P).index = p)
    (hpdvd : ¬ p ∣ Nat.card ↥(hInvariantStar ⊤ A {q})) :
    ∃ Q ∈ hInvariantStar ⊤ A {q}, P ≤ Subgroup.normalizer Q := by
  have : Fact p.Prime := ⟨hp⟩
  set Bbar : Subgroup ↥P := A.subgroupOf P with hBbar
  have hcardQ : Nat.card (↥P ⧸ Bbar) = p := by rw [← Subgroup.index_eq_card]; exact hindex
  have hcyc : IsCyclic (↥P ⧸ Bbar) := isCyclic_of_prime_card hcardQ
  obtain ⟨gbar, hgbar⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective Bbar gbar
  set g : G := (g' : G) with hg_def
  have hgP : g ∈ P := g'.2
  -- `g ^ p ∈ A`.
  have hgpA : g ^ p ∈ A := by
    have hpow : (QuotientGroup.mk' Bbar g') ^ p = 1 := by
      rw [← hcardQ]; exact pow_card_eq_one'
    rw [← map_pow] at hpow
    have hmem : (g' ^ p) ∈ Bbar := (QuotientGroup.eq_one_iff _).mp hpow
    rw [hBbar, Subgroup.mem_subgroupOf] at hmem
    have hcoe : ((g' ^ p : ↥P) : G) = g ^ p := by rw [Subgroup.coe_pow]
    rwa [hcoe] at hmem
  -- `A ⊔ zpowers g = P`.
  have hsup : A ⊔ Subgroup.zpowers g = P := by
    have htop : Bbar ⊔ Subgroup.zpowers g' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : QuotientGroup.mk' Bbar x ∈ Subgroup.zpowers (QuotientGroup.mk' Bbar g') := by
        rw [hgbar]; exact Subgroup.mem_top _
      rw [Subgroup.mem_zpowers_iff] at hx
      obtain ⟨n, hn⟩ := hx
      rw [← map_zpow] at hn
      have hmemB : x * (g' ^ n)⁻¹ ∈ Bbar := by
        rw [← QuotientGroup.eq_one_iff]
        rw [show ((x * (g' ^ n)⁻¹ : ↥P) : ↥P ⧸ Bbar) = QuotientGroup.mk' Bbar (x * (g' ^ n)⁻¹) from
          rfl, map_mul, map_inv, hn, mul_inv_cancel]
      have hx_eq : x = (x * (g' ^ n)⁻¹) * g' ^ n := by group
      rw [hx_eq]
      exact (Bbar ⊔ Subgroup.zpowers g').mul_mem (Subgroup.mem_sup_left hmemB)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩))
    -- Map `Bbar ⊔ ⟨g'⟩ = ⊤` from `↥P` to `G`.
    apply le_antisymm
    · exact sup_le hAP ((Subgroup.zpowers_le).mpr hgP)
    · intro x hxP
      have hximg : (⟨x, hxP⟩ : ↥P) ∈ Bbar ⊔ Subgroup.zpowers g' := htop ▸ Subgroup.mem_top _
      rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hximg
      obtain ⟨a, ha, z, hz, haz⟩ := hximg
      rw [SetLike.mem_coe, hBbar, Subgroup.mem_subgroupOf] at ha
      have hzG : (z : G) ∈ Subgroup.zpowers g := by
        rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hz
        obtain ⟨n, hn⟩ := hz
        have hzval : (z : G) = g ^ n := by rw [← hn, hg_def, Subgroup.coe_zpow]
        rw [hzval]
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
      have hxval : x = (a : G) * (z : G) := by
        have hc := congrArg (Subtype.val : ↥P → G) haz
        rw [Subgroup.coe_mul] at hc
        exact hc.symm
      rw [hxval]
      exact (A ⊔ Subgroup.zpowers g).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hzG)
  have hPnA : ∀ x ∈ P, MulAut.conj x • A = A := fun x hx =>
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer_of_normal_subgroupOf hAP hx)
  exact tp_exists_normalized hPnA hgP hgpA hsup hpdvd

/-- **Theorem 7.4(b)** (mmd L2234-2244): `O_{π'}(C_G(P))` is transitive on `ℋ_G*(P;q)`.
For `Q₁,Q₂ ∈ ℋ*(P;q)`: by (c) (`hc_sub`) both lie in `ℋ*(A;q)`, so `htrans` gives `k ∈ K`
with `Q₂ = Q₁^k`. Inside `V := (K⊔P)⊓N(Q₂) = (K∩N(Q₂))·P`, the Hall-`π` subgroups `P` and
`P^k` are conjugate by some `κ ∈ K∩N(Q₂)` (`exists_conj_eq_of_isHall_subgroupOf`); then
`c := κk ∈ K∩N(P)`, which centralizes `P` (`mem_centralizer_of_mem_kSubgroup_normalizer`),
so `c ∈ C_G(P)⊓K = O_{π'}(C_G(P))` by (a), and `Q₁^c = Q₂`. -/
private theorem tp_b [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (_hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) [hAnormal : (A.subgroupOf P).Normal]
    (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P) (_hPlt : P < ⊤)
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}))
    (hc_sub : hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q}) :
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) := by
  classical
  set K : Subgroup G := kSubgroup A with hK_def
  -- Standing facts.
  have hPnA : P ≤ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hAP
  have hKnA : K ≤ Subgroup.normalizer (A : Set G) :=
    (kSubgroup_le_centralizer A).trans (Subgroup.centralizer_le_normalizer _)
  have hK_pi' : Subgroup.IsPiSubgroup (primesOf A)ᶜ K := isPiSubgroup_kSubgroup A
  have hAne : A ≠ ⊥ := hA.ne_bot
  have hNA_lt : Subgroup.normalizer (A : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : A.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal A inferInstance with h | h
    · exact hAne h
    · exact (ne_of_lt hA.proper) h
  have hKsupP_lt : K ⊔ P < ⊤ := lt_of_le_of_lt (sup_le hKnA hPnA) hNA_lt
  have hKsupP_solv : Group.IsSolvable ↥(K ⊔ P) := hG.isSolvable_of_lt_top _ hKsupP_lt
  -- `P` normalizes `K` (since `P ≤ N(A)` normalizes `K = O_{π'}(C_G(A))`).
  have hPnK : P ≤ Subgroup.normalizer (K : Set G) :=
    fun x hx => mem_normalizer_of_conj_smul_eq_self (conj_smul_kSubgroup_eq (hPnA hx))
  have hKsupP_le_NK : K ⊔ P ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hPnK
  have hKnorm : (K.subgroupOf (K ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hKsupP_le_NK
  -- `P ⊓ K = ⊥` (coprime orders: `P` is `π`, `K` is `π'`).
  have hCopPK : Nat.Coprime (Nat.card ↥P) (Nat.card ↥K) :=
    OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun p hp => hP_pi p hp) (fun p hp => hK_pi' p hp)
  have hPK_bot : P ⊓ K = ⊥ := by
    have h1 : Nat.card ↥(P ⊓ K) ∣ Nat.card ↥P := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(P ⊓ K) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_right
    have : Nat.card ↥(P ⊓ K) = 1 :=
      Nat.dvd_one.mp (hCopPK.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
    exact Subgroup.card_eq_one.mp this
  -- Part (a): `O_{π'}(C_G(P)) = C_G(P) ⊓ K`.
  have hpartA : opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G))
      = Subgroup.centralizer (P : Set G) ⊓ K := (tp_centralizer_eq hG hA hAP).symm
  rw [hpartA]
  -- Main transitivity argument.
  intro Q₁ hQ₁ Q₂ hQ₂
  -- (c): both lie in `ℋ*(A;q)`; `htrans` gives `k ∈ K` with `Q₂ = Q₁^k`.
  obtain ⟨k, hkK, hkeq⟩ := htrans Q₁ (hc_sub hQ₁) Q₂ (hc_sub hQ₂)
  -- `P` normalizes both `Q₁, Q₂` and `P^k = conj k • P` normalizes `Q₂`.
  have hPnQ₁ : P ≤ Subgroup.normalizer Q₁ := hInvariantStar_le_normalizer hQ₁
  have hPnQ₂ : P ≤ Subgroup.normalizer Q₂ := hInvariantStar_le_normalizer hQ₂
  have hP'nQ₂ : MulAut.conj k • P ≤ Subgroup.normalizer Q₂ := by
    rw [← hkeq]; exact conj_smul_le_normalizer_of_le_normalizer hPnQ₁
  set P' : Subgroup G := MulAut.conj k • P with hP'_def
  set NQ₂ : Subgroup G := Subgroup.normalizer Q₂ with hNQ₂_def
  set V : Subgroup G := (K ⊔ P) ⊓ NQ₂ with hV_def
  set K' : Subgroup G := K ⊓ NQ₂ with hK'_def
  -- `P' = conj k • P ≤ K ⊔ P` (`k ∈ K ≤ K⊔P`, `P ≤ K⊔P`).
  have hP'_le_KsupP : P' ≤ K ⊔ P := by
    rw [hP'_def]
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hkmem : k ∈ K ⊔ P := Subgroup.mem_sup_left hkK
    have h := (K ⊔ P).mul_mem ((K ⊔ P).mul_mem hkmem (Subgroup.mem_sup_right hy)) (inv_mem hkmem)
    have heq : k * ((MulAut.conj k)⁻¹ • y) * k⁻¹ = y := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
    rwa [heq] at h
  -- Memberships in `V`.
  have hP_le_V : P ≤ V := le_inf le_sup_right hPnQ₂
  have hP'_le_V : P' ≤ V := le_inf hP'_le_KsupP hP'nQ₂
  have hK'_le_V : K' ≤ V := le_inf (le_trans inf_le_left le_sup_left) inf_le_right
  have hV_lt : V < ⊤ := lt_of_le_of_lt (le_trans inf_le_left (le_refl _)) hKsupP_lt
  have hV_solv : Group.IsSolvable ↥V := hG.isSolvable_of_lt_top V hV_lt
  -- `V = K' ⊔ P` (BG `N_{KP}(Q₂) = (K∩N(Q₂))·P`).
  have hKP_mul : (↑(K ⊔ P) : Set G) = (K : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K P hPnK
  have hV_eq : K' ⊔ P = V := by
    refine le_antisymm (sup_le hK'_le_V hP_le_V) ?_
    intro v hv
    rw [hV_def, Subgroup.mem_inf] at hv
    obtain ⟨hvKP, hvNQ₂⟩ := hv
    rw [← SetLike.mem_coe, hKP_mul, Set.mem_mul] at hvKP
    obtain ⟨κ, hκK, s, hsP, hvκs⟩ := hvKP
    have hsNQ₂ : s ∈ NQ₂ := hPnQ₂ hsP
    have hκNQ₂ : κ ∈ NQ₂ := by
      have : κ = v * s⁻¹ := by rw [← hvκs]; group
      rw [this]; exact NQ₂.mul_mem hvNQ₂ (NQ₂.inv_mem hsNQ₂)
    have hκK' : κ ∈ K' := Subgroup.mem_inf.mpr ⟨hκK, hκNQ₂⟩
    rw [← hvκs]
    exact (K' ⊔ P).mul_mem (Subgroup.mem_sup_left hκK') (Subgroup.mem_sup_right hsP)
  -- `K' ⊓ P = ⊥` (`K'≤K`, `K⊓P=⊥`).
  have hK'P_bot : K' ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    refine le_trans (inf_le_inf_right P (inf_le_left : K' ≤ K)) ?_
    rw [inf_comm]; exact le_of_eq hPK_bot
  -- `V` normalizes `K'` (each `v ∈ V` normalizes `K` and `N(Q₂)`).
  have hVnK' : V ≤ Subgroup.normalizer (K' : Set G) := by
    intro v hv
    apply mem_normalizer_of_conj_smul_eq_self
    have hvNK : MulAut.conj v • K = K := by
      have : v ∈ K ⊔ P := (le_trans inf_le_left (le_refl (K ⊔ P))) hv
      exact conj_smul_eq_self_of_mem_normalizer (hKsupP_le_NK this)
    have hvNQ₂ : v ∈ NQ₂ := (le_trans inf_le_right (le_refl NQ₂)) hv
    have hvNNQ₂ : MulAut.conj v • NQ₂ = NQ₂ := by
      have hvQ₂ : MulAut.conj v • Q₂ = Q₂ := conj_smul_eq_self_of_mem_normalizer hvNQ₂
      rw [hNQ₂_def, conj_smul_normalizer_eq, hvQ₂]
    rw [hK'_def, Subgroup.smul_inf, hvNK, hvNNQ₂]
  -- `K'` is normal in `↥V`.
  have hK'_normal : (K'.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK'_le_V).mpr hVnK'
  -- `IsComplement'` of `K'` and `P` inside `↥V`, giving `|V| = |K'| * |P|`.
  have hdisj : Disjoint (K'.subgroupOf V) (P.subgroupOf V) := by
    rw [disjoint_iff]
    rw [show K'.subgroupOf V ⊓ P.subgroupOf V = (K' ⊓ P).subgroupOf V from
      (Subgroup.comap_inf K' P V.subtype).symm, hK'P_bot, Subgroup.bot_subgroupOf]
  have hsup_top : K'.subgroupOf V ⊔ P.subgroupOf V = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK'_le_V hP_le_V, hV_eq, Subgroup.subgroupOf_self]
  have hcompl : Subgroup.IsComplement' (K'.subgroupOf V) (P.subgroupOf V) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
    have hmul := Subgroup.normal_mul (K'.subgroupOf V) (P.subgroupOf V)
    rw [hsup_top] at hmul
    rw [← hmul]; rfl
  have hVcard : Nat.card ↥K' * Nat.card ↥P = Nat.card ↥V := by
    have h := hcompl.card_mul_card
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'_le_V).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_V).toEquiv] at h
  -- `K'` is a `π'`-group (subgroup of `K`).
  have hK'_pi' : Subgroup.IsPiSubgroup (primesOf A)ᶜ K' := fun p hp =>
    hK_pi' p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
      (Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.card_dvd_of_le inf_le_left),
      Nat.card_pos.ne'⟩)
  -- Both `P` and `P'` are `π`-Hall subgroups of `V`.
  have mkHall : ∀ R : Subgroup G, R ≤ V → Nat.card ↥R = Nat.card ↥P →
      Ch03.IsHallSubgroup (primesOf A) (R.subgroupOf V) := by
    intro R hRV hRcard
    constructor
    · intro p hp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv, hRcard] at hp
      exact hP_pi p hp
    · intro p hp
      -- `index = card K'`, a `π'`-number.
      have hidx : (R.subgroupOf V).index = Nat.card ↥K' := by
        have hlag := Subgroup.card_mul_index (R.subgroupOf V)
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRV).toEquiv, hRcard, ← hVcard,
          mul_comm (Nat.card ↥K')] at hlag
        exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag
      rw [hidx] at hp
      exact hK'_pi' p hp
  have hP_hall : Ch03.IsHallSubgroup (primesOf A) (P.subgroupOf V) := mkHall P hP_le_V rfl
  have hP'_hall : Ch03.IsHallSubgroup (primesOf A) (P'.subgroupOf V) :=
    mkHall P' hP'_le_V (by
      rw [hP'_def, Nat.card_congr (Subgroup.equivSMul (MulAut.conj k) P).toEquiv])
  -- Conjugate `P'` to `P` inside `V` (Hall conjugacy).
  obtain ⟨w, hwV, hwconj⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hV_solv hP'_le_V hP_le_V hP'_hall
      hP_hall
  -- Decompose `w = s · κ` with `s ∈ P`, `κ ∈ K'` (`V = P · K'`, `K' ⊴ V`).
  have hPnK' : P ≤ Subgroup.normalizer (K' : Set G) := hP_le_V.trans hVnK'
  have hw_mem : w ∈ (P : Set G) * (K' : Set G) := by
    have hVcoe : (V : Set G) = (P : Set G) * (K' : Set G) := by
      rw [← hV_eq, sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right P K' hPnK'
    rw [← SetLike.mem_coe, hVcoe] at hwV
    exact hwV
  obtain ⟨s, hsP, κ, hκK', hwsκ⟩ := hw_mem
  simp only at hwsκ
  -- `conj κ • P' = P` (cancel the `P`-factor `s`).
  have hs : MulAut.conj s • P = P :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hsP)
  have hs' : MulAut.conj s⁻¹ • P = P := by
    conv_lhs => rw [← hs]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hκconj : MulAut.conj κ • P' = P := by
    have h1 : MulAut.conj s • (MulAut.conj κ • P') = P := by
      rw [smul_smul, ← map_mul, hwsκ]; exact hwconj
    have h2 : MulAut.conj s⁻¹ • (MulAut.conj s • (MulAut.conj κ • P'))
        = MulAut.conj s⁻¹ • P := congrArg _ h1
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hs'] at h2
    exact h2
  -- The conjugator `c := κ · k ∈ K ∩ N(P)`, which centralizes `P` (part a route).
  set c : G := κ * k with hc_def
  have hκK : κ ∈ K := (Subgroup.mem_inf.mp hκK').1
  have hκNQ₂ : κ ∈ NQ₂ := (Subgroup.mem_inf.mp hκK').2
  have hcK : c ∈ K := K.mul_mem hκK hkK
  have hcQ : MulAut.conj c • Q₁ = Q₂ := by
    rw [hc_def, map_mul, mul_smul, hkeq, conj_smul_eq_self_of_mem_normalizer hκNQ₂]
  have hcNP : c ∈ Subgroup.normalizer (P : Set G) := by
    apply mem_normalizer_of_conj_smul_eq_self
    rw [hc_def, map_mul, mul_smul, ← hP'_def, hκconj]
  have hcCP : c ∈ Subgroup.centralizer (P : Set G) :=
    mem_centralizer_of_mem_kSubgroup_normalizer hPnA hPK_bot hcK hcNP
  exact ⟨c, Subgroup.mem_inf.mpr ⟨hcCP, hcK⟩, hcQ⟩

/-- **Theorem 7.4(d)** (mmd L2246-2248): for `Q ∈ ℋ*(P;q)`, `N_G(P) = O_{π'}(C_G(P))·(N(P)∩N(Q))`
and `P ∩ N(P)′ ⊆ N(Q)′`. The factorization comes from (b) (transitivity): for `n ∈ N(P)`,
`conj n • Q ∈ ℋ*(P;q)`, so some `c ∈ O_{π'}(C_G(P))` has `conj c • Q = conj n • Q`, whence
`m := c⁻¹n ∈ N(P)∩N(Q)`. The commutator inclusion is **Lemma 6.5(a)**
(`inf_commutator_eq_of_coprime`) in `↥N(P)` with `K := O_{π'}(C_G(P))`, `U := N(P)∩N(Q)`,
`H := P`, using `derivedInG H = ⁅H,H⁆`. -/
private theorem tp_d [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    {q : ℕ} [Fact q.Prime] (_hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (_hAP : A ≤ P) (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P)
    (hPlt : P < ⊤) (hPne : P ≠ ⊥)
    (hb : ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}))
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ P {q}) :
    P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
    ∀ n : G, n ∈ Subgroup.normalizer P →
      ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
        ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m := by
  classical
  set π' : Set ℕ := (primesOf A)ᶜ with hπ'
  set OC : Subgroup G := opiCoreInG π' (Subgroup.centralizer (P : Set G)) with hOC_def
  set NP : Subgroup G := Subgroup.normalizer (P : Set G) with hNP_def
  set NQ : Subgroup G := Subgroup.normalizer (Q : Set G) with hNQ_def
  have hPnQ : P ≤ NQ := hInvariantStar_le_normalizer hQ
  have hOC_le_CP : OC ≤ Subgroup.centralizer (P : Set G) := opiCoreInG_le _ _
  have hOC_le_NP : OC ≤ NP := hOC_le_CP.trans (Subgroup.centralizer_le_normalizer _)
  have hP_le_NP : P ≤ NP := Subgroup.le_normalizer
  -- Factorization (the existential clause).
  have hfact : ∀ n : G, n ∈ NP →
      ∃ c ∈ OC, ∃ m ∈ NP ⊓ NQ, n = c * m := by
    intro n hn
    have hnP : MulAut.conj n • P = P := conj_smul_eq_self_of_mem_normalizer hn
    have hnQmem : MulAut.conj n • Q ∈ hInvariantStar ⊤ P {q} :=
      conj_smul_mem_hInvariantStar_of_normalizer hQ hnP
    obtain ⟨c, hcOC, hcQeq⟩ := hb Q hQ (MulAut.conj n • Q) hnQmem
    refine ⟨c, hcOC, c⁻¹ * n, ?_, by group⟩
    have hcNP : c ∈ NP := hOC_le_NP hcOC
    have hmNP : c⁻¹ * n ∈ NP := NP.mul_mem (NP.inv_mem hcNP) hn
    have hmNQ : c⁻¹ * n ∈ NQ := by
      apply mem_normalizer_of_conj_smul_eq_self
      rw [map_mul, mul_smul, map_inv, ← hcQeq, inv_smul_smul]
    exact Subgroup.mem_inf.mpr ⟨hmNP, hmNQ⟩
  refine ⟨?_, hfact⟩
  -- Commutator inclusion via Lemma 6.5(a) in `↥NP`.
  -- `NP < ⊤` (`P` not normal: `P ≠ ⊥, ⊤`, `G` simple), hence `↥NP` solvable.
  have hNP_lt : NP < ⊤ := by
    rw [hNP_def, lt_top_iff_ne_top]
    intro htop
    have : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal P inferInstance with h | h
    · exact hPne h
    · exact (ne_of_lt hPlt) h
  have hNP_solv : Group.IsSolvable ↥NP := hG.isSolvable_of_lt_top NP hNP_lt
  -- `OC = O_{π'}(C_G(P)) ⊴ NP`.
  have hOCnNP : NP ≤ Subgroup.normalizer (OC : Set G) := by
    intro x hx
    exact mem_normalizer_of_conj_smul_eq_self (conj_smul_opiCore_centralizer_eq hx)
  have hOC_normal : (OC.subgroupOf NP).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOC_le_NP).mpr hOCnNP
  -- `OC ⊔ (NP ⊓ NQ) = NP` from the factorization, so `K ⊔ U = ⊤` in `↥NP`.
  have hLU : OC ⊔ (NP ⊓ NQ) = NP := by
    refine le_antisymm (sup_le hOC_le_NP inf_le_left) ?_
    intro n hn
    obtain ⟨c, hcOC, m, hmNPNQ, hncm⟩ := hfact n hn
    rw [hncm]
    exact (OC ⊔ (NP ⊓ NQ)).mul_mem (Subgroup.mem_sup_left hcOC) (Subgroup.mem_sup_right hmNPNQ)
  have hKU : OC.subgroupOf NP ⊔ (NP ⊓ NQ).subgroupOf NP = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOC_le_NP inf_le_left, hLU, Subgroup.subgroupOf_self]
  -- Coprimality `|P|`, `|OC|`.
  have hcop : Nat.Coprime (Nat.card ↥(P.subgroupOf NP)) (Nat.card ↥(OC.subgroupOf NP)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_NP).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC_le_NP).toEquiv]
    refine OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := primesOf A) Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => hP_pi p hp) (fun p hp => ?_)
    exact isPiSubgroup_opiCoreInG π' (Subgroup.centralizer (P : Set G)) p hp
  have hHU : P.subgroupOf NP ≤ (NP ⊓ NQ).subgroupOf NP :=
    Subgroup.comap_mono (le_inf hP_le_NP hPnQ)
  -- Apply Lemma 6.5(a) inside `↥NP`.
  have h65 := OddOrder.BG.Ch1.S06.inf_commutator_eq_of_coprime
    (G := ↥NP) (K := OC.subgroupOf NP) (U := (NP ⊓ NQ).subgroupOf NP)
    (H := P.subgroupOf NP) hKU hHU hcop
  -- Map the equation back to `G` and deduce the inclusion.
  have hmap := congrArg (Subgroup.map NP.subtype) h65
  simp only [Subgroup.map_inf _ _ _ NP.subtype_injective, Subgroup.subgroupOf_map_subtype,
    Subgroup.map_subtype_commutator, Subgroup.map_commutator,
    inf_of_le_left hP_le_NP] at hmap
  -- `hmap : P ⊓ ⁅NP, NP⁆ = P ⊓ ⁅NP ⊓ NQ, NP ⊓ NQ⁆`.
  rw [show derivedInG NP = ⁅(NP : Subgroup G), NP⁆ from Subgroup.map_subtype_commutator NP, hmap]
  refine le_trans inf_le_right ?_
  rw [show derivedInG NQ = ⁅(NQ : Subgroup G), NQ⁆ from Subgroup.map_subtype_commutator NQ]
  exact Subgroup.commutator_mono (le_trans inf_le_left inf_le_right)
    (le_trans inf_le_left inf_le_right)

/-- **`|ℋ*(A;q)| ∣ |K|`** (mmd L2218): `K` acts transitively on the finite set `ℋ*(A;q)` by
conjugation (each `k ∈ K ≤ C_G(A) ≤ N(A)`), so by orbit-stabilizer its cardinality divides `|K|`. -/
private theorem tp_card_hStar_dvd_kSubgroup [Finite G] {A : Subgroup G} {q : ℕ}
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    Nat.card ↥(hInvariantStar ⊤ A {q}) ∣ Nat.card ↥(kSubgroup A) := by
  classical
  set S : Set (Subgroup G) := hInvariantStar ⊤ A {q} with hS_def
  set K : Subgroup G := kSubgroup A with hK_def
  -- `↥K` acts on `↥S` by conjugation.
  have hkA : ∀ k : ↥K, MulAut.conj (k : G) • A = A := fun k =>
    conj_smul_eq_self_of_mem_normalizer
      ((Subgroup.centralizer_le_normalizer _) (kSubgroup_le_centralizer A k.2))
  let smulFn : ↥K → ↥S → ↥S := fun k Q => ⟨MulAut.conj (k : G) • (Q : Subgroup G),
    conj_smul_mem_hInvariantStar_of_normalizer Q.2 (hkA k)⟩
  let act : MulAction ↥K ↥S :=
    { smul := smulFn
      one_smul := fun Q => by
        apply Subtype.ext
        change MulAut.conj ((1 : ↥K) : G) • (Q : Subgroup G) = (Q : Subgroup G)
        rw [Subgroup.coe_one, map_one, one_smul]
      mul_smul := fun x y Q => by
        apply Subtype.ext
        change MulAut.conj (((x * y : ↥K)) : G) • (Q : Subgroup G)
          = MulAut.conj ((x : G)) • MulAut.conj ((y : G)) • (Q : Subgroup G)
        rw [Subgroup.coe_mul, map_mul, mul_smul] }
  have hsmul_coe : ∀ (k : ↥K) (Q : ↥S),
      ((k • Q : ↥S) : Subgroup G) = MulAut.conj (k : G) • (Q : Subgroup G) := fun _ _ => rfl
  have hpre : MulAction.IsPretransitive ↥K ↥S := by
    refine ⟨fun Q₁ Q₂ => ?_⟩
    obtain ⟨k, hkK, hkeq⟩ := htrans Q₁ Q₁.2 Q₂ Q₂.2
    refine ⟨⟨k, hkK⟩, ?_⟩
    apply Subtype.ext
    rw [hsmul_coe]; exact hkeq
  -- Orbit-stabilizer: `|orbit Q₀| = (stab).index ∣ |K|`, and `orbit Q₀ = ↥S`.
  obtain ⟨Q₀⟩ : Nonempty ↥S := by
    have hbot_norm : (A : Subgroup G) ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      intro a _
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl; group
      · intro h
        have : z = a⁻¹ * 1 * a := by rw [← (h : a * z * a⁻¹ = 1)]; group
        simpa using this
    have hbot_mem : (⊥ : Subgroup G) ∈ hInvariant ⊤ A {q} :=
      ⟨le_top, hbot_norm, Subgroup.IsPiSubgroup.bot⟩
    obtain ⟨Qs, hQs, _⟩ := exists_le_hInvariantStar hbot_mem
    exact ⟨⟨Qs, hQs⟩⟩
  have horb_univ : MulAction.orbit ↥K Q₀ = Set.univ :=
    MulAction.orbit_eq_univ (M := ↥K) (α := ↥S) Q₀
  have hcard_orbit : Nat.card ↥(MulAction.orbit ↥K Q₀) = Nat.card ↥S := by
    rw [horb_univ]; exact Nat.card_congr (Equiv.Set.univ ↥S)
  have hdvd : Nat.card ↥(MulAction.orbit ↥K Q₀) ∣ Nat.card ↥K := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥K Q₀),
      ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card _
  rw [hcard_orbit] at hdvd
  exact hdvd

/-- **Theorem 7.4(c) base case** (mmd L2222-2232): `A ⊴ P` with `|P:A| = p` prime ⟹
`ℋ*(P;q) ⊆ ℋ*(A;q)`. For `Q ≠ ⊥` it is `tp_c_main`; for `Q = ⊥` (so `ℋ*(P;q) = {⊥}`), (7.3)
gives a `P`-normalized `Q₀ ∈ ℋ*(A;q)`, and `⊥`'s maximality in `ℋ(P;q)` forces `Q₀ = ⊥`. -/
private theorem tp_c_full [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) [hAnormal : (A.subgroupOf P).Normal]
    (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P) {p : ℕ} (hp : p.Prime)
    (hindex : (A.subgroupOf P).index = p)
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} := by
  -- `p ∈ π = primesOf A`, so `p ∤ |K|`, hence `p ∤ |ℋ*(A;q)|`.
  have hp_pi : p ∈ primesOf A := by
    refine hP_pi p (Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩)
    have hdvd : (A.subgroupOf P).index ∣ Nat.card ↥P := by
      rw [← Subgroup.index_mul_card (A.subgroupOf P)]; exact Dvd.intro _ rfl
    rw [hindex] at hdvd; exact hdvd
  have hpdvd : ¬ p ∣ Nat.card ↥(hInvariantStar ⊤ A {q}) := by
    intro hpd
    have hdvdK : p ∣ Nat.card ↥(kSubgroup A) :=
      hpd.trans (tp_card_hStar_dvd_kSubgroup htrans)
    exact (isPiSubgroup_kSubgroup A p (Nat.mem_primeFactors.mpr ⟨hp, hdvdK, Nat.card_pos.ne'⟩))
      hp_pi
  intro Q hQ
  by_cases hQbot : Q = ⊥
  · -- `Q = ⊥`: use (7.3) and maximality.
    subst hQbot
    obtain ⟨Q₀, hQ₀star, hPnQ₀⟩ :=
      tp_exists_normalized_of_prime_index hAP hp hindex hpdvd
    have hQ₀_hInvP : Q₀ ∈ hInvariant ⊤ P {q} :=
      ⟨le_top, hPnQ₀, hInvariantStar_isPiSubgroup hQ₀star⟩
    have hbot_eq : Q₀ = ⊥ := hInvariantStar_eq_of_le hQ hQ₀_hInvP bot_le
    rw [← hbot_eq]; exact hQ₀star
  · exact tp_c_main hG hA hq hAP hP_pi hQ hQbot

/-- **BG Theorem 7.4 base case** (`A ⊴ P` with `|P:A|` prime): conjuncts (a)/(b)/(c)/(d). -/
private theorem tp_base [Finite G] (hG : IsMinimalSimpleOdd G) {A : Subgroup G}
    (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    {P : Subgroup G} (hAP : A ≤ P) [hAnormal : (A.subgroupOf P).Normal]
    (hP_pi : Subgroup.IsPiSubgroup (primesOf A) P) (hPlt : P < ⊤) (hPne : P ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hindex : (A.subgroupOf P).index = p)
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) ∧
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ P {q},
      P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer P →
        ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
          ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m) := by
  have hcsub : hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} :=
    tp_c_full hG hA hq hAP hP_pi hp hindex htrans
  have hbpart : ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
      (hInvariantStar ⊤ P {q}) :=
    tp_b hG hA hq hAP hP_pi hPlt htrans hcsub
  refine ⟨tp_centralizer_eq hG hA hAP, hbpart, hcsub, ?_⟩
  intro Q hQ
  exact tp_d hG hq hAP hP_pi hPlt hPne hbpart hQ

/-- **BG Theorem 7.4** (Propagation, mmd L2197): Hypothesis 7.1, `q ∈ π'`, `P` は `A` を
subnormal に含む真 `π`-部分群、`K` は `ℋ_G*(A;q)` 上推移的とする。すると:

* (a) `C_K(P) = O_{π'}(C_G(P))`,
* (b) `O_{π'}(C_G(P))` は `ℋ_G*(P;q)` 上推移的,
* (c) `ℋ_G*(P;q) ⊆ ℋ_G*(A;q)`,
* (d) 各 `Q ∈ ℋ_G*(P;q)` で `P ∩ N_G(P)′ ⊆ N_G(Q)′` かつ
  `N_G(P) = O_{π'}(C_G(P))·(N_G(P) ∩ N_G(Q))`。

`|P:A|` の帰納 + composition series 還元。 -/
theorem transitivity_propagates [Finite G] (hG : IsMinimalSimpleOdd G)
    {A : Subgroup G} (hA : Hypothesis71 A) {q : ℕ} [Fact q.Prime] (hq : q ∈ (primesOf A)ᶜ)
    (P : Subgroup G) (hPproper : P < ⊤) (hPpi : Subgroup.IsPiSubgroup (primesOf A) P)
    (hAP : A ≤ P) (hAsub : Subgroup.IsSubnormal (A.subgroupOf P))
    (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) ∧
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ P {q},
      P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer P →
        ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
          ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m) := by
  classical
  -- The four-conjunct conclusion for a pair `(A, P)`.
  let Goal : Subgroup G → Subgroup G → Prop := fun A P =>
    Subgroup.centralizer (P : Set G) ⊓ kSubgroup A =
        opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) ∧
    ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)))
        (hInvariantStar ⊤ P {q}) ∧
    hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ P {q},
      P ⊓ derivedInG (Subgroup.normalizer P) ≤ derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer P →
        ∃ c ∈ opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)),
          ∃ m ∈ Subgroup.normalizer P ⊓ Subgroup.normalizer Q, n = c * m)
  suffices key : ∀ n : ℕ, ∀ A : Subgroup G, Hypothesis71 A → q ∈ (primesOf A)ᶜ →
      ∀ P : Subgroup G, P < ⊤ → Subgroup.IsPiSubgroup (primesOf A) P → A ≤ P →
      Subgroup.IsSubnormal (A.subgroupOf P) →
      ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q}) →
      (A.subgroupOf P).index = n → Goal A P by
    exact key _ A hA hq P hPproper hPpi hAP hAsub htrans rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hq P hPproper hPpi hAP hAsub htrans hn
    have hAne : A ≠ ⊥ := hA.ne_bot
    have hPne : P ≠ ⊥ := fun h => hAne (le_bot_iff.mp (h ▸ hAP))
    by_cases hAeqP : A = P
    · -- Base `A = P`: everything is reflexive / `tp_centralizer_eq`.
      subst hAeqP
      refine ⟨tp_centralizer_eq hG hA (le_refl A), ?_, ?_, ?_⟩
      · -- (b): `O_{π'}(C_G(A)) = kSubgroup A`, transitive `= htrans`.
        rw [show opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G)) = kSubgroup A from rfl]
        exact htrans
      · exact le_refl _
      · intro Q hQ
        refine ⟨?_, ?_⟩
        · exact tp_d hG hq (le_refl A) hPpi hPproper hPne
            (by rw [show opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G))
              = kSubgroup A from rfl]; exact htrans) hQ |>.1
        · exact tp_d hG hq (le_refl A) hPpi hPproper hPne
            (by rw [show opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (A : Set G))
              = kSubgroup A from rfl]; exact htrans) hQ |>.2
    · -- `A < P`: reduce to a normal subgroup `B` of prime index.
      have hAltP : A < P := lt_of_le_of_ne hAP hAeqP
      obtain ⟨B, hAB, hBlt, hBnorm, hBindex⟩ := tp_reduction hG hAP hAltP hPproper hAsub
      have := hBnorm
      have hBP : B ≤ P := le_of_lt hBlt
      -- `B` is a `π(A)`-subgroup; `primesOf B = primesOf A`.
      have hBpi : Subgroup.IsPiSubgroup (primesOf A) B := fun r hr =>
        hPpi r (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hr).1,
          (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.card_dvd_of_le hBP), Nat.card_pos.ne'⟩)
      have hprimesBA : primesOf B = primesOf A :=
        primesOf_eq_of_le_of_isPiSubgroup hAB hBP hPpi
      by_cases hAeqB : A = B
      · -- `A = B`: prime-index base case.
        subst hAeqB
        have : (A.subgroupOf P).Normal := hBnorm
        exact tp_base hG hA hq hAP hPpi hPproper hPne
          (p := (A.subgroupOf P).index) hBindex rfl htrans
      · -- `A < B`: double recursion on `(A, B)` and `(B, P)`.
        have hABlt : A < B := lt_of_le_of_ne hAB hAeqB
        have hBlt_top : B < ⊤ := lt_trans hBlt hPproper
        have hBne : B ≠ ⊥ := fun h => hAne (le_bot_iff.mp (h ▸ hAB))
        -- Measure: `|B:A| · |P:B| = |P:A| = n`, both factors `> 1`.
        have hmul : (A.subgroupOf B).index * (B.subgroupOf P).index = (A.subgroupOf P).index := by
          have h := Subgroup.relIndex_mul_relIndex A B P hAB hBP
          simpa only [Subgroup.relIndex] using h
        have hBA_ne0 : (A.subgroupOf B).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hPB_ne0 : (B.subgroupOf P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have hBA_gt : 1 < (A.subgroupOf B).index := by
          rcases Nat.lt_or_ge 1 (A.subgroupOf B).index with h | h
          · exact h
          · exfalso
            have : (A.subgroupOf B).index = 1 := by omega
            rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at this
            exact (ne_of_lt hABlt) (le_antisymm hAB this)
        have hPB_gt : 1 < (B.subgroupOf P).index := by
          rcases Nat.lt_or_ge 1 (B.subgroupOf P).index with h | h
          · exact h
          · exfalso
            have : (B.subgroupOf P).index = 1 := by omega
            rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at this
            exact (ne_of_lt hBlt) (le_antisymm hBP this)
        have hBA_lt_n : (A.subgroupOf B).index < n := by
          rw [← hn, ← hmul]
          exact lt_mul_of_one_lt_right (by omega) hPB_gt
        have hPB_lt_n : (B.subgroupOf P).index < n := by
          rw [← hn, ← hmul]
          exact lt_mul_of_one_lt_left (by omega) hBA_gt
        -- `A` subnormal in `B`, `B` subnormal in `P`.
        have hAsubB : (A.subgroupOf B).IsSubnormal := by
          have h := Subgroup.IsSubnormal.comap (Subgroup.inclusion hBP) hAsub
          rwa [Subgroup.comap_inclusion_subgroupOf hBP] at h
        have hBsubP : (B.subgroupOf P).IsSubnormal := (hBnorm).isSubnormal
        -- IH on `(A, B)`.
        obtain ⟨_, hbAB, hcAB, _⟩ :=
          ih _ hBA_lt_n A hA hq B hBlt_top hBpi hAB hAsubB htrans rfl
        -- `Hypothesis71 B`, `htrans` on `B`.
        have hBhyp : Hypothesis71 B := tp_hyp71_of_le hA hAB hprimesBA hBne hBlt_top
        have hqB : q ∈ (primesOf B)ᶜ := by rw [hprimesBA]; exact hq
        have hPpiB : Subgroup.IsPiSubgroup (primesOf B) P := by rw [hprimesBA]; exact hPpi
        have htransB : ConjTransitiveOn (kSubgroup B) (hInvariantStar ⊤ B {q}) := by
          have heqK :
              kSubgroup B = opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (B : Set G)) := by
            rw [kSubgroup, hprimesBA]
          rw [heqK]; exact hbAB
        -- IH on `(B, P)`.
        obtain ⟨_, hbBP, hcBP, hdBP⟩ :=
          ih _ hPB_lt_n B hBhyp hqB P hPproper hPpiB hBP hBsubP htransB rfl
        -- Compose. `primesOf B = primesOf A` lets us re-tag the `O_{π'}` parts.
        have hOCeq : opiCoreInG (primesOf B)ᶜ (Subgroup.centralizer (P : Set G))
            = opiCoreInG (primesOf A)ᶜ (Subgroup.centralizer (P : Set G)) := by rw [hprimesBA]
        refine ⟨tp_centralizer_eq hG hA hAP, ?_, ?_, ?_⟩
        · rw [← hOCeq]; exact hbBP
        · exact fun Q hQ => hcAB (hcBP hQ)
        · intro Q hQ
          obtain ⟨hd1, hd2⟩ := hdBP Q hQ
          refine ⟨hd1, ?_⟩
          intro nn hnn
          obtain ⟨c, hc, m, hm, hcm⟩ := hd2 nn hnn
          exact ⟨c, hOCeq ▸ hc, m, hm, hcm⟩

end OddOrder.BG.Ch2.S07


