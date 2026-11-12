-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_ExtraspecialCommutator
-- name    : OddOrder_BG_Ch1_Preliminary_S04_ExtraspecialCommutator
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:18.212479+00:00
-- url     : https://prove2.me/theorems/8a5c37e3-5a23-4755-84f1-59ba19f11ca9
-- title:
--   BG §4E: the extraspecial commutator constraint (Lemma 4.15)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Lemma 4.15: the commutator constraint in an extraspecial group acted on with prescribed rank bounds.
--
--   Main definition: `deltaHom`, the homomorphism $\delta_g:S\to Z(S)$, $s\mapsto(gsg^{-1})s^{-1}$ for $g\in R$. Supporting lemmas include `center_le_ker_deltaHom` ($\delta_g$ kills $Z(S)$) and `commutatorElement_mem_center`.
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04_ExtraspecialCommutator.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04_ExtraspecialCommutator.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_SmallRankBasic

namespace OddOrder.BG.Ch1.S04

open OddOrder.BG.Ch1.S02

section ExtraspecialCommutator

open OddOrder.GroupTheory

open scoped commutatorElement

open scoped IsMulCommutative

variable {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] {S : Subgroup R}

omit [Finite R] in
/-- `S` is normal in `R` from `⁅S, ⊤⁆ ≤ S`: the conjugation action lands in `S`. -/
private theorem extraspecial_normal_of_commutator_le
    (hSinR : ⁅S, (⊤ : Subgroup R)⁆ ≤ S) : S.Normal := by
  have hnorm : (⊤ : Subgroup R) ≤ Subgroup.normalizer S :=
    OddOrder.Isaacs.Ch04.le_normalizer_of_commutator_le hSinR
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)

omit [Finite R] in
/-- From `[S, R] ⊆ S' = Z(S)` the ambient inclusion `[S, R] ⊆ S` (image of a subgroup of `S`). -/
private theorem commutator_le_self_of_hSR
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) :
    ⁅S, (⊤ : Subgroup R)⁆ ≤ S :=
  le_trans hSR (Subgroup.map_subtype_le _)

omit [Finite R] in
/-- For `g ∈ R` and `s ∈ S`, the commutator `⁅g, ↑s⁆ = (g s g⁻¹) s⁻¹` lies in `S`
and, as an element of `↥S`, in the centre `Z(S)`. This is the heart of `[S, R] ⊆ Z(S)`. -/
private theorem commutatorElement_mem_center
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    ⁅g, (s : R)⁆ ∈ (Subgroup.center (↥S)).map S.subtype := by
  have hmem : ⁅(s : R), g⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ :=
    Subgroup.commutator_mem_commutator s.2 (Subgroup.mem_top g)
  have hinv : ⁅g, (s : R)⁆ ∈ ⁅S, (⊤ : Subgroup R)⁆ := by
    rw [← commutatorElement_inv]
    exact (⁅S, (⊤ : Subgroup R)⁆).inv_mem hmem
  exact hSR hinv

omit [Finite R] in
/-- The element `(g · s · g⁻¹) · s⁻¹ ∈ ↥S` lies in `Z(S)`. (`= ⁅g, s⁆ ∈ [S, R] ⊆ Z(S)`,
reflected back into `↥S` via injectivity of `S.subtype`.) Requires `S` normal so that
conjugation by `g` is an automorphism of `↥S`. -/
private theorem deltaElement_mem [S.Normal]
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    MulAut.conjNormal g s * s⁻¹ ∈ Subgroup.center (↥S) := by
  obtain ⟨z, hz_mem, hz_eq⟩ := commutatorElement_mem_center hSR g s
  have hcoe : ((MulAut.conjNormal g s * s⁻¹ : ↥S) : R) = ⁅g, (s : R)⁆ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
  have heq : MulAut.conjNormal g s * s⁻¹ = z := by
    apply S.subtype_injective
    rw [Subgroup.coe_subtype, hcoe, ← hz_eq, Subgroup.coe_subtype]
  rw [heq]; exact hz_mem

/-- **`δ_g : ↥S →* Z(S)`** (`g ∈ R`): the homomorphism `s ↦ (g s g⁻¹) s⁻¹`.

It is multiplicative because its values lie in the centre `Z(S)`: for `s, t`,
`δ_g(st) = δ_g(s) · δ_g(t)` after sliding the central factor `δ_g(t)` past `s⁻¹`.
This is the "displacement" homomorphism of the conjugation automorphism. -/
private noncomputable def deltaHom [S.Normal]
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) :
    ↥S →* Subgroup.center (↥S) :=
  MonoidHom.mk' (fun s => ⟨MulAut.conjNormal g s * s⁻¹, deltaElement_mem hSR g s⟩) (by
    intro s t
    apply Subtype.ext
    change MulAut.conjNormal g (s * t) * (s * t)⁻¹ =
      (MulAut.conjNormal g s * s⁻¹) * (MulAut.conjNormal g t * t⁻¹)
    have hcentral : MulAut.conjNormal g t * t⁻¹ ∈ Subgroup.center (↥S) :=
      deltaElement_mem hSR g t
    -- `(cg t) t⁻¹` is central, hence commutes with `s⁻¹`.
    have hcomm : Commute s⁻¹ (MulAut.conjNormal g t * t⁻¹) :=
      (Subgroup.mem_center_iff.mp hcentral s⁻¹)
    rw [map_mul, mul_inv_rev]
    calc
      MulAut.conjNormal g s * MulAut.conjNormal g t * (t⁻¹ * s⁻¹)
          = MulAut.conjNormal g s * ((MulAut.conjNormal g t * t⁻¹) * s⁻¹) := by
            simp only [mul_assoc]
      _ = MulAut.conjNormal g s * (s⁻¹ * (MulAut.conjNormal g t * t⁻¹)) := by
            rw [hcomm.symm.eq]
      _ = (MulAut.conjNormal g s * s⁻¹) * (MulAut.conjNormal g t * t⁻¹) := by
            simp only [mul_assoc])

omit [Finite R] in
@[simp]
private theorem deltaHom_apply [S.Normal]
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    (deltaHom hSR g s : ↥S) = MulAut.conjNormal g s * s⁻¹ := rfl

omit [Fact (Nat.Prime p)] in
omit [Finite R] in
/-- `δ_g` kills `Z(S)`: as a homomorphism into the abelian group `Z(S)` it kills `[S, S]`,
and `[S, S] = Z(S)` for extraspecial `S`. -/
private theorem center_le_ker_deltaHom [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) :
    Subgroup.center (↥S) ≤ (deltaHom hSR g).ker := by
  have hcomm_le : commutator (↥S) ≤ (deltaHom hSR g).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    -- `⁅δa, δb⁆ = 1` since `Z(S)` is commutative.
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm (deltaHom hSR g a) (deltaHom hSR g b))
  exact hS.commutator_eq_center.symm.le.trans hcomm_le

/-- The descent of `δ_g` to `S/Z(S) →* Z(S)`. -/
private noncomputable def deltaQuot [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) :
    (↥S ⧸ Subgroup.center (↥S)) →* Subgroup.center (↥S) :=
  QuotientGroup.lift (Subgroup.center (↥S)) (deltaHom hSR g) (center_le_ker_deltaHom hS hSR g)

omit [Fact (Nat.Prime p)] in
omit [Finite R] in
@[simp]
private theorem deltaQuot_mk [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) (g : R) (s : ↥S) :
    deltaQuot hS hSR g (QuotientGroup.mk s) = deltaHom hSR g s :=
  QuotientGroup.lift_mk' _ _ s

/-- `S/Z(S)` is elementary abelian: it is `S/Φ(S)` (since `Φ(S) = Z(S)` for extraspecial `S`),
and `S/Φ(S)` is elementary abelian for any finite `p`-group (Burnside). -/
private theorem quotientCenter_isElementaryAbelian (hS : IsExtraspecial p (↥S)) :
    IsElementaryAbelian p (↥S ⧸ Subgroup.center (↥S)) := by
  have hfrat : frattini (↥S) = Subgroup.center (↥S) := hS.frattini_eq_center
  have hEA := IsPGroup.quotient_frattini_isElementaryAbelian (p := p) (R := ↥S) hS.isPGroup
  have : (frattini (↥S)).Normal := inferInstance
  exact IsElementaryAbelian.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hfrat) hEA

omit [Finite R] in
omit [Fact (Nat.Prime p)] in
/-- `Z(S)` is elementary abelian: it is cyclic of prime order `p`. -/
private theorem centerS_isElementaryAbelian (hS : IsExtraspecial p (↥S)) :
    IsElementaryAbelian p (Subgroup.center (↥S)) := by
  refine ⟨fun x y => mul_comm x y, fun x => ?_⟩
  -- `|Z(S)| = p`, so every element has order dividing `p`.
  have hx : x ^ (Nat.card (Subgroup.center (↥S))) = 1 := pow_card_eq_one'
  rwa [hS.center_card] at hx

omit [Finite R] in
/-- The kernel of `R →* MulAut ↥S` (conjugation) is `C_R(S)`. -/
private theorem conjNormal_ker_eq_centralizer_local [S.Normal] :
    (MulAut.conjNormal (H := S) : R →* MulAut (↥S)).ker
      = Subgroup.centralizer (S : Set R) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg s hs
    have hfix0 : MulAut.conjNormal (H := S) g ⟨s, hs⟩ = (⟨s, hs⟩ : ↥S) := by
      rw [hg]; rfl
    have hfix : (g * s * g⁻¹ : R) = s := by
      have hh := congrArg (fun x : ↥S => (x : R)) hfix0
      simp only [MulAut.conjNormal_apply] at hh
      exact hh
    -- `g * s * g⁻¹ = s`, i.e. `s * g = g * s`.
    have : g * s * g⁻¹ * g = s * g := by rw [hfix]
    simpa [mul_assoc] using this.symm
  · intro hcent
    ext s
    have hcomm : (s : R) * g = g * (s : R) := hcent (s : R) s.2
    have hfix : MulAut.conjNormal (H := S) g s = s := by
      apply S.subtype_injective
      rw [Subgroup.coe_subtype, MulAut.conjNormal_apply, ← hcomm]; group
    rw [hfix]; rfl

omit [Fact (Nat.Prime p)] in
/-- The `ZMod p`-scalar-torsion condition `p • x = 0` for an elementary-abelian
multiplicative group viewed additively. -/
private theorem additive_nsmul_eq_zero {V : Type*} [Group V]
    (hV : IsElementaryAbelian p V) : ∀ x : Additive V, (p : ℕ) • x = 0 := by
  intro x
  apply Additive.toMul.injective
  show (p • x).toMul = (0 : Additive V).toMul
  rw [toMul_nsmul, toMul_zero]
  exact hV.pow_eq_one x.toMul

/-- **Upper bound** (Gorenstein 4.6 counting): `|R / C_R(S)| ≤ |S / Z(S)|`.

Every `g ∈ R` gives a linear map `Λ_g : S/Z(S) → Z(S)` (the additive form of `δ_g`),
and these are constant on `C_R(S)`-cosets and distinguish them (two `g` with the same `Λ_g`
induce the same conjugation, hence differ by an element of `C_R(S) = ker(conjugation)`). Reading
off `Λ_g` on a fixed `𝔽_p`-basis `b` of `S/Z(S)` embeds `R/C_R(S)` into `(basis) → Z(S)`, whose
cardinality is `|Z(S)|^{dim} = p^{dim} = |S/Z(S)|`. -/
private theorem card_quotient_centralizer_le [S.Normal] (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) :
    Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) ≤
      Nat.card (↥S ⧸ Subgroup.center (↥S)) := by
  classical
  -- Module structures on the two additive groups.
  set Q := ↥S ⧸ Subgroup.center (↥S) with hQ
  set Z := Subgroup.center (↥S) with hZ
  have hQ_EA : IsElementaryAbelian p Q := quotientCenter_isElementaryAbelian hS
  have hZ_EA : IsElementaryAbelian p Z := centerS_isElementaryAbelian hS
  have : IsMulCommutative Q := ⟨⟨hQ_EA.comm⟩⟩
  have : IsMulCommutative Z := ⟨⟨hZ_EA.comm⟩⟩
  have : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule (additive_nsmul_eq_zero hQ_EA)
  have : Module (ZMod p) (Additive Z) := AddCommGroup.zmodModule (additive_nsmul_eq_zero hZ_EA)
  -- A chosen `𝔽_p`-basis of `Additive Q`.
  let ι := Module.Free.ChooseBasisIndex (ZMod p) (Additive Q)
  let b : Module.Basis ι (ZMod p) (Additive Q) := Module.Free.chooseBasis (ZMod p) (Additive Q)
  -- The linear map attached to `g`.
  let Λ : R → (Additive Q →ₗ[ZMod p] Additive Z) :=
    fun g => (deltaQuot hS hSR g).toAdditive.toZModLinearMap p
  -- `Λ g = Λ g'` ⇔ `deltaQuot g = deltaQuot g'`.
  have hΛ_eq_iff : ∀ g g' : R, Λ g = Λ g' ↔ deltaQuot hS hSR g = deltaQuot hS hSR g' := by
    intro g g'
    constructor
    · intro h
      have h1 : (deltaQuot hS hSR g).toAdditive = (deltaQuot hS hSR g').toAdditive :=
        AddMonoidHom.toZModLinearMap_injective p h
      exact MonoidHom.toAdditive.injective h1
    · intro h; simp only [Λ, h]
  -- `deltaHom g = deltaHom g'` ⇒ `conjNormal g = conjNormal g'`.
  have hconj_of_delta : ∀ g g' : R, deltaHom hSR g = deltaHom hSR g' →
      MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) g' := by
    intro g g' hδ
    refine MulEquiv.ext fun s => ?_
    have hs : (deltaHom hSR g s : ↥S) = (deltaHom hSR g' s : ↥S) :=
      congrArg (fun t : Subgroup.center (↥S) => (t : ↥S)) (congrArg (fun f => f s) hδ)
    simp only [deltaHom_apply] at hs
    exact mul_right_cancel hs
  -- `deltaQuot g = deltaQuot g'` ⇒ `deltaHom g = deltaHom g'`.
  have hdelta_of_quot : ∀ g g' : R, deltaQuot hS hSR g = deltaQuot hS hSR g' →
      deltaHom hSR g = deltaHom hSR g' := by
    intro g g' h
    refine MonoidHom.ext fun s => ?_
    have hms := congrArg (fun f => f (QuotientGroup.mk s)) h
    simpa only [deltaQuot_mk] using hms
  -- `conjNormal g = conjNormal g'` ⇒ `deltaQuot g = deltaQuot g'`.
  have hquot_of_conj : ∀ g g' : R, MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) g' →
      deltaQuot hS hSR g = deltaQuot hS hSR g' := by
    intro g g' hconj
    have hδ : deltaHom hSR g = deltaHom hSR g' := by
      refine MonoidHom.ext fun s => ?_
      apply Subtype.ext
      simp only [deltaHom_apply]
      rw [show MulAut.conjNormal (H := S) g s = MulAut.conjNormal (H := S) g' s from
        congrArg (fun e => e s) hconj]
    -- both `deltaQuot` are lifts of `deltaHom g = deltaHom g'`.
    refine MonoidHom.ext fun q => ?_
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    rw [deltaQuot_mk, deltaQuot_mk, hδ]
  -- `conjNormal g = conjNormal g'` ⇔ `g⁻¹ g' ∈ C_R(S)`.
  have hconj_iff_mem : ∀ g g' : R,
      MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) g' ↔
        g⁻¹ * g' ∈ Subgroup.centralizer (S : Set R) := by
    intro g g'
    rw [← conjNormal_ker_eq_centralizer_local (S := S), MonoidHom.mem_ker, map_mul, map_inv]
    constructor
    · intro h; rw [h, inv_mul_cancel]
    · intro h
      have hkey := congrArg (fun e => MulAut.conjNormal (H := S) g * e) h
      simp only [mul_one, mul_inv_cancel_left] at hkey
      exact hkey.symm
  -- The embedding `R/C_R(S) ↪ (ι → Z)`.
  let F : R ⧸ Subgroup.centralizer (S : Set R) → (ι → Z) :=
    Quotient.lift (fun g => fun i => deltaQuot hS hSR g (Additive.toMul (b i)))
      (by
        intro g g' hrel
        -- `g⁻¹ g' ∈ C_R(S)`, so `conjNormal g = conjNormal g'`, so `deltaQuot` agree.
        have hmem : g⁻¹ * g' ∈ Subgroup.centralizer (S : Set R) :=
          (QuotientGroup.leftRel_apply).mp hrel
        have hconj := (hconj_iff_mem g g').mpr hmem
        have hquot := hquot_of_conj g g' hconj
        funext i
        exact congrArg (fun f => f (Additive.toMul (b i))) hquot)
  have hF_inj : Function.Injective F := by
    intro x y hxy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    -- From `F` agreeing: `Λ g (b i) = Λ g' (b i)` on basis, hence `Λ g = Λ g'`.
    have hbasis : ∀ i, Λ g (b i) = Λ g' (b i) := by
      intro i
      have hfi := congrFun hxy i
      simp only [F, Quotient.lift_mk] at hfi
      -- `Λ g (b i) = ofMul (deltaQuot g (toMul (b i)))`.
      change (Additive.ofMul (deltaQuot hS hSR g (Additive.toMul (b i)))) =
        (Additive.ofMul (deltaQuot hS hSR g' (Additive.toMul (b i))))
      rw [hfi]
    have hΛ : Λ g = Λ g' := Module.Basis.ext b hbasis
    have hconj := hconj_of_delta g g' (hdelta_of_quot g g' ((hΛ_eq_iff g g').mp hΛ))
    -- `conjNormal g = conjNormal g'` ⇒ `g⁻¹ g' ∈ C_R(S)` ⇒ same coset.
    exact QuotientGroup.eq.mpr ((hconj_iff_mem g g').mp hconj)
  -- Cardinality bookkeeping: `|ι → Z| = |Z|^|ι| = p^{finrank} = |Q|`.
  have hcardZ : Nat.card Z = p := hS.center_card
  have : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have hι_card : Nat.card ι = Module.finrank (ZMod p) (Additive Q) := by
    rw [Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]
  have hQ_pow : Nat.card Q = p ^ Module.finrank (ZMod p) (Additive Q) := by
    have hcard : Nat.card (Additive Q) = Nat.card Q := Nat.card_congr Additive.toMul
    have := FiniteField.pow_finrank_eq_natCard p (Additive Q)
    rw [hcard] at this
    exact this.symm
  calc
    Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) ≤ Nat.card (ι → Z) :=
      Nat.card_le_card_of_injective F hF_inj
    _ = Nat.card Z ^ Nat.card ι := Nat.card_fun
    _ = p ^ Module.finrank (ZMod p) (Additive Q) := by rw [hcardZ, hι_card]
    _ = Nat.card Q := hQ_pow.symm

omit [Finite R] in
/-- An element `s ∈ S` centralizes `S` (in `R`) iff, as an element of `↥S`, it lies in `Z(S)`. -/
private theorem mem_centralizer_iff_mem_center (s : ↥S) :
    (s : R) ∈ Subgroup.centralizer (S : Set R) ↔ s ∈ Subgroup.center (↥S) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
  constructor
  · intro h t
    apply S.subtype_injective
    exact h (t : R) t.2
  · intro h r hr
    have hv := congrArg (fun x : ↥S => (x : R)) (h ⟨r, hr⟩)
    push_cast at hv
    exact hv

/-- **Reverse bound**: `|S / Z(S)| ≤ |R / C_R(S)|`, via the injection of *coset spaces*
`S/Z(S) ↪ R/C_R(S)` induced by `S.subtype`. (`C_R(S)` need not be normal, so this is an
injection of `Quotient`s, not a group homomorphism.) -/
private theorem card_quotient_center_le_card_quotient_centralizer :
    Nat.card (↥S ⧸ Subgroup.center (↥S)) ≤
      Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) := by
  -- The coset-space map `S/Z(S) → R/C_R(S)`, `[s] ↦ [↑s]`.
  let ψ : (↥S ⧸ Subgroup.center (↥S)) → R ⧸ Subgroup.centralizer (S : Set R) :=
    Quotient.lift (fun s : ↥S => (QuotientGroup.mk (s : R)))
      (by
        intro a b hab
        -- `a⁻¹ b ∈ Z(S)` ⇒ `(↑a)⁻¹ (↑b) ∈ C_R(S)`.
        apply QuotientGroup.eq.mpr
        have hmem : a⁻¹ * b ∈ Subgroup.center (↥S) := (QuotientGroup.leftRel_apply).mp hab
        have hc : ((a⁻¹ * b : ↥S) : R) ∈ Subgroup.centralizer (S : Set R) :=
          (mem_centralizer_iff_mem_center (a⁻¹ * b)).mpr hmem
        simpa using hc)
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hrel : (QuotientGroup.mk (a : R)) = (QuotientGroup.mk (b : R)) := hxy
    have hmem : (a : R)⁻¹ * (b : R) ∈ Subgroup.centralizer (S : Set R) :=
      (QuotientGroup.leftRel_apply).mp (Quotient.exact hrel)
    apply QuotientGroup.eq.mpr
    have hmemS : (a⁻¹ * b : ↥S) ∈ Subgroup.center (↥S) := by
      rw [← mem_centralizer_iff_mem_center]
      simpa using hmem
    simpa using hmemS
  exact Nat.card_le_card_of_injective ψ hψ_inj

/-- **BG Lemma 4.15** (Gorenstein, _Finite Groups_, Lemma 5.4.6, p. 195): if `S` is an
extraspecial subgroup of a `p`-group `R` and `[S, R] ⊆ S'`, then `R = S · C_R(S)`.

The hypothesis `[S, R] ⊆ S'` is recorded as `⁅S, ⊤⁆ ≤ (Z(S)).map S.subtype`, using
`S' = Z(S)` for extraspecial `S` (so the right side is the ambient image of the centre).

The statement is `p`-general: `cl(S) ≤ 2` (i.e. `[S, S] = Z(S)`) and `|Z(S)| = p` are the only
structural inputs; the parity of `p` is not used. (Lemma 4.15 deliberately omits the `p`-odd
standing hypothesis carried by the neighbouring Lemmas 4.5, 4.7 and Prop 4.6.)

Used in BG Thm 4.16 (Blackburn) Case B-1, where `S = Ω₁(R)` is extraspecial with `[S, R] ⊆ S'`,
to split `R` as the central product `S · C_R(S)`. -/
theorem mul_centralizer_eq_top_of_isExtraspecial
    (hS : IsExtraspecial p (↥S))
    (hSR : ⁅S, (⊤ : Subgroup R)⁆ ≤ (Subgroup.center (↥S)).map S.subtype) :
    S ⊔ Subgroup.centralizer (S : Set R) = ⊤ := by
  classical
  -- `S` is normal in `R`.
  have : S.Normal := extraspecial_normal_of_commutator_le (commutator_le_self_of_hSR hSR)
  -- The two bounds force `|S/Z(S)| = |R/C_R(S)|`.
  have hle1 := card_quotient_centralizer_le hS hSR
  have hle2 := card_quotient_center_le_card_quotient_centralizer (S := S)
  have hcard_eq : Nat.card (↥S ⧸ Subgroup.center (↥S)) =
      Nat.card (R ⧸ Subgroup.centralizer (S : Set R)) := le_antisymm hle2 hle1
  -- The reverse injection `ψ : S/Z(S) ↪ R/C_R(S)` is then surjective.
  let ψ : (↥S ⧸ Subgroup.center (↥S)) → R ⧸ Subgroup.centralizer (S : Set R) :=
    Quotient.lift (fun s : ↥S => (QuotientGroup.mk (s : R)))
      (by
        intro a b hab
        apply QuotientGroup.eq.mpr
        have hmem : a⁻¹ * b ∈ Subgroup.center (↥S) := (QuotientGroup.leftRel_apply).mp hab
        have hc : ((a⁻¹ * b : ↥S) : R) ∈ Subgroup.centralizer (S : Set R) :=
          (mem_centralizer_iff_mem_center (a⁻¹ * b)).mpr hmem
        simpa using hc)
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : (a : R)⁻¹ * (b : R) ∈ Subgroup.centralizer (S : Set R) :=
      (QuotientGroup.leftRel_apply).mp (Quotient.exact (hxy : ψ _ = ψ _))
    apply QuotientGroup.eq.mpr
    have hmemS : (a⁻¹ * b : ↥S) ∈ Subgroup.center (↥S) := by
      rw [← mem_centralizer_iff_mem_center]; simpa using hmem
    simpa using hmemS
  have hψ_surj : Function.Surjective ψ := by
    have : Finite (↥S ⧸ Subgroup.center (↥S)) := Nat.finite_of_card_ne_zero (by
      rw [hcard_eq]; exact Nat.card_pos.ne')
    have := Fintype.ofFinite (↥S ⧸ Subgroup.center (↥S))
    have := Fintype.ofFinite (R ⧸ Subgroup.centralizer (S : Set R))
    have hcardF : Fintype.card (↥S ⧸ Subgroup.center (↥S)) =
        Fintype.card (R ⧸ Subgroup.centralizer (S : Set R)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard_eq]
    exact (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq hcardF)).mp hψ_inj
  -- Every `r ∈ R` lies in `S · C_R(S)`.
  rw [eq_top_iff]
  intro r _
  obtain ⟨q, hq⟩ := hψ_surj (QuotientGroup.mk r)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  -- `mk (↑s) = mk r`, so `(↑s)⁻¹ r ∈ C_R(S)`.
  have hrel : (QuotientGroup.mk (s : R) : R ⧸ Subgroup.centralizer (S : Set R)) =
      QuotientGroup.mk r := hq
  have hc : (s : R)⁻¹ * r ∈ Subgroup.centralizer (S : Set R) :=
    (QuotientGroup.leftRel_apply).mp (Quotient.exact hrel)
  -- `r = ↑s · ((↑s)⁻¹ r)` with `↑s ∈ S`, `(↑s)⁻¹ r ∈ C_R(S)`.
  have hr_eq : r = (s : R) * ((s : R)⁻¹ * r) := by group
  rw [hr_eq]
  exact Subgroup.mul_mem_sup s.2 hc

end ExtraspecialCommutator

end OddOrder.BG.Ch1.S04


