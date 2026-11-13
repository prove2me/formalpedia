-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_Props109To1011
-- name    : OddOrder_Peterfalvi_S12_Props109To1011
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:19:07.408897+00:00
-- url     : https://prove2.me/theorems/345096fa-4367-44e1-95db-4cf9485aca19
-- title:
--   Peterfalvi (10.9)–(11.8.3): propositions on the aligned $\omega^\sigma$-grid (continuation)
-- statement:
--   A continuation file for Peterfalvi (11.8.3), proving the row and column independence of the integer $\beta$ and the column-conjugation index on the aligned $\omega^\sigma$-grid.
--
--   Main declarations: `Hypothesis.exists_colInv_alignedOmegaSigma_conj` (Peterfalvi (11.8.3), the column-conjugation index at row `0`); `Hypothesis.beta_row_eq` (Peterfalvi (11.8.3) first part, row independence of `β`); `Hypothesis.beta_column_eq_zeroRow` (Peterfalvi (11.8.3) first part, column independence of `β` at row `0`); `Hypothesis.beta_isReal` (Peterfalvi (11.8.3), `β` is real).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_Props109To1011.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_Props109To1011.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_Prop109

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (11.8.3), the column-conjugation index at row `0`** ((3.9)(a)/(4.9)(a) on the
row-`0` grids; the `w₂`-side companion of `exists_rowInv_alignedOmegaSigma_conj`, Coq
`cfAut_cycTIiso`/`prTIirr_aut` + `aut_Iirr_eq0`): there is a column index `k` — the
**column-inversion** index, `χ₂(k) = χ₂(j)⁻¹` on the `W₂`-dual — such that complex conjugation
sends the row-`0` grid values at column `j` to the row-`0` values at column `k`, simultaneously
for the `σ`-grid (`(ω_{0j}^σ)‾ = ω_{0k}^σ`, the (3.9) Galois commutation) and for the `M`-side
`μ`-grid (`μ̄_{0j} = μ_{0k}`, the (4.9)(a) conjugation closure; the trivial row-`0` dual is fixed
by inversion, so the row does not move), with matching column signs `δ_k = δ_j` (the (4.9)(a)
sign bridge `δ_j·μ̄_{0j} = δ_k·μ_{0k}` against the common irreducible `μ_{0k}`).  Moreover
`k = 0 ↔ j = 0` (inversion fixes only the trivial column pointer; Coq `aut_Iirr_eq0`), which is
what lets the (11.8.3) reality argument apply the β-independence at column `k`. -/
theorem Hypothesis.exists_colInv_alignedOmegaSigma_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) :
    ∃ k : Fin hyp.w2,
      (k = 0 ↔ j = 0)
      ∧ ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          (hyp.alignedOmegaSigmaGrid hG hodd 0 j)
        = hyp.alignedOmegaSigmaGrid hG hodd 0 k
      ∧ ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.muGrid hG hodd 0 j)
        = hyp.muGrid hG hodd 0 k
      ∧ hyp.muColumnSign hG hodd k = hyp.muColumnSign hG hodd j := by
  have := hyp.finiteG
  classical
  -- reconstruct the `let`s of `alignedOmegaSigmaGrid`/`muGrid`/`muColumnSign`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- the `W₂`-dual of an arbitrary column `b`
  let χ₂ : Fin hyp.w2 → ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := fun b =>
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm b)
  -- the column-inversion translated index
  let k : Fin hyp.w2 :=
    finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹))
  -- the column dual at `k` is the inverse dual at `j`
  have hχ₂k : χ₂ k = (χ₂ j)⁻¹ := by
    change finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (finCongr hcardW2sub
        ((finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹)))) = (χ₂ j)⁻¹
    rw [show finCongr hcardW2sub.symm (finCongr hcardW2sub
          ((finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹)))
        = (finCardEquivCharacterGroup _).symm ((χ₂ j)⁻¹) from by simp]
    exact (finCardEquivCharacterGroup _).apply_symm_apply _
  -- the trivial-column detector: `χ₂ b = 1 ↔ b = 0`
  have hzero : ∀ b : Fin hyp.w2, χ₂ b = 1 ↔ b = 0 := by
    intro b
    constructor
    · intro hb
      rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at hb
      have hb0 : finCongr hcardW2sub.symm b = 0 := (finCardEquivCharacterGroup _).injective hb
      exact Fin.ext (by simpa using congrArg Fin.val hb0)
    · intro hb
      change finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm b) = 1
      rw [hb, show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
        finCardEquivCharacterGroup_zero]
  -- `k = 0 ↔ j = 0` (the Coq `aut_Iirr_eq0`)
  have hk0 : k = 0 ↔ j = 0 := by
    rw [← hzero k, ← hzero j, hχ₂k]
    exact @inv_eq_one ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _ (χ₂ j)
  -- §5 `G`-level TI-cyclic hypothesis (for `σ`) and the `W ≤ M ≤ G` transport
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported row-`0` linear character of `tic.W` at column `b`
  let ξ : Fin hyp.w2 → (↥tic.W →* ℂˣ) := fun b =>
    (h.sdiffTICyclicHypothesis.omegaProdChar
      (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ b)).comp e.toMonoidHom
  -- `alignedOmegaSigmaGrid 0 b = σ(ω ξ_b)` for any column `b`
  have step1 : ∀ b, hyp.alignedOmegaSigmaGrid hG hodd 0 b
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
          (tic.omega (ξ b) : ClassFunction ↥tic.W ℂ) := by
    intro b
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd)
        (tic.omega (ξ b) : ClassFunction ↥tic.W ℂ)
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd)
          (tic.omega (ξ b) : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- the row-`0` dual is trivial (so inversion fixes it)
  have hχ1 : h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 1 := by
    rw [show (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 from by simp, h.w1CharEquiv_zero]
  -- `ξ_j⁻¹ = ξ_k` (`omegaProdChar` inverts coordinatewise; the trivial row factor is fixed)
  have hχ1inv : (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)))⁻¹
      = h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1)) := by
    rw [hχ1]
    exact @inv_one ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _
  have hξinv : (ξ j)⁻¹ = ξ k := by
    have hprod : (h.sdiffTICyclicHypothesis.omegaProdChar
          (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ j))⁻¹
        = h.sdiffTICyclicHypothesis.omegaProdChar
            (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ k) := by
      rw [OddOrder.Peterfalvi.S06.omegaProdChar_inv, hχ₂k]
      exact congrArg
        (fun c => h.sdiffTICyclicHypothesis.omegaProdChar c ((χ₂ j)⁻¹)) hχ1inv
    change ((h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ j)).comp e.toMonoidHom)⁻¹
      = (h.sdiffTICyclicHypothesis.omegaProdChar
        (h.w1CharEquiv (finCongr hcardW1.symm (0 : Fin hyp.w1))) (χ₂ k)).comp e.toMonoidHom
    refine MonoidHom.ext fun w => Units.val_injective ?_
    rw [MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← hprod,
      MonoidHom.inv_apply]
  -- σ-side: `(ω_{0j}^σ)‾ = ω_{0k}^σ` ((3.9) commutation + conjugation inverts the source)
  have hconjσ : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (hyp.alignedOmegaSigmaGrid hG hodd 0 j) = hyp.alignedOmegaSigmaGrid hG hodd 0 k := by
    rw [step1 j, step1 k,
      tic.sigma_mapRingEquiv_comm rfl (hyp.canonicalFullDadeApp hG hodd) _ _,
      OddOrder.Peterfalvi.S06.galoisMap_conj_omega, hξinv]
  -- the row-`0` index is fixed by the (4.9)(a) row inversion
  have hrow0 : OddOrder.Peterfalvi.S06.rowInv h (finCongr hcardW1.symm (0 : Fin hyp.w1))
      = finCongr hcardW1.symm (0 : Fin hyp.w1) := by
    have h_inv_one :
        ((1 : (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)⁻¹) = 1 :=
      @inv_one ((h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _
    rw [OddOrder.Peterfalvi.S06.rowInv, hχ1, h_inv_one]
    exact h.w1CharEquiv.symm_apply_eq.mpr hχ1.symm
  -- μ-side: `μ̄_{0j} = μ_{0k}` ((4.9)(a) conjugation closure at the fixed row `0`)
  have hμconj : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.muGrid hG hodd 0 j)
      = hyp.muGrid hG hodd 0 k := by
    have ej : hyp.muGrid hG hodd 0 j
        = ((h.columnFamily (χ₂ j)).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid; rfl
    have ek : hyp.muGrid hG hodd 0 k
        = ((h.columnFamily (χ₂ k)).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid; rfl
    rw [ej, ek, ← IrreducibleCharacter.galoisMap_apply_coe,
      OddOrder.Peterfalvi.S06.certainType_mu_conj_eq h (χ₂ j) (finCongr hcardW1.symm 0),
      hrow0]
    exact congrArg
      (fun c => ((h.columnFamily c).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ))
      hχ₂k.symm
  -- sign match `δ_k = δ_j` ((4.9)(a) sign bridge against the common irreducible `μ_{0k}`)
  have hsign : hyp.muColumnSign hG hodd k = hyp.muColumnSign hG hodd j := by
    have esj : hyp.muColumnSign hG hodd j = (h.columnFamily (χ₂ j)).sign := by
      unfold Hypothesis.muColumnSign; rfl
    have esk : hyp.muColumnSign hG hodd k = (h.columnFamily (χ₂ k)).sign := by
      unfold Hypothesis.muColumnSign; rfl
    have hbr := OddOrder.Peterfalvi.S06.certainType_mu_conj_bridge h (χ₂ j)
      (finCongr hcardW1.symm 0)
    rw [← IrreducibleCharacter.galoisMap_apply_coe,
      OddOrder.Peterfalvi.S06.certainType_mu_conj_eq h (χ₂ j) (finCongr hcardW1.symm 0),
      ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily (χ₂ j)).sign
        (((h.columnFamily ((χ₂ j)⁻¹)).mu (OddOrder.Peterfalvi.S06.rowInv h
          (finCongr hcardW1.symm 0))) : ClassFunction ↥M ℂ),
      ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily ((χ₂ j)⁻¹)).sign
        (((h.columnFamily ((χ₂ j)⁻¹)).mu (OddOrder.Peterfalvi.S06.rowInv h
          (finCongr hcardW1.symm 0))) : ClassFunction ↥M ℂ)] at hbr
    have hI := congrArg (fun φ => ClassFunction.inner φ
      (((h.columnFamily ((χ₂ j)⁻¹)).mu (OddOrder.Peterfalvi.S06.rowInv h
        (finCongr hcardW1.symm 0))) : ClassFunction ↥M ℂ)) hbr
    simp only [ClassFunction.inner_smul_left, irreducibleCharacter_inner_eq_ite, if_true,
      mul_one] at hI
    rw [esk, esj, hχ₂k]
    exact_mod_cast hI.symm
  exact ⟨k, hk0, hconjσ, hμconj, hsign⟩

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.3) first part, row independence of `β`** (Coq `betaE`, row move): the
(11.8.3) residual `β_{ij} = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}` at row `i` equals the
row-`0` residual `β_{0j}`.  The `nζ` tails of `α_{ij}` and `α_{0j}` cancel, so the difference of
the `τ`-arguments is the four-corner `μ_{ij} − μ_{0j} − δμ_{i0} + δμ_{00}`, whose Dade image is
`δ·(ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ + ω_{00}^σ)` — the δ-scaled Peterfalvi (4.10), threaded here as
`h410` until the §10 instantiation of Hypothesis (4.6) lands (issue 9004) — and the `ω`-corners
cancel against the `δ(ω_{ij}^σ − ω_{i0}^σ)` terms. -/
theorem Hypothesis.beta_row_eq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) {ζ : ClassFunction ↥M ℂ} {δ : ℤ} {n : ℕ}
    (h410 : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
          - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0)) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
      + (n : ℂ) • coh.extension ζ
    = hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
      + (n : ℂ) • coh.extension ζ := by
  have harg : (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        + (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
          - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0) := by
    module
  rw [harg, map_add, h410]
  module

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.3) first part, column independence of `β` at row `0`** (Coq `betaE`, column
move): for two columns `j, k` of the *same* sign `δ`, the row-`0` residuals agree,
`β_{0j} = β_{0k}`.
The `−δμ_{00} − nζ` tails of `α_{0j}` and `α_{0k}` are identical, so the difference of the
`τ`-arguments is `μ_{0j} − μ_{0k}`, whose Dade image is `δ·(ω_{0j}^σ − ω_{0k}^σ)` — the row-`0`
Peterfalvi (4.8), threaded here as `h48` until the §10 instantiation of Hypothesis (4.6) lands
(issue 9004). -/
theorem Hypothesis.beta_column_eq_zeroRow [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (j k : Fin hyp.w2) {ζ : ClassFunction ↥M ℂ} {δ : ℤ} {n : ℕ}
    (h48 : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd 0 k)) :
    hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
      + (n : ℂ) • coh.extension ζ
    = hyp.tau (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 k - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
      + (n : ℂ) • coh.extension ζ := by
  have harg : (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      = (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        + (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k) := by
    module
  rw [harg, map_add, h48]
  module

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.3), `β` is real** (Coq `Rbeta`): the (11.8.3) residual
`β = α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ) + nζ^{τ₁}` satisfies `β̄ = β`.  This discharges the `hβr`
hypothesis of the (11.8.5) capstone `residualCoeff_eq_zero`.

Proof (Coq `PFsection11.v` 823-831): reduce to row `0` (`beta_row_eq`, the threaded (4.10)); apply
complex conjugation through each term — `(α_{0j}^τ)‾ = (ᾱ_{0j})^τ` (`tau_mapRingEquiv_comm`, the
`A₀`-support from `muGrid_alpha_support`), `ᾱ_{0j} = μ_{0k} − δμ_{00} − nζ̄` and
`(ω_{0j}^σ)‾ = ω_{0k}^σ`, `(ω_{00}^σ)‾ = ω_{00}^σ` (the column-conjugation index `k`,
`exists_colInv_alignedOmegaSigma_conj`), and `(ζ^{τ₁})‾ = ζ̄^{τ₁}` (`SHC_extension_conj`, odd
order).  The conjugate is thus `β_{0k}` computed at `ζ̄`; the `S(HC)`-coherence
`τ(ζ − ζ̄) = ζ^{τ₁} − ζ̄^{τ₁}` (`tau_zeta_sub_conj_eq_SHC_extension`) trades `ζ̄` back for `ζ`,
giving `β̄ = β_{0k}`; finally `β_{0k} = β_{0j}` by the column move (`beta_column_eq_zeroRow`, the
threaded row-`0` (4.8) at the conjugate column `k ≠ 0`).

The Peterfalvi (4.8)/(4.10) inputs are threaded as `h48`/`h410` until the §10 instantiation of
Hypothesis (4.6) lands (issue 9004); everything else is proved. -/
theorem Hypothesis.beta_isReal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hconj : ∀ {χ : ClassFunction ↥M ℂ}, χ ∈ inducedFamily M → IsIrreducibleCharacter χ →
      χ 1 = (hyp.w1 : ℂ) → (coh.extension χ).conj = coh.extension χ.conj)
    (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg0 : hyp.muGrid hG hodd 0 j 1 = (d : ℂ)) (hμ00 : hyp.muGrid hG hodd 0 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (h410 : hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
          - (δ : ℂ) • hyp.muGrid hG hodd i 0 + (δ : ℂ) • hyp.muGrid hG hodd 0 0)
        = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0))
    (h48 : ∀ k : Fin hyp.w2, k ≠ 0 →
        hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
          = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
              - hyp.alignedOmegaSigmaGrid hG hodd 0 k)) :
    ClassFunction.IsReal
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        + (n : ℂ) • coh.extension ζ) := by
  have := hyp.finiteG
  classical
  -- reduce to row `0` (the threaded (4.10) row move)
  have hrow := hyp.beta_row_eq hG coh hodd i j (ζ := ζ) (n := n) h410
  rw [ClassFunction.IsReal, hrow]
  -- the `.conj = mapRingEquiv conjAe` bridges
  have hbridgeG : ∀ X : ClassFunction G ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  have hbridgeM : ∀ X : ClassFunction ↥M ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  -- the column-conjugation index `k` (piece 1) at `j` and at `0`
  obtain ⟨k, hk0iff, hσconj, hμconj, hsign⟩ := hyp.exists_colInv_alignedOmegaSigma_conj hG hodd j
  have hk0 : k ≠ 0 := fun hk => hj0 (hk0iff.mp hk)
  obtain ⟨k₀, hk₀iff, hσ0, hμ0conj, -⟩ := hyp.exists_colInv_alignedOmegaSigma_conj hG hodd 0
  rw [hk₀iff.mpr rfl] at hσ0 hμ0conj
  -- distribute the conjugation over the three terms of `β_{0j}` (pointwise)
  have hdist : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd 0 0)
        + (n : ℂ) • coh.extension ζ)
      = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
          (hyp.tau (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ))
        - (δ : ℂ) • (ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (hyp.alignedOmegaSigmaGrid hG hodd 0 j)
          - ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (hyp.alignedOmegaSigmaGrid hG hodd 0 0))
        + (n : ℂ) • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
            (coh.extension ζ) := by
    ext g
    simp only [ClassFunction.mapRingEquiv_apply, ClassFunction.add_apply, ClassFunction.sub_apply,
      ClassFunction.smul_apply, map_add, map_sub, map_mul, map_intCast, map_natCast]
  -- conjugate of the `M`-side argument: `ᾱ_{0j} = μ_{0k} − δμ_{00} − nζ̄`
  have hαconj : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
      = hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ.conj := by
    have hdistM : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (hyp.muGrid hG hodd 0 j - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.muGrid hG hodd 0 j)
          - (δ : ℂ) • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
              (hyp.muGrid hG hodd 0 0)
          - (n : ℂ) • ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv ζ := by
      ext g
      simp only [ClassFunction.mapRingEquiv_apply, ClassFunction.sub_apply,
        ClassFunction.smul_apply, map_sub, map_mul, map_intCast, map_natCast]
    rw [hdistM, hμconj, hμ0conj, ← hbridgeM]
  -- conjugate the three terms: `τ`-Galois (piece 2), σ-grid (piece 1), `τ₁`-Galois (piece 3)
  have hτcomm := hyp.tau_mapRingEquiv_comm Complex.conjAe.toRingEquiv
    (hyp.muGrid_alpha_support hG hodd (i := 0) hj0 hζS hdeg0 hμ00 hζ1 hnf hδj)
  have hζτ : ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
      (coh.extension ζ) = coh.extension ζ.conj := by
    rw [← hbridgeG, hconj hζS hζirr hζ1]
  rw [hbridgeG, hdist, hσconj, hσ0, hζτ, ← hτcomm, hαconj]
  -- trade `ζ̄` for `ζ` through the `S(HC)`-coherence, landing on `β_{0k}`
  have hcoh := hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1
  have hswap : (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ.conj)
      = (hyp.muGrid hG hodd 0 k - (δ : ℂ) • hyp.muGrid hG hodd 0 0 - (n : ℂ) • ζ)
        + (n : ℂ) • (ζ - ζ.conj) := by
    module
  have hnτ : hyp.tau ((n : ℂ) • (ζ - ζ.conj)) = (n : ℂ) • hyp.tau (ζ - ζ.conj) := by
    rw [show (n : ℂ) • (ζ - ζ.conj) = ((n : ℤ) : ℂ) • (ζ - ζ.conj) from by norm_num,
      Int.cast_smul_eq_zsmul ℂ (n : ℤ), map_zsmul,
      show (n : ℂ) • hyp.tau (ζ - ζ.conj) = ((n : ℤ) : ℂ) • hyp.tau (ζ - ζ.conj) from by norm_num,
      Int.cast_smul_eq_zsmul ℂ (n : ℤ)]
  rw [hswap, map_add, hnτ, hcoh]
  -- the `β_{0j} = β_{0k}` column move (the threaded row-`0` (4.8) at the conjugate column)
  have hcol := hyp.beta_column_eq_zeroRow hG coh hodd j k (ζ := ζ) (n := n) (h48 k hk0)
  rw [hcol]
  -- assemble: both sides are `β_{0k}` up to the cancelling `nζ^{τ₁}` swap terms
  module

open scoped FiniteInduce in
/-- **Peterfalvi (5.3.b) for the S(HC)-coherent extension** (the (11.8.5) `a = 0` input).  For a
degree-`w₁` irreducible `ζ ∈ S(HC)`, the coherent image `ζ^{τ₁} = SHC_isCoherent.extension ζ` is
orthogonal to every aligned `σ`-grid vector `ω_{ij}^σ`.

Port of the intermediate of `tau1_zeta_vanishes_on_typePV` to the `S(HC)`-coherence (the by-contra
lacks the full-`S` `coh`). Writing `ω_{ij}^σ = χ_{P j}`
(`exists_alignedOmegaSigmaGrid_chiFam_family`,
the *same* `tic`/`canonicalFullDadeApp`), the difference `ζ^{τ₁} − ζ̄^{τ₁} = (ζ − ζ̄)^τ`
(`tau_zeta_sub_conj_eq_SHC_extension`) has `≤ 2 < min(w₁, w₂)` nonzero `σ`-coefficients (each of
`ζ^{τ₁}, ζ̄^{τ₁}` has `≤ 1`, being norm-`1` — `ncard_inner_chiFam_ne_zero_le_one`), so
`sigmaCoeff_eq_zero_of_sigmaNC_lt` gives `⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{P j}⟩ = 0`; the norm-`1` projection
`inner_left_eq_zero_of_inner_sub_eq_zero` (orthonormal `{ζ^{τ₁}, ζ̄^{τ₁}}` via
`SHC_extension_inner_*`)
then upgrades this to `⟨ζ^{τ₁}, χ_{P j}⟩ = 0`. -/
theorem Hypothesis.SHC_extension_inner_alignedOmegaSigma_eq_zero [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (coh.extension ζ)
      (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0 := by
  have := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  obtain ⟨P, _hPinj, hPeq⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  rw [hPeq j]
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have haZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hbZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  have ha1 : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ) = 1 := hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  have hb1 : ClassFunction.inner (coh.extension ζ.conj)
      (coh.extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG coh hζcS hζcirr hζc1
  have hab : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ.conj) = 0 :=
    hyp.SHC_extension_inner_of_ne hG coh hζS hζirr hζ1 hζcS hζcirr hζc1 (fun h => hζne h.symm)
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.extension ζ)
              (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.extension ζ.conj)
              (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (P j) = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (P j)
  have hdiff : ClassFunction.inner (coh.extension ζ
      - coh.extension ζ.conj) (tic.chiFam hVeq app (P j)) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1]; exact hL3
  have hsZ : tic.chiFam hVeq app (P j) ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (P j)
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (P j)) (tic.chiFam hVeq app (P j)) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ζ^{τ₁}` vanishes on `V`, S(HC)-coherent version** (the (11.8.2)/(11.8.5)
input).  For a degree-`w₁` irreducible `ζ ∈ S(HC)` with `ζ̄ ≠ ζ`, the S(HC)-coherent image
`ζ^{τ₁} = SHC_isCoherent.extension ζ` vanishes on `V = typePV`.

Port of `tau1_zeta_vanishes_on_typePV` to the `S(HC)`-coherence (the (11.8) by-contradiction lacks
the full-`S` `coh`).  Same argument as `SHC_extension_inner_alignedOmegaSigma_eq_zero`, but
concluded
against every `χ_{pq}` (`eq_zero_of_mem_V_of_inner_chiFam_eq_zero`, Peterfalvi (3.2.d)) rather than
a
single aligned grid vector: `(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` (`tau_zeta_sub_conj_eq_SHC_extension`)
vanishes on `V` with `NC ≤ 2 < min(w₁, w₂)`, so `sigmaCoeff_eq_zero_of_sigmaNC_lt` gives
`⟨ζ^{τ₁} − ζ̄^{τ₁}, χ_{pq}⟩ = 0`, and the norm-`1` projection
`inner_left_eq_zero_of_inner_sub_eq_zero`
(orthonormal `{ζ^{τ₁}, ζ̄^{τ₁}}`) upgrades it to `⟨ζ^{τ₁}, χ_{pq}⟩ = 0` for every `pq`. -/
theorem Hypothesis.SHC_tau1_zeta_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.extension ζ v = 0 := by
  have := hyp.finiteG
  classical
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have haZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hbZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩)
  have ha1 : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ) = 1 := hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  have hb1 : ClassFunction.inner (coh.extension ζ.conj)
      (coh.extension ζ.conj) = 1 :=
    hyp.SHC_extension_inner_self hG coh hζcS hζcirr hζc1
  have hab : ClassFunction.inner (coh.extension ζ)
      (coh.extension ζ.conj) = 0 :=
    hyp.SHC_extension_inner_of_ne hG coh hζS hζirr hζ1 hζcS hζcirr hζc1 (fun h => hζne h.symm)
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.extension ζ)
              (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.extension ζ.conj)
              (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.extension ζ)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.extension ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  refine tic.eq_zero_of_mem_V_of_inner_chiFam_eq_zero hVeq app (fun a' b' => ?_) hv
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (a', b') = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (a', b')
  have hdiff : ClassFunction.inner (coh.extension ζ
      - coh.extension ζ.conj) (tic.chiFam hVeq app (a', b')) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_SHC_extension hG coh hodd hζS hζirr hζ1]; exact hL3
  have hsZ : tic.chiFam hVeq app (a', b') ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (a', b')
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (a', b')) (tic.chiFam hVeq app (a', b')) =
      1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

open scoped FiniteInduce in
/-- **`S(HC)` `τ₁`-image vanishes on `V`** for any degree-`w₁` irreducible `χ ∈ inducedFamily M`.
The non-reality hypothesis `χ̄ ≠ χ` of `SHC_tau1_zeta_vanishes_on_typePV` is discharged via
`inducedFamily_degree_w1_conj_ne` (Peterfalvi (1.1)), so this needs only `χ ∈ S(HC)`.  Used to
vanish
the `∑_{λ∈S₁} λ^{τ₁}` correction of the (11.8.2) residual `X = α^τ + nζ^{τ₁} − a∑λ^{τ₁}` on `V` in
the general `a ∈ {0, 2}` case. -/
theorem Hypothesis.SHC_extension_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {χ : ClassFunction ↥M ℂ} (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (hχ1 : χ 1 = (hyp.w1 : ℂ)) {v : G} (hv : v ∈ typePV M hyp.typeP) :
    coh.extension χ v = 0 :=
  hyp.SHC_tau1_zeta_vanishes_on_typePV hG coh hodd hχS hχirr hχ1
    (hyp.inducedFamily_degree_w1_conj_ne hG hχirr hχ1) hv

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `ψ = X − δ(ω^σ diff)` vanishes on `V`, S(HC)-coherent version** (`a = 0`
form).  Port of `muGridPsi_vanishes_on_typePV` to `S(HC)`-coherence: with `X = α_{ij}^τ + n·ζ^{τ₁}`
(`ζ^{τ₁} = SHC_isCoherent.extension ζ`), the virtual character `ψ = X − δ·(ω_{ij}^σ − ω_{i0}^σ)`
vanishes on `V = typePV`.  Combines the value-on-`V` leg `tau_muGridAlpha_apply_eq_on_typePV`
(`α^τ = δ(ω^σ diff)` on `V`, coherence-free) with `SHC_tau1_zeta_vanishes_on_typePV`
(`ζ^{τ₁}` vanishes on `V`).  For the general `(11.8.2)` residual `X = α^τ + n·ζ^{τ₁} − a·∑λ^{τ₁}`
(`a ∈ {0, 2}`) the extra `∑λ^{τ₁}` also vanishes on `V` (each `λ ∈ S(HC)`, same lemma). -/
theorem Hypothesis.SHC_muGridPsi_vanishes_on_typePV [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        + (n : ℂ) • coh.extension ζ
        - (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v = 0 := by
  have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj hv
  have hζv := hyp.SHC_tau1_zeta_vanishes_on_typePV hG coh hodd hζS hζirr hζ1 hζne hv
  simp only [ClassFunction.sub_apply, ClassFunction.add_apply, ClassFunction.smul_apply] at hleg ⊢
  rw [hleg, hζv]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖X‖² = 2` and `X ⊥ ζ^{τ₁}`, S(HC)-coherent version** (`a = 0`), where
`X = α_{ij}^τ + n·ζ^{τ₁}` (`ζ^{τ₁} = SHC_isCoherent.extension ζ`).  Given the `a = 0` inner product
`⟨α_{ij}^τ, ζ^{τ₁}⟩ = −n` (`muGridAlpha_tau_residual_norm` with `a = 0`), with
`‖α_{ij}^τ‖² = 2 + n²`
(`muGridAlpha_tau_inner_self`) and `‖ζ^{τ₁}‖² = 1` (`SHC_extension_inner_self`):
`⟨X, ζ^{τ₁}⟩ = ⟨α^τ, ζ^{τ₁}⟩ + n‖ζ^{τ₁}‖² = −n + n = 0` and
`‖X‖² = ‖α^τ‖² + 2n⟨α^τ, ζ^{τ₁}⟩ + n²‖ζ^{τ₁}‖² = (2+n²) − 2n² + n² = 2`.  SHC port of
`muGridAlpha_tau_X_inner`, the norm-`2` input to the SHC Dade-image trichotomy (SHC
`alpha_tau_image`). -/
theorem Hypothesis.SHC_muGridAlpha_tau_X_inner [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1)
    (hα0 : ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = -(n : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ)
        (coh.extension ζ) = 0
    ∧ ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ)
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ) = 2 := by
  have hnorm_a := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  have hzz := hyp.SHC_extension_inner_self hG coh hζS hζirr hζ1
  have hα0' : ClassFunction.inner (coh.extension ζ)
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      = -(n : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hα0, star_neg, star_natCast]
  constructor
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_smul_left, hα0, hzz, mul_one]
    ring
  · simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hα0, hα0', hnorm_a, hzz, star_natCast, mul_one]
    ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.5) Dade-image identity, S(HC)-coherent version** (`a = 0`):
`α_{ij}^τ = δ·(ω_{ij}^σ − ω_{i0}^σ) − n·ζ^{τ₁}` with `ζ^{τ₁} = SHC_isCoherent.extension ζ`, given
the
`a = 0` inner product `⟨α_{ij}^τ, ζ^{τ₁}⟩ = −n` (`muGridAlpha_tau_residual_norm` with `a = 0`).

SHC port of `tau_muGridAlpha_eq` (the full-`coh` (10.5) endgame, which the (11.8) by-contradiction
cannot use).  Writing `X = α_{ij}^τ + n·ζ^{τ₁}` (`∈ ℤ[Irr G]`, `‖X‖² = 2` via
`SHC_muGridAlpha_tau_X_inner`), the aligned `σ`-grid entries are `χ`-family members
(`exists_alignedOmegaSigmaGrid_chiFam_family`) and `ψ = X − δ(ω^σ diff)` vanishes on `V`
(`SHC_muGridPsi_vanishes_on_typePV`), so the norm-`2` Dade-image trichotomy
`eq_smul_chiFam_diff_of_vanishOnV` forces `X = δ(ω_{ij}^σ − ω_{i0}^σ)`. -/
theorem Hypothesis.SHC_tau_muGridAlpha_eq [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1)
    (hα0 : ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = -(n : ℂ)) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        - (n : ℂ) • coh.extension ζ := by
  have := hyp.finiteG
  classical
  have hXfacts := hyp.SHC_muGridAlpha_tau_X_inner hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj
    hdζ h0ζ hδpm hα0
  have hτ1ζZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span ⟨hζS, hζirr, hζ1⟩)
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  have hXZ : hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      + (n : ℂ) • coh.extension ζ ∈ ZIrr G := by
    refine Submodule.add_mem _ hαZ ?_
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hτ1ζZ n
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hPne : P j ≠ P 0 := fun h => hj0 (hPinj h)
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hP0' : tic.chiFam hVeq app (P 0) = hyp.alignedOmegaSigmaGrid hG hodd i 0 := (hP 0).symm
  have hψV : ∀ v ∈ tic.V,
      (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
          + (n : ℂ) • coh.extension ζ
        - (δ : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P 0))) v = 0 := by
    intro v hv
    rw [hPj', hP0']
    exact hyp.SHC_muGridPsi_vanishes_on_typePV hG coh hodd hj0 hζS hζirr hζ1 hζne hdeg hμ0 hnf hδj
        hv
  rw [eq_sub_iff_add_eq, ← hPj', ← hP0']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hXZ hXfacts.2 hPne hδpm hψV

open scoped FiniteInduce in
/-- **General `S(HC)`-coherence split** `(ζ − η)^τ = ζ^{τ₁} − η^{τ₁}` for degree-`w₁` irreducibles
`ζ, η ∈ S(HC)` (α-grid `S₁`-`τ₁` input to (11.8.2)). Generalizes
`tau_zeta_sub_conj_eq_SHC_extension`
(the `η = ζ̄` case) to an arbitrary `S(HC)` member: since `ζ, η ∈ S(HC)` have equal degree `w₁`, the
difference `ζ − η` is `A₀`-supported (`inducedFamily_sub_support`) and lies in `ℤ[S(HC)]`, where
`SHC_isCoherent.extension` agrees with `hyp.tau` (`extends_on_supported`). -/
theorem Hypothesis.tau_sub_eq_SHC_extension [Finite G] {M : Subgroup G}
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ η : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hηS : η ∈ inducedFamily M) (hηirr : IsIrreducibleCharacter η) (hη1 : η 1 = (hyp.w1 : ℂ)) :
    hyp.tau (ζ - η)
      = coh.extension ζ - coh.extension η := by
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
  have hspanη : η ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hηS, hηirr, hη1⟩
  have hmem : (ζ - η) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanη, hyp.inducedFamily_sub_support hζS hηS (hζ1.trans hη1.symm)⟩
  rw [← coh.extends_on_supported _ hmem, map_sub]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.2), the `S₁^{τ₁}`-projection coefficient relation**:
`(α_{ij}^τ, ζ^{τ₁}) − (α_{ij}^τ, η^{τ₁}) = −n` for any degree-`w₁` irreducible `η ∈ S(HC)`, `η ≠ ζ`.
Combining the general split `(ζ − η)^τ = ζ^{τ₁} − η^{τ₁}` (`tau_sub_eq_SHC_extension`), the
`τ`-isometry
on the supported `α_{ij}` and `ζ − η` (`tau_inner_eq_of_supported`), and the source value `−n`
(`muGridAlpha_inner_zeta_sub_irr`).  Since the orthonormal `{λ^{τ₁} : λ ∈ S₁}` gives
`(α_{ij}^τ, λ^{τ₁})` as the projection coefficient, this forces `(α_{ij}^τ, η^{τ₁}) = a` (constant
in
`η ≠ ζ`) and `(α_{ij}^τ, ζ^{τ₁}) = a − n` — the coefficient structure of the (11.8.2) decomposition
`α_{ij}^τ = X − nζ^{τ₁} + a∑_{λ∈S₁}λ^{τ₁}`. -/
theorem Hypothesis.muGridAlpha_tau_inner_SHC_extension_sub [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ η : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hηS : η ∈ inducedFamily M) (hηirr : IsIrreducibleCharacter η)
    (hη1 : η 1 = (hyp.w1 : ℂ)) (hηne : η ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ)
      - ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension η) = -(n : ℂ) := by
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hζηsupp : (ζ - η).support ⊆ hyp.A0 :=
    hyp.inducedFamily_sub_support hζS hηS (hζ1.trans hη1.symm)
  rw [← ClassFunction.inner_sub_right,
    ← hyp.tau_sub_eq_SHC_extension hG coh hζS hζirr hζ1 hηS hηirr hη1,
    hyp.tau_inner_eq_of_supported hαsupp hζηsupp,
    hyp.muGridAlpha_inner_zeta_sub_irr hG hodd i j hζirr hηirr hdζ h0ζ (hη1.trans hζ1.symm) hηne]

open scoped FiniteInduce in
/-- **`SHC_isCoherent.extension` is injective on `S(HC)`** (α-grid `S₁`-`τ₁` input to (11.8.2)):
distinct degree-`w₁` irreducibles of `S(HC)` have distinct coherent images.  Immediate from the
orthonormality (`SHC_extension_inner_self` = 1, `SHC_extension_inner_of_ne` = 0): if the images
coincided, `1 = ⟨φ^{τ₁}, φ^{τ₁}⟩ = ⟨φ^{τ₁}, ψ^{τ₁}⟩ = 0`.  Needed to materialize
`{λ^{τ₁} : λ ∈ S(HC)}` as an orthonormal `Finset` for the (11.8.2) integer projection
(`exists_intProjection_of_orthonormal_ZIrr`). -/
theorem Hypothesis.SHC_extension_inj [Finite G] {M : Subgroup G}
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {φ ψ : ClassFunction ↥M ℂ}
    (hφS : φ ∈ inducedFamily M) (hφirr : IsIrreducibleCharacter φ) (hφ1 : φ 1 = (hyp.w1 : ℂ))
    (hψS : ψ ∈ inducedFamily M) (hψirr : IsIrreducibleCharacter ψ) (hψ1 : ψ 1 = (hyp.w1 : ℂ))
    (heq : coh.extension φ = coh.extension ψ) :
    φ = ψ := by
  by_contra hne
  have h0 : ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 0 :=
    coh.inner_extension_eq_zero_of_ne ⟨hφS, hφirr, hφ1⟩ hφirr ⟨hψS, hψirr, hψ1⟩ hψirr hne
  have h1 : ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 1 := by
    rw [← heq]; exact coh.inner_extension_self_eq_one ⟨hφS, hφirr, hφ1⟩ hφirr
  rw [h0] at h1
  exact one_ne_zero h1.symm

open scoped Classical FiniteInduce in
/-- **`{λ^{τ₁} : λ ∈ S(HC)}` as an orthonormal `ZIrr` `Finset`** (α-grid (11.8.2) setup).  The
coherent images of the degree-`w₁` irreducibles of `S(HC)` form an orthonormal family of virtual
characters of `G`, ready for the integer projection `exists_intProjection_of_orthonormal_ZIrr` of
`α_{ij}^τ` in (11.8.2).  Materialized as the image of the `S(HC)` `IrreducibleCharacter` `Finset`
(the same filter used by `SHC_isCoherent`) under `extension`; orthonormality is
`SHC_extension_inner_self`/`SHC_extension_inner_of_ne` + the injectivity `SHC_extension_inj`. -/
theorem Hypothesis.exists_SHC_extension_orthonormal [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) :
    ∃ R : Finset (ClassFunction G ℂ),
      (∀ β ∈ R, β ∈ ZIrr G) ∧
      (∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) ∧
      (∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
        φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R) ∧
      (∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) ∧
      R.card = (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
        (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
          (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)).card := by
  have := hyp.finiteG
  classical
  set s : Finset (IrreducibleCharacter ↥M) :=
    Finset.univ.filter (fun χ => (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      (χ : ClassFunction ↥M ℂ) 1 = (hyp.w1 : ℂ)) with hs
  refine ⟨s.image (fun χ : IrreducibleCharacter ↥M =>
      coh.extension (χ : ClassFunction ↥M ℂ)), ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    rw [Finset.mem_image] at hβ
    obtain ⟨χ, hχs, rfl⟩ := hβ
    rw [hs, Finset.mem_filter] at hχs
    exact coh.extension_mem_ZIrr _
      (Submodule.subset_span ⟨hχs.2.1, χ.2, hχs.2.2⟩)
  · intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨χ, hχs, rfl⟩ := hα
    obtain ⟨χ', hχ's, rfl⟩ := hβ
    rw [hs, Finset.mem_filter] at hχs hχ's
    by_cases hχχ' : χ = χ'
    · subst hχχ'; rw [if_pos rfl]
      exact coh.inner_extension_self_eq_one ⟨hχs.2.1, χ.2, hχs.2.2⟩ χ.2
    · have hne : (χ : ClassFunction ↥M ℂ) ≠ (χ' : ClassFunction ↥M ℂ) :=
        fun h => hχχ' (Subtype.ext h)
      rw [coh.inner_extension_eq_zero_of_ne ⟨hχs.2.1, χ.2, hχs.2.2⟩ χ.2 ⟨hχ's.2.1, χ'.2, hχ's.2.2⟩
          χ'.2 hne,
        if_neg (fun hαβ => hχχ' (Subtype.ext
          (hyp.SHC_extension_inj hG coh hχs.2.1 χ.2 hχs.2.2 hχ's.2.1 χ'.2 hχ's.2.2 hαβ)))]
  · intro φ hφS hφirr hφ1
    rw [Finset.mem_image]
    exact ⟨⟨φ, hφirr⟩, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hφS, hφ1⟩, rfl⟩
  · intro β hβ
    rw [Finset.mem_image] at hβ
    obtain ⟨χ, hχs, rfl⟩ := hβ
    rw [hs, Finset.mem_filter] at hχs
    exact ⟨χ, hχs.2.1, χ.2, hχs.2.2, rfl⟩
  · -- `|R| = |S₁|`: the image is injective (`SHC_extension_inj`)
    refine Finset.card_image_of_injOn ?_
    intro χ hχs χ' hχ's hext
    have h1 := Finset.mem_coe.mp hχs
    have h2 := Finset.mem_coe.mp hχ's
    rw [hs, Finset.mem_filter] at h1 h2
    exact Subtype.ext
      (hyp.SHC_extension_inj hG coh h1.2.1 χ.2 h1.2.2 h2.2.1 χ'.2 h2.2.2 hext)

/-- **Peterfalvi (11.8.2) arithmetic core**: the integer inequality `n·(a² − 2a) ≤ 2` with `2 ≤ n`
forces `a ∈ {0, 1, 2}`.  (If `a ∉ {0, 1, 2}` then `a ≤ −1` or `a ≥ 3`, so `a² − 2a ≥ 3` and
`n·(a² − 2a) ≥ 2·3 = 6 > 2`.)  This is the numeric heart of (11.8.2)'s `a = 0/1/2` conclusion, fed
by
the projection-norm bound `(a − n)² + (|S₁| − 1)a² ≤ n² + 2` once `|S₁| = n` (Peterfalvi
(11.8.1)). -/
theorem charParam_a_mem_of_norm_ineq {a : ℤ} {n : ℕ} (hn : 2 ≤ n)
    (h : (n : ℤ) * (a ^ 2 - 2 * a) ≤ 2) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have hn2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  by_contra hcon
  push Not at hcon
  obtain ⟨ha0, ha1, ha2⟩ := hcon
  have ha : a ≤ -1 ∨ 3 ≤ a := by omega
  have hge : 3 ≤ a ^ 2 - 2 * a := by rcases ha with h | h <;> nlinarith
  nlinarith [hge, hn2]

open scoped Classical FiniteInduce in
/-- **Parseval with orthogonal remainder** for the integer projection of a virtual character onto an
orthonormal `ZIrr` family.  For `φ ∈ ZIrr G` and an orthonormal family `R ⊆ ZIrr G`, the integer
projection `exists_intProjection_of_orthonormal_ZIrr` gives coefficients `c` and remainder `Y ⊥ R`
with `φ = ∑ c_α·α + Y`; then `‖φ‖² = ∑_{α∈R} c_α² + ‖Y‖²` (`inner_self_orthonormalSum_eq_sum_sq`,
the cross terms vanishing by `Y ⊥ R`).  This is the (11.8.2) projection-norm identity feeding
`(a − n)² + (|S₁| − 1)a² ≤ ‖α^τ‖²`. -/
theorem inner_self_eq_sum_sq_add_of_intProjection [Finite G] {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) {R : Finset (ClassFunction G ℂ)} (hZ : ∀ α ∈ R, α ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0) :
    ∃ (c : ClassFunction G ℂ → ℤ) (Y : ClassFunction G ℂ),
      (∀ α ∈ R, ClassFunction.inner φ α = (c α : ℂ)) ∧
      ClassFunction.inner φ φ = (∑ α ∈ R, (c α : ℂ) ^ 2) + ClassFunction.inner Y Y ∧
      (∀ α ∈ R, ClassFunction.inner Y α = 0) ∧
      φ = (∑ α ∈ R, (c α : ℂ) • α) + Y ∧ Y ∈ ZIrr G := by
  obtain ⟨c, Y, hcoeff, hdecomp, hYorth⟩ :=
    OddOrder.RepresentationTheory.ClassFunction.exists_intProjection_of_orthonormal_ZIrr hφ hZ horth
  refine ⟨c, Y, hcoeff, ?_, hYorth, hdecomp, ?_⟩
  · have hXY : ClassFunction.inner (∑ α ∈ R, (c α : ℂ) • α) Y = 0 := by
      rw [inner_sum_left]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [ClassFunction.inner_smul_left]
      have haY : ClassFunction.inner a Y = 0 := by
        rw [inner_conj_symm Y a, hYorth a ha, star_zero]
      rw [haY, mul_zero]
    have hYX : ClassFunction.inner Y (∑ α ∈ R, (c α : ℂ) • α) = 0 := by
      rw [inner_sum_right]
      refine Finset.sum_eq_zero fun a ha => ?_
      rw [OddOrder.RepresentationTheory.inner_smul_right, hYorth a ha, mul_zero]
    conv_lhs => rw [hdecomp]
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right, ClassFunction.inner_add_right,
      inner_self_orthonormalSum_eq_sum_sq horth, hXY, hYX]
    ring
  · have hsumZ : (∑ α ∈ R, (c α : ℂ) • α) ∈ ZIrr G :=
      Submodule.sum_mem _ fun α hα => by
        rw [Int.cast_smul_eq_zsmul]; exact zsmul_mem (hZ α hα) _
    have hYeq : Y = φ - (∑ α ∈ R, (c α : ℂ) • α) := by rw [hdecomp]; abel
    rw [hYeq]; exact Submodule.sub_mem _ hφ hsumZ

open scoped Classical in
/-- **Sum of squares with one distinguished coefficient.**  If `e ∈ R`, `f e = x`, and `f β = y` for
every `β ∈ R` with `β ≠ e`, then `∑_{β∈R} (f β)² = x² + (|R| − 1)·y²`.  Used in (11.8.2) to evaluate
`∑_{λ∈S(HC)} c(λ^{τ₁})² = (a − n)² + (|S₁| − 1)·a²` (the `ζ^{τ₁}` coefficient is `a − n`, every
other
coefficient is `a`). -/
theorem sum_sq_eq_of_split {R : Finset (ClassFunction G ℂ)} {e : ClassFunction G ℂ} (he : e ∈ R)
    {f : ClassFunction G ℂ → ℤ} {x y : ℤ} (hx : f e = x)
    (hy : ∀ β ∈ R, β ≠ e → f β = y) :
    (∑ β ∈ R, (f β : ℂ) ^ 2) = (x : ℂ) ^ 2 + ((R.card : ℂ) - 1) * (y : ℂ) ^ 2 := by
  classical
  rw [← Finset.add_sum_erase R (fun β => (f β : ℂ) ^ 2) he]
  have he2 : ((f e : ℂ)) ^ 2 = (x : ℂ) ^ 2 := by rw [hx]
  have hsum : ∑ β ∈ R.erase e, (f β : ℂ) ^ 2 = ((R.erase e).card : ℂ) * (y : ℂ) ^ 2 := by
    rw [Finset.sum_congr rfl fun β hβ => by
          rw [hy β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ)],
      Finset.sum_const, nsmul_eq_mul]
  have hcard : ((R.erase e).card : ℂ) = (R.card : ℂ) - 1 := by
    have h1 : 1 ≤ R.card := Finset.card_pos.mpr ⟨e, he⟩
    rw [Finset.card_erase_of_mem he, Nat.cast_sub h1, Nat.cast_one]
  rw [he2, hsum, hcard]

open scoped FiniteInduce in
/-- **Integer bound from a Parseval remainder.**  If `(A : ℂ) + ⟨Y, Y⟩ = (B : ℂ)` with `A, B ∈ ℤ`,
then `A ≤ B` — since `⟨Y, Y⟩` is a non-negative real (`inner_self_re_nonneg`).  Turns the (11.8.2)
Parseval equality `∑ c_β² + ‖Y‖² = ‖α^τ‖²` into the inequality `∑ c_β² ≤ ‖α^τ‖²`. -/
theorem int_le_of_add_inner_self_eq [Finite G] {A B : ℤ} {Y : ClassFunction G ℂ}
    (h : (A : ℂ) + ClassFunction.inner Y Y = (B : ℂ)) : A ≤ B := by
  have hnn : (0 : ℝ) ≤ (ClassFunction.inner Y Y).re := inner_self_re_nonneg Y
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.intCast_re, Complex.intCast_re] at hre
  have hle : (A : ℝ) ≤ (B : ℝ) := by linarith
  exact_mod_cast hle

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.2), residual decomposition + norm.**  Projecting `α_{ij}^τ` onto the
orthonormal `S₁^{τ₁} = R` (`exists_intProjection`) gives integer coefficients `c_β = ⟨α_{ij}^τ, β⟩`
and remainder `Y ⊥ R` (this `Y` is Peterfalvi's residual `X`, with `α_{ij}^τ = X − nζ^{τ₁} +
a·∑_{λ∈S₁} λ^{τ₁}`).  The coefficient relation (`muGridAlpha_tau_inner_SHC_extension_sub`, cont.³²)
forces `c(η^{τ₁}) = a` (constant, `η ≠ ζ`) with `a := c(ζ^{τ₁}) + n`, so `⟨α_{ij}^τ, ζ^{τ₁}⟩ =
c(ζ^{τ₁}) = a − n`.  Parseval (`inner_self_eq_sum_sq_add_of_intProjection`) + the sum split
(`sum_sq_eq_of_split`) + `‖α_{ij}^τ‖² = 2 + n²` (`muGridAlpha_tau_inner_self`) give the residual
norm
`‖X‖² = 2 + n² − ((a−n)² + (n−1)a²)`.  With `‖X‖² ≥ 0` (`int_le_of_add_inner_self_eq`) this is
`n(a²−2a) ≤ 2`, whence `a ∈ {0,1,2}` (`charParam_a_mem_of_norm_ineq`); and for `a = 0` or `a = 2`
the norm collapses to `‖X‖² = 2` — the input to Peterfalvi's `X = ω_{ij}^σ − ω_{i0}^σ`.

`R` and `|R| = n` are supplied by the caller: `R` from `exists_SHC_extension_orthonormal`, and
`|R| = n` is the (11.8.1) `|S₁| = n` (gated on the §9↔§10 carrier bridge). -/
theorem Hypothesis.muGridAlpha_tau_residual_norm [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ∃ (a : ℤ) (Y : ClassFunction G ℂ),
      (a = 0 ∨ a = 1 ∨ a = 2) ∧
      (∀ β ∈ R, ClassFunction.inner Y β = 0) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      ClassFunction.inner Y Y
        = (2 : ℂ) + (n : ℂ) ^ 2 - (((a : ℂ) - (n : ℂ)) ^ 2 + ((n : ℂ) - 1) * (a : ℂ) ^ 2) ∧
      ((a = 0 ∨ a = 2) → ClassFunction.inner Y Y = 2) ∧
      Y ∈ ZIrr G ∧
      (∀ v ∈ typePV M hyp.typeP,
        Y v = hyp.tau
          (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v) ∧
      hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
  classical
  have hζR : coh.extension ζ ∈ R := hRmem ζ hζS hζirr hζ1
  have hαZ := hyp.muGridAlpha_tau_mem_ZIrr hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
  obtain ⟨c, Y, hcoeff, hnorm, hYorth, hdecomp, hYZ⟩ :=
    inner_self_eq_sum_sq_add_of_intProjection hαZ hZ horth
  set a : ℤ := c (coh.extension ζ) + (n : ℤ) with hadef
  have hcζ : c (coh.extension ζ) = a - (n : ℤ) := by rw [hadef]; ring
  have hcη : ∀ β ∈ R, β ≠ coh.extension ζ → c β = a := by
    intro β hβR hβne
    obtain ⟨η, hηS, hηirr, hη1, rfl⟩ := hRrev β hβR
    have hηζ : η ≠ ζ := fun h => hβne (by rw [h])
    have hsub := hyp.muGridAlpha_tau_inner_SHC_extension_sub hG coh hodd i hj0 hζS hζirr hζ1
      hηS hηirr hη1 hηζ hdeg hμ0 hnf hδj hdζ h0ζ
    rw [hcoeff _ hζR, hcoeff _ (hRmem η hηS hηirr hη1)] at hsub
    have hcast : ((c (coh.extension η) : ℤ) : ℂ) = ((a : ℤ) : ℂ) := by
      rw [hadef]; push_cast; linear_combination -hsub
    exact_mod_cast hcast
  have hsplit := sum_sq_eq_of_split hζR hcζ hcη
  rw [hRn] at hsplit
  have hnorm2 := hyp.muGridAlpha_tau_inner_self hG hodd i hj0 hζS hζirr hdeg hμ0 hζ1 hnf hδj
    hdζ h0ζ hδpm
  rw [hnorm2, hsplit] at hnorm
  have hnormY : ClassFunction.inner Y Y
      = (2 : ℂ) + (n : ℂ) ^ 2 - (((a : ℂ) - (n : ℂ)) ^ 2 + ((n : ℂ) - 1) * (a : ℂ) ^ 2) := by
    push_cast at hnorm ⊢
    linear_combination -hnorm
  have hbound : a = 0 ∨ a = 1 ∨ a = 2 := by
    have hineq : (a - (n : ℤ)) ^ 2 + ((n : ℤ) - 1) * a ^ 2 ≤ 2 + (n : ℤ) ^ 2 := by
      apply int_le_of_add_inner_self_eq (Y := Y)
      push_cast at hnorm ⊢
      linear_combination -hnorm
    have hfinal : (n : ℤ) * (a ^ 2 - 2 * a) ≤ 2 := by nlinarith [hineq]
    exact charParam_a_mem_of_norm_ineq hn2 hfinal
  have hYV : ∀ v ∈ typePV M hyp.typeP,
      Y v = hyp.tau
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v := by
    intro v hv
    have hsumv : (∑ β ∈ R, (c β : ℂ) • β) v = 0 := by
      rw [ClassFunction.finset_sum_apply]
      refine Finset.sum_eq_zero fun β hβR => ?_
      obtain ⟨φ, hφS, hφirr, hφ1, rfl⟩ := hRrev β hβR
      rw [ClassFunction.smul_apply,
        hyp.SHC_extension_vanishes_on_typePV hG coh hodd hφS hφirr hφ1 hv, mul_zero]
    have hYeq : Y = hyp.tau
        (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        - (∑ β ∈ R, (c β : ℂ) • β) := by rw [hdecomp]; abel
    rw [hYeq, ClassFunction.sub_apply, hsumv, sub_zero]
  have hdecompA : hyp.tau
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
      = Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
    have hkey : (∑ β ∈ R, (c β : ℂ) • β)
        = -((n : ℂ) • coh.extension ζ) + (a : ℂ) • ∑ β ∈ R, β := by
      rw [Finset.smul_sum,
        ← Finset.add_sum_erase R (fun β => (c β : ℂ) • β) hζR,
        ← Finset.add_sum_erase R (fun β => (a : ℂ) • β) hζR, hcζ]
      have herase : ∑ β ∈ R.erase (coh.extension ζ), (c β : ℂ) • β
          = ∑ β ∈ R.erase (coh.extension ζ), (a : ℂ) • β :=
        Finset.sum_congr rfl fun β hβ => by
          rw [hcη β (Finset.mem_of_mem_erase hβ) (Finset.ne_of_mem_erase hβ)]
      rw [herase]; push_cast; module
    rw [hdecomp, hkey]; abel
  refine ⟨a, Y, hbound, hYorth, ?_, hnormY, ?_, hYZ, hYV, hdecompA⟩
  · rw [hcoeff _ hζR, hcζ]; push_cast; ring
  · intro ha02
    rw [hnormY]
    rcases ha02 with h | h <;> rw [h] <;> push_cast <;> ring

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.2), the residual is a `σ`-grid difference** (general `a ∈ {0, 2}` case):
the residual `X = α_{ij}^τ + n·ζ^{τ₁} − a·∑_{λ∈S₁} λ^{τ₁}` (`= Y`, the `S₁^{τ₁}`-orthogonal Parseval
remainder) equals `δ·(ω_{ij}^σ − ω_{i0}^σ)` when `a ∈ {0, 2}` (`‖X‖² = 2`).

Feeds the (11.8.5) `a = 0` argument (`β = a·∑λ^{τ₁}` then (5.3.b)).  From
`muGridAlpha_tau_residual_norm` the residual `Y` satisfies `‖Y‖² = 2` (for `a ∈ {0, 2}`),
`Y ∈ ℤ[Irr G]`, and — crucially — `Y = α_{ij}^τ` on `V` (the `∑λ^{τ₁}` correction vanishes there,
each
`λ ∈ S(HC)` being a non-real degree-`w₁` irreducible, `SHC_extension_vanishes_on_typePV`).  Then
`ψ = Y − δ(ω^σ diff)` vanishes on `V` (with the value-on-`V` leg
`tau_muGridAlpha_apply_eq_on_typePV`,
`α^τ = δ(ω^σ diff)` there), so the norm-`2` Dade-image trichotomy `eq_smul_chiFam_diff_of_vanishOnV`
forces `Y = δ(ω_{ij}^σ − ω_{i0}^σ)`. -/
theorem Hypothesis.SHC_residual_eq_omegaSigma_diff [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) (hn2 : 2 ≤ n)
    {R : Finset (ClassFunction G ℂ)} (hRn : R.card = n)
    (hZ : ∀ β ∈ R, β ∈ ZIrr G)
    (horth : ∀ α ∈ R, ∀ β ∈ R, ClassFunction.inner α β = if α = β then (1 : ℂ) else 0)
    (hRmem : ∀ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M → IsIrreducibleCharacter φ →
      φ 1 = (hyp.w1 : ℂ) → coh.extension φ ∈ R)
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ∃ (a : ℤ) (Y : ClassFunction G ℂ),
      (a = 0 ∨ a = 1 ∨ a = 2) ∧
      ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.extension ζ) = (a : ℂ) - (n : ℂ) ∧
      ((a = 0 ∨ a = 2) → Y = (δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0)) ∧
      hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        = Y - (n : ℂ) • coh.extension ζ + (a : ℂ) • ∑ β ∈ R, β := by
  obtain ⟨a, Y, hbound, hYorth, hinner, hnorm, hnorm2case, hYZ, hYV, hdecompA⟩ :=
    hyp.muGridAlpha_tau_residual_norm hG coh hodd i hj0 hζS hζirr hζ1 hdeg hμ0 hnf hδj hdζ h0ζ hδpm
        hn2
      hRn hZ horth hRmem hRrev
  refine ⟨a, Y, hbound, hinner, ?_, hdecompA⟩
  intro ha02
  have := hyp.finiteG
  classical
  obtain ⟨P, hPinj, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hPne : P j ≠ P 0 := fun h => hj0 (hPinj h)
  have hPj' : tic.chiFam hVeq app (P j) = hyp.alignedOmegaSigmaGrid hG hodd i j := (hP j).symm
  have hP0' : tic.chiFam hVeq app (P 0) = hyp.alignedOmegaSigmaGrid hG hodd i 0 := (hP 0).symm
  have hψV : ∀ v ∈ tic.V,
      (Y - (δ : ℂ) • (tic.chiFam hVeq app (P j) - tic.chiFam hVeq app (P 0))) v = 0 := by
    intro v hv
    rw [hPj', hP0']
    have hleg := hyp.tau_muGridAlpha_apply_eq_on_typePV hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj hv
    rw [ClassFunction.sub_apply, hYV v hv, hleg, sub_self]
  rw [← hPj', ← hP0']
  exact tic.eq_smul_chiFam_diff_of_vanishOnV hVeq app hYZ (hnorm2case ha02) hPne hδpm hψV

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) `G`-side `ω`-grid pairing** `(ω_{ij}^σ − ω_{i0}^σ, ∑_r ω_{r0}^σ) = −1`
(`0 < j`).  By `alignedOmegaSigmaGrid_inner`: `(ω_{ij}^σ, ω_{r0}^σ) = 0` (`j ≠ 0`) and
`(ω_{i0}^σ, ω_{r0}^σ) = [i = r]`, so the sum is `0 − 1 = −1`.  Feeds the
`(α_{ij}^τ, ∑ω_{r0}^σ) = −δ`
step of the (11.8.5) two-way computation. -/
theorem Hypothesis.alignedOmegaSigma_diff_inner_zeroColumnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) :
    ClassFunction.inner
        (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd i 0)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = -1 := by
  classical
  rw [ClassFunction.inner_sub_left, OddOrder.RepresentationTheory.inner_sum_right,
    OddOrder.RepresentationTheory.inner_sum_right]
  have h1 : ∀ r : Fin hyp.w1, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i j)
      (hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 := fun r => by
    rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i r j 0, if_neg]; rintro ⟨_, h⟩; exact hj0 h
  have h2 : ∀ r : Fin hyp.w1, ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i 0)
      (hyp.alignedOmegaSigmaGrid hG hodd r 0) = (if i = r then (1 : ℂ) else 0) := fun r => by
    rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i r 0 0]; simp
  rw [Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_congr rfl (fun r _ => h2 r),
    Finset.sum_const_zero, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  ring

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) `G`-side (5.3.b) sum** `(ζ^{τ₁}, ∑_r ω_{r0}^σ) = 0`: each
`(ζ^{τ₁}, ω_{r0}^σ) = 0` (`SHC_extension_inner_alignedOmegaSigma_eq_zero`), summed over the rows. -/
theorem Hypothesis.SHC_extension_inner_zeroColumnOmegaSigma_sum [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hζne : ζ.conj ≠ ζ) :
    ClassFunction.inner (coh.extension ζ)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 := by
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  refine Finset.sum_eq_zero fun r _ => ?_
  exact hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζS hζirr hζ1 hζne r 0

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) `G`-side (5.3.b) sum over `S₁`** `(∑_{β∈R} β, ∑_r ω_{r0}^σ) = 0`: each
`β = λ^{τ₁}` (`hRrev`) is a degree-`w₁` `S(HC)` coherent image, non-real
(`inducedFamily_degree_w1_conj_ne`),
so `(λ^{τ₁}, ∑_r ω_{r0}^σ) = 0` (`SHC_extension_inner_zeroColumnOmegaSigma_sum`), summed over
`R`. -/
theorem Hypothesis.R_sum_inner_zeroColumnOmegaSigma_sum [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {R : Finset (ClassFunction G ℂ)}
    (hRrev : ∀ β ∈ R, ∃ φ : ClassFunction ↥M ℂ, φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
      φ 1 = (hyp.w1 : ℂ) ∧ β = coh.extension φ) :
    ClassFunction.inner (∑ β ∈ R, β)
        (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0) = 0 := by
  rw [inner_sum_left]
  refine Finset.sum_eq_zero fun β hβR => ?_
  obtain ⟨φ, hφS, hφirr, hφ1, rfl⟩ := hRrev β hβR
  exact hyp.SHC_extension_inner_zeroColumnOmegaSigma_sum hG coh hodd hφS hφirr hφ1
    (hyp.inducedFamily_degree_w1_conj_ne hG hφirr hφ1)

end OddOrder.Peterfalvi.S12


