-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TICyclicSigmaBridge
-- name    : OddOrder_Peterfalvi_S12_TICyclicSigmaBridge
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:04:56.44647+00:00
-- url     : https://prove2.me/theorems/a1f0c305-90f4-46b2-b000-023078f13e9b
-- title:
--   Peterfalvi (2.5)/(3.2)/(3.5): the generic $\sigma$-agreement and transpose bridge
-- statement:
--   Formalizes generic bridge results for `TICyclicHypothesis` setups relating the $\sigma$-isometries and transposes of two TI-cyclic structures (Peterfalvi, *Character Theory for the Odd Order Theorem*, §§2-3, results (2.5), (3.2), (3.5)).
--
--   Main declarations: `ticyclicSupportedOnVCongr` (value restriction); `ticyclic_V_nonempty` (The TI-set `V = W ∖ (W₁ ∪ W₂)` of a (3.1) setup is nonempty); `subgroupOfTransport` (Value-level transport of `subgroupOf`-members along inclusions of both the ambient and the…); `subgroupOfTransportCharEquiv` (Precomposition with the two-level transport is a bijection of character groups).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TICyclicSigmaBridge.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TICyclicSigmaBridge.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaTrichotomy

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

open scoped IsMulCommutative

variable {G : Type*} [Group G]

section GenericBridge

variable [Fintype G]

/-- Two Peterfalvi (2.2) hypotheses on the same `(A, L)` whose `H`-fields are all trivial are
**equal**: `H` is the only data field of `S04.Hypothesis`, every other field being a proof.
This is what makes the Dade hypothesis of a TI-setup canonical — e.g. the `M`-side and
`S`-side `toDadeHypothesis` of a type-P pair coincide once `V` and `W` do. -/
theorem dadeHypothesis_eq_of_forall_H_eq_bot {A : Set G} {L : Subgroup G}
    {hyp hyp' : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (hH : ∀ a, hyp.H a = ⊥) (hH' : ∀ a, hyp'.H a = ⊥) : hyp = hyp' := by
  obtain ⟨s₁, l₁, n₁, H₁, c₁, ce₁, cd₁, hn₁, cc₁⟩ := hyp
  obtain ⟨s₂, l₂, n₂, H₂, c₂, ce₂, cd₂, hn₂, cc₂⟩ := hyp'
  have hHeq : H₁ = H₂ := funext fun a => (hH a).trans (hH' a).symm
  subst hHeq
  rfl

/-- **Peterfalvi (2.5), cross-hypothesis uniqueness** (TI-special case): candidate Dade maps
for two — possibly differently packaged — hypotheses on the same `(A, L)`, both with all
`H(a) = 1`, agree.  Reduces to `S04.IsDadeMap.unique` through
`dadeHypothesis_eq_of_forall_H_eq_bot`. -/
theorem dadeMap_unique_of_forall_H_eq_bot {k : Type*} [CommRing k]
    {A : Set G} {L : Subgroup G}
    {hyp hyp' : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    {τ₁ τ₂ : OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L}
    (h₁ : OddOrder.Peterfalvi.S04.IsDadeMap hyp τ₁)
    (h₂ : OddOrder.Peterfalvi.S04.IsDadeMap hyp' τ₂)
    (hH : ∀ a, hyp.H a = ⊥) (hH' : ∀ a, hyp'.H a = ⊥) : τ₁ = τ₂ := by
  rw [← dadeHypothesis_eq_of_forall_H_eq_bot hH hH'] at h₂
  exact h₁.unique h₂

/-- Transport `CF(W, V)` along equalities `hyp₁.V = hyp₂.V`, `hyp₁.W = hyp₂.W` of the
underlying TI data, by **value restriction** (`ClassFunction.compHom` along
`Subgroup.inclusion hW.ge`) rather than by `Eq.rec` — so evaluating the transported function
is definitional (`ticyclicSupportedOnVCongr_coe_apply` is `rfl`) and no `HEq`/motive issues
ever arise downstream. -/
def ticyclicSupportedOnVCongr {k : Type*} [CommRing k]
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV k hyp₁) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV k hyp₂ :=
  ⟨ClassFunction.compHom (Subgroup.inclusion hW.ge) (α : ClassFunction ↥hyp₁.W k), by
    rw [ClassFunction.mem_supportedSubmodule]
    intro w hw
    rw [ClassFunction.mem_support, ClassFunction.compHom_apply] at hw
    have hmem := ClassFunction.mem_supportedSubmodule.mp α.2
      (ClassFunction.mem_support.mpr hw)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, ← hV]
    simpa using hmem⟩

@[simp] theorem ticyclicSupportedOnVCongr_coe_apply {k : Type*} [CommRing k]
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (α : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV k hyp₁) (w : ↥hyp₂.W) :
    (ticyclicSupportedOnVCongr hyp₁ hyp₂ hV hW α : ClassFunction ↥hyp₂.W k) w
      = (α : ClassFunction ↥hyp₁.W k) ⟨(w : G), hW.ge w.2⟩ :=
  rfl

/-- **Peterfalvi (8.8), swap-invariance of the exceptional set**: `Vdiff = W ∖ (W₁ ∪ W₂)`
only sees the *unordered* pair `{W₁, W₂}`, so two TI-cyclic setups with the same `W` and the
roles of `W₁`/`W₂` exchanged (the (8.8) pair situation, `S ∩ M = W = W₁ × W₂` with swapped
factors) have the same `Vdiff` — just `Set.union_comm`. -/
theorem ticyclic_Vdiff_eq_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1) :
    hyp₁.Vdiff = hyp₂.Vdiff := by
  simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.Vdiff]
  rw [hW, hW12, hW21, Set.union_comm (hyp₂.W2 : Set G) (hyp₂.W1 : Set G)]

/-- **Peterfalvi (8.8), the pair shares its TI-set**: two TI-cyclic setups in the `Vdiff`
shape (`hVeq₁`, `hVeq₂`) with the same `W` and swapped `W₁`/`W₂` have equal `V`.  This is
the `hV` input of the σ-agreement bridge (`ticyclic_toDadeMap_eq_of_V_eq`,
`ticyclic_sigma_eq_of_V_eq`) in the (10.7) grid-transpose situation. -/
theorem ticyclic_V_eq_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1) :
    hyp₁.V = hyp₂.V :=
  hVeq₁.trans ((ticyclic_Vdiff_eq_of_swap hyp₁ hyp₂ hW hW12 hW21).trans hVeq₂.symm)

variable [Invertible (Nat.card G : ℂ)]

/-- Integrality of the inner product on `ZIrr` (both slots): `⟨φ, η⟩ ∈ ℤ` for virtual
characters `φ, η`.  Right-slot span induction over `Irr(G)` on top of the single-irreducible
case `mem_ZIrr_inner_int`. -/
theorem inner_intCast_of_mem_ZIrr {φ η : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (hη : η ∈ ZIrr G) :
    ∃ m : ℤ, ClassFunction.inner φ η = (m : ℂ) := by
  rw [ZIrr_eq_span] at hη
  induction hη using Submodule.span_induction with
  | mem x hx => exact mem_ZIrr_inner_int (⟨x, hx⟩ : IrreducibleCharacter G) hφ
  | zero =>
      refine ⟨0, ?_⟩
      rw [show (0 : ClassFunction G ℂ) = (0 : ℂ) • 0 from (zero_smul ℂ _).symm,
        OddOrder.RepresentationTheory.inner_smul_right]
      simp
  | add x y _ _ ihx ihy =>
      obtain ⟨mx, hmx⟩ := ihx
      obtain ⟨my, hmy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ClassFunction.inner_add_right, hmx, hmy]
      push_cast; ring
  | smul a x _ ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨a * m, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ a x, OddOrder.RepresentationTheory.inner_smul_right,
        hm, star_intCast]
      push_cast; ring

omit [Invertible (Nat.card G : ℂ)] in
/-- The TI-set `V = W ∖ (W₁ ∪ W₂)` of a (3.1) setup is nonempty: both cyclic factors are
nontrivial, so the internal product `W = W₁ × W₂` has an element with both components
nontrivial (`supportInVdiffEquiv`). -/
theorem ticyclic_V_nonempty (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hVeq : hyp.V = hyp.Vdiff) : hyp.V.Nonempty := by
  have hne1 : hyp.W1.subgroupOf hyp.W ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hyp.W1_nontrivial (hd.eq_bot_of_le hyp.W1_le_W)
  have hne2 : hyp.W2.subgroupOf hyp.W ≠ ⊥ := by
    rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hyp.W2_nontrivial (hd.eq_bot_of_le hyp.W2_le_W)
  have := (Subgroup.nontrivial_iff_ne_bot _).mpr hne1
  have := (Subgroup.nontrivial_iff_ne_bot _).mpr hne2
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(hyp.W1.subgroupOf hyp.W))
  obtain ⟨b, hb⟩ := exists_ne (1 : ↥(hyp.W2.subgroupOf hyp.W))
  refine ⟨(((hyp.supportInVdiffEquiv.symm (⟨a, ha⟩, ⟨b, hb⟩)).1 : ↥hyp.W) : G), ?_⟩
  rw [hVeq]
  exact OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp
    (hyp.supportInVdiffEquiv.symm (⟨a, ha⟩, ⟨b, hb⟩)).2

/-- **The (3.5)-determination of the σ-grid** (Coq `eq_in_cycTIiso`, `PFsection3.v:1750`):
a norm-one virtual character of `G` that agrees on `V` with the linear character
`ω = ω(ξ)` of `W` **is** `ω^σ`.  This is the uniqueness underlying the per-index
identification of the two σ-grids of an (8.8) pair (Coq `cycTIisoC`): the grid vectors are
pinned by their `V`-restrictions alone.

Proof (mirroring Coq): let `η = ω^σ` and `ψ = η − φ`; `ψ` vanishes on `V` (both agree with
`ω` there — (3.2.c) `sigma_apply_irreducibleCharacter_of_mem_V` for `η`).  The integer
`c = ⟨φ, η⟩` satisfies `‖η ∓ φ‖² = 2 ∓ 2c ≥ 0`, so `c ∈ {−1, 0, 1}`:
`c = 1` forces `ψ = 0` (positive definiteness); `c = 0` gives `‖ψ‖² = 2`, so all
σ-coefficients of the `V`-vanishing `ψ` vanish (`sigmaCoeff_eq_zero_of_vanishOnV`, the
(3.7)/(3.8) counting) — contradicting `⟨ψ, η⟩ = 1`; `c = −1` forces `φ = −η`, making
`ω` vanish on the nonempty `V` — impossible for a unit-valued linear character. -/
theorem ticyclic_eq_sigma_omega_of_eqOn_V
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp)
    (ξ : hyp.W →* ℂˣ) {φ : ClassFunction G ℂ}
    (hφZ : φ ∈ ZIrr G) (hφ1 : ClassFunction.inner φ φ = 1)
    (hφV : ∀ (v : G) (hv : v ∈ hyp.V),
      φ v = (hyp.omega ξ : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩) :
    φ = hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) := by
  classical
  set η := hyp.sigma hVeq app (hyp.omega ξ : ClassFunction hyp.W ℂ) with hηdef
  -- `η` is the (3.5) family member at the index of `ξ`: `ZIrr`, norm one
  have hηchi : η = hyp.chiFam hVeq app (hyp.omegaProdEquiv.symm ξ) :=
    hyp.sigma_omega hVeq app ξ
  have hηZ : η ∈ ZIrr G := by
    rw [hηchi]; exact (hyp.chiFam_spec hVeq app).2.1 _
  have hη1 : ClassFunction.inner η η = 1 := by
    rw [hηchi, (hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  -- `η` agrees with `ω` on `V` ((3.2.c)), so `ψ = η − φ` vanishes on `V`
  have hηV : ∀ (v : G) (hv : v ∈ hyp.V),
      η v = (hyp.omega ξ : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ := fun v hv =>
    hyp.sigma_apply_irreducibleCharacter_of_mem_V hVeq app (hyp.omega ξ) hv
  have hψV : ∀ v ∈ hyp.V, (η - φ) v = 0 := fun v hv => by
    rw [ClassFunction.sub_apply, hηV v hv, hφV v hv, sub_self]
  -- the integer inner product `c = ⟨φ, η⟩`
  obtain ⟨c, hc⟩ := inner_intCast_of_mem_ZIrr hφZ hηZ
  have hcstar : ClassFunction.inner η φ = (c : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc, star_intCast]
  -- `‖η − φ‖² = 2 − 2c` and `‖φ + η‖² = 2 + 2c`
  have hsub : ClassFunction.inner (η - φ) (η - φ) = ((2 - 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hη1, hφ1, hc, hcstar]
    push_cast; ring
  have hadd : ClassFunction.inner (φ + η) (φ + η) = ((2 + 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hη1, hφ1, hc, hcstar]
    push_cast; ring
  -- positivity bounds: `−1 ≤ c ≤ 1`
  have hle : c ≤ 1 := by
    have h0 := inner_self_re_nonneg (η - φ)
    rw [hsub, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 - 2 * c := by exact_mod_cast h0
    omega
  have hge : -1 ≤ c := by
    have h0 := inner_self_re_nonneg (φ + η)
    rw [hadd, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 + 2 * c := by exact_mod_cast h0
    omega
  interval_cases c
  · -- `c = −1`: `φ = −η`, so `ω` vanishes on the nonempty `V` — impossible
    exfalso
    have hzero : φ + η = 0 := by
      refine eq_zero_of_inner_self_re_eq_zero ?_
      rw [hadd]
      norm_num
    obtain ⟨v, hv⟩ := ticyclic_V_nonempty hyp hVeq
    have hφv : φ v = -(η v) := by
      have h := congrArg (fun f : ClassFunction G ℂ => f v) hzero
      simp only [ClassFunction.add_apply, ClassFunction.zero_apply] at h
      exact eq_neg_of_add_eq_zero_left h
    have homega : (hyp.omega ξ : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ = 0 := by
      have h1 := hφV v hv
      have h2 := hηV v hv
      rw [hφv, h2] at h1
      -- `−ω(v) = ω(v)` forces `ω(v) = 0`
      linear_combination -h1 / 2
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply] at homega
    exact Units.ne_zero _ homega
  · -- `c = 0`: `‖ψ‖² = 2` and `ψ|_V = 0`, so all σ-coefficients vanish — but `⟨ψ, η⟩ = 1`
    exfalso
    have hψZ : η - φ ∈ ZIrr G := Submodule.sub_mem _ hηZ hφZ
    have hψ2 : ClassFunction.inner (η - φ) (η - φ) = 2 := by rw [hsub]; norm_num
    have hall := hyp.sigmaCoeff_eq_zero_of_vanishOnV hVeq app hψZ hψ2 hψV
    have hcoeff : hyp.sigmaCoeff hVeq app (η - φ) (hyp.omegaProdEquiv.symm ξ)
        = ClassFunction.inner (η - φ) (hyp.chiFam hVeq app (hyp.omegaProdEquiv.symm ξ)) := rfl
    have h1 : ClassFunction.inner (η - φ) η = 0 := by
      have h := hall (hyp.omegaProdEquiv.symm ξ)
      rw [hcoeff, ← hηchi] at h
      exact h
    rw [ClassFunction.inner_sub_left, hη1, hc] at h1
    norm_num at h1
  · -- `c = 1`: `‖ψ‖² = 0`, so `φ = η`
    have hzero : η - φ = 0 := by
      refine eq_zero_of_inner_self_re_eq_zero ?_
      rw [hsub]
      norm_num
    exact (sub_eq_zero.mp hzero).symm

/-- **The per-index σ-grid identification** (Coq `cycTIisoC`, `PFsection3.v:1849`): two
TI-cyclic setups sharing the TI-set `V` and the ambient `W` have the *same* σ-image on each
grid character — `σ₁(ω(ξ)) = σ₂(ω(ξ'))`, where `ξ'` is `ξ` read along the `W`-identification
(value restriction along `Subgroup.inclusion`, no cast).

The grid characters are not `V`-supported, so this does **not** follow from the Dade-map
agreement (`ticyclic_sigma_eq_of_V_eq`); it is the (3.5)-determination
(`ticyclic_eq_sigma_omega_of_eqOn_V`) instead: `σ₁(ω(ξ))` is a norm-one virtual character
(σ is an isometry into `ZIrr`) agreeing with `ω(ξ')` on the shared `V` ((3.2.c) on the
`hyp₁` side — `ξ` and `ξ'` take the same values), so it *is* `σ₂(ω(ξ'))`. -/
theorem ticyclic_sigma_omega_eq_of_V_eq
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (ξ : hyp₁.W →* ℂˣ) :
    hyp₁.sigma hVeq₁ app₁ (hyp₁.omega ξ : ClassFunction hyp₁.W ℂ)
      = hyp₂.sigma hVeq₂ app₂
          (hyp₂.omega (ξ.comp (Subgroup.inclusion hW.ge)) : ClassFunction hyp₂.W ℂ) := by
  refine ticyclic_eq_sigma_omega_of_eqOn_V hyp₂ hVeq₂ app₂
    (ξ.comp (Subgroup.inclusion hW.ge))
    (hyp₁.sigma_mem_ZIrr hVeq₁ app₁
      (IsIrreducibleCharacter.mem_ZIrr (hyp₁.omega ξ).2)) ?_ ?_
  · rw [hyp₁.sigma_inner hVeq₁ app₁, irreducibleCharacter_inner_eq_ite, if_pos rfl]
  · intro v hv₂
    have hv₁ : v ∈ hyp₁.V := hV ▸ hv₂
    rw [hyp₁.sigma_apply_irreducibleCharacter_of_mem_V hVeq₁ app₁ (hyp₁.omega ξ) hv₁,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
      OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply]
    rfl

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Value-level transport of `subgroupOf`-members along inclusions of both the ambient and
the subgroup: `⟨⟨v, _⟩, _⟩ ↦ ⟨⟨v, _⟩, _⟩` (membership proofs re-derived, no `Eq.rec`).
Upstream-hoist candidate (`OddOrder/Mathlib/Subgroup.lean`). -/
def subgroupOfTransport {W W' H H' : Subgroup G} (hW : W' ≤ W) (hH : H' ≤ H) :
    ↥(H'.subgroupOf W') →* ↥(H.subgroupOf W) :=
  MonoidHom.codRestrict ((Subgroup.inclusion hW).comp (H'.subgroupOf W').subtype)
    (H.subgroupOf W) fun x => by
      rw [Subgroup.mem_subgroupOf, MonoidHom.comp_apply, Subgroup.coe_inclusion]
      exact hH (Subgroup.mem_subgroupOf.mp x.2)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
@[simp] theorem subgroupOfTransport_coe {W W' H H' : Subgroup G} (hW : W' ≤ W) (hH : H' ≤ H)
    (x : ↥(H'.subgroupOf W')) :
    ((subgroupOfTransport hW hH x : ↥W) : G) = ((x : ↥W') : G) := rfl

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Precomposition with the two-level transport is a bijection of character groups: the
transports in the two directions compose to the identity by proof irrelevance (the
underlying element never moves). -/
def subgroupOfTransportCharEquiv {W W' H H' : Subgroup G}
    (hW : W' ≤ W) (hW' : W ≤ W') (hH : H' ≤ H) (hH' : H ≤ H') :
    (↥(H.subgroupOf W) →* ℂˣ) ≃ (↥(H'.subgroupOf W') →* ℂˣ) where
  toFun χ := χ.comp (subgroupOfTransport hW hH)
  invFun χ := χ.comp (subgroupOfTransport hW' hH')
  left_inv _ := MonoidHom.ext fun _ => rfl
  right_inv _ := MonoidHom.ext fun _ => rfl

omit [Invertible (Nat.card G : ℂ)] in
/-- **The `W = W₁ × W₂` decomposition transposes along a role swap**: reading a
`hyp₂.W`-element in `hyp₁` (same `W`, factors swapped), its `hyp₁`-`W₁`-component is its
`hyp₂`-`W₂`-component and vice versa — the internal-product decomposition is unique, and
the two factorizations differ only by the (abelian) reordering. -/
theorem ticyclic_wFstSnd_inclusion_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1)
    (w : ↥hyp₂.W) :
    hyp₁.wFst (Subgroup.inclusion hW.ge w)
        = subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w)
      ∧ hyp₁.wSnd (Subgroup.inclusion hW.ge w)
        = subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w) := by
  have hcomm : hyp₂.wProj2 w * hyp₂.wProj1 w = w := by
    have := hyp₂.isMulCommutative_W
    rw [mul_comm]
    exact hyp₂.wProj1_mul_wProj2 w
  have hsymm : hyp₁.wProdEquiv.symm (Subgroup.inclusion hW.ge w)
      = (subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w),
         subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w)) := by
    apply hyp₁.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp₁.wProdEquiv_apply]
    apply Subtype.ext
    calc ((Subgroup.inclusion hW.ge w : ↥hyp₁.W) : G)
        = ((w : ↥hyp₂.W) : G) := by rw [Subgroup.coe_inclusion]
      _ = ((hyp₂.wProj2 w * hyp₂.wProj1 w : ↥hyp₂.W) : G) := by rw [hcomm]
      _ = ((subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w) : ↥hyp₁.W) : G)
            * ((subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w) : ↥hyp₁.W) : G) := by
          rw [Subgroup.coe_mul, subgroupOfTransport_coe, subgroupOfTransport_coe]
          rfl
      _ = (((subgroupOfTransport hW.ge hW12.ge (hyp₂.wSnd w) : ↥hyp₁.W)
            * (subgroupOfTransport hW.ge hW21.ge (hyp₂.wFst w) : ↥hyp₁.W) : ↥hyp₁.W) : G) := by
          rw [Subgroup.coe_mul]
  exact ⟨by rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.wFst_apply, hsymm],
    by rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.wSnd_apply, hsymm]⟩

omit [Invertible (Nat.card G : ℂ)] in
/-- **The grid characters transpose along a role swap** (the index translation of the
(8.8) grid transpose): reading the `hyp₁`-grid character `ω_{(p, kcol)}` on `hyp₂.W`
(same `W`), it is the `hyp₂`-grid character at the transported *swapped* pair —
the `W₁`-factor `p` becomes the `W₂`-factor and the `W₂`-factor `kcol` the `W₁`-factor. -/
theorem ticyclic_omegaProdChar_comp_inclusion_of_swap
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    (hW : hyp₁.W = hyp₂.W) (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1)
    (p : (hyp₁.W1.subgroupOf hyp₁.W) →* ℂˣ) (kcol : (hyp₁.W2.subgroupOf hyp₁.W) →* ℂˣ) :
    (hyp₁.omegaProdChar p kcol).comp (Subgroup.inclusion hW.ge)
      = hyp₂.omegaProdChar (kcol.comp (subgroupOfTransport hW.ge hW21.ge))
          (p.comp (subgroupOfTransport hW.ge hW12.ge)) := by
  ext w
  obtain ⟨h1, h2⟩ := ticyclic_wFstSnd_inclusion_of_swap hyp₁ hyp₂ hW hW12 hW21 w
  simp only [MonoidHom.comp_apply, OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar,
    MonoidHom.mul_apply]
  rw [h1, h2, mul_comm]

/-- **The grid vectors transpose per index** (Coq `cycTIisoC` in `chiFam` form; the
single-index core of `ticyclic_chiFam_columnSum_transpose`): for two TI-cyclic setups
sharing `V` and `W` with the `W₁`/`W₂` roles swapped, each `hyp₁`-grid vector **is** the
`hyp₂`-grid vector at the transported *swapped* index.  The vector at `P = (p, kcol)` is
`σ₁(ω(ω_{(p, kcol)}))`; the (3.5)-determination transposes the σ's
(`ticyclic_sigma_omega_eq_of_V_eq`), and the index translation is
`ticyclic_omegaProdChar_comp_inclusion_of_swap`. -/
theorem ticyclic_chiFam_transpose
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (P : ((hyp₁.W1.subgroupOf hyp₁.W) →* ℂˣ) × ((hyp₁.W2.subgroupOf hyp₁.W) →* ℂˣ)) :
    hyp₁.chiFam hVeq₁ app₁ P
      = hyp₂.chiFam hVeq₂ app₂ (P.2.comp (subgroupOfTransport hW.ge hW21.ge),
          P.1.comp (subgroupOfTransport hW.ge hW12.ge)) := by
  obtain ⟨p, kcol⟩ := P
  have h1 : hyp₁.chiFam hVeq₁ app₁ (p, kcol)
      = hyp₁.sigma hVeq₁ app₁
          (hyp₁.omega (hyp₁.omegaProdChar p kcol) : ClassFunction hyp₁.W ℂ) := by
    rw [hyp₁.sigma_omega hVeq₁ app₁, hyp₁.omegaProdEquiv_symm_omegaProdChar]
  have h2 := ticyclic_sigma_omega_eq_of_V_eq hyp₁ hyp₂ hVeq₁ hVeq₂ hV hW app₁ app₂
    (hyp₁.omegaProdChar p kcol)
  have h3 := ticyclic_omegaProdChar_comp_inclusion_of_swap hyp₁ hyp₂ hW hW12 hW21 p kcol
  have h4 : hyp₂.sigma hVeq₂ app₂
      (hyp₂.omega (hyp₂.omegaProdChar (kcol.comp (subgroupOfTransport hW.ge hW21.ge))
          (p.comp (subgroupOfTransport hW.ge hW12.ge))) : ClassFunction hyp₂.W ℂ)
      = hyp₂.chiFam hVeq₂ app₂ (kcol.comp (subgroupOfTransport hW.ge hW21.ge),
          p.comp (subgroupOfTransport hW.ge hW12.ge)) := by
    rw [hyp₂.sigma_omega hVeq₂ app₂, hyp₂.omegaProdEquiv_symm_omegaProdChar]
  rw [h1, h2, h3, h4]

open scoped Classical in
/-- **The (5.8) column sum is a row sum of the transposed grid** (issue 9079 item 4, the
generic core of the `S`-grid = `M`-grid transpose): for two TI-cyclic setups sharing `V`
and `W` with the `W₁`/`W₂` roles swapped, the full `hyp₁`-grid column at `kcol` equals the
full `hyp₂`-grid row at the transported index `kcol'`.  Every grid vector transposes by the
(3.5)-determination (`ticyclic_sigma_omega_eq_of_V_eq` at the index translation
`ticyclic_omegaProdChar_comp_inclusion_of_swap`), and the summation reindexes along the
character-group bijection `p ↦ p ∘ transport`.

This is what turns the `S`-side (5.8) column pin (`typeII_nu_tau2_dichotomy`) into the
`M`-side row-sum form `ν^{τ₂} = ±∑_j ω_{r'j}^σ` that the (10.7) cross-isometry package
(`TypeIICrossIsometryData.nu_tau2_eq`) consumes. -/
theorem ticyclic_chiFam_columnSum_transpose
    (hyp₁ hyp₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis G)
    [Fintype hyp₁.W] [Invertible (Nat.card hyp₁.W : ℂ)]
    [Fintype hyp₂.W] [Invertible (Nat.card hyp₂.W : ℂ)]
    [Fintype ((hyp₁.W1.subgroupOf hyp₁.W) →* ℂˣ)]
    [Fintype ((hyp₂.W2.subgroupOf hyp₂.W) →* ℂˣ)]
    (hVeq₁ : hyp₁.V = hyp₁.Vdiff) (hVeq₂ : hyp₂.V = hyp₂.Vdiff)
    (hV : hyp₁.V = hyp₂.V) (hW : hyp₁.W = hyp₂.W)
    (hW12 : hyp₁.W1 = hyp₂.W2) (hW21 : hyp₁.W2 = hyp₂.W1)
    (app₁ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₁)
    (app₂ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (G := G) hyp₂)
    (kcol : (hyp₁.W2.subgroupOf hyp₁.W) →* ℂˣ) :
    ∑ p : (hyp₁.W1.subgroupOf hyp₁.W) →* ℂˣ, hyp₁.chiFam hVeq₁ app₁ (p, kcol)
      = ∑ q : (hyp₂.W2.subgroupOf hyp₂.W) →* ℂˣ,
          hyp₂.chiFam hVeq₂ app₂ (kcol.comp (subgroupOfTransport hW.ge hW21.ge), q) := by
  refine Fintype.sum_equiv
    (subgroupOfTransportCharEquiv hW.ge hW.le hW12.ge hW12.le) _ _ fun p => ?_
  -- the `hyp₁`-grid vector at `(p, kcol)` is `σ₁(ω(ξ))` at `ξ = ω_{(p, kcol)}`
  have h1 : hyp₁.chiFam hVeq₁ app₁ (p, kcol)
      = hyp₁.sigma hVeq₁ app₁
          (hyp₁.omega (hyp₁.omegaProdChar p kcol) : ClassFunction hyp₁.W ℂ) := by
    rw [hyp₁.sigma_omega hVeq₁ app₁, hyp₁.omegaProdEquiv_symm_omegaProdChar]
  -- transpose per index, then read the transported character as a `hyp₂`-grid pair
  have h2 := ticyclic_sigma_omega_eq_of_V_eq hyp₁ hyp₂ hVeq₁ hVeq₂ hV hW app₁ app₂
    (hyp₁.omegaProdChar p kcol)
  have h3 := ticyclic_omegaProdChar_comp_inclusion_of_swap hyp₁ hyp₂ hW hW12 hW21 p kcol
  have h4 : hyp₂.sigma hVeq₂ app₂
      (hyp₂.omega (hyp₂.omegaProdChar (kcol.comp (subgroupOfTransport hW.ge hW21.ge))
          (p.comp (subgroupOfTransport hW.ge hW12.ge))) : ClassFunction hyp₂.W ℂ)
      = hyp₂.chiFam hVeq₂ app₂ (kcol.comp (subgroupOfTransport hW.ge hW21.ge),
          p.comp (subgroupOfTransport hW.ge hW12.ge)) := by
    rw [hyp₂.sigma_omega hVeq₂ app₂, hyp₂.omegaProdEquiv_symm_omegaProdChar]
  rw [h1, h2, h3, h4]
  rfl

end GenericBridge

end OddOrder.Peterfalvi.S12


