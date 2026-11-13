-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
-- name    : OddOrder_Peterfalvi_S15_SAndTGrid
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:19:34.617194+00:00
-- url     : https://prove2.me/theorems/3f2de946-75e0-46f5-9813-2193a9635fc0
-- title:
--   Peterfalvi (13.19): type I orthogonality, producer and grid-facts layer
-- statement:
--   Formalizes the producer and grid-facts layer for the type I orthogonality of Peterfalvi (13.19), with the data structure `TypeIOrthogonalityGridData`.
--
--   Main declarations: `OddIntegerInner` (The parity conclusion in Peterfalvi (13.19.c2)); `TypeIOrthogonalityGridData` (Faithful §13 grid/Dade producer for Peterfalvi (13.19)); `typeIBetaL` ((13.19) `β_L^τ`); `betaTGridChar` (T-side (14.3.b) bridge character).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTGrid.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The parity conclusion in Peterfalvi (13.19.c2): the character inner
product is an odd integer, recorded inside `ℂ`. -/
def OddIntegerInner (χ ψ : ClassFunction G ℂ) : Prop :=
  ∃ n : ℤ, Odd n ∧
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)], ClassFunction.inner χ ψ = (n : ℂ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Faithful §13 grid/Dade producer for Peterfalvi (13.19).**

Given a type-I maximal subgroup `L` with its (12.1) `S14.Hypothesis` `typeISetup`, this bundles the
genuinely grid-dependent data and facts of (13.19) against a concrete kernel index `e`, family
`Lset` and generator `phi`:

* the Dade images `β_L`, `β_S`, disjoint-supported (13.18.a-style);
* `phi ∈ Lset` of degree `e = |L : H|`;
* **(13.19.a)** `L^{τ₁} ⊥ {η_ij}` and `β_L ⊥ {η_ij}` (grid orthogonality, the `Ltau_orthogonal_eta`
  / `betaL_eta_independent` content), bottoming out at the (3.9) `τ`-isometry (σ-pinned);
* **(13.19.c)** the S- and T-side dichotomies `caseC1 ∨ caseC2` where `caseC1` is the rational
  degree bound `(|H|−1)/e ≤ (u−1)/q` and `caseC2` is the genuine `η`-axis odd-integer parity
  `∀ j ≠ 0, ⟨β_L, η_0j⟩ ∈ 2ℤ+1` (dual: `(v−1)/p`, `η_i0`).

Everything grid-dependent is isolated here; the assembling theorem
`typeI_orthogonality_dichotomy` supplies the honest §14 bundle `dataL` (whose
`typeISetup = dataL.typeIHyp` is the (12.1) Dade setup and whose `τ₁ = dataL.coh.extension`
is the (12.6) coherent extension), and reads the dichotomy implication fields off as
identities (no over-claim).  Single-character images use `τ₁` (the raw `tau` is arbitrary
off the supported subspace); the `A(L)`-supported difference `β_L` uses `tau` directly. -/
structure TypeIOrthogonalityGridData [Finite G] (hyp : Hypothesis (G := G)) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L) where
  e : ℕ
  e_eq_index : ((maxNilpotentNormalHall L).subgroupOf L).index = e
  Lset : Set (ClassFunction ↥L ℂ)
  phi : ClassFunction ↥L ℂ
  phi_mem : phi ∈ Lset
  phi_degree_eq_e : phi 1 = (e : ℂ)
  betaL : ClassFunction G ℂ
  betaS : ClassFunction G ℂ
  /-- The T-side companion `β_T^τ` (the S↔T-swapped `β_S^τ`), pairing with `φ^{τ₁}` in the dual
  (13.19.c1) parity. -/
  betaT : ClassFunction G ℂ
  disjoint_support : Disjoint betaL.support betaS.support
  /-- **(13.19)**: `β_L` is the Dade image `β_L^τ = (Ind_H^L 1_H − φ)^{τ₁}` (the extension
  `τ₁` agrees with `τ = dataL.typeIHyp.tau` on the `A(L)`-supported `Ind_H^L 1_H − φ`). -/
  betaL_eq :
    ∀ [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
      [Invertible (Nat.card ↥((dataL.typeIHyp.H).subgroupOf L) : ℂ)],
      betaL = dataL.typeIHyp.tau
        (ClassFunction.induce ((dataL.typeIHyp.H).subgroupOf L)
          (trivialClassFunction ↥((dataL.typeIHyp.H).subgroupOf L)) - phi)
  Ltau_orthogonal_eta :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (dataL.coh.extension phi) (hyp.eta i j) = 0
  /-- **(13.19.c)**, first clause: `(β_L^τ, η_{0j})` is independent of `j` for `1 ≤ j < p`. -/
  betaL_eta0_row_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (j j' : Fin hyp.p), (j : ℕ) ≠ 0 → (j' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)
          = ClassFunction.inner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j')
  /-- **(13.19.c)**, first clause after the S↔T swap: `(β_L^τ, η_{i0})` is independent of `i`
  for `1 ≤ i < q`. -/
  betaL_eta0_col_constant :
    ∀ [Fintype G] [Invertible (Nat.card G : ℂ)],
      ∀ (i i' : Fin hyp.q), (i : ℕ) ≠ 0 → (i' : ℕ) ≠ 0 →
        ClassFunction.inner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)
          = ClassFunction.inner betaL (hyp.eta i' ⟨0, hyp.p_prime.pos⟩)
  /-- **(13.19.c)** S-side dichotomy, faithful form: **(c1)** `(β_S^τ, φ^{τ₁}) ≡ 1 (mod 2)` and
  the degree bound `(|H|−1)/e ≤ (u−1)/q`, or **(c2)** the `η_{0j}` odd-parity and `p ≤ e`. -/
  caseC :
    (OddIntegerInner betaS (dataL.coh.extension phi) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.u - 1 : ℕ) : ℚ) / (hyp.q : ℚ))) ∨
      ((∀ j : Fin hyp.p, (j : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta ⟨0, hyp.q_prime.pos⟩ j)) ∧ hyp.p ≤ e)
  /-- **(13.19.c)** T-side (S↔T swapped) dichotomy, faithful form: **(c1)**
  `(β_T^τ, φ^{τ₁}) ≡ 1 (mod 2)` and `(|H|−1)/e ≤ (v−1)/p`, or **(c2)** the `η_{i0}` odd-parity
  and `q ≤ e`. -/
  caseC_dual :
    (OddIntegerInner betaT (dataL.coh.extension phi) ∧
      (((Nat.card ↥dataL.typeIHyp.H - 1 : ℕ) : ℚ) / (e : ℚ) ≤
        ((hyp.v - 1 : ℕ) : ℚ) / (hyp.p : ℚ))) ∨
      ((∀ i : Fin hyp.q, (i : ℕ) ≠ 0 →
        OddIntegerInner betaL (hyp.eta i ⟨0, hyp.p_prime.pos⟩)) ∧ hyp.q ≤ e)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(13.19) `β_L^τ`**: the Dade image `τ₁(Ind_H^L 1_H − φ)` of the `L`-side bridge character,
for a chosen degree-`e` member `φ ∈ 𝓛` (`τ₁ = typeISetup.tau` agrees with `τ` on the
`A(L)`-supported difference). -/
noncomputable def typeIBetaL [Finite G] {L : Subgroup G}
    (typeISetup : OddOrder.Peterfalvi.S14.Hypothesis L) (φ : ClassFunction ↥L ℂ) :
    ClassFunction G ℂ :=
  typeISetup.tau (ClassFunction.induce ((typeISetup.H).subgroupOf L)
    (trivialClassFunction ↥((typeISetup.H).subgroupOf L)) - φ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **T-side (14.3.b) bridge character** `β_T = Ind_{QW₂}^T 1_{QW₂} − ν_{10} ∈ CF(T)` — the
S↔T mirror of `betaGrid` (`β_S = Ind_{PW₁}^S 1 − μ_{01}`), with the grid entry `ν_{10}` in
place of `μ_{01}`. -/
noncomputable def betaTGridChar [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction ↥hyp.T ℂ :=
  ClassFunction.induce ((hyp.Q ⊔ hyp.W2).subgroupOf hyp.T)
      (trivialClassFunction ↥((hyp.Q ⊔ hyp.W2).subgroupOf hyp.T))
    - hyp.nu ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **T-side (13.18)-dual Dade image** `τ_T(β_T)` — the S↔T-swapped `tauSbetaGrid`, pairing
with `φ^{τ₁}` in the dual (13.19.c1) parity.  Built from the honest `T`-instance `'A0(T)` Dade
(`hyp.dadeHypT0`), which requires `IsTypeP2 T` — a **(14.9) conclusion** — and a reconciled
`T`-side `TypePData` (`reconciled_typePData_T`), both taken as parameters. -/
noncomputable def tauTbetaGrid [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) : ClassFunction G ℂ :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
    ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
    (betaTGridChar hyp)

end OddOrder.Peterfalvi.S15


