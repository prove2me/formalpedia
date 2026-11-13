-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:23:16.307775+00:00
-- url     : https://prove2.me/theorems/3910848b-5849-4c89-be0b-bf57c9985aee
-- title:
--   Peterfalvi (14.10)–(14.11): the $M$-carrier and norm-cascade groundwork
-- statement:
--   Formalizes the carrier `MHypothesis` of Peterfalvi (14.10) with the numeric layer of (14.11.1)–(14.11.3): the norm-cascade arithmetic, size bounds and sign parity.
--
--   Main declarations: `MHypothesis` (Peterfalvi (14.10)); `typeIHyp` (The type-I Dade setup retained inside the complete coherent bundle); `h78` (The canonical §7.8 datum derived from the retained coherent bundle); `Mset` (Peterfalvi's coherent source family `𝓜`).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (14.10)**: the type-I maximal subgroup `M` containing
`N_G(V)`, its Fitting kernel `K`, the Dade extension, and `beta_M`. -/
structure MHypothesis (hyp : Hypothesis (G := G)) where
  [finiteG : Finite G]
  M : Subgroup G
  K : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  normalizer_V_le_M : Subgroup.normalizer (hyp.base.V : Set G) ≤ M
  K_eq_MF : K = maxNilpotentNormalHall M
  /-- The minimal odd-order counterexample fixed throughout §14.  Retaining this proof lets the
  coherent bundle expose its canonical `Hypothesis78` without erasing the proof argument used in
  that construction. -/
  hG : OddOrder.BG.IsMinimalSimpleOdd G
  /-- **Peterfalvi (5)--(8)/(12.1) for `M`**: the complete constructible type-I coherence bundle:
  the Dade setup, Frobenius complement, coherent extension, and placed induced family.  Earlier
  versions kept only the derived raw `Hypothesis78`, losing the family/coherence pins needed by
  (13.19) and (14.11.2).  This is upstream proof data, not a conclusion of (14.11). -/
  coherent78 : TypeICoherent78Data M
  e : ℕ
  k : ℕ
  /-- **Peterfalvi (14.10)**: `e = |M : K|` (the degree of `ψ`).  De-opacified from the former
  opaque `Prop` to the concrete index identity (lane-c §16 char-endpoint, carrier honesty). -/
  e_eq_index : e = (K.subgroupOf M).index
  /-- **Peterfalvi (13.17.c), V-side dual**: the faithful complement-index alternatives
  `e = p` or `e = p q`.  This is upstream input to (14.11), not either of its conclusions. -/
  complementIndex_cases : e = hyp.base.p ∨ e = hyp.base.p * hyp.base.q
  k_eq_card_K : k = Nat.card ↥K
  G0 : Set G
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: `G₀ ⊆ G − Ã(M)`.  The (14.11.3) set
  `G₀ = G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]` lies inside the family `(7.4)` support complement
  `famG₀ = (toFamilyHypothesis71).G0 = G − Ã(M)`, since every `g ∈ G₀` is off the Dade support
  `Ã(M)` of `A(M)` (`typeIHyp.dadeData.dade.dadeSupport`).  This is the inclusion `G₀ ⊆ famG₀`
  used to drop the `G₀`-part of the (7.5) sum in (14.11.4). -/
  G0_off_dadeSupport : ∀ g ∈ G0, g ∉ coherent78.typeIHyp.dadeData.dade.dadeSupport
  /-- **Peterfalvi (14.11.3)/(14.11.4)**: the complement of `G₀` is covered by the Dade support
  `Ã(M)` and the three orbits `(W − (W₁∪W₂))^G`, `(P#)^G`, `(Q#)^G`.  Concretely, `G₀` is the
  (14.11.3) set `G − [Ã(M) ∪ (W−(W₁∪W₂))^G ∪ (P#)^G ∪ (Q#)^G]`, so any `g` off `Ã(M)` and off `G₀`
  lies in the orbit union.  This is the §8 TI-counting input: `famG₀ ∖ G₀ ⊆ orbits` lets the
  `(7.5)` `G₀`-drop in line 83 (`chiRhoNormSq_psi_le_line83`) be bounded by the orbit cardinalities
  (the genuine §8 structural fact, supplied from the partner type-`P` structure). -/
  G0_orbit_cover : ∀ g : G, g ∉ coherent78.typeIHyp.dadeData.dade.dadeSupport → g ∉ G0 →
    g ∈ OddOrder.GroupTheory.conjClassSet
          ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
        ∪ OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
        ∪ OddOrder.GroupTheory.conjClassSet (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  /-- **Peterfalvi (14.11.3), avoidance half**: the generic set meets none of the three
  singular orbits — no conjugate of the regular Weyl set `W − (W₁∪W₂)`, of `P#`, or of `Q#`.
  Together with `G0_off_dadeSupport` this pins `G₀` inside Peterfalvi's (14.11.3) complement
  `G − [Ã(M) ∪ (W#)^G ∪ (P#)^G ∪ (Q#)^G]`; the support half of (14.11.3) — every `g ∈ G₀`
  has order prime to `pq` — follows through `orderOf_coprime_pq_of_not_mem_conj`
  (`G0_orderOf_coprime` below). -/
  G0_avoid : ∀ g ∈ G0,
    g ∉ OddOrder.GroupTheory.conjClassSet
        ((hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)))
      ∧ g ∉ OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.P)
      ∧ g ∉ OddOrder.GroupTheory.conjClassSet
          (OddOrder.GroupTheory.sharpSubgroup hyp.base.Q)
  /-- **Peterfalvi §13 `normalizer_V` for the `W`-set**: `N_G(X) = W` for every nonempty
  `X ⊆ W − (W₁∪W₂)` (the type-`P` exceptional-set normalizer, from the partner structure).  The
  `hnorm` input to the `W`-orbit TI count (`orbit_sdiff_sup_normSq_term`). -/
  W_normalizer_V : ∀ X : Set G, X.Nonempty →
    X ⊆ (hyp.base.W : Set G) \ ((hyp.base.W1 : Set G) ∪ (hyp.base.W2 : Set G)) →
    Subgroup.normalizer X = hyp.base.W
  -- **Peterfalvi (14.11)/(14.11.3)**: `|W| = p q`, `|W₁| + |W₂| = p + q`, and the nonemptiness of
  -- `W − (W₁∪W₂)` are **base-derived** (`S15.card_W_eq_pq`, `S15.card_W1_add_W2`,
  -- `S15.W_sdiff_nonempty`), so they are no longer carried as fields — the `W = W₁ × W₂` cyclic
  -- structure is an elementary consequence of the base `Hypothesis`, not a §13-14 σ-obligation.
  /-- **Peterfalvi §8**: `P` is a TI-subgroup (distinct conjugates meet trivially). -/
  P_isTI : Subgroup.IsTI hyp.base.P
  /-- **Peterfalvi §8**: `Q` is a TI-subgroup. -/
  Q_isTI : Subgroup.IsTI hyp.base.Q
  /-- **Peterfalvi (14.11.4)**: `|N_G(P)| = |P| u q` (the Type-II partner `S = (H ⋊ U) ⋊ W₂`). -/
  card_normalizer_P_eq : Nat.card ↥(Subgroup.normalizer (hyp.base.P : Set G))
    = Nat.card ↥hyp.base.P * hyp.base.u * hyp.base.q
  /-- **Peterfalvi (14.11.4)**: `|N_G(Q)| = |Q| v p` (the `T`-side partner). -/
  card_normalizer_Q_eq : Nat.card ↥(Subgroup.normalizer (hyp.base.Q : Set G))
    = Nat.card ↥hyp.base.Q * hyp.base.v * hyp.base.p

namespace MHypothesis

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

/-- The type-I Dade setup retained inside the complete coherent bundle. -/
abbrev typeIHyp [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    OddOrder.Peterfalvi.S14.Hypothesis Mdata.M := Mdata.coherent78.typeIHyp

/-- The canonical §7.8 datum derived from the retained coherent bundle. -/
noncomputable abbrev h78 [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    OddOrder.Peterfalvi.S09.Hypothesis78 G
      (OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI) Mdata.M :=
  Mdata.coherent78.h78 Mdata.hG

/-- Peterfalvi's coherent source family `𝓜`. -/
noncomputable abbrev Mset [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Set (ClassFunction ↥Mdata.M ℂ) := Mdata.typeIHyp.Sset

/-- The coherent extension `τ₁`; unlike `τ`, it is defined on every member of `𝓜`. -/
noncomputable abbrev tau1 [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥Mdata.M G := Mdata.coherent78.coh.extension

/-- The placed distinguished member `ψ = ζ₀` of degree `[M : K]`. -/
noncomputable abbrev psi [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    ClassFunction ↥Mdata.M ℂ := Mdata.coherent78.zeta 0

/-- `β_M^τ`, the canonical §7.8 Dade image attached to the retained coherent bundle. -/
noncomputable abbrev betaM [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    ClassFunction G ℂ := Mdata.h78.beta

@[simp] theorem betaM_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.betaM = Mdata.h78.beta := rfl

@[simp] theorem psi_tau1_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.tau1 Mdata.psi =
      Mdata.h78.nu (Mdata.h78.hyp76.zeta Mdata.h78.zetaDistinct) := rfl

@[simp] theorem h78_hyp_eq [Finite G] {hyp : Hypothesis (G := G)} (Mdata : MHypothesis hyp) :
    Mdata.h78.hyp76.hyp71.hyp = Mdata.typeIHyp.dadeData.dade :=
  Mdata.coherent78.h78_hyp_eq Mdata.hG

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Peterfalvi (7.4) one-member family `{(M, A(M))}` for the V-side type-I subgroup `M`** —
the §7 input bridging `M` to the family inequality (7.5) `S09.family_inequality`, the common
foundation of the (14.11) norm-cascade producers (`normCascadeData`, …).

Built genuinely from the type-I Dade setup carried by `typeIHyp` (its (8.15) Dade support
`dadeData` for `A(M) = typeIA M` and the conjugation invariance `hconj`), mirroring
`S12.Hypothesis.toFamilyHypothesis71` for type-`P` subgroups — but on the type-I support `typeIA`,
so no `A_0(M) → A(M)` restriction is needed.  The single member's (7.1) data is the restricted Dade
map of `dadeData`, the `IsDadeIsometry` certificate is `FullDadeIsometryData`'s, and
`pairwise_disjoint` is vacuous over `Fin 1`.  **Sorry-free + self-contained** from the genuine
`typeIHyp`. -/
noncomputable def toFamilyHypothesis71 [Finite G] {hyp : Hypothesis (G := G)}
    (Mdata : MHypothesis hyp) : OddOrder.Peterfalvi.S09.FamilyHypothesis71 G 1 where
  L := fun _ => Mdata.M
  A := fun _ => OddOrder.GroupTheory.typeIA Mdata.M Mdata.typeIHyp.typeI
  fintypeL := fun _ => inferInstance
  invertibleL := fun _ => inferInstance
  hyp71 := fun _ =>
    { hyp := Mdata.typeIHyp.dadeData.dade
      τ := (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData).toDadeMap
      isDadeMap :=
        Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData.toDadeIsometryData.isDadeMap }
  isDadeIsometry := fun _ =>
    (Mdata.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeIsometry
  pairwise_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

end MHypothesis

/-- The displayed rational inequality produced by the norm calculation in
**Peterfalvi (14.11.4)**, after substituting `e = p q`.  It is kept concrete so
future character-theoretic producers can target the exact arithmetic consumer
without adding another opaque proposition. -/
def normCascadeBound (hyp : Hypothesis (G := G)) (k : ℕ) : Prop :=
  (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
    ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
      2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
      1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (13.19.c), M-side bound-or-parity alternatives.**

This is the projection of each textbook (13.19.c) conjunction needed by (14.11.2): either the
corresponding degree bound holds, or the actual coefficient of `β_M^τ` on the non-principal zero
axis is an odd integer.  No parity branch is selected inside the carrier. -/
structure BetaMGridParityAlternatives [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  row :
    ((((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≤
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)) ∨
      ∀ j : Fin hyp.base.p, (j : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j))
  col :
    ((((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) ≤
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∨
      ∀ i : Fin hyp.base.q, (i : ℕ) ≠ 0 →
        OddOrder.Peterfalvi.S15.OddIntegerInner Mdata.betaM
          (hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩))

/-- Negation `i ↦ -i ≡ (n − i) (mod n)` on `Fin n`, for `0 < n`.  This is the index map
realizing the conjugation pairing `(i,j) ↦ (−i,−j)` of the Dade `η`-grid in (3.9.a)/(14.11.3). -/
def finNeg {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩

@[simp] theorem finNeg_val {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (finNeg hn i).val = (n - i.val) % n := rfl

end OddOrder.Peterfalvi.S16


