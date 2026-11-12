-- Prove2me | Definitions.Def_OddOrder_GroupTheory_CoprimeFixedPoints
-- name    : OddOrder_GroupTheory_CoprimeFixedPoints
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:01.125404+00:00
-- url     : https://prove2.me/theorems/8684ad93-60e1-4e9d-95ef-7248bfb11803
-- title:
--   Multiplicativity of coprime fixed points across a chief step
-- statement:
--   The group-theoretic core of the chief-series assembly of Peterfalvi (9.1) (Wielandt's fixed-point formula). Let $\varphi:L\to\mathrm{Aut}(H)$ be an action of a finite group $L$ on a finite group $H$, $X\le L$ a subgroup and $N\lhd H$ an $L$-invariant normal subgroup; the file shows multiplicativity of the coprime fixed points across the chief step. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/CoprimeFixedPoints.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/CoprimeFixedPoints.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_CoprimeAction
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

variable {L H : Type*} [Group L] [Group H]

section ChiefStep

variable {φ : L →* MulAut H} {X : Subgroup L} {N : Subgroup H}

/-- Restriction of `A`-invariance along a subgroup inclusion `X ≤ L`: if `N` is invariant under
the whole action `φ : L →* MulAut H`, it is invariant under the restricted action
`φ.comp X.subtype : X →* MulAut H`. -/
theorem isAInvariant_comp_subtype (hN : IsAInvariant φ N) :
    IsAInvariant (φ.comp X.subtype) N := by
  rw [isAInvariant_iff_smul_mem]
  intro a g hg
  simpa only [MonoidHom.comp_apply] using hN.smul_mem (X.subtype a) hg

/-- **The reduction map sends `C_H(X)` onto `C_{H/N}(X)`.**  The image of the fixed subgroup
`C_H(X) = fixedSubgroup φ X` under `QuotientGroup.mk' N` equals the fixed subgroup
`C_{H/N}(X) = fixedSubgroup hN.quotientMulAutHom X` of the induced quotient action.

`⊆` is automatic from `quotientMulAutHom_apply_mk'`; `⊇` is **Isaacs Cor 3.28**: an `X`-fixed
coset `gN` contains an `X`-fixed representative `c`, so `gN = cN` lies in the image. -/
theorem map_fixedSubgroup_eq_fixedSubgroup_quotient [N.Normal] [Finite ↥X] [Finite H]
    (hN : IsAInvariant φ N)
    (hCop : Nat.Coprime (Nat.card ↥X) (Nat.card H))
    (hSolv : Group.IsSolvable ↥X ∨ Group.IsSolvable H) :
    (fixedSubgroup φ X).map (QuotientGroup.mk' N) =
      fixedSubgroup (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) X := by
  ext q
  simp only [Subgroup.mem_map, mem_fixedSubgroup]
  constructor
  · rintro ⟨c, hc, rfl⟩ l hl
    rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk' hN, hc l hl]
  · intro hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    -- The coset `gN` is `X`-fixed: each `φ l g` lies in `gN`.
    have hfix : ∀ a : ↥X, ∃ n ∈ N, (φ.comp X.subtype) a g = g * n := by
      intro a
      have h := hq (X.subtype a) a.2
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk' hN,
        QuotientGroup.mk'_eq_mk'] at h
      obtain ⟨z, hz, hzeq⟩ := h
      exact ⟨z⁻¹, N.inv_mem hz, by
        rw [MonoidHom.comp_apply, eq_mul_inv_iff_mul_eq]; exact hzeq⟩
    -- Cor 3.28 produces an `X`-fixed representative `c ∈ gN`.
    obtain ⟨c, hc_fix, n, hn, hc_eq⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient (φ := φ.comp X.subtype)
        hCop hSolv (isAInvariant_comp_subtype hN) hfix
    refine ⟨c, fun l hl => ?_, ?_⟩
    · simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply] using hc_fix ⟨l, hl⟩
    · have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [hc_eq, map_mul, hn1, mul_one]

/-- **Peterfalvi (9.1), I-5 chief-step multiplicativity.**  For a coprime solvable action
`φ : L →* MulAut H`, a subgroup `X ≤ L`, and an `L`-invariant normal subgroup `N ◁ H`, the
fixed points split across the chief step `1 → N → H → H/N → 1`:
`|C_H(X)| = |C_H(X) ⊓ N| · |C_{H/N}(X)|`.

The reduction homomorphism `C_H(X) →* H/N` has kernel `C_H(X) ⊓ N` and image `C_{H/N}(X)`
(surjectivity is Isaacs Cor 3.28, `map_fixedSubgroup_eq_fixedSubgroup_quotient`); Lagrange's
theorem and Noether's first isomorphism theorem give the product. -/
theorem card_fixedSubgroup_eq_mul [N.Normal] [Finite ↥X] [Finite H]
    (hN : IsAInvariant φ N)
    (hCop : Nat.Coprime (Nat.card ↥X) (Nat.card H))
    (hSolv : Group.IsSolvable ↥X ∨ Group.IsSolvable H) :
    Nat.card ↥(fixedSubgroup φ X) =
      Nat.card ↥((fixedSubgroup φ X ⊓ N : Subgroup H)) *
        Nat.card ↥(fixedSubgroup (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) X) := by
  set C := fixedSubgroup φ X with hC
  -- The reduction map `f : C →* H/N`, its image and its kernel.
  have hr : ((QuotientGroup.mk' N).comp C.subtype).range =
      fixedSubgroup (OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hC]
    exact map_fixedSubgroup_eq_fixedSubgroup_quotient hN hCop hSolv
  have hke : ((QuotientGroup.mk' N).comp C.subtype).ker = N.subgroupOf C := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hk : Nat.card ↥((QuotientGroup.mk' N).comp C.subtype).ker
      = Nat.card ↥((C ⊓ N : Subgroup H)) := by
    rw [hke, Nat.card_congr ((N.subgroupOf C).equivMapOfInjective C.subtype
      C.subtype_injective).toEquiv, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((QuotientGroup.mk' N).comp C.subtype).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange
      ((QuotientGroup.mk' N).comp C.subtype)).toEquiv, hr, hk, mul_comm]

/-- The fixed subgroup of the **restricted action** `hN.restrict : L →* MulAut ↥N` on an
`L`-invariant subgroup `N ≤ H` is, as a subgroup of `↥N`, exactly `(C_H(X)).subgroupOf N`: an
element `n ∈ N` is fixed by the restricted `X`-action iff it is fixed by the ambient action
(`IsAInvariant.restrict_apply_val`). -/
theorem fixedSubgroup_restrict_eq (hN : IsAInvariant φ N) :
    fixedSubgroup hN.restrict X = (fixedSubgroup φ X).subgroupOf N := by
  ext x
  simp only [mem_fixedSubgroup, Subgroup.mem_subgroupOf]
  constructor
  · intro hx l hl
    have h := congrArg Subtype.val (hx l hl)
    rwa [IsAInvariant.restrict_apply_val] at h
  · intro hx l hl
    exact Subtype.ext ((IsAInvariant.restrict_apply_val hN l x).trans (hx l hl))

/-- **Card of the restricted fixed subgroup.**  `|C_N(X)| = |C_H(X) ⊓ N|`: the fixed points of the
`X`-action restricted to an `L`-invariant subgroup `N ≤ H` are exactly the ambient fixed points
lying in `N`.  This is the subgroup-side bridge feeding the per-chief-factor Wielandt identity on an
elementary-abelian chief factor `N` (its module `C_N(X)` of fixed points has this cardinality). -/
theorem card_fixedSubgroup_restrict (hN : IsAInvariant φ N) :
    Nat.card ↥(fixedSubgroup hN.restrict X) =
      Nat.card ↥((fixedSubgroup φ X ⊓ N : Subgroup H)) := by
  rw [fixedSubgroup_restrict_eq,
    Nat.card_congr (((fixedSubgroup φ X).subgroupOf N).equivMapOfInjective N.subtype
      N.subtype_injective).toEquiv, Subgroup.subgroupOf_map_subtype]

end ChiefStep

section AssemblyStep

/-- Readable alias for the induced quotient action `L →* MulAut (H ⧸ N)`; the underlying
`quotientMulAutHom` has an awkward fully-qualified name (it is declared inside `namespace …Ch04`
with a `…Ch03`-qualified head, see the `naming wart` note in
`notes/peterfalvi/s11_wielandt_91_design.md`). -/
local notation3 "quotMulAut " hN => OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN

variable {L H : Type*} [Group L] [Group H]

/-- **The arithmetic core of the chief-series induction.**  If the per-chief-factor identity holds
on `N` (`hfac`) and the Wielandt identity holds on the quotient `H/N` (`hIH`, the induction
hypothesis), the two combine multiplicatively.  Pure `ℕ`-arithmetic: writing each ambient term as
`a_X · b_X` (the chief-step multiplicativity) and `|H| = |N| · |H/N|`, the exponent-`e` product of
`hfac` and `hIH` is exactly the group identity. -/
theorem wielandt_card_combine {e aT aE aU bT bE bU n m : ℕ}
    (hfac : aT ^ e * n = aE ^ e * aU) (hIH : bT ^ e * m = bE ^ e * bU) :
    (aT * bT) ^ e * (n * m) = (aE * bE) ^ e * (aU * bU) := by
  rw [mul_pow, mul_pow]
  calc aT ^ e * bT ^ e * (n * m) = (aT ^ e * n) * (bT ^ e * m) := by ring
    _ = (aE ^ e * aU) * (bE ^ e * bU) := by rw [hfac, hIH]
    _ = aE ^ e * bE ^ e * (aU * bU) := by ring

/-- **Peterfalvi (9.1), the chief-series induction step.**  Given a coprime solvable action
`φ : L →* MulAut H`, an `L`-invariant normal subgroup `N ◁ H`, the per-chief-factor Wielandt
identity on `N` (`hfac`), and the Wielandt identity on the quotient `H/N` (`hIH`), the group-level
Wielandt identity holds for `H`:
`|C_H(UE)|^{|E|} · |H| = |C_H(E)|^{|E|} · |C_H(U)|` (with `C_H(UE) = fixedSubgroup φ ⊤`).

This is the inductive step of `wielandt_fixedPoint_frobenius`: the chief-step multiplicativity
`card_fixedSubgroup_eq_mul` rewrites each ambient fixed-point count as
`|C_H(X) ⊓ N| · |C_{H/N}(X)|`,
`|H| = |N| · |H/N|`, and `wielandt_card_combine` multiplies `hfac` and `hIH`. -/
theorem wielandt_step [Finite L] [Finite H] {φ : L →* MulAut H} {U E : Subgroup L}
    {N : Subgroup H} [N.Normal] [Group.IsSolvable H] (hN : IsAInvariant φ N)
    (hcop : Nat.Coprime (Nat.card L) (Nat.card H))
    (hfac : Nat.card ↥(fixedSubgroup φ ⊤ ⊓ N) ^ Nat.card ↥E * Nat.card ↥N =
      Nat.card ↥(fixedSubgroup φ E ⊓ N) ^ Nat.card ↥E *
        Nat.card ↥(fixedSubgroup φ U ⊓ N))
    (hIH : Nat.card ↥(fixedSubgroup (quotMulAut hN) ⊤) ^ Nat.card ↥E * Nat.card (H ⧸ N) =
      Nat.card ↥(fixedSubgroup (quotMulAut hN) E) ^ Nat.card ↥E *
        Nat.card ↥(fixedSubgroup (quotMulAut hN) U)) :
    Nat.card ↥(fixedSubgroup φ ⊤) ^ Nat.card ↥E * Nat.card H =
      Nat.card ↥(fixedSubgroup φ E) ^ Nat.card ↥E * Nat.card ↥(fixedSubgroup φ U) := by
  have hcopOfDvd : ∀ X : Subgroup L, Nat.Coprime (Nat.card ↥X) (Nat.card H) := fun X =>
    hcop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card X)
  have mT := card_fixedSubgroup_eq_mul (φ := φ) (X := ⊤) hN
    (by rw [Nat.card_congr (Subgroup.topEquiv (G := L)).toEquiv]; exact hcop) (Or.inr ‹_›)
  have mE := card_fixedSubgroup_eq_mul (φ := φ) (X := E) hN (hcopOfDvd E) (Or.inr ‹_›)
  have mU := card_fixedSubgroup_eq_mul (φ := φ) (X := U) hN (hcopOfDvd U) (Or.inr ‹_›)
  have hH : Nat.card H = Nat.card ↥N * Nat.card (H ⧸ N) := by
    rw [mul_comm]; exact Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [mT, mE, mU, hH]
  exact wielandt_card_combine hfac hIH

end AssemblyStep

end OddOrder.GroupTheory


