-- Prove2me | Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType
-- name    : OddOrder_GroupTheory_MaximalSubgroupType
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:35:50.918006+00:00
-- url     : https://prove2.me/theorems/1177520d-757c-4008-9833-d34c636e2476
-- title:
--   Maximal subgroup types for BG/Peterfalvi
-- statement:
--   The shared scaffold for the maximal-subgroup type taxonomy used by BG Chapter IV and Peterfalvi Sections 10-16. The definitions follow Peterfalvi Section 10 in the plain derived-series formulation and are exposed as `Prop`s.
--
--   Auxiliary definitions include `secondDerivedInAmbient` ($M''$), `sharpSubgroup`, `centralizerSupport`, `escapingCentralizerSet` and `leftCosetSet`; `TypeFData` and `IsTypeF` capture Peterfalvi (8.1), a solvable group of type $F$, and the file also defines the other type predicates `IsTypeI` and so on.
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/MaximalSubgroupType.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupType.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_MaxNilpotentNormalHall
import Definitions.Def_OddOrder_GroupTheory_SubgroupInAmbient
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- The second derived subgroup `M''` of `M`, viewed in the ambient group.
(`M' = derivedInG M`, canonical in `GroupTheory.SubgroupInAmbient`, issue 0052.) -/
def secondDerivedInAmbient (M : Subgroup G) : Subgroup G :=
  derivedInG (derivedInG M)

/-- Nonidentity elements of a subgroup, as a subset of the ambient group. -/
def sharpSubgroup (H : Subgroup G) : Set G :=
  (H : Set G) \ {1}

/-- A centralizer-union set: nonidentity elements of `host` centralizing some
 element of `source`.  This packages the repeated `A(M)` pattern in (8.10). -/
def centralizerSupport (source : Set G) (host : Subgroup G) : Set G :=
  {y | y ∈ host ∧ y ≠ 1 ∧ ∃ x ∈ source, y ∈ Subgroup.centralizer ({x} : Set G)}

/-- Elements of `X` whose ambient centralizer is not contained in `M`. -/
def escapingCentralizerSet (M : Subgroup G) (X : Set G) : Set G :=
  {x | x ∈ X ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}

/-- The left coset `aH`, as a subset of the ambient group. -/
def leftCosetSet (a : G) (H : Subgroup G) : Set G :=
  (fun h : G => a * h) '' (H : Set G)

/-- Data for Peterfalvi (8.1), a solvable group of type `F`.

`H` is `M_F`, `U` is a Hall complement in `M`, `U_1` is the abelian normal
subgroup controlling centralizers of elements of `H#`, and `U_0` is the
Frobenius-complement realization with the same exponent as `U`. -/
structure TypeFData (M : Subgroup G) where
  H : Subgroup G
  U : Subgroup G
  U1 : Subgroup G
  U0 : Subgroup G
  H_eq : H = maxNilpotentNormalHall M
  H_nontrivial : H ≠ ⊥
  U_nontrivial : U ≠ ⊥
  H_le : H ≤ M
  U_le : U ≤ M
  U1_le : U1 ≤ U
  U0_le : U0 ≤ U
  complement : Subgroup.IsComplement' (H.subgroupOf M) (U.subgroupOf M)
  U1_normal : (U1.subgroupOf U).Normal
  U1_commutative : IsMulCommutative ↥U1
  centralizer_le_U1 : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set G) ≤ U1
  exponent_eq : Monoid.exponent U0 = Monoid.exponent U
  frobenius_HU0 : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥(H ⊔ U0) (H.subgroupOf (H ⊔ U0)) (U0.subgroupOf (H ⊔ U0))

/-- Predicate form of Peterfalvi type `F`. -/
def IsTypeF (M : Subgroup G) : Prop :=
  Nonempty (TypeFData M)

/-- Data for Peterfalvi (8.3), type I. -/
structure TypeIData (M : Subgroup G) where
  typeF : TypeFData M
  alternative :
    IsTISubset (sharpSubgroup typeF.H) (Subgroup.normalizer (typeF.H : Set G)) ∨
    (IsMulCommutative ↥typeF.H ∧ rank ↥typeF.H = 2) ∨
    ((∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥typeF.H).primeFactors →
        Monoid.exponent typeF.U ∣ p - 1) ∧
      ∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥typeF.H).primeFactors ∧
        IsCyclic ↥(opiCoreInG {p}ᶜ typeF.H))

/-- Predicate form of Peterfalvi type I. -/
def IsTypeI (M : Subgroup G) : Prop :=
  Nonempty (TypeIData M)

/-- Data for Peterfalvi (8.4), type `P`.

The fields mirror the derived-series presentation in the text: `M = M' W_1`,
`M' = H U`, `H = M_F`, `W_2 = C_{M'}(W_1#)`, and the set
`V = W - (W_1 union W_2)` has normalizer exactly `W` for every nonempty subset. -/
structure TypePData (M : Subgroup G) where
  H : Subgroup G
  U : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  H_eq : H = maxNilpotentNormalHall M
  H_le : H ≤ derivedInG M
  U_le : U ≤ derivedInG M
  W1_le : W1 ≤ M
  W2_le : W2 ≤ H ⊓ secondDerivedInAmbient M
  W_eq : W = W1 ⊔ W2
  W_cyclic : IsCyclic ↥W
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  W1_cyclic : IsCyclic ↥W1
  W2_cyclic : IsCyclic ↥W2
  M_complement : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W1.subgroupOf M)
  -- (8.4.b) "`U` normalized by `W₁`" = `W₁ ≤ N(U)`.  NOT "`U ◁ M'`": in the semidirect product
  -- `M' = H ⋊ U`, `U ◁ M'` forces a direct product hence `U = 1`, vacuating types II–IV (issue
  -- 7008).
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  U_nilpotent : Group.IsNilpotent ↥U
  derived_complement :
    Subgroup.IsComplement' (H.subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M))
  H_noncyclic : ¬ IsCyclic ↥H
  secondDerived_le_fitting :
    secondDerivedInAmbient M ≤ H ⊔ (U ⊓ Subgroup.centralizer (H : Set G))
  -- (8.5.a) `F(M) = H · C_U(H) = H ⊔ (U ⊓ C_M(H))`.  The LHS is the **real Fitting** `F(M)`, NOT
  -- `M_F = maxNilpotentNormalHall M` (= `H`): with `M_F` the field would force `C_U(H) ≤ M_F`,
  -- excluding type IV and (with `derived_complement`) collapsing `M_F = M'` (issue 7008).  The old
  -- `fitting_lt_derived : M_F < M'` is deleted: `F(M) ⊆ M'` is derivable from this `fitting_eq`,
  -- `H_le`, `U_le`, and is `≤` (non-strict; equality at type V where `U = ⊥`,
  -- `F(M) = H = M' = M_F`).
  fitting_eq :
    (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype = H ⊔ (U ⊓ Subgroup.centralizer (H : Set G))
  centralizer_W1 : ∀ x ∈ W1, x ≠ 1 →
    derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = W2
  normalizer_V : ∀ X : Set G, X.Nonempty →
    X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W

/-- **Peterfalvi (8.8.b1) / BG (T6)(2)**: the cyclic factor `W₁` of a type-`P` maximal subgroup
has order `|M : M'|` — it complements the derived subgroup `M' = [M,M]` in `M` (the `M_complement`
field, mirroring `M = M' ⋊ W₁`).  This is the order that BG Theorem C(10) (type II–IV) shows to be
prime; `TypePNontrivialCore` carries that primality.  Both this `W₁` and any Hall `κ(M)`-subgroup
`K` of `M` complement `M'`, so they share this order — the bridge to BG §14 `typeP_duality`. -/
theorem TypePData.card_W1_eq_derived_index {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥data.W1 = ((derivedInG M).subgroupOf M).index := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv,
    ← data.M_complement.symm.index_eq_card]

/-- The complement `U` of `H = M_F` in `M' = [M,M]` has order the canonical index
`[M' : M_F]`, independent of the choice of type-`P` witness (`derived_complement`).  In particular
any two `TypePData` on the same `M` have `|U|` equal — used to transfer `U ≠ 1` between
witnesses. -/
theorem TypePData.card_U_eq_index {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥data.U = ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).index := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.U_le).toEquiv, ← data.H_eq,
    ← data.derived_complement.symm.index_eq_card]

/-- **Peterfalvi (13.1.b) `S' = PU` / BG Theorem C(3) `M' = U M_σ`** (type-data form): the derived
subgroup of a type-`P` maximal subgroup is the join of its Fitting kernel `M_F` and the complement
`U`, `M' = M_F ⊔ U`.  Immediate from the `derived_complement` field (`U` complements `H = M_F` in
`M'`).  This is the `S_deriv_eq_PU` field of `Section16TypePStructure`, sourced from the type
data. -/
theorem TypePData.derivedInG_eq_fitting_sup_U {M : Subgroup G} (data : TypePData M) :
    derivedInG M = maxNilpotentNormalHall M ⊔ data.U := by
  rw [← data.H_eq]
  refine le_antisymm ?_ (sup_le data.H_le data.U_le)
  have hsup : (data.H.subgroupOf (derivedInG M)) ⊔ (data.U.subgroupOf (derivedInG M)) = ⊤ :=
    data.derived_complement.sup_eq_top
  rw [← Subgroup.subgroupOf_sup data.H_le data.U_le] at hsup
  exact Subgroup.subgroupOf_eq_top.mp hsup

/-- The Fitting kernel `M_F` and the complement `U` of a `TypePData` intersect trivially.

This is the ambient-subgroup form of the disjoint half of `data.derived_complement`, using
`data.H_eq : data.H = M_F`. -/
theorem TypePData.fitting_inf_U_eq_bot {M : Subgroup G} (data : TypePData M) :
    maxNilpotentNormalHall M ⊓ data.U = ⊥ := by
  rw [← data.H_eq, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have hxD : x ∈ derivedInG M := data.H_le hx.1
  have hmem : (⟨x, hxD⟩ : ↥(derivedInG M)) ∈
      (data.H.subgroupOf (derivedInG M)) ⊓ (data.U.subgroupOf (derivedInG M)) := by
    rw [Subgroup.mem_inf]
    exact ⟨Subgroup.mem_subgroupOf.mpr hx.1, Subgroup.mem_subgroupOf.mpr hx.2⟩
  have hd := data.derived_complement.disjoint
  rw [disjoint_iff] at hd
  rw [hd, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact Subtype.ext_iff.mp hmem

/-- **Peterfalvi (8.4.d) / Coq `PFsection8.typeP_cent_compl`**: `C_{M'}(W₁) = W₂` — the centralizer
in the derived subgroup of the *whole* cyclic factor `W₁` (not merely of a single `k ∈ W₁#`) is
exactly the dual cyclic factor `W₂`.

Both inclusions are immediate from the datum, no generator needed:
* `⊆`: pick any `g ∈ W₁#` (`W₁` nontrivial); `C(W₁) ≤ C({g})` by monotonicity, and
  `M' ⊓ C({g}) = W₂` is the `centralizer_W1` field.
* `⊇`: `W₂ ≤ H ≤ M'` (`W2_le`/`H_le`) and `W₂ ≤ C(W₁)` because `W₁, W₂ ≤ W` with `W` cyclic hence
  abelian, so the two factors commute.

This is the reusable form consumed by the type-`P` *pairing* reconciliation: the partner `T` of `M`
(sharing the cyclic `W = W₁ × W₂`) carries the swapped law `C_{T'}(W₂) = W₁`, which is exactly this
lemma applied to `T`'s type-`P` datum with the roles of `W₁`, `W₂` exchanged. -/
theorem TypePData.derivedInG_inf_centralizer_W1_eq {M : Subgroup G} (data : TypePData M) :
    derivedInG M ⊓ Subgroup.centralizer (data.W1 : Set G) = data.W2 := by
  refine le_antisymm ?_ ?_
  · -- `⊆`: any nontrivial `g ∈ W₁` gives `C(W₁) ≤ C({g})`, then the `centralizer_W1` field.
    obtain ⟨g, hgW1, hgne⟩ : ∃ g ∈ data.W1, g ≠ 1 := by
      have : Nontrivial ↥data.W1 := (Subgroup.nontrivial_iff_ne_bot _).mpr data.W1_nontrivial
      obtain ⟨y, hy⟩ := exists_ne (1 : ↥data.W1)
      exact ⟨y, y.2, fun h => hy (Subtype.ext h)⟩
    have hle : Subgroup.centralizer (data.W1 : Set G) ≤ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hgW1)
    calc derivedInG M ⊓ Subgroup.centralizer (data.W1 : Set G)
        ≤ derivedInG M ⊓ Subgroup.centralizer ({g} : Set G) := inf_le_inf_left _ hle
      _ = data.W2 := data.centralizer_W1 g hgW1 hgne
  · -- `⊇`: `W₂ ≤ M'` and `W₂ ≤ C(W₁)` (the two cyclic factors of the abelian `W` commute).
    refine le_inf (le_trans data.W2_le (le_trans inf_le_left data.H_le)) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hxW : x ∈ data.W := data.W_eq ▸ Subgroup.mem_sup_right hx
    have hhW : h ∈ data.W := data.W_eq ▸ Subgroup.mem_sup_left hh
    have := data.W_cyclic
    let : CommGroup ↥data.W := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨h, hhW⟩ : ↥data.W) ⟨x, hxW⟩)

/-- Common type II--IV hypotheses from Peterfalvi (8.6). -/
def TypePNontrivialCore (M : Subgroup G) (data : TypePData M) : Prop :=
  data.U ≠ ⊥ ∧ (Nat.card ↥data.W1).Prime ∧
    IsTISubset (sharpSubgroup (maxNilpotentNormalHall M))
      (Subgroup.normalizer ((maxNilpotentNormalHall M : Subgroup G) : Set G))

/-- Data for Peterfalvi type II. -/
structure TypeIIData (M : Subgroup G) where
  typeP : TypePData M
  common : TypePNontrivialCore M typeP
  U_commutative : IsMulCommutative ↥typeP.U
  normalizer_not_le : ¬ Subgroup.normalizer (typeP.U : Set G) ≤ M
  derived_typeF : IsTypeF (derivedInG M)
  derived_fitting_eq : maxNilpotentNormalHall (derivedInG M) = typeP.H

/-- Data for Peterfalvi type III. -/
structure TypeIIIData (M : Subgroup G) where
  typeP : TypePData M
  common : TypePNontrivialCore M typeP
  U_commutative : IsMulCommutative ↥typeP.U
  normalizer_le : Subgroup.normalizer (typeP.U : Set G) ≤ M

/-- Data for Peterfalvi type IV. -/
structure TypeIVData (M : Subgroup G) where
  typeP : TypePData M
  common : TypePNontrivialCore M typeP
  U_not_commutative : ¬ IsMulCommutative ↥typeP.U
  normalizer_le : Subgroup.normalizer (typeP.U : Set G) ≤ M

/-- Data for Peterfalvi type V. -/
structure TypeVData (M : Subgroup G) where
  typeP : TypePData M
  U_eq_bot : typeP.U = ⊥
  alternative :
    IsTISubset (sharpSubgroup typeP.H) (Subgroup.normalizer (typeP.H : Set G)) ∨
    (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥typeP.H).primeFactors ∧
      Nat.card ↥typeP.W1 ∣ p - 1 ∧ IsCyclic ↥(opiCoreInG {p}ᶜ typeP.H)) ∨
    (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥typeP.H).primeFactors ∧
      Nat.card ↥(opiCoreInG {p} typeP.H) = p ^ 3 ∧ Nat.card ↥typeP.W1 ∣ p + 1 ∧
      IsCyclic ↥(opiCoreInG {p}ᶜ typeP.H))

/-- Predicate form of Peterfalvi type II. -/
def IsTypeII (M : Subgroup G) : Prop :=
  Nonempty (TypeIIData M)

/-- Predicate form of Peterfalvi type III. -/
def IsTypeIII (M : Subgroup G) : Prop :=
  Nonempty (TypeIIIData M)

/-- Predicate form of Peterfalvi type IV. -/
def IsTypeIV (M : Subgroup G) : Prop :=
  Nonempty (TypeIVData M)

/-- Predicate form of Peterfalvi type V. -/
def IsTypeV (M : Subgroup G) : Prop :=
  Nonempty (TypeVData M)

/-- The non-Type-I alternatives in Peterfalvi (8.8). -/
def IsTypeNonI (M : Subgroup G) : Prop :=
  IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M

/-- **The (8.6) nontrivial core transfers between type-`P` witnesses**: `TypePNontrivialCore` for
one `TypePData` on `M` gives it for any other.  Its three clauses are witness-independent: the TI
condition mentions only `M_F = maxNilpotentNormalHall M`; `|W₁|` is the derived index
(`card_W1_eq_derived_index`); and `|U|` is the index `[M' : M_F]` (`card_U_eq_index`), so `U ≠ ⊥`
transfers through the cardinality. -/
theorem TypePNontrivialCore.transfer [Finite G] {M : Subgroup G} {data : TypePData M}
    (h : TypePNontrivialCore M data) (data' : TypePData M) :
    TypePNontrivialCore M data' := by
  obtain ⟨hU, hW1, hTI⟩ := h
  refine ⟨?_, ?_, hTI⟩
  · intro hbot
    have hcard : Nat.card ↥data'.U = Nat.card ↥data.U := by
      rw [data.card_U_eq_index, data'.card_U_eq_index]
    rw [hbot, Subgroup.card_bot] at hcard
    exact hU (Subgroup.card_eq_one.mp hcard.symm)
  · rw [data'.card_W1_eq_derived_index, ← data.card_W1_eq_derived_index]
    exact hW1

/-- **Types III and IV carry the (8.6) nontrivial core for every type-`P` witness** (the `hnt`
input of the §9 `TypesIIIIIIVSetup`): the bundled `TypeIIIData`/`TypeIVData` provides
`TypePNontrivialCore` for *its own* `typeP`, and `TypePNontrivialCore.transfer` moves it to any
given `TypePData` on the same `M`. -/
theorem typePNontrivialCore_of_isTypeIIIorIV [Finite G] {M : Subgroup G}
    (htype : IsTypeIII M ∨ IsTypeIV M) (data : TypePData M) :
    TypePNontrivialCore M data := by
  rcases htype with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · exact d.common.transfer data
  · exact d.common.transfer data

/-- Every non-Type-I maximal subgroup carries type-`P` data: all four of `TypeII`–`TypeV` bundle a
`TypePData` (the type-`P` structure `M = M' ⋊ W₁`, `M' = M_F ⋊ U`, `W = W₁ × W₂`).  This is the
entry point that lets the §16 producer extract the structure of `S` and `T` from
`Section16MaximalPair.S_nonI`/`T_nonI`. -/
theorem typePData_of_isTypeNonI {M : Subgroup G} (h : IsTypeNonI M) : Nonempty (TypePData M) := by
  rcases h with h | h | h | h <;> exact ⟨h.some.typeP⟩

/-- The five named Peterfalvi maximal-subgroup types. -/
inductive PeterfalviType where
  | I | II | III | IV | V
  deriving DecidableEq, Repr

/-- Predicate selecting the corresponding type predicate. -/
def HasPeterfalviType (tau : PeterfalviType) (M : Subgroup G) : Prop :=
  match tau with
  | .I => IsTypeI M
  | .II => IsTypeII M
  | .III => IsTypeIII M
  | .IV => IsTypeIV M
  | .V => IsTypeV M

/-- Peterfalvi (8.10), the subgroup `M_s`: it is `M_F` for types I, II, V and
`M'` for types III, IV. -/
noncomputable def mainSubgroup (M : Subgroup G) (tau : PeterfalviType) : Subgroup G :=
  match tau with
  | .III => derivedInG M
  | .IV => derivedInG M
  | .I => maxNilpotentNormalHall M
  | .II => maxNilpotentNormalHall M
  | .V => maxNilpotentNormalHall M

/-- Peterfalvi (8.10), `A_1(M) = M_s#`. -/
def A1 (M : Subgroup G) (tau : PeterfalviType) : Set G :=
  sharpSubgroup (mainSubgroup M tau)

/-- The `A(M)` set associated to type I data. -/
def typeIA (M : Subgroup G) (data : TypeIData M) : Set G :=
  centralizerSupport (sharpSubgroup data.typeF.H) M

/-- `1 ∉ A(M)`: the type-`I` support `typeIA` consists of nonidentity elements. -/
theorem one_notMem_typeIA {M : Subgroup G} (data : TypeIData M) :
    (1 : G) ∉ typeIA M data := fun h => h.2.1 rfl

/-- `H^# ⊆ A(M)` for type-`I` data (the Coq `Fcore_sub_FTsupp` shape): a nonidentity element
of the kernel `H = M_F` lies in the support `A(M)` — it centralizes itself.  For a Frobenius
`M` this inclusion is an equality, but for a general type-`I` maximal `A(M)` is strictly
larger; the (12.5) chain needs only this inclusion. -/
theorem sharpSubgroup_H_subset_typeIA {M : Subgroup G} (data : TypeIData M) :
    sharpSubgroup data.typeF.H ⊆ typeIA M data := by
  intro y hy
  refine ⟨data.typeF.H_le hy.1, fun h1 => hy.2 h1, y, hy, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Set.mem_singleton_iff.mp hg]

/-- **Peterfalvi (8.10)**: the host of the centralizers in `A(M) = ⋃_{x∈M_s^#} C_K(x)^#` — the
whole of `M` for Type I, and the derived subgroup `M' = [M,M]` for the types of class `𝒫`
(Types II, III, IV, V). -/
noncomputable def supportHost (M : Subgroup G) (tau : PeterfalviType) : Subgroup G :=
  match tau with
  | .I => M
  | _ => derivedInG M

/-- **Peterfalvi (8.10)**, the type-uniform support `A(M) = ⋃_{x ∈ M_s^#} C_K(x)^#` with
`K = supportHost M tau`.  It specialises to `typeIA` on Type I (`typeA_eq_typeIA`) and to the
book-literal `OddOrder.Peterfalvi.S10.typePACore` on the types of class `𝒫`
(`typeA_eq_typePACore`). -/
noncomputable def typeA (M : Subgroup G) (tau : PeterfalviType) : Set G :=
  centralizerSupport (sharpSubgroup (mainSubgroup M tau)) (supportHost M tau)

@[simp] theorem supportHost_typeI (M : Subgroup G) : supportHost M .I = M := rfl

/-- The host of `A(M)` lies in `M`: it is `M` itself on Type I and `M' ≤ M` otherwise. -/
theorem supportHost_le (M : Subgroup G) (tau : PeterfalviType) : supportHost M tau ≤ M := by
  cases tau <;> first | exact le_rfl | exact Subgroup.map_subtype_le _

/-- `A(M) ⊆ M` for every type. -/
theorem typeA_subset {M : Subgroup G} {tau : PeterfalviType} :
    typeA M tau ⊆ (M : Set G) := fun _ hy => supportHost_le M tau hy.1

theorem supportHost_of_ne_typeI (M : Subgroup G) {tau : PeterfalviType} (h : tau ≠ .I) :
    supportHost M tau = derivedInG M := by
  cases tau <;> first | exact absurd rfl h | rfl

/-- **`A₁(M) ⊆ A(M)`** (the first inclusion of (8.10)'s closing sentence), for every type:
a nonidentity `x ∈ M_s` centralizes itself, and `M_s ≤ K` — for Type I because `M_s = M_F ≤ M`,
otherwise because `M_s` lies in `M'`.  Both containments are supplied by the caller as `hle`,
since they are §15/§16 facts rather than definitional ones. -/
theorem A1_subset_typeA {M : Subgroup G} {tau : PeterfalviType}
    (hle : mainSubgroup M tau ≤ supportHost M tau) : A1 M tau ⊆ typeA M tau := by
  intro y hy
  exact ⟨hle hy.1, fun h1 => hy.2 h1, y, hy,
    Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Set.mem_singleton_iff.mp hg]⟩

/-- **(8.10) on Type I**: the type-uniform `A(M)` is the type-I support `typeIA`
(`H = M_F = M_s`, `TypeFData.H_eq`). -/
theorem typeA_eq_typeIA {M : Subgroup G} (data : TypeIData M) :
    typeA M .I = typeIA M data := by
  rw [typeA, typeIA, data.typeF.H_eq]
  rfl

/-- The `A(M)` set associated to type `P` data. -/
def typePA (M : Subgroup G) (_data : TypePData M) : Set G :=
  centralizerSupport (sharpSubgroup M) (derivedInG M)

/-- The exceptional `V = W - (W_1 union W_2)` set attached to type `P` data. -/
def typePV (M : Subgroup G) (data : TypePData M) : Set G :=
  (data.W : Set G) \ ((data.W1 : Set G) ∪ (data.W2 : Set G))

/-- Peterfalvi (8.10), `A_0(M) = A(M) ∪ V^M` for type `P` data.

The exceptional part is the **`M`-conjugacy** closure `V^M = conjClassSetIn M (typePV M data)`
(Coq `class_support V L`), *not* the `G`-closure `conjClassSet`: the Dade hypothesis (8.15)
requires `A_0(M) ⊆ M`, and the `G`-closure of the nonempty `V` cannot lie in the proper `M`
(its normal closure would be a nontrivial proper normal subgroup, contradicting simplicity). -/
def typePA0 (M : Subgroup G) (data : TypePData M) : Set G :=
  typePA M data ∪ conjClassSetIn M (typePV M data)

/-- **A `centralizerSupport` over a sharp source collapses to the sharp of its host** as soon as
the host lies inside the source subgroup: the centralizer condition is then vacuous, because every
`y ∈ H^# ⊆ K^#` centralizes itself (take `x = y`).  So
`centralizerSupport (K^#) H = H^#` whenever `H ≤ K`.

This is the degenerate case of Peterfalvi's `⋃_{x ∈ K^#} C_H(x)^#` construction (8.10): the union
is only informative when the index subgroup `K` is *smaller* than the host `H`.  It specialises to
`typePA_eq_sharpSubgroup_derivedInG` (`K = M`, `H = M'`) and, in the type-`P₁` regime where
`M_σ = M'`, to the `typePACore`/`typePA` bridge (`K = H = M'`; see
`OddOrder.Peterfalvi.S10.typePACore_eq_typePA_of_isTypeP1`). -/
theorem centralizerSupport_sharpSubgroup_of_le {K H : Subgroup G} (hHK : H ≤ K) :
    centralizerSupport (sharpSubgroup K) H = sharpSubgroup H := by
  ext y
  simp only [centralizerSupport, sharpSubgroup, Set.mem_ofPred_eq, Set.mem_sdiff_singleton]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, y, ⟨hHK h1, h2⟩,
      Subgroup.mem_centralizer_iff.mpr fun g hg => by
        rw [Set.mem_singleton_iff] at hg; subst hg; rfl⟩

/-- **The type-`P` support is the sharp of the derived subgroup**: `A(M) = (M')#`.

`typePA M = centralizerSupport (M#) M'` is by definition `{y ∈ M' | y ≠ 1 ∧ ∃ x ∈ M#, y ∈ C_G(x)}`,
but the centralizer condition is vacuous on `(M')#`: every `y ∈ (M')# ⊆ M#` centralizes itself
(`x = y`).  Hence `A(M) = (M')# = sharpSubgroup (derivedInG M)`, the sharp of the **normal**
subgroup
`M' = derivedInG M ⊴ M`.  This is the `A = H#` shape (with `H = M'`) that Peterfalvi (10.8) needs to
apply the (7.6)/(7.8.b) coherence norm estimate to `(M, A(M))`.

**Caveat (issue 9008, settled by the 9163 hub ruling)**: `typePA = (M')#` equals Peterfalvi's
actual `A(M)` only for type `P₁` (BG III/IV/V, where `M_σ = M'`).  Peterfalvi (8.10) indexes over
the **core** `M_s^# = M_σ^#` (`A(M) = ⋃_{x∈M_σ^#} C_{M'}(x)^#`), so for type `P₂` (type II,
`M_σ ⊊ M'`) the true `A(M)` is the strictly smaller `(M')# ∩ hatMsigma`, excluding the
Frobenius-complement points `U^#`.

**The book-literal `A(M)`, valid for every type, is
`OddOrder.Peterfalvi.S10.typePACore`** (`S10_StructureSetup.lean`); this `typePA` is the
`P₁`-regime specialisation, kept because that is the regime all of its consumers use
(`dadeSupportHypotheses_typeP` carries an `IsTypeP1` hypothesis).  The two agree on `P₁` by
`typePACore_eq_typePA_of_isTypeP1`.  `typePA` may not be used for type `P₂` (= type II). -/
theorem typePA_eq_sharpSubgroup_derivedInG (M : Subgroup G) (data : TypePData M) :
    typePA M data = sharpSubgroup (derivedInG M) :=
  centralizerSupport_sharpSubgroup_of_le (Subgroup.map_subtype_le _)

/-- **`W = W₁·W₂` factorization**: every element of `W = W₁ ⊔ W₂` (cyclic, hence commutative)
is a product `v₁ · v₂` with `v₁ ∈ W₁`, `v₂ ∈ W₂` — the coprod of the two inclusions surjects
onto `W`.  No disjointness or coprimality is needed. -/
theorem TypePData.exists_mul_eq_of_mem_W {M : Subgroup G} (data : TypePData M)
    {v : G} (hv : v ∈ data.W) :
    ∃ v₁ ∈ data.W1, ∃ v₂ ∈ data.W2, v₁ * v₂ = v := by
  have := data.W_cyclic
  let : CommGroup ↥data.W := IsCyclic.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  set f := (Subgroup.inclusion hW1le).coprod (Subgroup.inclusion hW2le) with hf
  have hrange : ∀ w : ↥data.W, w ∈ f.range := by
    have hsub : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W ≤ f.range := by
      refine sup_le ?_ ?_
      · rw [← Subgroup.inclusion_range hW1le]
        rintro x ⟨y, rfl⟩
        exact ⟨(y, 1), by simp [hf, MonoidHom.coprod_apply]⟩
      · rw [← Subgroup.inclusion_range hW2le]
        rintro x ⟨y, rfl⟩
        exact ⟨(1, y), by simp [hf, MonoidHom.coprod_apply]⟩
    intro w
    refine hsub ?_
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq]
    exact Subgroup.mem_subgroupOf.mpr w.2
  obtain ⟨⟨y₁, y₂⟩, hy⟩ := hrange ⟨v, hv⟩
  refine ⟨(y₁ : G), y₁.2, (y₂ : G), y₂.2, ?_⟩
  have := congrArg (Subtype.val (p := fun x => x ∈ data.W)) hy
  simpa [hf, MonoidHom.coprod_apply] using this

end OddOrder.GroupTheory


