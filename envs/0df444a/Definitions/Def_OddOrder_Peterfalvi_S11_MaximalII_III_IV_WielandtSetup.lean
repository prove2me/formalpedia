-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:29:57.981382+00:00
-- url     : https://prove2.me/theorems/f2fb247d-ccfb-4649-babb-fe13360175e5
-- title:
--   Peterfalvi (9.1)–(9.4): Wielandt's fixed-point formula, type II–IV setup, Frobenius action
-- statement:
--   The Wielandt fixed-point formula and the type II–IV setup in Peterfalvi, *Character Theory for the Odd Order Theorem*, split from the former monolithic §11 file. It defines the conjugation action of $UW_1$ on $H=M_F$ descended to a quotient, the elementary-abelian seed of Peterfalvi (9.4), and the data `ChiefFactorData` for the chief factor $H/H_0$ selected in (9.4).
--
--   Main declarations: `typeP_quotientCoprimeAction`; `ChiefFactorData` (Data for the chief factor `H/H_0` selected in Peterfalvi (9.4)); `exists_chiefFactor_seed` (Peterfalvi (9.4), the elementary-abelian seed (the remaining group-theoretic input)).
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/WielandtSetup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/WielandtSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleStructure
import Definitions.Def_OddOrder_Peterfalvi_S10_CoherenceWiring
import Definitions.Def_OddOrder_GroupTheory_CoprimeAction
import Definitions.Def_OddOrder_GroupTheory_WielandtFixedPoint
import Definitions.Def_OddOrder_GroupTheory_CoprimeFixedPoints
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupTypeConj
import Definitions.Def_OddOrder_GroupTheory_AInvariantPiSubgroups
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Helpers
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_WitnessPGroup
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerLineBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtElabBridge
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordSingleOrbit
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_OrbitOnIrr
import Definitions.Def_OddOrder_Mathlib_SchurZassenhausConj
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetupBasic

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

/-- The fixed subgroup `C_H(K)` of a *normal* subgroup `K ◁ L` under an action `φ : L →* MulAut H`
is `φ`-invariant: `φ` permutes the fixed subgroups `C_H(K)` according to its action on the `K`'s,
and a normal `K` is sent to itself. -/
theorem isAInvariant_fixedSubgroup_of_normal {L H : Type*} [Group L] [Group H]
    (φ : L →* MulAut H) {K : Subgroup L} (hK : K.Normal) :
    IsAInvariant φ (fixedSubgroup φ K) := by
  rw [isAInvariant_iff_smul_mem]
  intro a x hx k hk
  change (φ k) ((φ a) x) = (φ a) x
  have hmem : a⁻¹ * k * a ∈ K := by
    have := hK.conj_mem k hk a⁻¹
    simpa using this
  have hfix : (φ (a⁻¹ * k * a)) x = x := hx _ hmem
  calc (φ k) ((φ a) x)
      = (φ a) ((φ (a⁻¹ * k * a)) x) := by
        simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.apply_inv_self]
    _ = (φ a) x := by rw [hfix]

variable {M : Subgroup G}

/-- The conjugation action of `U W₁` on `H = M_F`, descended to a `U W₁`-invariant quotient
`H̄ = ↥H ⧸ N` (a coprime Frobenius action — the carrier for Wielandt's formula on the chief
factor of (9.4)). -/
noncomputable def typeP_quotientCoprimeAction [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥)
    {N : Subgroup ↥data.H} [N.Normal]
    (hN : IsAInvariant (typeP_conjAction data) N) :
    CoprimeFrobeniusAction ↥(data.U ⊔ data.W1) (↥data.H ⧸ N) where
  U := data.U.subgroupOf (data.U ⊔ data.W1)
  E := data.W1.subgroupOf (data.U ⊔ data.W1)
  frobenius := typeP_uW1_frobenius data hU
  H_solvable := by
    have := (typeP_coprimeAction data hU).H_solvable
    exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N)
  φ := OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN
  coprime_order := Nat.Coprime.coprime_dvd_left (Subgroup.card_quotient_dvd_card N)
    (typeP_coprime_H_uW1 data hU)

/-- A cyclic subgroup `C` of a group of exponent dividing a prime `p` has order dividing `p`:
the generator `g` satisfies `g^p = 1`, so `|C| = orderOf g ∣ p`. -/
theorem card_dvd_prime_of_isCyclic_of_pow {H : Type*} [Group H] {p : ℕ}
    (hexp : ∀ x : H, x ^ p = 1) {C : Subgroup H} (hcyc : IsCyclic ↥C) :
    Nat.card ↥C ∣ p := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgp : g ^ p = 1 := by
    have h := hexp (g : H)
    rw [← Subgroup.coe_pow] at h
    exact Subtype.ext (h.trans (Subgroup.coe_one C).symm)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact orderOf_dvd_of_pow_eq_one hgp

/-- **Chief-factor order via Wielandt's formula** (the arithmetic core of Peterfalvi (9.6),
abstracted from the carrier).  For a coprime Frobenius action `act` (kernel `act.U` normal in `L`,
complement `act.E`) on an elementary abelian `p`-group `K`: if `act` is `L`-irreducible (every
invariant subgroup is `⊥` or `⊤`), `act.U` does not centralize `K` (`fixedByU ≠ ⊤`), the `E`-fixed
points `C_K(E) = fixedByE` are cyclic, and `K ≠ 1`, then `|K| = p^{|E|}` *and* `|C_K(E)| = p`.

`C_K(U) = fixedByU` is `L`-invariant (as `act.U ◁ L`) and `≠ K`, so `= ⊥` by irreducibility;
`|C_K(E)| ∣ p` since `C_K(E)` is cyclic of exponent `p`, and `≠ 1` (else `|K| = |C_K(E)|^{|E|} = 1`
by Wielandt), so `= p`; Wielandt's fixed-point formula then gives `|K| = p^{|E|}`. The
`|C_K(E)| = p`
clause feeds the type III/IV identity `p = |W₂|` (the chief factor's `E`-fixed points are the image
of `W₂`).  This serves both the quotient chief factor `H̄ = ↥H ⧸ N` (`typeP_chiefFactor_card`) and
the irreducible *summand* of the elementary abelian seed in the (9.4) existence proof. -/
theorem coprimeFrobeniusChiefFactor_card {L K : Type*} [Group L] [Group K] [Finite K] [Finite L]
    (act : CoprimeFrobeniusAction L K) (hUnorm : act.U.Normal)
    {p : ℕ} (hp : p.Prime) (hK : IsElementaryAbelian p K)
    (hirr : ∀ J : Subgroup K, IsAInvariant act.φ J → J = ⊥ ∨ J = ⊤)
    (hUntriv : act.fixedByU ≠ ⊤) (hEcyc : IsCyclic ↥act.fixedByE)
    (hK1 : Nat.card K ≠ 1) :
    Nat.card K = p ^ Nat.card ↥act.E ∧ Nat.card ↥act.fixedByE = p := by
  have hUinv : IsAInvariant act.φ act.fixedByU :=
    isAInvariant_fixedSubgroup_of_normal act.φ hUnorm
  have hfixU : act.fixedByU = ⊥ := (hirr _ hUinv).resolve_right hUntriv
  have hdvd : Nat.card ↥act.fixedByE ∣ p := card_dvd_prime_of_isCyclic_of_pow hK.2 hEcyc
  have hcard := coprimeFrobeniusAction_card_eq_prime_pow act hfixU hp hdvd hK1
  refine ⟨hcard, ?_⟩
  have hne : Nat.card ↥act.fixedByE ≠ 1 := fun h => hK1 (by
    have key := wielandt_fixedPoint_trivial_U_fixed act hfixU
    rwa [h, one_pow] at key)
  exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne

/-- **Chief-factor order on an irreducible summand** (the form (9.4)/(9.6) use).  For a coprime
Frobenius action `act` on an elementary abelian `p`-group `V` (kernel `act.U ◁ L`, `C_V(E)` cyclic),
and an `act.φ`-invariant subgroup `S ≠ ⊥` that is `L`-irreducible *inside `V`* (`hirr`) and met
trivially by `C_V(U)` (`hUnc`, so `U` is fixed-point-free on `S`), the order of `S` is `p^{|E|}`,
and `|C_V(E) ⊓ S| = |C_S(E)| = p`.

This is `coprimeFrobeniusChiefFactor_card` transported to the *summand* `S` via the restricted
action `hSinv.restrict` on `↥S`: `S` is elementary abelian (subgroup of `V`); `L`-irreducible
(invariant subgroups of `↥S` correspond, via `S.subtype`, to invariant subgroups of `V` inside `S`);
`U`-noncentral (`C_S(U) = C_V(U) ⊓ S = ⊥ ≠ S`); and `C_S(E) = C_V(E) ⊓ S` is cyclic (subgroup of the
cyclic `C_V(E)`).  Together with the Maschke summand
`exists_aInvariant_irreducible_summand_disjoint`
this furnishes the chief factor `|H̄| = p^q` of Peterfalvi (9.4) once the elementary-abelian seed is
in place. -/
theorem coprimeFrobeniusChiefFactor_card_of_summand
    {L V : Type*} [Group L] [Group V] [Finite V] [Finite L]
    (act : CoprimeFrobeniusAction L V) (hUnorm : act.U.Normal)
    {p : ℕ} (hp : p.Prime) (hV : IsElementaryAbelian p V)
    {S : Subgroup V} (hSinv : IsAInvariant act.φ S) (hSne : S ≠ ⊥)
    (hirr : ∀ K : Subgroup V, IsAInvariant act.φ K → K ≤ S → K = ⊥ ∨ K = S)
    (hUnc : act.fixedByU ⊓ S = ⊥) (hEcyc : IsCyclic ↥act.fixedByE) :
    Nat.card ↥S = p ^ Nat.card ↥act.E ∧
      Nat.card ↥(act.fixedByE ⊓ S : Subgroup V) = p := by
  have hSel : IsElementaryAbelian p ↥S := hV.to_subgroup S
  have hSsolv : Group.IsSolvable ↥S := by
    let : CommGroup ↥S := { (inferInstance : Group ↥S) with mul_comm := hSel.comm }
    infer_instance
  -- the restricted Frobenius action on the summand `↥S`
  let act_S : CoprimeFrobeniusAction L ↥S :=
    { U := act.U
      E := act.E
      frobenius := act.frobenius
      H_solvable := hSsolv
      φ := hSinv.restrict
      coprime_order :=
        Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card S) act.coprime_order }
  -- `L`-irreducibility of `↥S`: invariant subgroups correspond to invariant subgroups of `V ≤ S`.
  have hirr_S : ∀ J : Subgroup ↥S, IsAInvariant act_S.φ J → J = ⊥ ∨ J = ⊤ := by
    intro J hJinv
    rcases hirr (J.map S.subtype) (aInvariant_map_subtype_of_restrict hSinv hJinv)
        (Subgroup.map_subtype_le J) with h | h
    · exact Or.inl (Subgroup.map_injective S.subtype_injective (by rw [h, Subgroup.map_bot]))
    · exact Or.inr (Subgroup.map_injective S.subtype_injective
        (by rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]))
  -- `U` is non-central on `↥S`: `|C_S(U)| = |C_V(U) ⊓ S| = 1 ≠ |S|`.
  have hUntriv_S : act_S.fixedByU ≠ ⊤ := by
    intro htop
    have hc : Nat.card ↥act_S.fixedByU = 1 := by
      have hr := card_fixedSubgroup_restrict (φ := act.φ) (N := S) (X := act.U) hSinv
      rwa [show fixedSubgroup act.φ act.U ⊓ S = ⊥ from hUnc, Subgroup.card_bot] at hr
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
    exact hSne (Subgroup.card_eq_one.mp hc)
  -- `C_S(E) = C_V(E) ⊓ S` is a subgroup of the cyclic `C_V(E)`, hence cyclic.
  have hEcyc_S : IsCyclic ↥act_S.fixedByE := by
    have : IsCyclic ↥(fixedSubgroup act.φ act.E) := hEcyc
    have : IsCyclic ↥(fixedSubgroup act.φ act.E ⊓ S : Subgroup V) :=
      Subgroup.isCyclic_of_le inf_le_left
    have e := Subgroup.equivMapOfInjective
      ((fixedSubgroup act.φ act.E).subgroupOf S) S.subtype S.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at e
    have hcyc : IsCyclic ↥((fixedSubgroup act.φ act.E).subgroupOf S) :=
      isCyclic_of_surjective e.symm e.symm.surjective
    change IsCyclic ↥(fixedSubgroup hSinv.restrict act.E)
    rwa [fixedSubgroup_restrict_eq hSinv]
  have hK1 : Nat.card ↥S ≠ 1 := fun h => hSne (Subgroup.card_eq_one.mp h)
  obtain ⟨hScard, hEcard⟩ :=
    coprimeFrobeniusChiefFactor_card act_S hUnorm hp hSel hirr_S hUntriv_S hEcyc_S hK1
  refine ⟨hScard, ?_⟩
  -- `|C_V(E) ⊓ S| = |C_S(E)| = p` via `card_fixedSubgroup_restrict`.
  have hr := card_fixedSubgroup_restrict (φ := act.φ) (N := S) (X := act.E) hSinv
  rw [show fixedSubgroup hSinv.restrict act.E = act_S.fixedByE from rfl, hEcard] at hr
  exact hr.symm

/-- The `E`-fixed points `C_{H̄}(W₁)` of the quotient chief-factor action are cyclic: they are the
image (under `mk' N`, Isaacs Cor 3.28 `map_fixedSubgroup_eq_fixedSubgroup_quotient`) of the cyclic
`W₂ = C_H(W₁)`.  This is the cyclic-`C_K(E)` hypothesis of `coprimeFrobeniusChiefFactor_card` for
both the chief factor (`typeP_chiefFactor_card`) and the (9.4) existence proof. -/
theorem typeP_quotient_fixedByE_cyclic [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥)
    {N : Subgroup ↥data.H} [N.Normal] (hN : IsAInvariant (typeP_conjAction data) N) :
    IsCyclic ↥(typeP_quotientCoprimeAction data hU hN).fixedByE := by
  set act' := typeP_quotientCoprimeAction data hU hN with hact'
  have hcopHW1 : Nat.Coprime
      (Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1))) (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  have : Group.IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
  have hmap : (fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))).map (QuotientGroup.mk' N) = act'.fixedByE :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient hN hcopHW1 (Or.inr inferInstance)
  have hCHW1 : (fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))).map data.H.subtype = data.W2 := by
    rw [typeP_fixedSubgroup_map data le_sup_right, typeP_H_inf_centralizer_W1]
  have : IsCyclic ↥data.W2 := data.W2_cyclic
  have hcycCHW1 : IsCyclic ↥(fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))) := by
    have e := Subgroup.equivMapOfInjective
      (fixedSubgroup (typeP_conjAction data) (data.W1.subgroupOf (data.U ⊔ data.W1)))
      data.H.subtype data.H.subtype_injective
    rw [hCHW1] at e
    exact isCyclic_of_surjective e.symm e.symm.surjective
  let f := (QuotientGroup.mk' N).comp (fixedSubgroup (typeP_conjAction data)
      (data.W1.subgroupOf (data.U ⊔ data.W1))).subtype
  have hrange : f.range = act'.fixedByE := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hmap
  rw [← hrange]
  exact isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective

/-- **Peterfalvi (9.4) input**: `U` does not centralize `H = M_F` (in action form): the fixed
subgroup `C_H(U)` of the Frobenius kernel is a *proper* subgroup, `C_H(U) ≠ H`.  This is the
non-centrality that the (9.4) chief factor selection requires; it is the action-level reading of
Peterfalvi (8.5.b) (`typeP_U_not_centralizes_H`): a nontrivial `U` cannot centralize `H`. -/
theorem typeP_U_noncentral_on_H [Finite G] (data : TypePData M) (hU : data.U ≠ ⊥) :
    (typeP_coprimeAction data hU).fixedByU ≠ ⊤ := by
  intro htop
  refine typeP_U_not_centralizes_H data hU (Subgroup.le_centralizer_iff.mp ?_)
  have key := typeP_card_fixedSubgroup data (le_sup_left : data.U ≤ data.U ⊔ data.W1)
  rw [show fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1))
      = (typeP_coprimeAction data hU).fixedByU from rfl, htop,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at key
  have heq : data.H ⊓ Subgroup.centralizer (data.U : Set G) = data.H :=
    Subgroup.eq_of_le_of_card_ge inf_le_left key.le
  exact heq ▸ inf_le_right

/-- A surjective homomorphic image of an elementary abelian `p`-group is elementary abelian. -/
private theorem isElementaryAbelian_of_surjective {A B : Type*} [Group A] [Group B] {p : ℕ}
    {f : A →* B} (hf : Function.Surjective f) (hA : IsElementaryAbelian p A) :
    IsElementaryAbelian p B := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, hA.comm]
  · obtain ⟨a, rfl⟩ := hf x
    rw [← map_pow, hA.pow_eq_one, map_one]

/-- **Peterfalvi (9.4), the chief-factor kernel** (given the elementary-abelian seed `N₀`).  From a
`U W₁`-invariant normal `N₀ ◁ H = M_F` with `H/N₀` elementary abelian `p` on which `U` is
non-central
(`hUnc`), the operator Maschke summand and the summand Wielandt order produce a chief-factor kernel
`N ⊇ N₀` with `|H/N| = p^q` (the chief factor `|H̄|`) and `p ∣ |W₂|`.

`V = H/N₀ = S ⊕ W` (Maschke), `S` irreducible with `U` fixed-point-free (`C_V(U) ⊓ S = ⊥`), so
`|S| = p^q` and `|C_V(W₁) ⊓ S| = p` (`coprimeFrobeniusChiefFactor_card_of_summand`).  Take
`N = W.comap (mk' N₀)`: then `H/N ≅ V/W ≅ S`, so `|H/N| = W.index = |S| = p^q`; and
`p = |C_V(W₁) ⊓ S| ∣ |C_V(W₁)| ∣ |W₂|` since `C_V(W₁)` is the image of `W₂`. -/
theorem exists_chiefFactor_kernel [Finite G] {M : Subgroup G} (data : TypePData M)
    (hU : data.U ≠ ⊥) {p : ℕ} (hp : p.Prime) {N₀ : Subgroup ↥data.H} [N₀.Normal]
    (hN₀ : IsAInvariant (typeP_conjAction data) N₀)
    (hpe : IsElementaryAbelian p (↥data.H ⧸ N₀))
    (hUnc : (typeP_quotientCoprimeAction data hU hN₀).fixedByU ≠ ⊤) :
    ∃ N : Subgroup ↥data.H, N₀ ≤ N ∧ ∃ (hNnorm : N.Normal)
      (hNinv : IsAInvariant (typeP_conjAction data) N),
      Nat.card (↥data.H ⧸ N) = p ^ Nat.card ↥data.W1 ∧ p ∣ Nat.card ↥data.W2 ∧
        (letI := hNnorm
         IsElementaryAbelian p (↥data.H ⧸ N) ∧
           (∀ J : Subgroup (↥data.H ⧸ N),
               IsAInvariant (quotientMulAutHom hNinv) J → J = ⊥ ∨ J = ⊤) ∧
           fixedSubgroup (quotientMulAutHom hNinv)
             (data.U.subgroupOf (data.U ⊔ data.W1)) ≠ ⊤) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set act_V := typeP_quotientCoprimeAction data hU hN₀ with hact_V
  have hUnorm : act_V.U.Normal := (typeP_uW1_frobenius data hU).isNormal
  have hCinv : IsAInvariant act_V.φ act_V.fixedByU :=
    isAInvariant_fixedSubgroup_of_normal act_V.φ hUnorm
  -- Operator Maschke: an irreducible summand `S` with `U`-noncentral complement structure.
  obtain ⟨S, W, hSinv, hWinv, hSW_inf, hSW_sup, hSne, hirr, hCS⟩ :=
    OddOrder.BG.Ch1_Preliminary.exists_aInvariant_irreducible_summand_disjoint hpe
      act_V.coprime_order.symm hCinv hUnc
  have hEcyc : IsCyclic ↥act_V.fixedByE := typeP_quotient_fixedByE_cyclic data hU hN₀
  obtain ⟨hScard, hCSEcard⟩ :=
    coprimeFrobeniusChiefFactor_card_of_summand act_V hUnorm hp hpe hSinv hSne hirr hCS hEcyc
  have hEcard : Nat.card ↥act_V.E = Nat.card ↥data.W1 := by
    change Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1)) = Nat.card ↥data.W1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hScard' : Nat.card ↥S = p ^ Nat.card ↥data.W1 := by rw [hScard, hEcard]
  -- `V` is abelian, so all its subgroups are normal.
  have hSnorm : S.Normal := ⟨fun n hn g => by
    rwa [show g * n * g⁻¹ = n by rw [hpe.comm g n]; group]⟩
  have hWnorm : W.Normal := ⟨fun n hn g => by
    rwa [show g * n * g⁻¹ = n by rw [hpe.comm g n]; group]⟩
  -- `S` complements `W` in `V`, so `W.index = |S|`.
  have hcompl : Subgroup.IsComplement' S W :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hSW_inf)
      (by rw [← Subgroup.normal_mul, hSW_sup, Subgroup.coe_top])
  set N := W.comap (QuotientGroup.mk' N₀) with hNdef
  -- `N₀ ≤ N`: `N₀ = ker (mk' N₀) ≤ comap _ W`.
  have hN₀leN : N₀ ≤ N := by
    intro x hx
    rw [hNdef, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact W.one_mem
  -- `N` is `U W₁`-invariant (preimage of the invariant `W`); hence normal.
  have hNinv : IsAInvariant (typeP_conjAction data) N :=
    OddOrder.BG.Ch1_Preliminary.isAInvariant_comap_mk' hN₀ hWinv
  have hNnorm : N.Normal := inferInstance
  have hNmapW : N.map (QuotientGroup.mk' N₀) = W :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N₀) W
  -- `|H/N| = W.index = |S| = p^q`.
  have hcardN : Nat.card (↥data.H ⧸ N) = p ^ Nat.card ↥data.W1 := by
    change N.index = p ^ Nat.card ↥data.W1
    rw [hNdef, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N₀),
      hcompl.index_eq_card, hScard']
  -- `p ∣ |W₂|`: `p = |C_V(W₁) ⊓ S| ∣ |C_V(W₁)| = |act_V.fixedByE| ∣ |W₂|`.
  have hpW2 : p ∣ Nat.card ↥data.W2 := by
    have h1 : p ∣ Nat.card ↥act_V.fixedByE :=
      hCSEcard ▸ Subgroup.card_dvd_of_le inf_le_left
    refine h1.trans ?_
    set CHW1 := fixedSubgroup (typeP_conjAction data) (data.W1.subgroupOf (data.U ⊔ data.W1))
      with hCHW1def
    have hcopHW1 : Nat.Coprime
        (Nat.card ↥(data.W1.subgroupOf (data.U ⊔ data.W1))) (Nat.card ↥data.H) :=
      (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have : Group.IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
    have hmap : CHW1.map (QuotientGroup.mk' N₀) = act_V.fixedByE :=
      map_fixedSubgroup_eq_fixedSubgroup_quotient hN₀ hcopHW1 (Or.inr inferInstance)
    have hCHW1card : Nat.card ↥CHW1 = Nat.card ↥data.W2 := by
      have hCHW1eq : CHW1.map data.H.subtype = data.W2 := by
        rw [hCHW1def, typeP_fixedSubgroup_map data le_sup_right, typeP_H_inf_centralizer_W1]
      rw [← hCHW1eq]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective CHW1 data.H.subtype data.H.subtype_injective).toEquiv
    rw [← hmap, ← hCHW1card]
    exact Subgroup.card_map_dvd CHW1 (QuotientGroup.mk' N₀)
  -- shared coprimality / solvability for the fixed-point and quotient-action lemmas.
  have hcopU : Nat.Coprime (Nat.card ↥(data.U.subgroupOf (data.U ⊔ data.W1)))
      (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  have hHsolv : Group.IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
  -- **Elementary abelian**: `H/N ≅ (H/N₀)/W` is a quotient of the elementary abelian `V = H/N₀`.
  have hEA : IsElementaryAbelian p (↥data.H ⧸ N) := by
    have : (N.map (QuotientGroup.mk' N₀)).Normal := hNmapW ▸ hWnorm
    exact IsElementaryAbelian.of_mulEquiv
      (QuotientGroup.quotientQuotientEquivQuotient N₀ N hN₀leN)
      (isElementaryAbelian_of_surjective
        (QuotientGroup.mk'_surjective (N.map (QuotientGroup.mk' N₀))) hpe)
  -- **`C_V(U) ≤ W`**: a `U`-fixed `x = a·b` (`a ∈ S`, `b ∈ W`) has both components `U`-fixed, and
  -- `C_S(U) = C_V(U) ⊓ S = ⊥` kills `a`.
  have hCsubW : act_V.fixedByU ≤ W := by
    let : CommGroup (↥data.H ⧸ N₀) :=
      { (inferInstance : Group (↥data.H ⧸ N₀)) with mul_comm := hpe.comm }
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hSW_sup ▸ Subgroup.mem_top x)
    have hxfix : a * b ∈ fixedSubgroup act_V.φ act_V.U := hx
    have hafix : a ∈ act_V.fixedByU := by
      change a ∈ fixedSubgroup act_V.φ act_V.U
      rw [mem_fixedSubgroup]
      intro l hl
      have hxl : act_V.φ l a * act_V.φ l b = a * b := by
        have hf := (mem_fixedSubgroup.mp hxfix) l hl
        rwa [map_mul] at hf
      have hla : act_V.φ l a ∈ S := hSinv.smul_mem l ha
      have hlb : act_V.φ l b ∈ W := hWinv.smul_mem l hb
      have hdiv : act_V.φ l a / a = b / act_V.φ l b := by
        rw [div_eq_div_iff_mul_eq_mul, hxl]; exact mul_comm a b
      have hmem : act_V.φ l a / a ∈ S ⊓ W := ⟨S.div_mem hla ha, hdiv ▸ W.div_mem hb hlb⟩
      rw [hSW_inf, Subgroup.mem_bot, div_eq_one] at hmem
      exact hmem
    have ha1 : a = 1 := by
      have hmem : a ∈ act_V.fixedByU ⊓ S := ⟨hafix, ha⟩
      rw [hCS, Subgroup.mem_bot] at hmem
      exact hmem
    subst ha1
    simpa using hb
  -- `C_H(U) ≤ N` (preimage of `C_V(U) ≤ W`), so `U` is fixed-point-free on `H/N`.
  set CHU := fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1))
    with hCHUdef
  have hCHU_V : CHU.map (QuotientGroup.mk' N₀) = act_V.fixedByU :=
    map_fixedSubgroup_eq_fixedSubgroup_quotient hN₀ hcopU (Or.inr inferInstance)
  have hCHUleN : CHU ≤ N := by
    rw [hNdef, ← Subgroup.map_le_iff_le_comap, hCHU_V]; exact hCsubW
  have hNonc : fixedSubgroup (quotientMulAutHom hNinv)
      (data.U.subgroupOf (data.U ⊔ data.W1)) ≠ ⊤ := by
    have hfixN : CHU.map (QuotientGroup.mk' N) =
        fixedSubgroup (quotientMulAutHom hNinv) (data.U.subgroupOf (data.U ⊔ data.W1)) :=
      map_fixedSubgroup_eq_fixedSubgroup_quotient hNinv hcopU (Or.inr inferInstance)
    have hbot : fixedSubgroup (quotientMulAutHom hNinv)
        (data.U.subgroupOf (data.U ⊔ data.W1)) = ⊥ := by
      rw [← hfixN, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']; exact hCHUleN
    rw [hbot]
    have : Nontrivial (↥data.H ⧸ N) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardN]
      exact Nat.one_lt_pow Nat.card_pos.ne' hp.one_lt
    exact bot_ne_top
  -- **`U W₁`-irreducibility of `H̄ = H/N`** (the chief factor): pull `J` back to `J̃ ◁ H`
  -- (`N ≤ J̃`), push to `J̄ ≤ V` (`W ≤ J̄`), and split on `J̄ ⊓ S ∈ {⊥, S}`.
  have hIrr : ∀ J : Subgroup (↥data.H ⧸ N),
      IsAInvariant (quotientMulAutHom hNinv) J → J = ⊥ ∨ J = ⊤ := by
    intro J hJinv
    set Jt := J.comap (QuotientGroup.mk' N) with hJtdef
    have hJtinv : IsAInvariant (typeP_conjAction data) Jt :=
      OddOrder.BG.Ch1_Preliminary.isAInvariant_comap_mk' hNinv hJinv
    have hNleJt : N ≤ Jt := by
      intro x hx
      rw [hJtdef, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact J.one_mem
    set Jb := Jt.map (QuotientGroup.mk' N₀) with hJbdef
    have hJbinv : IsAInvariant act_V.φ Jb :=
      OddOrder.BG.Ch1_Preliminary.isAInvariant_map_mk' hN₀ hJtinv
    have hWleJb : W ≤ Jb := by rw [hJbdef, ← hNmapW]; exact Subgroup.map_mono hNleJt
    have hScapinv : IsAInvariant act_V.φ (Jb ⊓ S) := by
      rw [isAInvariant_iff_smul_mem]
      intro l x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hJbinv.smul_mem l hx.1, hSinv.smul_mem l hx.2⟩
    have hcap : Jb ⊓ S = ⊥ ∨ Jb ⊓ S = S := hirr (Jb ⊓ S) hScapinv inf_le_right
    have hJtcomap : Jt = Jb.comap (QuotientGroup.mk' N₀) := by
      rw [hJbdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
        sup_eq_left.mpr (hN₀leN.trans hNleJt)]
    have hJmap : J = Jt.map (QuotientGroup.mk' N) := by
      rw [hJtdef]
      exact (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) J).symm
    rcases hcap with hbotS | htopS
    · -- `J̄ ⊓ S = ⊥`: the component argument gives `J̄ = W`, so `J̃ = N` and `J = ⊥`.
      refine Or.inl ?_
      have hJbleW : Jb ≤ W := by
        let : CommGroup (↥data.H ⧸ N₀) :=
          { (inferInstance : Group (↥data.H ⧸ N₀)) with mul_comm := hpe.comm }
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp (hSW_sup ▸ Subgroup.mem_top x)
        have haJb : a ∈ Jb := by
          have ha_eq : a = a * b / b := by rw [mul_div_assoc, div_self', mul_one]
          rw [ha_eq]; exact Jb.div_mem hx (hWleJb hb)
        have ha1 : a = 1 := by
          have hmem : a ∈ Jb ⊓ S := ⟨haJb, ha⟩
          rw [hbotS, Subgroup.mem_bot] at hmem
          exact hmem
        subst ha1
        simpa using hb
      have hJbW : Jb = W := le_antisymm hJbleW hWleJb
      have hJtN : Jt = N := by rw [hJtcomap, hJbW]
      rw [hJmap, hJtN]
      exact N.map_eq_bot_iff.mpr (le_of_eq (QuotientGroup.ker_mk' N).symm)
    · -- `J̄ ⊓ S = S`: then `S ⊔ W ≤ J̄`, so `J̄ = ⊤`, `J̃ = ⊤`, `J = ⊤`.
      refine Or.inr ?_
      have hSleJb : S ≤ Jb := htopS ▸ inf_le_left
      have hJbtop : Jb = ⊤ := top_le_iff.mp (hSW_sup ▸ sup_le hSleJb hWleJb)
      have hJttop : Jt = ⊤ := by rw [hJtcomap, hJbtop, Subgroup.comap_top]
      rw [hJmap, hJttop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  exact ⟨N, hN₀leN, hNnorm, hNinv, hcardN, hpW2, hEA, hIrr, hNonc⟩

/-- **`M`-normality of the chief-factor kernel image.**  For a `U W₁`-invariant normal subgroup
`N ◁ H = M_F`, its image `H₀ = N.map H.subtype` in `G` is normalized by all of `M`.  Indeed
`M = H ⊔ U ⊔ W₁` (the `M' = H ⋊ U`, `M = M' ⋊ W₁` complement splittings), `H` normalizes `H₀`
(`N ◁ H`, via `Subgroup.le_normalizer_map`), and `U W₁` normalizes `H₀` (`N` is `U W₁`-invariant:
conjugation by `g ∈ U W₁` is `typeP_conjAction` and preserves `N`). -/
theorem typeP_aInvariantNormal_le_normalizer [Finite G] {M : Subgroup G} (data : TypePData M)
    {N : Subgroup ↥data.H} [hNn : N.Normal] (hN : IsAInvariant (typeP_conjAction data) N) :
    M ≤ Subgroup.normalizer ((N.map data.H.subtype : Subgroup G) : Set G) := by
  -- `M ≤ (H ⊔ U) ⊔ W₁`.
  have hM1 : M ≤ derivedInG M ⊔ data.W1 := by
    have hsup := data.M_complement.sup_eq_top
    rw [← Subgroup.subgroupOf_sup (derivedInG_le_self M) data.W1_le] at hsup
    exact Subgroup.subgroupOf_eq_top.mp hsup
  have hderiv : derivedInG M = data.H ⊔ data.U := by
    rw [data.derivedInG_eq_fitting_sup_U, ← data.H_eq]
  have hM2 : M ≤ (data.H ⊔ data.U) ⊔ data.W1 := hderiv ▸ hM1
  -- `H` normalizes `H₀` (`N ◁ H`): `H = subtype '' (normalizer N = ⊤) ≤ normalizer (image)`.
  have hH_norm : data.H ≤ Subgroup.normalizer ((N.map data.H.subtype : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := N) data.H.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr hNn, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  -- `U W₁` normalizes `H₀`: conjugation by `g ∈ U W₁` is `typeP_conjAction`, which preserves `N`.
  have hconj : ∀ (l : ↥(data.U ⊔ data.W1)) {m : ↥data.H}, m ∈ N →
      (l : G) * data.H.subtype m * (l : G)⁻¹ ∈ N.map data.H.subtype := fun l m hm =>
    ⟨typeP_conjAction data l m, hN.smul_mem l hm, typeP_conjAction_apply data l m⟩
  have hUW1_norm :
      data.U ⊔ data.W1 ≤ Subgroup.normalizer ((N.map data.H.subtype : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    rintro h
    refine ⟨fun ⟨m, hm, hval⟩ => hval ▸ hconj ⟨g, hg⟩ hm, fun hh => ?_⟩
    obtain ⟨m, hm, hval⟩ := hh
    have key := hconj ⟨g, hg⟩⁻¹ hm
    have hE : ((⟨g, hg⟩ : ↥(data.U ⊔ data.W1))⁻¹ : G) * data.H.subtype m
        * (((⟨g, hg⟩ : ↥(data.U ⊔ data.W1))⁻¹ : G))⁻¹ = h := by
      rw [hval]; change g⁻¹ * (g * h * g⁻¹) * (g⁻¹ : G)⁻¹ = h; group
    exact hE ▸ key
  exact hM2.trans (sup_le (sup_le hH_norm (le_sup_left.trans hUW1_norm))
    (le_sup_right.trans hUW1_norm))

/-- A subgroup containing a Sylow `p`-subgroup for every prime `p` is the whole group: its order is
divisible by every maximal prime power `p^{v_p(|G|)} = |Sylow_p|`, hence by `|G|`. -/
theorem eq_top_of_forall_sylow_le {Γ : Type*} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p Γ), (↑P : Subgroup Γ) ≤ K) : K = ⊤ := by
  refine Subgroup.eq_top_of_card_eq K
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card K) ?_)
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hdvd : p ^ (Nat.card Γ).factorization p ∣ Nat.card ↥K := by
      have := Subgroup.card_dvd_of_le (h p (default : Sylow p Γ))
      rwa [Sylow.card_eq_multiplicity] at this
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- In a finite **nilpotent** group `H`, a Sylow `p`-subgroup `P` (for a prime `p ∣ |H|`) has a
**characteristic complement** `Q` — the `p`-complement `⨆_{q ≠ p} O_q(H)`.  Each `O_q = opCore q H`
is characteristic; their join is characteristic; the `O_q` have pairwise coprime order hence are
independent (so `O_p` is disjoint from the join of the others); and they jointly generate `H`
(nilpotent), so `Q` complements the normal Sylow `O_p = ↑P`.  Characteristic ⟹ both `Q.Normal`
and (for any operator action) `IsAInvariant`, which is what the (9.4) seed needs. -/
theorem exists_characteristic_complement_to_sylow_of_nilpotent
    {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    {p : ℕ} [Fact p.Prime] (P : Sylow p H) (hp_mem : p ∈ (Nat.card H).primeFactors) :
    ∃ Q : Subgroup H, Q.Characteristic ∧ Subgroup.IsComplement' (↑P : Subgroup H) Q := by
  classical
  set O : (Nat.card H).primeFactors → Subgroup H :=
    fun q => OddOrder.Isaacs.Ch01.opCore (q : ℕ) H with hOdef
  -- The `opCore`'s have pairwise coprime order, hence are independent.
  have hindep : iSupIndep O := by
    apply OddOrder.Isaacs.Ch01.iSupIndep_of_coprime_card_of_normal O
    intro i j hij
    have : Fact (i : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors i.2⟩
    have : Fact (j : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors j.2⟩
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    exact IsPGroup.coprime_card_of_ne (i : ℕ) (j : ℕ) hne _ _
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (i : ℕ) H)
      (OddOrder.Isaacs.Ch01.opCore_isPGroup (j : ℕ) H)
  -- `↑P = O ⟨p, hp_mem⟩` (a normal Sylow is the `p`-core).
  have hPnorm : (↑P : Subgroup H).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  set i₀ : (Nat.card H).primeFactors := ⟨p, hp_mem⟩ with hi₀
  have hPeq : (↑P : Subgroup H) = O i₀ := OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPnorm
  -- The join of all `opCore`'s is `⊤` (nilpotent: Sylows generate, and each = its `p`-core).
  have htop : (⨆ q, O q) = ⊤ := by
    have hrw : (⨆ q, O q)
        = ⨆ q : (Nat.card H).primeFactors, ((default : Sylow (q : ℕ) H) : Subgroup H) :=
      iSup_congr fun q => by
        have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
        exact (OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal default
          (OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent default)).symm
    rw [hrw]; exact OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent H
  refine ⟨⨆ (j) (_ : j ≠ i₀), O j, ?_, ?_⟩
  · -- characteristic: join of characteristic `opCore`'s.
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    simp_rw [Subgroup.map_iSup]
    exact iSup_congr fun j => iSup_congr fun _ =>
      Subgroup.characteristic_iff_map_eq.mp (OddOrder.Isaacs.Ch01.opCore.characteristic (j : ℕ) H) φ
  · -- complement: disjoint (independence) + join `⊤`.
    rw [hPeq]
    have hdisj : Disjoint (O i₀) (⨆ (j) (_ : j ≠ i₀), O j) := (iSupIndep_def.mp hindep) i₀
    have hsup : O i₀ ⊔ (⨆ (j) (_ : j ≠ i₀), O j) = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← htop]
      refine iSup_le fun j => ?_
      by_cases hj : j = i₀
      · exact hj ▸ le_sup_left
      · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i₀) => O j) j hj)
    exact Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Peterfalvi (9.4), the elementary-abelian seed** (the remaining group-theoretic input).
There is a `U W₁`-invariant normal subgroup `N₀ ◁ H = M_F` with `H/N₀` elementary abelian `p`
on which `U` is non-central (`C_H(U) ⊔ N₀ ≠ H`, action-free form).

*Proof.* `H = M_F` is nilpotent and `U` does not centralise it (`typeP_U_noncentral_on_H`).  Since
`C_H(U) ≠ ⊤`, `eq_top_of_forall_sylow_le` produces a Sylow `p`-subgroup `P` with `↑P ⊄ C_H(U)`.  As
`H` is nilpotent, `P = O_p(H)` is characteristic and has a characteristic `p`-complement `Q`
(`exists_characteristic_complement_to_sylow_of_nilpotent`), so `B := H/Q ≅ P` is a `p`-group.  Take
`N₀ = (mk' Q)⁻¹ (Φ(B))`: it is normal, `A`-invariant (`isAInvariant_comap_mk'` + `Φ(B)`
characteristic), and `H/N₀ ≅ B/Φ(B)` is elementary abelian `p`
(`IsPGroup.quotient_frattini_isElementaryAbelian`).  If `C_H(U) ⊔ N₀ = ⊤`, projecting to `B` gives
`C_B(U) ⊔ Φ(B) = ⊤`, so `C_B(U) = ⊤` by the Frattini non-generating property
(`frattini_nongenerating`); then for `x ∈ P`, `(φ l x) x⁻¹ ∈ P ⊓ Q = ⊥`, i.e. `↑P ≤ C_H(U)`,
contradicting the choice of `P`. -/
theorem exists_chiefFactor_seed [Finite G] {M : Subgroup G} (data : TypePData M) (hU : data.U ≠ ⊥) :
    ∃ (p : ℕ) (N₀ : Subgroup ↥data.H) (_ : N₀.Normal), p.Prime ∧
      IsAInvariant (typeP_conjAction data) N₀ ∧
      IsElementaryAbelian p (↥data.H ⧸ N₀) ∧
      fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1)) ⊔ N₀ ≠ ⊤ := by
  classical
  -- `H = M_F` is nilpotent.
  have hHnil : Group.IsNilpotent ↥data.H := by
    rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
  set CU := fixedSubgroup (typeP_conjAction data) (data.U.subgroupOf (data.U ⊔ data.W1)) with hCU
  -- `U` does not centralise `H`: `C_H(U) = CU ≠ ⊤`.
  have hCUtop : CU ≠ ⊤ := typeP_U_noncentral_on_H data hU
  -- A Sylow `p`-subgroup `P` of `H` with `U` non-central on it (`↑P ⊄ CU`).
  obtain ⟨p, hpfact, P, hP_not⟩ :
      ∃ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p ↥data.H),
        ¬ ((↑P : Subgroup ↥data.H) ≤ CU) := by
    by_contra hcon
    push Not at hcon
    exact hCUtop (eq_top_of_forall_sylow_le hcon)
  have := hpfact
  have hp : p.Prime := hpfact.out
  -- `↑P ≠ ⊥` (else `↑P ≤ CU`), so `p ∣ |H|`, i.e. `p ∈ primeFactors |H|`.
  have hPbot : (↑P : Subgroup ↥data.H) ≠ ⊥ := fun h => hP_not (h ▸ bot_le)
  have hp_mem : p ∈ (Nat.card ↥data.H).primeFactors := by
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, Nat.card_pos.ne'⟩
    by_contra hpdvd
    refine hPbot (Subgroup.eq_bot_of_card_eq _ ?_)
    rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hpdvd, pow_zero]
  -- The characteristic `p`-complement `Q` (so `H = P × Q` internally).
  obtain ⟨Q, hQchar, hQcompl⟩ :=
    exists_characteristic_complement_to_sylow_of_nilpotent P hp_mem
  have : Q.Characteristic := hQchar
  have : Q.Normal := inferInstance
  have hQinv : IsAInvariant (typeP_conjAction data) Q :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (typeP_conjAction data)
  -- `↑P` is characteristic (`= O_p(H)`), hence `A`-invariant.
  have hPnorm : (↑P : Subgroup ↥data.H).Normal :=
    OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  have hPchar : (↑P : Subgroup ↥data.H).Characteristic := by
    rw [OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPnorm]; infer_instance
  have hPinv : IsAInvariant (typeP_conjAction data) (↑P : Subgroup ↥data.H) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (typeP_conjAction data)
  -- `B = H/Q` is a `p`-group (`|B| = [H:Q] = |P| = p^k`).
  have hBpgroup : IsPGroup p (↥data.H ⧸ Q) :=
    IsPGroup.of_card (by
      calc Nat.card (↥data.H ⧸ Q) = Nat.card (↑P : Subgroup ↥data.H) := hQcompl.index_eq_card
        _ = p ^ (Nat.card ↥data.H).factorization p := Sylow.card_eq_multiplicity P)
  -- `N₀ = (mk' Q)⁻¹ Φ(B)`: normal, `A`-invariant, and `H/N₀ ≅ B/Φ(B)` el. abelian `p`.
  set N₀ := Subgroup.comap (QuotientGroup.mk' Q) (frattini (↥data.H ⧸ Q)) with hN₀
  have : N₀.Normal := inferInstance
  have hN₀inv : IsAInvariant (typeP_conjAction data) N₀ :=
    OddOrder.BG.Ch1_Preliminary.isAInvariant_comap_mk' hQinv
      (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (quotientMulAutHom hQinv))
  have hQleN₀ : Q ≤ N₀ := by
    intro x hx
    rw [hN₀, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hN₀map : N₀.map (QuotientGroup.mk' Q) = frattini (↥data.H ⧸ Q) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) _
  have hEA : IsElementaryAbelian p (↥data.H ⧸ N₀) := by
    have : (N₀.map (QuotientGroup.mk' Q)).Normal :=
      (inferInstance : N₀.Normal).map _ (QuotientGroup.mk'_surjective Q)
    exact IsElementaryAbelian.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hN₀map).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient Q N₀ hQleN₀))
      (OddOrder.GroupTheory.IsPGroup.quotient_frattini_isElementaryAbelian hBpgroup)
  refine ⟨p, N₀, inferInstance, hp, hN₀inv, hEA, ?_⟩
  -- Non-centrality `CU ⊔ N₀ ≠ ⊤`.
  intro htop
  have hcopU : Nat.Coprime (Nat.card ↥(data.U.subgroupOf (data.U ⊔ data.W1)))
      (Nat.card ↥data.H) :=
    (typeP_coprime_H_uW1 data hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
  have : Group.IsSolvable ↥data.H := (typeP_coprimeAction data hU).H_solvable
  -- Project to `B`: `C_B(U) ⊔ Φ(B) = ⊤`, so by the Frattini argument `C_B(U) = ⊤`.
  have hCUmap := map_fixedSubgroup_eq_fixedSubgroup_quotient
    (φ := typeP_conjAction data) (N := Q) hQinv hcopU (Or.inr inferInstance)
  have hproj : fixedSubgroup (quotientMulAutHom hQinv)
      (data.U.subgroupOf (data.U ⊔ data.W1)) ⊔ frattini (↥data.H ⧸ Q) = ⊤ := by
    rw [← hCUmap, ← hN₀map, ← Subgroup.map_sup, ← hCU, htop,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
  have hfix := frattini_nongenerating hproj
  -- Hence `↑P ≤ CU`, contradicting `hP_not`.
  apply hP_not
  intro x hxP
  rw [hCU, mem_fixedSubgroup]
  intro l hl
  -- `mk' Q x` is `U`-fixed in `B`, so `mk' Q (φ l x) = mk' Q x`.
  have hxfix : quotientMulAutHom hQinv l (QuotientGroup.mk' Q x) = QuotientGroup.mk' Q x := by
    have hmem : QuotientGroup.mk' Q x ∈ fixedSubgroup (quotientMulAutHom hQinv)
        (data.U.subgroupOf (data.U ⊔ data.W1)) := by rw [hfix]; exact Subgroup.mem_top _
    exact mem_fixedSubgroup.mp hmem l hl
  rw [quotientMulAutHom_apply_mk'] at hxfix
  -- `(φ l x)⁻¹ * x ∈ Q ∩ ↑P = ⊥`, so `φ l x = x`.
  have hQmem : (typeP_conjAction data l x)⁻¹ * x ∈ Q := by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxfix
  have hPmem : (typeP_conjAction data l x)⁻¹ * x ∈ (↑P : Subgroup ↥data.H) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPinv.smul_mem l hxP)) hxP
  have hinf : (typeP_conjAction data l x)⁻¹ * x ∈ ((↑P : Subgroup ↥data.H) ⊓ Q) := ⟨hPmem, hQmem⟩
  rw [disjoint_iff.mp hQcompl.disjoint, Subgroup.mem_bot, inv_mul_eq_one] at hinf
  exact hinf

/-- Data for the chief factor `H/H_0` selected in Peterfalvi (9.4).

The chief factor is recorded through the kernel `N ◁ H` (with `H₀ = N.map H.subtype`): `H̄ ≅ ↥H ⧸ N`
is elementary abelian, `U W₁`-irreducible, and not centralized by `U` (the genuine chief-factor
structure produced by `exists_chiefFactorData`). -/
structure ChiefFactorData {M : Subgroup G} (data : TypesIIIIIIVSetup M) where
  H0 : Subgroup G
  H0_lt_H : H0 < data.H
  H0_normalized_by_M : M ≤ Subgroup.normalizer (H0 : Set G)
  p : ℕ
  p_prime : p.Prime
  /-- The chief-factor kernel realized inside `H`: a normal subgroup `N ◁ H` with
  `H₀ = N.map H.subtype`.  The module structure of the chief factor `H̄ = H/H₀` is recorded
  through the isomorphic quotient `↥H ⧸ N`. -/
  N : Subgroup ↥data.H
  [N_normal : N.Normal]
  H0_eq : H0 = N.map data.H.subtype
  /-- `N` is `U W₁`-invariant. -/
  N_aInvariant : IsAInvariant (typeP_conjAction data.typeP) N
  /-- **`H̄ = H/H₀ ≅ ↥H ⧸ N` is elementary abelian `p`.** -/
  quotient_elementaryAbelian : IsElementaryAbelian p (↥data.H ⧸ N)
  /-- **`H̄` is `U W₁`-irreducible** (a chief factor of `M`): every `U W₁`-invariant subgroup of
  `H̄` is `⊥` or `⊤`. -/
  quotient_chiefFactor :
    ∀ J : Subgroup (↥data.H ⧸ N),
      IsAInvariant (quotientMulAutHom (N := N) N_aInvariant) J → J = ⊥ ∨ J = ⊤
  quotient_order : Nat.card ↥data.H = p ^ data.q * Nat.card ↥H0
  typeIII_IV_p_eq_W2 : IsTypeIII M ∨ IsTypeIV M → Nat.card ↥data.W2 = p
  /-- **`U` does not centralize `H̄`** (it acts fixed-point-freely). -/
  U_noncentral_on_quotient :
    fixedSubgroup (quotientMulAutHom (N := N) N_aInvariant)
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) ≠ ⊤

attribute [instance] ChiefFactorData.N_normal

/-- **Peterfalvi (9.4)**: existence of a nontrivial elementary abelian chief
factor `H/H_0` not centralized by `U`.  Assembles the elementary-abelian seed
(`exists_chiefFactor_seed`), the chief-factor kernel (`exists_chiefFactor_kernel`,
`|H/H₀| = p^q`, `p ∣ |W₂|`), and the `M`-normality of the kernel image
(`typeP_aInvariantNormal_le_normalizer`) into the `ChiefFactorData`. -/
theorem exists_chiefFactorData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    ∃ chief : ChiefFactorData data, chief.H0 < data.H := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  obtain ⟨p, N₀, hN₀norm, hp, hN₀inv, hpe, hUnc_seed⟩ := exists_chiefFactor_seed data.typeP hU
  have := hN₀norm
  -- Convert the action-free non-centrality `C_H(U) ⊔ N₀ ≠ H` to the quotient form `fixedByU ≠ ⊤`.
  have hUnc : (typeP_quotientCoprimeAction data.typeP hU hN₀inv).fixedByU ≠ ⊤ := by
    have hcopU : Nat.Coprime
        (Nat.card ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
        (Nat.card ↥data.typeP.H) :=
      (typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have : Group.IsSolvable ↥data.typeP.H := (typeP_coprimeAction data.typeP hU).H_solvable
    have hmap := map_fixedSubgroup_eq_fixedSubgroup_quotient (φ := typeP_conjAction data.typeP)
      (N := N₀) (X := data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) hN₀inv hcopU
      (Or.inr inferInstance)
    rw [show (typeP_quotientCoprimeAction data.typeP hU hN₀inv).fixedByU
        = (fixedSubgroup (typeP_conjAction data.typeP)
            (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))).map
            (QuotientGroup.mk' N₀) from hmap.symm]
    intro htop
    refine hUnc_seed ?_
    have hc := congrArg (Subgroup.comap (QuotientGroup.mk' N₀)) htop
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hc
  -- The chief-factor kernel and its image `H₀ = N.map subtype`.
  obtain ⟨N, hN₀leN, hNnorm, hNinv, hcardN, hpW2, hEA, hIrr, hNonc⟩ :=
    exists_chiefFactor_kernel data.typeP hU hp hN₀inv hpe hUnc
  have := hNnorm
  have hqpos : Nat.card ↥data.typeP.W1 ≠ 0 := Nat.card_pos.ne'
  have hNtop : N ≠ ⊤ := by
    intro h
    rw [h, show Nat.card (↥data.typeP.H ⧸ (⊤ : Subgroup ↥data.typeP.H)) = 1
      from Subgroup.index_top] at hcardN
    exact (Nat.one_lt_pow hqpos hp.one_lt).ne' hcardN.symm
  have hlt : N.map data.typeP.H.subtype < data.typeP.H :=
    lt_of_le_of_ne (Subgroup.map_subtype_le N) fun heq => hNtop <| by
      apply Subgroup.map_injective data.typeP.H.subtype_injective
      rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨{ H0 := N.map data.typeP.H.subtype
            H0_lt_H := hlt
            H0_normalized_by_M := typeP_aInvariantNormal_le_normalizer data.typeP hNinv
            p := p
            p_prime := hp
            N := N
            N_normal := hNnorm
            H0_eq := rfl
            N_aInvariant := hNinv
            quotient_elementaryAbelian := hEA
            quotient_chiefFactor := hIrr
            quotient_order := ?_
            typeIII_IV_p_eq_W2 := ?_
            U_noncentral_on_quotient := hNonc }, hlt⟩
  · -- `|H| = |H/N| · |N| = p^q · |H₀|`.
    change Nat.card ↥data.typeP.H
        = p ^ Nat.card ↥data.typeP.W1 * Nat.card ↥(N.map data.typeP.H.subtype)
    rw [← Subgroup.index_mul_card N,
      show N.index = p ^ Nat.card ↥data.typeP.W1 from hcardN,
      Nat.card_congr (Subgroup.equivMapOfInjective N data.typeP.H.subtype
        data.typeP.H.subtype_injective).toEquiv]
  · -- `p = |W₂|` for type III/IV: `p ∣ |W₂|` and `|W₂|` is prime.
    intro hIIIIV
    exact ((Nat.prime_dvd_prime_iff_eq hp
      (typeIIIorIV_W2_prime hG data.typeP data.maximal hIIIIV)).mp hpW2).symm

end OddOrder.Peterfalvi.S11


