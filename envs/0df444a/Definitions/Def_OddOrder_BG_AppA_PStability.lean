-- Prove2me | Definitions.Def_OddOrder_BG_AppA_PStability
-- name    : OddOrder_BG_AppA_PStability
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:45:49.907198+00:00
-- url     : https://prove2.me/theorems/23a249d8-c364-4edc-bb04-03293fee2732
-- title:
--   Bender–Glauberman Appendix A: $p$-stability, Theorems A.4 and A.5
-- statement:
--   Formalizes Bender–Glauberman, Appendix A (pp. 136–138), Theorems A.4 and A.5; the definitions and A.1–A.3 are in the basics file. Theorem A.4(a): for odd $p$ and $|G|$ odd with $O_p(G)=1$, $G$ is $p$-stable (contrapositive of A.3); A.4(b)(c) are the solvable versions; A.5 has two parts.
--
--   Main results: `coprime_chainStabilizer_le_centralizer` (a chain stabilizer is in the centralizer, coprime case), `stability_perFactor` (per-chief-factor $p$-stability, Gorenstein 6.5.3 steps 1–3), `stabilityLiftAux` (abstract stability lift, the body of Gorenstein 6.5.3), `thmA4a`, `thmA4b`, `thmA4c`, `thmA5_part1`, `thmA5_part2`.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppA_PStability.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppA_PStability.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppA_PStabilityBasic
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroupAbelian
import Definitions.Def_OddOrder_Isaacs_Ch09_MoreSubnormality_SylowSubnormal

namespace OddOrder.BG.AppA

open Representation Module Function LinearMap Submodule

universe uF uG uV

variable {p : ℕ} [Fact p.Prime]

variable {F : Type uF} [Field F] [CharP F p]

variable {V : Type uV} [AddCommGroup V] [Module F V] [Module.Finite F V]

variable {G : Type uG} [Group G]

section PStability

/-- **BG Theorem A.4(a)** (mmd L4480, = Gorenstein Ch.6 §5 の特殊形): `p` odd, `G` 有限・
奇数位数で `O_p(G) = 1` (非自明な正規 `p`-部分群が無い) なら `G` は `p`-stable.

A.3 (`thmA3`) の対偶。`thmA3` が `¬IsPStable ∧ O_p(G)=1 ⇒ ¬Odd|G|` を与えるので,
`Odd|G|` のもとで `O_p(G)=1` なら `IsPStable`。BG の標準仮定「`G` solvable」は (a) には不要. -/
theorem thmA4a [Finite G] (hp_odd : p ≠ 2) (hodd : Odd (Nat.card G))
    (h_Op_trivial : OddOrder.Isaacs.Ch01.opCore p G = ⊥) :
    IsPStable p G := by
  by_contra h_not
  exact thmA3 hp_odd h_Op_trivial h_not hodd

open scoped commutatorElement in
open OddOrder.GroupTheory OddOrder.Isaacs.Ch03 OddOrder.BG.Ch1.S01 in
omit [Fact (Nat.Prime p)] in
/-- **Chain-stabilizer ⊆ centralizer (coprime)**: `M` 有限, `K ◁ M` を `p`-群, `D ≤ M` が
`K` と coprime (`(|D|,|K|)=1`) で `K` の chief series を stabilize
(`⁅Pᵢ, D⁆ ≤ Pᵢ₊₁`) するなら, `D ≤ C_M(K)`.

`MulAut.conjNormal : M →* MulAut ↥K` で `D` の作用を作り,
`coprime_stabilizes_chain_trivial` (BG Lem 1.9 多段一般形, S01 へ昇格済) を
`K` の chief series (`subgroupOf K` 化) に適用. -/
private theorem coprime_chainStabilizer_le_centralizer
    {M : Type*} [Group M] [Finite M]
    {K : Subgroup M} [K.Normal] (_hK : IsPGroup p K)
    {D : Subgroup M} (hcop : (Nat.card ↥D).Coprime (Nat.card ↥K))
    (hsolv : Group.IsSolvable ↥D ∨ Group.IsSolvable ↥K)
    (hstab : ∀ i, ⁅chiefSeriesInside K i, D⁆ ≤ chiefSeriesInside K (i + 1)) :
    D ≤ Subgroup.centralizer (K : Set M) := by
  classical
  obtain ⟨N, hN⟩ := chiefSeriesInside_exists_eq_bot K
  set ψ : ↥D →* MulAut ↥K := (MulAut.conjNormal (H := K)).comp D.subtype with hψ
  set s : ℕ → Subgroup ↥K := fun i => (chiefSeriesInside K i).subgroupOf K with hs
  -- helper: `↑(ψ a g) = ↑a * ↑g * (↑a)⁻¹`
  have hψcoe : ∀ (a : ↥D) (g : ↥K), ((ψ a) g : M) = (a : M) * (g : M) * (a : M)⁻¹ := by
    intro a g; rw [hψ]; simp [MulAut.conjNormal_apply]
  have htrivψ : ∀ a : ↥D, ψ a = 1 := by
    refine coprime_stabilizes_chain_trivial ψ hcop hsolv s ?_ ?_ (n := N) ?_ ?_ ?_ ?_
    · -- Antitone s
      intro i j hij
      exact Subgroup.comap_mono (chiefSeriesInside_antitone K hij)
    · -- s 0 = ⊤
      simp [hs, chiefSeriesInside_zero, Subgroup.subgroupOf_self]
    · -- s N = ⊥
      simp [hs, hN, Subgroup.bot_subgroupOf]
    · -- normal
      intro i
      exact (inferInstance : (chiefSeriesInside K i).Normal).subgroupOf K
    · -- IsAInvariant
      intro i
      rw [isAInvariant_iff_smul_mem]
      intro a g hg
      rw [hs, Subgroup.mem_subgroupOf] at hg ⊢
      rw [hψcoe]
      exact (chiefSeriesInside_instNormal K i).conj_mem _ hg _
    · -- stabilize each factor
      intro i a x hx
      rw [hs, Subgroup.mem_subgroupOf] at hx
      refine ⟨x⁻¹ * ψ a x, ?_, by group⟩
      rw [hs, Subgroup.mem_subgroupOf]
      have hcoe : ((x⁻¹ * ψ a x : ↥K) : M) = ⁅(x : M)⁻¹, (a : M)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hψcoe, commutatorElement_def]; group
      rw [hcoe]
      exact hstab i (Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem _ hx) (SetLike.coe_mem a))
  -- conclude `D ≤ C_M(K)`
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := DFunLike.congr_fun (htrivψ ⟨x, hx⟩) ⟨k, hk⟩
  have h2 : (x : M) * k * x⁻¹ = k := by
    have := congrArg (Subtype.val) h1
    rwa [hψcoe] at this
  have h3 : x * k = k * x := by
    have := congrArg (· * x) h2
    simpa [mul_assoc] using this
  exact h3.symm

open OddOrder.GroupTheory OddOrder.BG.Ch1.S02 OddOrder.RepresentationTheory in
open scoped commutatorElement IsMulCommutative in
/-- **PSTAB — per-chief-factor p-stability** (= Gorenstein 6.5.3 steps 1-3, A.4(c)):
`M` 有限可解奇数位数, `p` odd, `K ◁ M` を `p`-群, `A ≤ M` を `p`-部分群で `[K,A,A]=1`.
このとき `K` の各 `M`-chief factor 上で `A` は trivial, すなわち `⁅Pᵢ, A⁆ ≤ Pᵢ₊₁`
(`Pᵢ := chiefSeriesInside K i`).

**証明 (issue #0047 PSTAB, sorry-free)**: `U := chiefSeriesInside K i`,
`V := chiefSeriesInside K (i+1)`. `U = ⊥` なら `⁅⊥,A⁆ = ⊥ ≤ V`. 以下 `U/V` が `M`-chief
factor (`isChiefFactor_chiefSeriesInside`) の場合:
1. `U/V` は elementary abelian `p`-群 (`IsChiefFactor.commutator_le_of_isSolvable` で abelian,
   `K` が `p`-群なので exponent `p`) ⇒ `AddCommGroup.zmodModule` で `ZMod p`-ベクトル空間.
2. `M` の conjugation 作用は `ZMod p`-線形 ⇒ `H_i := chiefFactorCentralizer U V` を kernel と
   する `Representation (ZMod p) (M ⧸ H_i) (U/V)`. **faithful** (kernel = `H_i`) + **irreducible**
   (`U/V` chief = `M/V` の minimal normal, `IsChiefFactor.isMinimalNormal_map_quotient`).
3. faithful + irreducible char-`p` ⇒ `O_p(M/H_i) = 1` (`PGroupFixedVector` =
   `IsPGroup.invariants_ne_bot`: 正規 `p`-部分群の固定空間は `M`-不変・非零 ⇒ irreducible で全空間
   ⇒ 自明作用 ⇒ faithful で `= 1`).
4. `M/H_i` は奇数位数可解 section で `O_p = 1` ⇒ **`thmA4a` で `IsPStable p (M/H_i)`**.
5. `[K,A,A]=1` ∧ `U ≤ K` ⇒ `[U,A,A] ≤ V` ⇒ 各 `ā ∈ Ā` (= `A` の `M/H_i` 像) は `U/V` 上
   quadratic (`(ρ ā - 1)² = 0`); `ā` は `p`-element (`A` `p`-群).
6. `IsPStable` は alg-closed 上定義 ⇒ `baseChangeRepresentation` (S02_Representations, 要 expose)
   で `ρ` を `AlgebraicClosure (ZMod p)` に持ち上げ (faithful + quadratic 保存) ⇒ `IsPStable` で
   `ρ' ā = 1` ⇒ faithful で `ā = 1` ⇒ `Ā = 1` ⇒ `A ⊆ H_i` ⇒ `⁅U, A⁆ ≤ V`. ∎

主要 API: `isChiefFactor_chiefSeriesInside`, `IsChiefFactor.isMinimalNormal_map_quotient`,
`minimal_normal_isElementaryAbelian_of_isSolvable`, `AddCommGroup.zmodModule`,
`OddOrder.BG.Ch1_Preliminary.mulAutToEnd` (共有版, `OperatorMaschke`),
`IsPGroup.invariants_ne_bot` (step 3 の O_p=1), `thmA4a`, `baseChangeRepresentation`
(+ `_faithful`). -/
private theorem stability_perFactor
    {M : Type*} [Group M] [Finite M] [Group.IsSolvable M]
    (hp_odd : p ≠ 2) (hodd : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K)
    {A : Subgroup M} (hA_p : IsPGroup p A)
    (hKAA : ⁅⁅K, A⁆, A⁆ = (⊥ : Subgroup M)) (i : ℕ) :
    ⁅chiefSeriesInside K i, A⁆ ≤ chiefSeriesInside K (i + 1) := by
  classical
  rcases eq_or_ne (chiefSeriesInside K i) ⊥ with hU0 | hU0
  · rw [hU0, Subgroup.commutator_bot_left]; exact bot_le
  -- chief factor case
  have hchief : IsChiefFactor (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
    isChiefFactor_chiefSeriesInside hU0
  set U : Subgroup M := chiefSeriesInside K i with hUdef
  set V : Subgroup M := chiefSeriesInside K (i + 1) with hVdef
  have hVn : V.Normal := hchief.normal_bot
  have hUn : U.Normal := hchief.normal_top
  -- reduce to A ≤ C_M(U/V)
  suffices hAC : A ≤ chiefFactorCentralizer U V from
    chiefFactorCentralizer.commutator_le_of_le hAC
  -- W := U/V as a (normal, minimal-normal) subgroup of M/V
  set W : Subgroup (M ⧸ V) := U.map (QuotientGroup.mk' V) with hWdef
  have hWn : W.Normal := hUn.map _ (QuotientGroup.mk'_surjective V)
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal W := hchief.isMinimalNormal_map_quotient
  have hW_ne_bot : W ≠ ⊥ := hMin.2.1
  obtain ⟨q, hq_prime, hElem⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hMin
  -- the elementary-abelian prime is p (W is a section of the p-group K)
  have hq_eq_p : q = p := by
    have hUp : IsPGroup p ↥U := by
      rw [hUdef]; exact hK.to_le (chiefSeriesInside_le K i)
    have hWp : IsPGroup p ↥W := by
      rw [hWdef]; exact hUp.map (QuotientGroup.mk' V)
    have hElemG : OddOrder.GroupTheory.IsElementaryAbelian q ↥W := hElem
    have : Fact q.Prime := ⟨hq_prime⟩
    have hp_prime : p.Prime := Fact.out
    have : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW_ne_bot
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥W)
    obtain ⟨ka, hka⟩ := IsPGroup.iff_orderOf.mp hElemG.isPGroup x
    obtain ⟨kb, hkb⟩ := IsPGroup.iff_orderOf.mp hWp x
    have hox : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
    have hka0 : ka ≠ 0 := fun h => hox (by rw [hka, h, pow_zero])
    have hqd : q ∣ orderOf x := hka ▸ dvd_pow_self q hka0
    rw [hkb] at hqd
    exact (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp (hq_prime.dvd_of_dvd_pow hqd)
  rw [hq_eq_p] at hElem
  have hElemT : OddOrder.GroupTheory.IsElementaryAbelian p ↥W := hElem
  -- module structure on Additive ↥W
  have hWcomm : IsMulCommutative ↥W :=
    ⟨⟨fun a b => hElemT.comm a b⟩⟩
  have hpsmul : ∀ x : Additive ↥W, (p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hElemT.pow_eq_one x.toMul
  have hWmod : Module (ZMod p) (Additive ↥W) := AddCommGroup.zmodModule hpsmul
  have hWnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW_ne_bot
  have : Finite ↥W := inferInstance
  -- the conjugation representation ρ : M → End (Additive ↥W)
  set ρ : Representation (ZMod p) M (Additive ↥W) :=
    (OddOrder.BG.Ch1_Preliminary.mulAutToEnd ↥W p).comp
      ((MulAut.conjNormal (H := W)).comp (QuotientGroup.mk' V)) with hρdef
  have hρ_apply : ∀ (g : M) (x : Additive ↥W),
      ρ g x = Additive.ofMul (MulAut.conjNormal (H := W) (QuotientGroup.mk' V g)
        (Additive.toMul x)) := by
    intro g x; rfl
  -- faithfulness: ker ρ = C_M(U/V)
  have hker : ∀ g : M, ρ g = 1 ↔ g ∈ chiefFactorCentralizer U V := by
    intro g
    rw [chiefFactorCentralizer.mem_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg w hw
      have hx := DFunLike.congr_fun hg (Additive.ofMul (⟨w, hw⟩ : ↥W))
      rw [hρ_apply, Module.End.one_apply] at hx
      have hcoe := congrArg (Subtype.val) (Additive.ofMul.injective hx)
      rw [MulAut.conjNormal_apply] at hcoe
      exact (mul_inv_eq_iff_eq_mul.mp hcoe).symm
    · intro hg
      ext x
      have h : MulAut.conjNormal (H := W) (QuotientGroup.mk' V g) (Additive.toMul x)
          = Additive.toMul x := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        have hcomm := hg ((Additive.toMul x : ↥W) : M ⧸ V) (Additive.toMul x).2
        exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
      simp only [hρ_apply, Module.End.one_apply, h, ofMul_toMul]
  -- quotient M̄ := M / C and the lifted (faithful) representation
  set C : Subgroup M := chiefFactorCentralizer U V with hCdef
  have hCn : C.Normal := chiefFactorCentralizer.normal
  have hC_le_ker : C ≤ (ρ : M →* _).ker := fun g hg => (hker g).mpr hg
  set ρbar : Representation (ZMod p) (M ⧸ C) (Additive ↥W) :=
    QuotientGroup.lift C ρ hC_le_ker with hρbardef
  have hρbar_mk : ∀ g : M, ρbar (QuotientGroup.mk' C g) = ρ g := fun g => rfl
  have hρbar_faithful : Function.Injective ρbar := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [hρbar_mk] at hx
    exact (QuotientGroup.eq_one_iff g).mpr ((hker g).mp hx)
  -- O_p(M̄) = ⊥: faithful + irreducible (chief factor) ⇒ no nontrivial normal p-subgroup.
  have hOp : OddOrder.Isaacs.Ch01.opCore p (M ⧸ C) = ⊥ := by
    set Q : Subgroup (M ⧸ C) := OddOrder.Isaacs.Ch01.opCore p (M ⧸ C) with hQdef
    have hQp : IsPGroup p ↥Q := OddOrder.Isaacs.Ch01.opCore_isPGroup p (M ⧸ C)
    have hQn : Q.Normal := OddOrder.Isaacs.Ch01.opCore.normal p (M ⧸ C)
    -- the restriction of `ρbar` to `Q`, and its (nonzero) invariant submodule
    set σ : Representation (ZMod p) ↥Q (Additive ↥W) := ρbar.comp Q.subtype with hσdef
    have hσ_apply : ∀ (q : ↥Q) (z : Additive ↥W), σ q z = ρbar (Q.subtype q) z :=
      fun _ _ => rfl
    have hWtop_ne : (⊤ : Submodule (ZMod p) (Additive ↥W)) ≠ ⊥ := by
      obtain ⟨w, hw⟩ := exists_ne (1 : ↥W)
      rw [Submodule.ne_bot_iff]
      refine ⟨Additive.ofMul w, Submodule.mem_top, fun h => hw ?_⟩
      rwa [← ofMul_one, Equiv.apply_eq_iff_eq] at h
    have hinv_ne : σ.invariants ≠ ⊥ := hQp.invariants_ne_bot σ hWtop_ne
    -- the subgroup of `W` fixed (pointwise) by `Q`
    let Wfix : Subgroup ↥W :=
      { carrier := {w : ↥W | ∀ q : ↥Q, σ q (Additive.ofMul w) = Additive.ofMul w}
        one_mem' := fun q => by rw [ofMul_one, map_zero]
        mul_mem' := fun {w w'} hw hw' q => by rw [ofMul_mul, map_add, hw q, hw' q]
        inv_mem' := fun {w} hw q => by rw [ofMul_inv, map_neg, hw q] }
    have hmem_Wfix : ∀ w : ↥W,
        w ∈ Wfix ↔ ∀ q : ↥Q, σ q (Additive.ofMul w) = Additive.ofMul w := fun _ => Iff.rfl
    set N : Subgroup (M ⧸ V) := Wfix.map W.subtype with hNdef
    -- (A) `N ≤ W`
    have hNle : N ≤ W := by rw [hNdef]; rintro _ ⟨w, _, rfl⟩; exact w.2
    -- (B) `N ≠ ⊥`: a nonzero invariant vector gives a nontrivial fixed element
    have hN_ne : N ≠ ⊥ := by
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinv_ne
      have hfix : Additive.toMul v ∈ Wfix :=
        (hmem_Wfix _).mpr fun q => by
          rw [ofMul_toMul]; exact (Representation.mem_invariants σ v).mp hv_mem q
      have hmemN : ((Additive.toMul v : ↥W) : M ⧸ V) ∈ N := by
        rw [hNdef]; exact ⟨Additive.toMul v, hfix, rfl⟩
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hmemN
      have hone : Additive.toMul v = 1 := by
        have hcoe : ((Additive.toMul v : ↥W) : M ⧸ V) = ((1 : ↥W) : M ⧸ V) := by
          rw [Subgroup.coe_one]; exact hmemN
        exact Subtype.coe_inj.mp hcoe
      exact hv_ne (by rw [← ofMul_toMul v, hone, ofMul_one])
    -- (C) `N` is normal in `M ⧸ V`: `Q ◁ M̄` makes the fixed set `M̄`-stable
    have hNnorm : N.Normal := by
      rw [hNdef]
      refine ⟨?_⟩
      rintro _ ⟨w, hw, rfl⟩ gbar
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V gbar
      have hconjW :
          (QuotientGroup.mk' V g) * (W.subtype w) * (QuotientGroup.mk' V g)⁻¹ ∈ W :=
        hWn.conj_mem _ w.2 _
      refine ⟨⟨_, hconjW⟩, (hmem_Wfix _).mpr fun q => ?_, rfl⟩
      have heq : (⟨_, hconjW⟩ : ↥W) = MulAut.conjNormal (QuotientGroup.mk' V g) w := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply, Subgroup.coe_subtype]
      rw [heq]
      have hρg : ρ g (Additive.ofMul w)
          = Additive.ofMul (MulAut.conjNormal (QuotientGroup.mk' V g) w) := by
        rw [hρ_apply, toMul_ofMul]
      rw [hσ_apply, ← hρg, ← hρbar_mk g, ← Module.End.mul_apply, ← map_mul]
      have hq' : (QuotientGroup.mk' C g)⁻¹ * Q.subtype q * QuotientGroup.mk' C g ∈ Q := by
        simpa using hQn.conj_mem (Q.subtype q) q.2 ((QuotientGroup.mk' C g)⁻¹)
      have hfixq' :
          ρbar ((QuotientGroup.mk' C g)⁻¹ * Q.subtype q * QuotientGroup.mk' C g)
              (Additive.ofMul w) = Additive.ofMul w := by
        have h2 := (hmem_Wfix w).mp hw ⟨_, hq'⟩
        rwa [hσ_apply] at h2
      have hconj_eq : Q.subtype q * QuotientGroup.mk' C g
          = QuotientGroup.mk' C g * ((QuotientGroup.mk' C g)⁻¹ * Q.subtype q
              * QuotientGroup.mk' C g) := by group
      rw [hconj_eq, map_mul, Module.End.mul_apply, hfixq']
    -- (D) minimality ⇒ `N = W` ⇒ `Q` acts trivially ⇒ `Q = ⊥`
    have hNW : N = W := (hMin.2.2 N hNnorm hNle).resolve_left hN_ne
    have hWfix_top : ∀ w : ↥W, w ∈ Wfix := by
      intro w
      have hwN : ((w : ↥W) : M ⧸ V) ∈ N := by rw [hNW]; exact w.2
      rw [hNdef] at hwN
      obtain ⟨w', hw', hw'eq⟩ := hwN
      rwa [← Subtype.coe_inj.mp hw'eq]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hρx : ρbar x = 1 := by
      have hone : ρbar (Q.subtype ⟨x, hx⟩) = 1 := by
        refine LinearMap.ext fun z => ?_
        rw [Module.End.one_apply, ← hσ_apply, ← ofMul_toMul z]
        exact (hmem_Wfix _).mp (hWfix_top (Additive.toMul z)) ⟨x, hx⟩
      exact hone
    exact hρbar_faithful (by rw [hρx, map_one])
  -- M̄ odd order ⇒ p-stable
  have hodd_bar : Odd (Nat.card (M ⧸ C)) :=
    hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card C)
  have hpstable : IsPStable p (M ⧸ C) := thmA4a hp_odd hodd_bar hOp
  -- now A ≤ C
  intro a ha
  set abar : M ⧸ C := QuotientGroup.mk' C a with habardef
  have habar_p : IsPGroup p (Subgroup.zpowers abar) := by
    have hmem : abar ∈ A.map (QuotientGroup.mk' C) := by
      rw [habardef]; exact Subgroup.mem_map_of_mem _ ha
    exact (hA_p.map (QuotientGroup.mk' C)).to_le (Subgroup.zpowers_le.mpr hmem)
  -- quadratic over the algebraic closure
  have hquadZ : ((ρbar abar : Module.End (ZMod p) (Additive ↥W)) - 1) ^ 2 = 0 := by
    have hρbar_eq : ρbar abar = ρ a := by rw [habardef]; exact hρbar_mk a
    -- `(ρ a - 1) y = ofMul (⁅ā, toMul y⁆)`  with `ā = mk' V a`
    have hsub : ∀ y : Additive ↥W,
        (ρ a - (1 : Module.End (ZMod p) (Additive ↥W))) y
          = Additive.ofMul (MulAut.conjNormal (QuotientGroup.mk' V a) (Additive.toMul y)
              * (Additive.toMul y)⁻¹) := by
      intro y
      rw [LinearMap.sub_apply, Module.End.one_apply, hρ_apply, ofMul_mul, ofMul_inv,
        ofMul_toMul, sub_eq_add_neg]
    -- coercion of `⁅ā, s⁆`-as-element-of-`↥W` into `M ⧸ V`
    have hcomm_coe : ∀ s : ↥W,
        ((MulAut.conjNormal (QuotientGroup.mk' V a) s * s⁻¹ : ↥W) : M ⧸ V)
          = ⁅(QuotientGroup.mk' V a), (s : M ⧸ V)⁆ := by
      intro s
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
        commutatorElement_def]
    rw [hρbar_eq]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, pow_two, Module.End.mul_apply, hsub x, hsub, toMul_ofMul,
      ← ofMul_one]
    refine congrArg Additive.ofMul ?_
    -- `↑w ∈ W = U.map (mk' V)`: pick `u ∈ U ≤ K` with `mk' V u = ↑w`
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp
      (show ((Additive.toMul x : ↥W) : M ⧸ V) ∈ U.map (QuotientGroup.mk' V) by
        rw [← hWdef]; exact (Additive.toMul x).2)
    apply Subtype.ext
    rw [Subgroup.coe_one,
      hcomm_coe (MulAut.conjNormal (QuotientGroup.mk' V a) (Additive.toMul x)
        * (Additive.toMul x)⁻¹),
      hcomm_coe (Additive.toMul x), ← hux, ← map_commutatorElement (QuotientGroup.mk' V),
      ← map_commutatorElement (QuotientGroup.mk' V)]
    -- `⁅a, ⁅a, u⁆⁆ ∈ ⁅⁅K, A⁆, A⁆ = ⊥`
    have huK : u ∈ K := chiefSeriesInside_le K i (hUdef ▸ hu)
    have hc1 : ⁅a, u⁆ ∈ ⁅K, A⁆ := by
      rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator ha huK
    have hc2 : ⁅a, ⁅a, u⁆⁆ ∈ ⁅⁅K, A⁆, A⁆ := by
      rw [Subgroup.commutator_comm ⁅K, A⁆ A]
      exact Subgroup.commutator_mem_commutator ha hc1
    rw [hKAA] at hc2
    rw [Subgroup.mem_bot.mp hc2, map_one]
  set Kalg := AlgebraicClosure (ZMod p)
  have : CharP Kalg p := inferInstance
  have hρ'_faithful : Function.Injective (baseChangeRepresentation Kalg ρbar) :=
    baseChangeRepresentation_faithful Kalg ρbar hρbar_faithful
  have hquad' :
      ((baseChangeRepresentation Kalg ρbar abar :
          Module.End Kalg (TensorProduct (ZMod p) Kalg (Additive ↥W))) - 1) ^ 2 = 0 := by
    have happ : (baseChangeRepresentation Kalg ρbar abar :
        Module.End Kalg (TensorProduct (ZMod p) Kalg (Additive ↥W)))
        = Module.End.baseChangeHom (ZMod p) Kalg (Additive ↥W) (ρbar abar) := rfl
    rw [happ, show (1 : Module.End Kalg (TensorProduct (ZMod p) Kalg (Additive ↥W)))
          = Module.End.baseChangeHom (ZMod p) Kalg (Additive ↥W) 1 from (map_one _).symm,
        ← map_sub (Module.End.baseChangeHom (ZMod p) Kalg (Additive ↥W)), ← map_pow, hquadZ,
        map_zero]
  -- IsPStable kills ā
  have h1 : baseChangeRepresentation Kalg ρbar abar = 1 :=
    hpstable (baseChangeRepresentation Kalg ρbar) hρ'_faithful abar habar_p hquad'
  have habar1 : abar = 1 := hρ'_faithful (by rw [h1, map_one])
  exact (QuotientGroup.eq_one_iff a).mp habar1

open OddOrder.GroupTheory in
/-- **Stability lift, abstract form** (= Gorenstein 6.5.3 本体, normalizer 化を剥がした版):
`M` 有限可解奇数位数, `p` odd, `K ◁ M` を正規 `p`-部分群, `A ≤ M` を `p`-部分群で
`[K, A, A] = 1`. このとき `A` の `M / C_M(K)` での像は `O_p(M / C_M(K))` に含まれる.

`thmA4c` は本補題を `M := ↥N_G(P)`, `K := P.subgroupOf N` に instantiate して得る
(`C_M(K) = C_G(P).subgroupOf N`).

**証明骨格 (Gorenstein 6.5.3, mmd L4796)**: `Pᵢ := chiefSeriesInside K`,
`H := ⨅ᵢ C_M(Pᵢ/Pᵢ₊₁)`. (1) `C_M(K) ≤ H` (K を centralize ⇒ 各 factor も).
(2) `A ≤ H` — 各 chief factor で p-stability (`thmA4a`) + quadratic (`[K,A,A]=1`) ⇒
`A` は factor を centralize [= `stability_le_chiefFactorCentralizer`]. (3) `H/C_M(K)` は
`p`-群 — `H/C` は `Aut K` の chain-stabilizer, coprime stability で p'-元は自明
[= `chiefSeries_stabilizer_isPGroup`]. (4) `H ◁ M` かつ `H/C` p-群 ⇒
`H/C ⊆ O_p(M/C)` (`normal_pgroup_le_opCore`), `A ≤ H` で結論. -/
private theorem stabilityLiftAux
    {M : Type*} [Group M] [Finite M] [Group.IsSolvable M]
    (hp_odd : p ≠ 2) (hodd : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hK : IsPGroup p K)
    {A : Subgroup M} (hA_p : IsPGroup p A)
    (hKAA : ⁅⁅K, A⁆, A⁆ = (⊥ : Subgroup M))
    {C₀ : Subgroup M} [C₀.Normal] (hC₀ : C₀ = Subgroup.centralizer (K : Set M)) :
    A.map (QuotientGroup.mk' C₀) ≤ OddOrder.Isaacs.Ch01.opCore p (M ⧸ C₀) := by
  subst hC₀
  classical
  have hCnorm : (Subgroup.centralizer (K : Set M)).Normal := inferInstance
  -- `H := ⨅ᵢ C_M(Pᵢ/Pᵢ₊₁)`, intersection of chief-factor centralizers of the N-chief series of K.
  set H : Subgroup M :=
    ⨅ i : ℕ, chiefFactorCentralizer (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))
    with hH
  -- (1) `C_M(K) ≤ H`: the centralizer of all of `K` centralizes every chief factor.
  have hC_le_H : Subgroup.centralizer (K : Set M) ≤ H := by
    rw [hH]
    refine le_iInf (fun i => ?_)
    rw [chiefFactorCentralizer.le_iff_commutator_le]
    refine le_trans ?_ (bot_le : (⊥ : Subgroup M) ≤ _)
    rw [Subgroup.commutator_le]
    intro u hu c hc
    have huK : u ∈ K := chiefSeriesInside_le K i hu
    have hcomm : u * c = c * u := Subgroup.mem_centralizer_iff.mp hc u huK
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  -- (2) `A ≤ H`: the per-chief-factor p-stability argument (Gorenstein 6.5.3 steps 1-3).
  have hA_le_H : A ≤ H := by
    rw [hH, le_iInf_iff]
    intro i
    rw [chiefFactorCentralizer.le_iff_commutator_le]
    exact stability_perFactor hp_odd hodd hK hA_p hKAA i
  -- (3) `H ◁ M`.
  have hHnorm : H.Normal := by
    rw [hH]; exact Subgroup.normal_iInf_normal (fun _ => inferInstance)
  -- (4) `H / C_M(K)` is a p-group (Gorenstein 6.5.3 steps 4-5, coprime stability).
  have hHmap_pgroup :
      IsPGroup p (H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))) := by
    -- `H` stabilizes every chief factor of `K`.
    have hH_stab : ∀ i, ⁅chiefSeriesInside K i, H⁆ ≤ chiefSeriesInside K (i + 1) := by
      intro i
      rw [← chiefFactorCentralizer.le_iff_commutator_le, hH]
      exact iInf_le _ i
    -- A Hall `{p}'`-subgroup `D` of `↥H` (exists: `↥H` finite solvable).
    obtain ⟨D, hD⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥H) {q : ℕ | q ≠ p}
    have hpD : ¬ p ∣ Nat.card ↥D := by
      intro hpdvd
      exact absurd rfl (hD.primeFactors_card_subset p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd, Nat.card_pos.ne'⟩))
    -- `|D.map subtype| = |D|` is coprime to `|K| = p^j`.
    have hcardD' : Nat.card ↥(D.map H.subtype) = Nat.card ↥D :=
      (Nat.card_congr (D.equivMapOfInjective H.subtype (Subgroup.subtype_injective H)).toEquiv).symm
    have hcop : (Nat.card ↥(D.map H.subtype)).Coprime (Nat.card ↥K) := by
      obtain ⟨j, hjK⟩ := hK.exists_card_eq
      rw [hcardD', hjK]
      exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpD).symm.pow_right j
    -- `D.map subtype ≤ H` stabilizes the chief series, hence `≤ C_M(K)` (the helper).
    have hstabD' : ∀ i,
        ⁅chiefSeriesInside K i, D.map H.subtype⁆ ≤ chiefSeriesInside K (i + 1) :=
      fun i => le_trans (Subgroup.commutator_mono le_rfl (Subgroup.map_subtype_le D)) (hH_stab i)
    have hsolvD' : Group.IsSolvable ↥(D.map H.subtype) ∨ Group.IsSolvable ↥K := by
      have := hK.isNilpotent; exact Or.inr inferInstance
    have hD'C : D.map H.subtype ≤ Subgroup.centralizer (K : Set M) :=
      coprime_chainStabilizer_le_centralizer hK hcop hsolvD' hstabD'
    have hDC : D ≤ (Subgroup.centralizer (K : Set M)).subgroupOf H :=
      Subgroup.map_le_iff_le_comap.mp hD'C
    -- `D.index` is a power of `p` (Hall `{p}'` ⇒ index a `{p}`-number).
    obtain ⟨k, hk⟩ : ∃ k, D.index = p ^ k := by
      refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite
        (fun {d} hd hdvd => ?_)⟩
      simpa using hD.index_no_pi d
        (Nat.mem_primeFactors.mpr ⟨hd, hdvd, Subgroup.index_ne_zero_of_finite⟩)
    -- `|H.map(mk' C)| = (C ∩ H).index ∣ D.index = p^k`, so it is a power of `p`.
    set ψH : ↥H →* M ⧸ Subgroup.centralizer (K : Set M) :=
      (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))).comp H.subtype with hψH
    have hrange : ψH.range = H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))) := by
      rw [hψH, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : ψH.ker = (Subgroup.centralizer (K : Set M)).subgroupOf H := by
      rw [hψH, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hcard_eq :
        Nat.card ↥(H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))))
          = ((Subgroup.centralizer (K : Set M)).subgroupOf H).index := by
      rw [← hrange, ← hker]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψH).toEquiv).symm
    rw [IsPGroup.iff_card]
    have hdvd :
        Nat.card ↥(H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))) ∣ p ^ k := by
      rw [hcard_eq, ← hk]; exact Subgroup.index_dvd_of_le hDC
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
    exact ⟨j, hj⟩
  have hHmap_norm :
      (H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))).Normal :=
    hHnorm.map _ (QuotientGroup.mk'_surjective _)
  calc A.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M)))
      ≤ H.map (QuotientGroup.mk' (Subgroup.centralizer (K : Set M))) :=
        Subgroup.map_mono hA_le_H
    _ ≤ OddOrder.Isaacs.Ch01.opCore p (M ⧸ Subgroup.centralizer (K : Set M)) :=
        OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hHmap_pgroup

/-- **BG Theorem A.4(b)** (mmd L4480(b), = Gorenstein 6.5.2 翻訳 = BG Thm 6.1, Hall-Higman 特殊形):
`p` odd, `G` solvable odd order, `P ∈ Syl_p(G)`, `A` を `P` の正規 abelian 部分群とする
(`A ≤ P` かつ `P ≤ N_G(A)`)。このとき `A ≤ O_{p',p}(G)`。

**証明 (Gorenstein 5.2 直接ルート)**: `N := O_{p'}(G)`, `Ḡ := G/N`, `R̄ := O_p(Ḡ)`,
`Ā := A の像`。`Ḡ` では `O_{p'}=⊥`。`Ā` は abelian `p`-群で `R̄ ≤ P̄ ≤ N_Ḡ(Ā)` ⇒
`⁅R̄,Ā,Ā⁆ ≤ ⁅Ā,Ā⁆ = ⊥`。`stabilityLiftAux` を `K := R̄` に適用し
`Ā·C_Ḡ(R̄)/C_Ḡ(R̄) ⊆ O_p(Ḡ/C_Ḡ(R̄))`。Hall-Higman (`O_{p'}(Ḡ)=⊥ ⇒ C_Ḡ(R̄) ⊆ R̄`,
`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`) で `C_Ḡ(R̄)` は `p`-群 ⇒ 商を
引き戻して `Ā ⊆ R̄ = O_p(Ḡ)` ⇒ `A ⊆ O_{p',p}(G)`。Gorenstein の Remark (A.4(c) の系) が
隠す "`A ⊆ P`" 推論を回避するため, A.4(c) でなく 5.2 自身 (= `stabilityLiftAux@K=O_p(Ḡ)`) を翻訳。 -/
theorem thmA4b [Finite G] (hp_odd : p ≠ 2) (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (P : Sylow p G) {A : Subgroup G} (hA_le : A ≤ (P : Subgroup G))
    (hA_norm : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G)) [IsMulCommutative A] :
    A ≤ OddOrder.Isaacs.Ch03.oPiPrimePiCore ({p} : Set ℕ) G := by
  have : Group.IsSolvable G := hsolv
  set N : Subgroup G := OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G with hN
  set mk := QuotientGroup.mk' N with hmk
  set Abar : Subgroup (G ⧸ N) := A.map mk with hAbar
  set Rbar : Subgroup (G ⧸ N) := OddOrder.Isaacs.Ch01.opCore p (G ⧸ N) with hRbar
  -- Step 0: instances / odd order on `Ḡ`; the `{q ∉ {p}} = {q ≠ p}` set identity
  have hset : {p_1 | p_1 ∉ ({p} : Set ℕ)} = {q | q ≠ p} := by ext q; simp
  have hoddBar : Odd (Nat.card (G ⧸ N)) :=
    hodd.of_dvd_nat (Subgroup.card_quotient_dvd_card N)
  -- Step 1: `O_{p'}(Ḡ) = ⊥`
  have hOp'Bar : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} (G ⧸ N) = ⊥ :=
    OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot {q | q ≠ p}
  -- Step 2: `Ā` is an abelian `p`-group, `R̄ ≤ P̄ ≤ N_Ḡ(Ā)`
  have hA_pg : IsPGroup p A := P.2.to_le hA_le
  have hAbar_pg : IsPGroup p Abar := hA_pg.map mk
  set Pbar : Sylow p (G ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N) with hPbar
  have hPbar_coe : (Pbar : Subgroup (G ⧸ N)) = (P : Subgroup G).map mk :=
    P.coe_mapSurjective (QuotientGroup.mk'_surjective N)
  have hR_le_NAbar : Rbar ≤ Subgroup.normalizer (Abar : Set (G ⧸ N)) := by
    refine le_trans (OddOrder.Isaacs.Ch01.opCore_le Pbar) ?_
    rw [hPbar_coe, hAbar]
    exact le_trans (Subgroup.map_mono hA_norm) (Subgroup.le_normalizer_map mk)
  -- Step 3: `⁅R̄, Ā, Ā⁆ = ⊥`
  have hAA : ⁅A, A⁆ = (⊥ : Subgroup G) := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (‹IsMulCommutative A›.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hAbarAbar : ⁅Abar, Abar⁆ = (⊥ : Subgroup (G ⧸ N)) := by
    rw [hAbar, ← Subgroup.map_commutator, hAA, Subgroup.map_bot]
  have hRAbar_le : ⁅Rbar, Abar⁆ ≤ Abar := by
    rw [Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hR_le_NAbar
  have hKAA : ⁅⁅Rbar, Abar⁆, Abar⁆ = (⊥ : Subgroup (G ⧸ N)) :=
    le_bot_iff.mp (le_trans (Subgroup.commutator_mono hRAbar_le le_rfl) hAbarAbar.le)
  -- Step 4: stabilityLiftAux with `K := R̄`
  have hStab := stabilityLiftAux (M := G ⧸ N) (K := Rbar) (A := Abar)
    hp_odd hoddBar (OddOrder.Isaacs.Ch01.opCore_isPGroup p (G ⧸ N)) hAbar_pg hKAA
    (C₀ := Subgroup.centralizer (Rbar : Set (G ⧸ N))) rfl
  -- Step 5: `C₀ := C_Ḡ(R̄) ≤ R̄` (Hall-Higman) ⇒ `C₀` is a `p`-group
  have hC₀_le_R : Subgroup.centralizer (Rbar : Set (G ⧸ N)) ≤ Rbar := by
    have hHH := OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization (p := p) (G := G ⧸ N)
      (by rw [hset]; exact hOp'Bar)
    rwa [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore, ← hRbar] at hHH
  have hC₀_pg : IsPGroup p (Subgroup.centralizer (Rbar : Set (G ⧸ N))) :=
    (OddOrder.Isaacs.Ch01.opCore_isPGroup p (G ⧸ N)).to_le hC₀_le_R
  -- Step 6: pull back `Ā.map(mk' C₀) ≤ O_p(Ḡ/C₀)` to `Ā ≤ R̄`
  set C₀ := Subgroup.centralizer (Rbar : Set (G ⧸ N)) with hC₀
  have hcomap_pg : IsPGroup p
      ((OddOrder.Isaacs.Ch01.opCore p ((G ⧸ N) ⧸ C₀)).comap (QuotientGroup.mk' C₀)) := by
    refine (OddOrder.Isaacs.Ch01.opCore_isPGroup p _).comap_of_ker_isPGroup
      (QuotientGroup.mk' C₀) ?_
    rw [QuotientGroup.ker_mk']
    exact hC₀_pg
  have hcomap_le_R : (OddOrder.Isaacs.Ch01.opCore p ((G ⧸ N) ⧸ C₀)).comap
      (QuotientGroup.mk' C₀) ≤ Rbar :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hcomap_pg
  have hAbar_le_R : Abar ≤ Rbar :=
    le_trans (Subgroup.map_le_iff_le_comap.mp hStab) hcomap_le_R
  -- Step 7: `A ≤ O_{p',p}(G)`, which is defeq `comap (mk' N) (O_p(Ḡ))`
  -- (`{p_1 | p_1 ∉ {p}}` is defeq `{q | q ≠ p}` since `x ∈ {p} ≡ x = p`).
  change A ≤ Subgroup.comap mk (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N))
  rw [← Subgroup.map_le_iff_le_comap, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
  exact hAbar_le_R

open scoped commutatorElement in
/-- **BG Theorem A.5(1)** (mmd L4488): `p` odd, `G` solvable odd order, `P ◁ G` を `p`-部分群,
`X` を「`P` で正規化される abelian `p`-群」で生成される部分群とする。このとき
`X·C_G(P)/C_G(P) ⊆ O_p(G/C_G(P))`。

各生成子 `A` (abelian `p`-群, `P`-正規化) は `⁅P,A⁆ ≤ A` ∧ `⁅A,A⁆ = ⊥` ⇒ `⁅⁅P,A⁆,A⁆ = ⊥`
なので `stabilityLiftAux` (`K := P`, `P ◁ G`) で `A·C/C ⊆ O_p(G/C)`。`X ≤ ⨆ A` を iSup で分解。 -/
theorem thmA5_part1 [Finite G] (hp_odd : p ≠ 2) (hsolv : Group.IsSolvable G) (hodd : Odd
    (Nat.card G))
    {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {X : Subgroup G}
    (hX : X ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧ IsPGroup p ↥A ∧
        P ≤ Subgroup.normalizer (A : Set G)}, A) :
    X.map (QuotientGroup.mk' (Subgroup.centralizer (P : Set G)))
      ≤ OddOrder.Isaacs.Ch01.opCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  have : Group.IsSolvable G := hsolv
  refine le_trans (Subgroup.map_mono hX) ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  obtain ⟨hAcomm, hA_pg, hA_norm⟩ := hA
  have hPAA : ⁅⁅P, A⁆, A⁆ = (⊥ : Subgroup G) := by
    have hPA_le : ⁅P, A⁆ ≤ A := by
      rw [Subgroup.commutator_comm]
      exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hA_norm
    have hAA : ⁅A, A⁆ = (⊥ : Subgroup G) := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hAcomm.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    exact le_bot_iff.mp (le_trans (Subgroup.commutator_mono hPA_le le_rfl) hAA.le)
  exact stabilityLiftAux hp_odd hodd hP hA_pg hPAA rfl

/-- **BG Theorem A.5(2)** (mmd L4488, part 2): `p` odd, `G` solvable odd order, `P ◁ G` a `p`-group,
`X` generated by `P`-normalized abelian `p`-groups. If `O_{p'}(G) = 1` and `C_{O_p(G)}(P) ⊆ P`,
then `X ⊆ O_p(G)`.

`Q := O_p(G)`, `C := C_G(P)`. (1) `P ≤ Q` (normal `p`-group). (2) `C_G(Q) ≤ Q`
(Hall-Higman, Prop 1.15(b)). (3) every `p'`-element `u ∈ C` centralizes `Q` via Prop 1.10
(`⟨u⟩` acts on `Q` by conjugation; `C_Q(C_Q(u)) ⊆ C_Q(P) = C∩Q ⊆ P ⊆ C_Q(u)`), hence
`u ∈ C_G(Q) ⊆ Q` forces `u = 1`. (4) so `C` is a `p`-group (Cauchy), and `C ◁ G` gives `C ≤ Q`.
(5) `C ≤ Q` lets part (1)'s `XC/C ⊆ O_p(G/C)` pull back (`comap`, `ker(mk' C) = C` a `p`-group)
to `X ⊆ Q`. -/
theorem thmA5_part2 [Finite G] (hp_odd : p ≠ 2) (hsolv : Group.IsSolvable G)
    (hodd : Odd (Nat.card G))
    {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    {X : Subgroup G}
    (hX : X ≤ ⨆ A ∈ {A : Subgroup G | IsMulCommutative ↥A ∧ IsPGroup p ↥A ∧
        P ≤ Subgroup.normalizer (A : Set G)}, A)
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥)
    (hCP : Subgroup.centralizer (P : Set G) ⊓ OddOrder.Isaacs.Ch01.opCore p G ≤ P) :
    X ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  have : Group.IsSolvable G := hsolv
  classical
  set Q : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hQ
  set C : Subgroup G := Subgroup.centralizer (P : Set G) with hC
  -- Step 1: `P ≤ Q` (normal `p`-group).
  have hP_le_Q : P ≤ Q := OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hP
  -- Step 2: `C_G(Q) ≤ Q` (Hall-Higman, Prop 1.15(b)).
  have hset : {p_1 | p_1 ∉ ({p} : Set ℕ)} = {q | q ≠ p} := by ext q; simp
  have hCGQ_le_Q : Subgroup.centralizer (Q : Set G) ≤ Q := by
    have hHH := OddOrder.BG.Ch1.S01.hall_higman_solvable_specialization (p := p) (G := G)
      (by rw [hset]; exact hOp')
    rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore, ← hQ] at hHH
    exact hHH
  -- Step 3: every `p'`-element `u ∈ C` is trivial.
  have hstep3 : ∀ u : G, u ∈ C → (orderOf u).Coprime p → u = 1 := by
    intro u huC hu_cop
    -- conjugation action of `⟨u⟩` on `Q`
    set φ : ↥(Subgroup.zpowers u) →* MulAut ↥Q :=
      (MulAut.conjNormal (H := Q)).comp (Subgroup.zpowers u).subtype with hφ
    have hφcoe : ∀ (a : ↥(Subgroup.zpowers u)) (g : ↥Q),
        ((φ a) g : G) = (a : G) * (g : G) * (a : G)⁻¹ := by
      intro a g; rw [hφ]; simp [MulAut.conjNormal_apply]
    -- (i) `P.subgroupOf Q ≤ fixedPointsOfMulAut φ`  (`P ⊆ C_Q(u)`)
    have hPsub_le_fix : P.subgroupOf Q ≤ Subgroup.fixedPointsOfMulAut φ := by
      intro g hg
      rw [Subgroup.mem_subgroupOf] at hg
      rw [Subgroup.mem_fixedPointsOfMulAut]
      intro a
      refine Subtype.ext ?_
      rw [hφcoe]
      have hcu : Commute (g : G) u := Subgroup.mem_centralizer_iff.mp huC (g : G) hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hcomm_a : Commute (a : G) (g : G) := by
        rw [← hk]; exact (hcu.symm).zpow_left k
      rw [hcomm_a.eq, mul_assoc, mul_inv_cancel, mul_one]
    -- (ii) `C_Q(P) ≤ P.subgroupOf Q`  (`= C∩Q ⊆ P`)
    have hCQP_le_Psub : Subgroup.centralizer ((P.subgroupOf Q : Subgroup ↥Q) : Set ↥Q)
        ≤ P.subgroupOf Q := by
      intro g hg
      rw [Subgroup.mem_subgroupOf]
      apply hCP
      rw [Subgroup.mem_inf]
      refine ⟨?_, g.2⟩
      rw [hC, Subgroup.mem_centralizer_iff]
      intro x hxP
      have hxQ : x ∈ Q := hP_le_Q hxP
      have hx'_mem : (⟨x, hxQ⟩ : ↥Q) ∈ (P.subgroupOf Q : Subgroup ↥Q) := by
        rw [Subgroup.mem_subgroupOf]; exact hxP
      have h := Subgroup.mem_centralizer_iff.mp hg ⟨x, hxQ⟩ hx'_mem
      have h2 := congrArg Subtype.val h
      simpa using h2
    -- combine: `C_Q(C_Q(u)) ⊆ C_Q(u)`
    have hCC : Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥Q)
        ≤ Subgroup.fixedPointsOfMulAut φ :=
      calc Subgroup.centralizer (Subgroup.fixedPointsOfMulAut φ : Set ↥Q)
          ≤ Subgroup.centralizer ((P.subgroupOf Q : Subgroup ↥Q) : Set ↥Q) :=
            Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPsub_le_fix)
        _ ≤ P.subgroupOf Q := hCQP_le_Psub
        _ ≤ Subgroup.fixedPointsOfMulAut φ := hPsub_le_fix
    -- coprimality + nilpotence for Prop 1.10
    have : Group.IsNilpotent ↥Q := (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).isNilpotent
    have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers u)) (Nat.card ↥Q) := by
      obtain ⟨n, hn⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).exists_card_eq
      rw [Nat.card_zpowers, hQ, hn]
      exact hu_cop.pow_right n
    -- Prop 1.10: `⟨u⟩` acts trivially on `Q`
    have htrivφ := OddOrder.BG.Ch1.S01.coprime_nilpotent_acts_trivially_of_centralizer_self
      (A := ↥(Subgroup.zpowers u)) (G := ↥Q) (φ := φ) hcop hCC
    -- `u` centralizes `Q`
    have hu_cent_Q : u ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxQ
      have h := htrivφ ⟨u, Subgroup.mem_zpowers u⟩ ⟨x, hxQ⟩
      have hco := congrArg Subtype.val h
      rw [hφcoe] at hco
      have hco' : u * x * u⁻¹ = x := hco
      have hux : u * x = x * u := by
        have := congrArg (· * u) hco'
        simpa [mul_assoc] using this
      exact hux.symm
    -- `u ∈ C_G(Q) ⊆ Q`, and `u` is both a `p`- and `p'`-element ⇒ `u = 1`
    have huQ : u ∈ Q := hCGQ_le_Q hu_cent_Q
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (OddOrder.Isaacs.Ch01.opCore_isPGroup p G))
      ⟨u, huQ⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk1 : orderOf u = 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa using hk
      · exact absurd (Nat.eq_one_of_dvd_coprimes hu_cop
          (by rw [hk]; exact dvd_pow_self p hkpos.ne') (dvd_refl p)) (Fact.out : p.Prime).ne_one
    exact orderOf_eq_one_iff.mp hk1
  -- Step 4: `C` is a `p`-group (no nontrivial `p'`-element, via Cauchy).
  have hC_pg : IsPGroup p ↥C := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro q hq hqdvd
    by_contra hqp
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqdvd
    have hg_cop : (orderOf (g : G)).Coprime p := by
      rw [Subgroup.orderOf_coe, hg]
      exact (Nat.coprime_primes hq Fact.out).mpr hqp
    have hg1 : (g : G) = 1 := hstep3 (g : G) g.2 hg_cop
    have hq1 : q = 1 := by rw [← hg, ← Subgroup.orderOf_coe, hg1, orderOf_one]
    exact hq.ne_one hq1
  -- Step 5: pull back part (1) through `mk' C` (since `C ≤ Q` and `ker(mk' C) = C` a `p`-group).
  have hPart1 := thmA5_part1 hp_odd hsolv hodd hP hX
  have hcomap_pg : IsPGroup p
      ((OddOrder.Isaacs.Ch01.opCore p (G ⧸ C)).comap (QuotientGroup.mk' C)) := by
    refine (OddOrder.Isaacs.Ch01.opCore_isPGroup p _).comap_of_ker_isPGroup
      (QuotientGroup.mk' C) ?_
    rw [QuotientGroup.ker_mk']
    exact hC_pg
  have hcomap_le_Q :
      (OddOrder.Isaacs.Ch01.opCore p (G ⧸ C)).comap (QuotientGroup.mk' C) ≤ Q :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hcomap_pg
  have hX_comap : X ≤ (OddOrder.Isaacs.Ch01.opCore p (G ⧸ C)).comap (QuotientGroup.mk' C) :=
    Subgroup.map_le_iff_le_comap.mp hPart1
  exact le_trans hX_comap hcomap_le_Q

end PStability

end OddOrder.BG.AppA


