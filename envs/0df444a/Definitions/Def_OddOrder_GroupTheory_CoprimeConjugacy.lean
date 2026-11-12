-- Prove2me | Definitions.Def_OddOrder_GroupTheory_CoprimeConjugacy
-- name    : OddOrder_GroupTheory_CoprimeConjugacy
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:34.64102+00:00
-- url     : https://prove2.me/theorems/a74b64ed-1d48-422e-a94a-49b44f0d6c6a
-- title:
--   Conjugacy of commuting coprime products
-- statement:
--   Collects elementary counting facts needed for the Dade isometry (Peterfalvi §4, notably the adjoint formula (2.7)). The setting: an element $a\in G$ and a subgroup $H\le C_G(a)$ of order coprime to $\mathrm{ord}(a)$. For $x\in H$ the product $ax$ behaves like a coprime decomposition into a $\pi$-part $a$ and a $\pi'$-part $x$, with a single exponent $k$ from the Chinese remainder theorem fixing $a$ and $x$-parts simultaneously.
--
--   Main definitions: `cosetConjImage` (the $H$-conjugates of the coset $C_H(g)g$ as an image) and `cosetConjImage_subset_coset` (each conjugate lies in the coset $Hg$).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/CoprimeConjugacy.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/CoprimeConjugacy.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.ModEq
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- The Chinese-remainder exponent: if `n` is coprime to `orderOf a`, there is a
single exponent `k` with `a ^ k = a` that simultaneously sends every element of
order dividing `n` to `1`.

This is the elementary substitute for "raising to the `π`-part" used throughout
Peterfalvi §4: with `H ≤ C_G(a)` of order coprime to `orderOf a`, taking `k`-th
powers extracts the `a`-component of `a * x` for `x ∈ H`. -/
theorem exists_pow_eq_self_and_forall_pow_eq_one (a : G) {n : ℕ}
    (hn : Nat.Coprime (orderOf a) n) :
    ∃ k : ℕ, a ^ k = a ∧ ∀ x : G, orderOf x ∣ n → x ^ k = 1 := by
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hn 1 0
  refine ⟨k, ?_, ?_⟩
  · have : a ^ k = a ^ 1 := pow_eq_pow_iff_modEq.mpr hk1
    simpa using this
  · intro x hx
    have hnk : n ∣ k := (Nat.modEq_zero_iff_dvd).mp hk0
    exact orderOf_dvd_iff_pow_eq_one.mp (hx.trans hnk)

/-- **Conjugacy rigidity** for commuting coprime products.

If `a * x` is conjugate (by `t`) to `a * x'`, where `x` and `x'` commute with `a`
and have orders dividing some `n` coprime to `orderOf a`, then `t` already
centralizes `a` and conjugates `x` to `x'`.

This is the formal content of Peterfalvi's "`a = (a x)_π` is conjugate to
`b = (b v)_π`" step. -/
theorem conj_fixes_of_commute {a x x' t : G} (hx : Commute a x) (hx' : Commute a x')
    {n : ℕ} (hn : Nat.Coprime (orderOf a) n)
    (hxn : orderOf x ∣ n) (hx'n : orderOf x' ∣ n)
    (hconj : t * (a * x) * t⁻¹ = a * x') :
    t * a * t⁻¹ = a ∧ t * x * t⁻¹ = x' := by
  obtain ⟨k, hak, hone⟩ := exists_pow_eq_self_and_forall_pow_eq_one a hn
  have hfix : t * a * t⁻¹ = a := by
    have hpow : (t * (a * x) * t⁻¹) ^ k = (a * x') ^ k := by rw [hconj]
    rw [conj_pow, hx.mul_pow, hx'.mul_pow, hak, hone x hxn, hone x' hx'n,
      mul_one] at hpow
    exact hpow
  refine ⟨hfix, mul_left_cancel (a := a) ?_⟩
  calc a * (t * x * t⁻¹)
      = (t * a * t⁻¹) * (t * x * t⁻¹) := by rw [hfix]
    _ = t * (a * x) * t⁻¹ := by group
    _ = a * x' := hconj

/-- **Cross conjugacy rigidity** (Peterfalvi (2.4.b) core): if `a * u` is conjugate
to `b * v`, where `u` commutes with `a`, `v` commutes with `b`, both `u, v` have
order dividing some `m` coprime to `orderOf a` and to `orderOf b`, then already
`a` is conjugate to `b`.

Peterfalvi extracts the `π`-parts `a = (a u)_π` and `b = (b v)_π`; here a single
CRT exponent `k`, built modulo `lcm (orderOf a) (orderOf b)` and `m`, plays that
role. -/
theorem isConj_of_isConj_mul {a b u v : G} (hu : Commute a u) (hv : Commute b v)
    {m : ℕ} (ham : Nat.Coprime (orderOf a) m) (hbm : Nat.Coprime (orderOf b) m)
    (hum : orderOf u ∣ m) (hvm : orderOf v ∣ m)
    (h : IsConj (a * u) (b * v)) : IsConj a b := by
  obtain ⟨t, ht⟩ := isConj_iff.mp h
  have modEq_of_dvd : ∀ {x y d M : ℕ}, d ∣ M → x ≡ y [MOD M] → x ≡ y [MOD d] := by
    intro x y d M hd hxy
    rw [Nat.modEq_iff_dvd] at hxy ⊢
    exact (Int.natCast_dvd_natCast.mpr hd).trans hxy
  have hlcmcop : Nat.Coprime (Nat.lcm (orderOf a) (orderOf b)) m :=
    Nat.Coprime.coprime_dvd_left
      (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
      (Nat.coprime_mul_iff_left.mpr ⟨ham, hbm⟩)
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hlcmcop 1 0
  have hak : a ^ k = a := by
    have : a ^ k = a ^ 1 :=
      pow_eq_pow_iff_modEq.mpr (modEq_of_dvd (dvd_lcm_left _ _) hk1)
    simpa using this
  have hbk : b ^ k = b := by
    have : b ^ k = b ^ 1 :=
      pow_eq_pow_iff_modEq.mpr (modEq_of_dvd (dvd_lcm_right _ _) hk1)
    simpa using this
  have hmk : m ∣ k := (Nat.modEq_zero_iff_dvd).mp hk0
  have huk : u ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (hum.trans hmk)
  have hvk : v ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (hvm.trans hmk)
  refine isConj_iff.mpr ⟨t, ?_⟩
  have hpow : (t * (a * u) * t⁻¹) ^ k = (b * v) ^ k := by rw [ht]
  rw [conj_pow, hu.mul_pow, hv.mul_pow, hak, hbk, huk, hvk, mul_one, mul_one] at hpow
  exact hpow

/-- **Fiber count for the Dade-map computation.**

Fix `a : G` and a subgroup `H ≤ C_G(a)` of order coprime to `orderOf a`, with
`C_G(a)` normalizing `H`.  For `g` conjugate to some `a * x₀` (`x₀ ∈ H`), the set
of pairs `(x, t)` with `x ∈ H` and `t * (a * x) * t⁻¹ = g` is a single left coset
of `C_G(a)`, hence has cardinality `|C_G(a)|`.

This is the precise content of Peterfalvi's "`𝒜(g, H(a)a) = x C_G(a)`" remark in
the proof of (2.10.3); it drives the inner-product reduction (2.7). -/
theorem card_conj_fiber {a : G} {H : Subgroup G}
    (hcomm : ∀ x ∈ H, Commute a x)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ x ∈ H, c * x * c⁻¹ ∈ H)
    (hcop : Nat.Coprime (orderOf a) (Nat.card H))
    {g x₀ : G} (hx₀H : x₀ ∈ H) (hx₀ : IsConj (a * x₀) g) :
    Nat.card {p : G × G // p.1 ∈ H ∧ p.2 * (a * p.1) * p.2⁻¹ = g}
      = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  classical
  obtain ⟨t₀, ht₀⟩ := isConj_iff.mp hx₀
  have hx₀n : orderOf x₀ ∣ Nat.card H := H.orderOf_dvd_natCard hx₀H
  -- Conjugacy rigidity, packaged for the elements appearing below.
  have key : ∀ x ∈ H, ∀ k : G, k * (a * x) * k⁻¹ = a * x₀ →
      k * a * k⁻¹ = a ∧ k * x * k⁻¹ = x₀ := fun x hx k hk =>
    conj_fixes_of_commute (hcomm x hx) (hcomm x₀ hx₀H) hcop
      (H.orderOf_dvd_natCard hx) hx₀n hk
  have memK : ∀ k : G, k * a * k⁻¹ = a → k ∈ Subgroup.centralizer ({a} : Set G) :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hk)
  have ofK : ∀ k ∈ Subgroup.centralizer ({a} : Set G), k * a * k⁻¹ = a :=
    fun k hk => mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_singleton_iff.mp hk)
  refine Nat.card_congr ?_
  refine
    { toFun := fun p => ⟨t₀⁻¹ * p.1.2, memK _ ?_⟩
      invFun := fun k => ⟨(k.1⁻¹ * x₀ * k.1, t₀ * k.1), ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- `t₀⁻¹ * t` conjugates `a*x` to `a*x₀`, so it centralizes `a`.
    have hconj : (t₀⁻¹ * p.1.2) * (a * p.1.1) * (t₀⁻¹ * p.1.2)⁻¹ = a * x₀ := by
      have e : (t₀⁻¹ * p.1.2) * (a * p.1.1) * (t₀⁻¹ * p.1.2)⁻¹
          = t₀⁻¹ * (p.1.2 * (a * p.1.1) * p.1.2⁻¹) * t₀ := by group
      rw [e, p.2.2, ← ht₀]; group
    exact (key p.1.1 p.2.1 _ hconj).1
  · -- `k⁻¹ * x₀ * k ∈ H`
    have h := hnorm k.1⁻¹ (Subgroup.inv_mem _ k.2) x₀ hx₀H
    rwa [inv_inv] at h
  · -- `(t₀ k) * (a * (k⁻¹ x₀ k)) * (t₀ k)⁻¹ = g`
    have hk := ofK k.1 k.2
    calc (t₀ * k.1) * (a * (k.1⁻¹ * x₀ * k.1)) * (t₀ * k.1)⁻¹
        = t₀ * ((k.1 * a * k.1⁻¹) * x₀) * t₀⁻¹ := by group
      _ = t₀ * (a * x₀) * t₀⁻¹ := by rw [hk]
      _ = g := ht₀
  · -- left inverse
    rintro ⟨⟨x, t⟩, hx, ht⟩
    have hconj : (t₀⁻¹ * t) * (a * x) * (t₀⁻¹ * t)⁻¹ = a * x₀ := by
      have e : (t₀⁻¹ * t) * (a * x) * (t₀⁻¹ * t)⁻¹
          = t₀⁻¹ * (t * (a * x) * t⁻¹) * t₀ := by group
      rw [e, ht, ← ht₀]; group
    have hx_eq : (t₀⁻¹ * t)⁻¹ * x₀ * (t₀⁻¹ * t) = x := by
      have h2 := (key x hx _ hconj).2
      rw [← h2]; group
    apply Subtype.ext
    apply Prod.ext
    · exact hx_eq
    · change t₀ * (t₀⁻¹ * t) = t; group
  · -- right inverse
    rintro ⟨k, hk⟩
    apply Subtype.ext
    change t₀⁻¹ * (t₀ * k) = k; group

section CosetConjugacy

variable {g : G} {H : Subgroup G}

/-- **Conjugacy rigidity for the normalizing coset** (Peterfalvi (2.1), the
"`g^x = (ug)^x_π = (vg)^y_π = g^y`" step).

If `u, v` commute with `g` and have order coprime-killed by the CRT exponent for
`g` (here: order dividing `n` with `n` coprime to `orderOf g`), then any equality
of conjugates `x⁻¹ (u g) x = y⁻¹ (v g) y` forces `y x⁻¹` to centralize `g`.

This is a direct consequence of `conj_fixes_of_commute` applied to `g` and the
conjugator `y x⁻¹`. -/
theorem conj_centralizes_of_coset_conj_eq {x y u v : G} (hu : Commute g u)
    (hv : Commute g v) {n : ℕ} (hn : Nat.Coprime (orderOf g) n)
    (hun : orderOf u ∣ n) (hvn : orderOf v ∣ n)
    (h : x⁻¹ * (u * g) * x = y⁻¹ * (v * g) * y) :
    (y * x⁻¹) * g * (y * x⁻¹)⁻¹ = g := by
  -- Rewrite the hypothesis as a single conjugation `t (g u) t⁻¹ = g v` with `t = y x⁻¹`.
  have hconj : (y * x⁻¹) * (g * u) * (y * x⁻¹)⁻¹ = g * v := by
    rw [hu.eq, hv.eq]
    have e : (y * x⁻¹) * (u * g) * (y * x⁻¹)⁻¹
        = y * (x⁻¹ * (u * g) * x) * y⁻¹ := by group
    rw [e, h]; group
  exact (conj_fixes_of_commute hu hv hn hun hvn hconj).1

/-- **Membership form of `(2.1)` rigidity.**  With `C_H(g) = H ⊓ C_G(g)`: if
`u, v ∈ C_H(g)` (so `|C_H(g)|`, hence `orderOf u, orderOf v`, is coprime to
`orderOf g`) and `x, y ∈ H` satisfy `x⁻¹ (u g) x = y⁻¹ (v g) y`, then
`y x⁻¹ ∈ C_H(g)`.  Equivalently the right cosets `C_H(g) x` and `C_H(g) y`
coincide — the disjointness in the statement of (2.1). -/
theorem mem_centralizer_of_coset_conj_eq
    (hcop : Nat.Coprime (orderOf g) (Nat.card H)) [Finite H]
    {x y u v : G} (hx : x ∈ H) (hy : y ∈ H)
    (hu : u ∈ H ⊓ Subgroup.centralizer ({g} : Set G))
    (hv : v ∈ H ⊓ Subgroup.centralizer ({g} : Set G))
    (h : x⁻¹ * (u * g) * x = y⁻¹ * (v * g) * y) :
    y * x⁻¹ ∈ H ⊓ Subgroup.centralizer ({g} : Set G) := by
  obtain ⟨huH, hucomm⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨hvH, hvcomm⟩ := Subgroup.mem_inf.mp hv
  have hu' : Commute g u :=
    (Subgroup.mem_centralizer_singleton_iff.mp hucomm).symm
  have hv' : Commute g v :=
    (Subgroup.mem_centralizer_singleton_iff.mp hvcomm).symm
  have hfix := conj_centralizes_of_coset_conj_eq hu' hv' hcop
    (H.orderOf_dvd_natCard huH) (H.orderOf_dvd_natCard hvH) h
  exact Subgroup.mem_inf.mpr
    ⟨H.mul_mem hy (H.inv_mem hx),
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)⟩

/-- The `H`-conjugates of the coset `C_H(g) g`, packaged as the image of
`(c, x) ↦ x⁻¹ (c g) x` (`c ∈ C_H(g)`, `x ∈ H`).  This is the set `K = Hg` of
the textbook proof of (2.1). -/
private def cosetConjImage (g : G) (H : Subgroup G) : Set G :=
  Set.range fun p : ↥(H ⊓ Subgroup.centralizer ({g} : Set G)) × ↥H =>
    (p.2 : G)⁻¹ * ((p.1 : G) * g) * (p.2 : G)

variable (hnorm : ∀ x ∈ H, g * x * g⁻¹ ∈ H)

include hnorm in
/-- Each conjugate `x⁻¹ (c g) x` (`c ∈ C_H(g)`, `x ∈ H`) lies in the coset `Hg`. -/
private theorem cosetConjImage_subset_coset :
    cosetConjImage g H ⊆ {w | w * g⁻¹ ∈ H} := by
  rintro _ ⟨⟨c, x⟩, rfl⟩
  obtain ⟨hcH, _⟩ := Subgroup.mem_inf.mp c.2
  -- `x⁻¹ (c g) x g⁻¹ = (x⁻¹ c) (g x g⁻¹) ∈ H`.
  have hgxg : g * (x : G) * g⁻¹ ∈ H := hnorm _ x.2
  have key : (x : G)⁻¹ * ((c : G) * g) * (x : G) * g⁻¹
      = ((x : G)⁻¹ * (c : G)) * (g * (x : G) * g⁻¹) := by group
  rw [Set.mem_ofPred_eq, key]
  exact H.mul_mem (H.mul_mem (H.inv_mem x.2) hcH) hgxg

/-- **Cardinality of the conjugate image** (Peterfalvi (2.1)).  The set
`K = ⋃_{x∈H} (C_H(g) g)^x` has exactly `|H|` elements: it is the disjoint union
of `|H : C_H(g)|` translated copies of `C_H(g) g`, each of size `|C_H(g)|`.

The proof is the textbook count `|K| = |H : C_H(g)| · |C_H(g) g| = |H|` realized
as a fiberwise count of the surjection `(c, x) ↦ x⁻¹ (c g) x` onto `K`: every
fiber is the orbit `{(e c₀ e⁻¹, e x₀) : e ∈ C_H(g)}` of a witness, hence has size
`|C_H(g)|`, and the domain has size `|C_H(g)| · |H|`.  (Normalization of `H` by
`g` is not needed for the count itself, only for `K ⊆ Hg`.) -/
private theorem card_cosetConjImage
    [Finite G] (hcop : Nat.Coprime (orderOf g) (Nat.card H)) :
    Nat.card (cosetConjImage g H) = Nat.card H := by
  classical
  let : Fintype G := Fintype.ofFinite G
  set C : Subgroup G := H ⊓ Subgroup.centralizer ({g} : Set G) with hC
  -- The conjugation map and the target finset `T = K`.
  set Φ : ↥C × ↥H → G := fun p => (p.2 : G)⁻¹ * ((p.1 : G) * g) * (p.2 : G) with hΦ
  set T : Finset G := (Finset.univ : Finset (↥C × ↥H)).image Φ with hT
  have hrange : (T : Set G) = cosetConjImage g H := by
    rw [hT, Finset.coe_image, Finset.coe_univ, Set.image_univ]; rfl
  -- Fiber count: each fiber over `w ∈ T` has card `|C|`.
  have hfiber : ∀ w ∈ T, (Finset.univ.filter (fun p => Φ p = w)).card = Nat.card C := by
    intro w hw
    rw [hT, Finset.mem_image] at hw
    obtain ⟨⟨c₀, x₀⟩, -, hcx₀⟩ := hw
    have hcx₀' : (x₀ : G)⁻¹ * ((c₀ : G) * g) * (x₀ : G) = w := hcx₀
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := ↥C)]
    -- `e ↦ (e c₀ e⁻¹, e x₀)` bijects `C` with the fiber; inverse `(c,x) ↦ x x₀⁻¹`.
    -- membership of `x x₀⁻¹` in `C` (via rigidity), packaged for `i`.
    have hiMem : ∀ p : ↥C × ↥H, p ∈ Finset.univ.filter (fun p => Φ p = w) →
        (p.2 : G) * (x₀ : G)⁻¹ ∈ C := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have heq : (p.2 : G)⁻¹ * ((p.1 : G) * g) * (p.2 : G)
          = (x₀ : G)⁻¹ * ((c₀ : G) * g) * (x₀ : G) := by
        have : Φ p = w := hp.2; rw [hcx₀']; exact this
      have hmemC := mem_centralizer_of_coset_conj_eq (g := g) (H := H) hcop
        p.2.2 x₀.2 p.1.2 c₀.2 heq
      have := C.inv_mem hmemC
      rwa [mul_inv_rev, inv_inv] at this
    have hjMem : ∀ e : ↥C, (e : G) * (x₀ : G) ∈ H := fun e =>
      H.mul_mem ((Subgroup.mem_inf.mp e.2).1) x₀.2
    refine Finset.card_bij'
      (i := fun (p : ↥C × ↥H) hp => (⟨(p.2 : G) * (x₀ : G)⁻¹, hiMem p hp⟩ : ↥C))
      (j := fun (e : ↥C) _ =>
        ((e * c₀ * e⁻¹ : ↥C), (⟨(e : G) * (x₀ : G), hjMem e⟩ : ↥H)))
      (fun p _ => Finset.mem_univ _) ?_ ?_ ?_
    · -- `j e ∈ fiber`
      intro e _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨-, hecomm⟩ := Subgroup.mem_inf.mp e.2
      have hge : Commute (e : G) g := Subgroup.mem_centralizer_singleton_iff.mp hecomm
      have hge' : (e : G)⁻¹ * g = g * (e : G)⁻¹ := hge.inv_left
      change ((e : G) * (x₀ : G))⁻¹ * (((e : G) * (c₀ : G) * (e : G)⁻¹) * g)
        * ((e : G) * (x₀ : G)) = w
      rw [← hcx₀']
      calc ((e : G) * (x₀ : G))⁻¹ * (((e : G) * (c₀ : G) * (e : G)⁻¹) * g) * ((e : G) * (x₀ : G))
          = (x₀ : G)⁻¹ * ((c₀ : G) * ((e : G)⁻¹ * g * (e : G))) * (x₀ : G) := by group
        _ = (x₀ : G)⁻¹ * ((c₀ : G) * g) * (x₀ : G) := by rw [hge']; group
    · -- left inverse: `j (i p) = p`.  With `e := x x₀⁻¹`, recover `c` and `x`.
      rintro ⟨c, x⟩ hmem
      rw [Finset.mem_filter] at hmem
      have hΦeq : (x : G)⁻¹ * ((c : G) * g) * (x : G) = w := hmem.2
      have heq : (x : G)⁻¹ * ((c : G) * g) * (x : G)
          = (x₀ : G)⁻¹ * ((c₀ : G) * g) * (x₀ : G) := by rw [hΦeq, hcx₀']
      obtain ⟨-, hecomm⟩ :=
        Subgroup.mem_inf.mp
          (mem_centralizer_of_coset_conj_eq (g := g) (H := H) hcop x.2 x₀.2 c.2 c₀.2 heq)
      -- `x₀ x⁻¹` centralizes `g`.
      have hcomm : (x₀ : G) * (x : G)⁻¹ * g = g * ((x₀ : G) * (x : G)⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp hecomm
      apply Prod.ext
      · -- first coordinate `(x x₀⁻¹) c₀ (x x₀⁻¹)⁻¹ = c`
        apply Subtype.ext
        change (x : G) * (x₀ : G)⁻¹ * (c₀ : G) * ((x : G) * (x₀ : G)⁻¹)⁻¹ = (c : G)
        -- from `x⁻¹ c g x = x₀⁻¹ c₀ g x₀`, conjugate by `x` and `x₀`.
        have e1 : (x : G)⁻¹ * (c : G) * g * (x : G) = (x₀ : G)⁻¹ * (c₀ : G) * g * (x₀ : G) := by
          rw [show (x : G)⁻¹ * (c : G) * g * (x : G) = (x : G)⁻¹ * ((c : G) * g) * (x : G) by group,
            show (x₀ : G)⁻¹ * (c₀ : G) * g * (x₀ : G)
              = (x₀ : G)⁻¹ * ((c₀ : G) * g) * (x₀ : G) by group]
          exact heq
        -- `c g = (x x₀⁻¹) c₀ g (x₀ x⁻¹)`
        have e2 : (c : G) * g = (x : G) * (x₀ : G)⁻¹ * ((c₀ : G) * g) * ((x₀ : G) * (x : G)⁻¹) := by
          calc (c : G) * g
              = (x : G) * ((x : G)⁻¹ * (c : G) * g * (x : G)) * (x : G)⁻¹ := by group
            _ = (x : G) * ((x₀ : G)⁻¹ * (c₀ : G) * g * (x₀ : G)) * (x : G)⁻¹ := by rw [e1]
            _ = (x : G) * (x₀ : G)⁻¹ * ((c₀ : G) * g) * ((x₀ : G) * (x : G)⁻¹) := by group
        -- swap `g` past `x₀ x⁻¹` on the RHS via `hcomm`, then cancel `g`.
        have e3 : (c : G) * g
            = (x : G) * (x₀ : G)⁻¹ * (c₀ : G) * ((x : G) * (x₀ : G)⁻¹)⁻¹ * g := by
          rw [e2, mul_inv_rev, inv_inv]
          calc (x : G) * (x₀ : G)⁻¹ * ((c₀ : G) * g) * ((x₀ : G) * (x : G)⁻¹)
              = (x : G) * (x₀ : G)⁻¹ * (c₀ : G) * (g * ((x₀ : G) * (x : G)⁻¹)) := by group
            _ = (x : G) * (x₀ : G)⁻¹ * (c₀ : G) * (((x₀ : G) * (x : G)⁻¹) * g) := by rw [hcomm]
            _ = (x : G) * (x₀ : G)⁻¹ * (c₀ : G) * ((x₀ : G) * (x : G)⁻¹) * g := by group
        rw [mul_right_cancel e3]
      · -- second coordinate `x x₀⁻¹ · x₀ = x`
        apply Subtype.ext
        change (x : G) * (x₀ : G)⁻¹ * (x₀ : G) = (x : G)
        group
    · -- right inverse: `i (j e) = e`
      intro e _
      apply Subtype.ext
      change (e : G) * (x₀ : G) * (x₀ : G)⁻¹ = (e : G)
      group
  -- Domain card `= |C| · |H|`, fiberwise sum `= T.card · |C|`.
  have hsum := Finset.card_eq_sum_card_fiberwise (f := Φ)
    (s := (Finset.univ : Finset (↥C × ↥H))) (t := T)
    (fun p _ => Finset.mem_image_of_mem Φ (Finset.mem_univ p))
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hsum
  rw [Finset.card_univ, Fintype.card_prod, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at hsum
  -- `Nat.card K = T.card` (coe), and conclude.
  have hcardC : 0 < Nat.card C := Nat.card_pos
  have hTcard : T.card = Nat.card H := by
    have : Nat.card C * Nat.card H = T.card * Nat.card C := hsum
    have := this.symm
    rw [mul_comm (Nat.card C) (Nat.card H)] at this
    exact Nat.eq_of_mul_eq_mul_right hcardC this
  rw [← hrange, Nat.card_coe_set_eq, Set.ncard_coe_finset, hTcard]

/-- **Peterfalvi (2.1), set form.**  If `g` normalizes `H` and `⟨g⟩`, `H` have
coprime orders, then the coset `Hg` *equals* the union `⋃_{x∈H} (C_H(g) g)^x` of
the `H`-conjugates of `C_H(g) g`.

The textbook counting closure: the union is contained in `Hg` and has cardinality
`|H : C_H(g)| · |C_H(g)| = |H| = |Hg|`, so the two finite sets coincide. -/
theorem coset_eq_cosetConjImage [Finite G]
    (hcop : Nat.Coprime (orderOf g) (Nat.card H)) (hnorm : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    {w | w * g⁻¹ ∈ H} = cosetConjImage g H := by
  classical
  have hsub := cosetConjImage_subset_coset (g := g) (H := H) hnorm
  -- `Hg` is a translate of `H`, hence has `|H|` elements.
  have hcoset_card : Nat.card {w : G | w * g⁻¹ ∈ H} = Nat.card H := by
    refine Nat.card_congr (Equiv.symm ?_)
    refine
      { toFun := fun h => ⟨(h : G) * g, by
          rw [Set.mem_ofPred_eq, mul_assoc, mul_inv_cancel, mul_one]; exact h.2⟩
        invFun := fun w => ⟨(w : G) * g⁻¹, w.2⟩
        left_inv := fun h => by apply Subtype.ext; group
        right_inv := fun w => by apply Subtype.ext; group }
  -- Equal cardinalities + inclusion ⟹ equal sets.
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcoset_card,
    card_cosetConjImage (g := g) (H := H) hcop]

/-- **Peterfalvi (2.1), existence form.**  If `g` normalizes `H` and `⟨g⟩`, `H`
have coprime orders, then every element `h g` of the coset `Hg` is `H`-conjugate
to an element `c g` with `c ∈ C_H(g) = H ⊓ C_G(g)`.

This is the principal consequence used throughout the text: the coset `Hg`
collapses, under `H`-conjugation, onto `C_H(g) g`. -/
theorem exists_mem_centralizer_conj [Finite G]
    (hcop : Nat.Coprime (orderOf g) (Nat.card H)) (hnorm : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    {h : G} (hh : h ∈ H) :
    ∃ c ∈ H ⊓ Subgroup.centralizer ({g} : Set G), ∃ x ∈ H, x * (h * g) * x⁻¹ = c * g := by
  have hmem : h * g ∈ cosetConjImage g H := by
    rw [← coset_eq_cosetConjImage (g := g) (H := H) hcop hnorm]
    simpa using hh
  obtain ⟨⟨c, x⟩, hcx⟩ := hmem
  -- `hcx : x⁻¹ (c g) x = h g`, so `x (h g) x⁻¹ = c g`.
  refine ⟨c, c.2, (x : G), x.2, ?_⟩
  have hcx' : (x : G)⁻¹ * ((c : G) * g) * (x : G) = h * g := hcx
  calc (x : G) * (h * g) * (x : G)⁻¹
      = (x : G) * ((x : G)⁻¹ * ((c : G) * g) * (x : G)) * (x : G)⁻¹ := by rw [hcx']
    _ = (c : G) * g := by group

end CosetConjugacy

end OddOrder.GroupTheory


