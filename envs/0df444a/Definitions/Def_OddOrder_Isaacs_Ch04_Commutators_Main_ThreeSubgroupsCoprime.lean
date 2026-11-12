-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
-- name    : OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:16:03.896196+00:00
-- url     : https://prove2.me/theorems/ddc41869-fd5b-4046-bdd8-911cc5469e16
-- title:
--   Isaacs §4B: three-subgroups lemma for coprime actions (tail)
-- statement:
--   The tail of the coprime-action version of the three-subgroups development in the Isaacs, *Finite Group Theory*, Chapter 4 formalization. The main definition is `fittingProductHom`, the Fitting product homomorphism $\theta:G\to G$, $\theta(g)=\prod_{a\in A}\varphi_a(g)$.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/Main/ThreeSubgroupsCoprime.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/Main/ThreeSubgroupsCoprime.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- **Isaacs Lemma 4.28** ⭐ (= BG Prop 1.6(a), **FT クリティカル**):
A acts on G via φ. Coprime (`|A|, |G|`) + one of A or G solvable ⇒
`fixedPointsOfMulAut φ ⊔ actionCommutator φ = ⊤` (= `G = C_G(A) · [G, A]`).

**証明** (Isaacs p.138, ~6 lines): Write `Ḡ = G / [G, A]`. By Cor 3.28 (coprime fixed points
come from G fixed points), `C_Ḡ(A) = image of C_G(A) under quotient`. But A acts trivially
on `Ḡ` (definition of `[G, A]` ⇒ `A` fixes every coset, so `C_Ḡ(A) = Ḡ`).
Hence `image of C_G(A) = Ḡ`, i.e., `C_G(A) ⊔ [G, A] = G`.

**Lean 化**: 各 `g ∈ G`, Cor 3.28 を `N = [G, A]` で適用 ⇒ ∃ `c ∈ C_G(A), c ∈ g · [G, A]`,
i.e., `c = g * n` for `n ∈ [G, A]`. Then `g = c * n⁻¹ ∈ C_G(A) * [G, A]`. -/
theorem fixedPoints_sup_actionCommutator_eq_top
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G) :
    Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ = ⊤ := by
  rw [eq_top_iff]
  intro g _
  -- Setup: N := actionCommutator φ, which is normal and A-invariant
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φ) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
  -- For every a ∈ A, (φ a) g = g * n with n := g⁻¹ * (φ a) g ∈ actionCommutator
  -- (Lem 4.20 left form: actionCommutator ≤ actionCommutator gives this)
  have hg_fix : ∀ a : A, ∃ n ∈ actionCommutator φ, (φ a) g = g * n := by
    intro a
    refine ⟨g⁻¹ * (φ a) g, ?_, ?_⟩
    · exact (actionCommutator_le_iff_left φ (actionCommutator φ)).mp le_rfl a g
    · group
  -- Apply Cor 3.28: ∃ c ∈ C_G(A), c ∈ g · actionCommutator
  obtain ⟨c, hc_fix, ⟨n, hn_mem, hc_eq⟩⟩ :=
    coprime_fixedPoints_quotient hCop hSolv hN_inv hg_fix
  -- c ∈ fixedPointsOfMulAut, n⁻¹ ∈ actionCommutator
  have hc_mem : c ∈ Subgroup.fixedPointsOfMulAut φ := hc_fix
  -- g = c * n⁻¹: from hc_eq : c = g * n, so g = c * n⁻¹
  have hg_eq : g = c * n⁻¹ := by rw [hc_eq]; group
  -- g ∈ fixedPointsOfMulAut * actionCommutator ⊆ sup
  rw [hg_eq]
  exact Subgroup.mul_mem_sup hc_mem ((actionCommutator φ).inv_mem hn_mem)

/-- **Isaacs Lemma 4.29** (Γ form, solvable case = 書籍証明の第 1 段落): coprime +
(A or G solvable) ⇒
`iterCommutator inl(G).range inr(A).range 2 = iterCommutator inl(G).range inr(A).range 1`
in Γ = G ⋊[φ] A. Equivalent (Isaacs notation): `[G, A, A] = [G, A]`.

書籍の印刷形は solvability 仮定の無い無条件版
`iterCommutator_inl_inr_two_eq_one_of_coprime` (下記) — 本定理はその engine.

**証明** (Isaacs p.139): Each generator `⁅inl g, inr a⁆` of [G, A]_Γ is in [G, A, A]_Γ.
By Lem 4.28: g = c * x with c ∈ C_G(A), x ∈ actionCommutator.
- `⁅inl c, inr a⁆ = 1` (c ∈ C_G(A) ⇒ inl c and inr a commute in Γ).
- Commutator identity: `⁅inl c · inl x, inr a⁆ = inl c · ⁅inl x, inr a⁆ · inl c⁻¹ · ⁅inl c, inr a⁆`
  `= inl c · ⁅inl x, inr a⁆ · inl c⁻¹`.
- Conjugate by inl c (= conjugate_commutatorElement): `= ⁅inl(cxc⁻¹), inr a⁆` (using
  inl c commutes with inr a).
- `cxc⁻¹ ∈ actionCommutator` (G-normal), so `inl(cxc⁻¹) ∈ inl(actionCommutator) = [G, A]_Γ`
  (`actionCommutator_map_inl`).
- Hence `⁅inl(cxc⁻¹), inr a⁆ ∈ ⁅[G, A]_Γ, inr(A).range⁆ = [G, A, A]_Γ`. -/
theorem iterCommutator_inl_inr_two_eq_one
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G) :
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                   (SemidirectProduct.inr : A →* G ⋊[φ] A).range 2 =
    iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
                   (SemidirectProduct.inr : A →* G ⋊[φ] A).range 1 := by
  set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
  set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
  -- I1 = ⁅XG, YA⁆ = [G, A]_Γ, I2 = ⁅I1, YA⁆ = [G, A, A]_Γ
  -- I1.Normal in Γ (Lem 4.1 系 via XG ⊔ YA = ⊤)
  have hI1_normal : (⁅XG, YA⁆).Normal :=
    commutator_normal_of_sup_eq_top SemidirectProduct.inl_range_sup_inr_range_eq_top
  refine le_antisymm ?_ ?_
  · -- I2 ≤ I1 (trivial: I1 normal in Γ, so ⁅I1, F⁆ ≤ I1)
    show iterCommutator XG YA 2 ≤ iterCommutator XG YA 1
    change ⁅iterCommutator XG YA 1, YA⁆ ≤ iterCommutator XG YA 1
    rw [show iterCommutator XG YA 1 = ⁅XG, YA⁆ from rfl]
    exact Subgroup.commutator_le_left _ _
  · -- I1 ≤ I2 (the substantive direction)
    show iterCommutator XG YA 1 ≤ iterCommutator XG YA 2
    change ⁅XG, YA⁆ ≤ ⁅iterCommutator XG YA 1, YA⁆
    rw [Subgroup.commutator_le]
    rintro _ ⟨g_0, rfl⟩ _ ⟨a, rfl⟩
    -- Goal: ⁅inl g_0, inr a⁆ ∈ ⁅iterCommutator XG YA 1, YA⁆
    -- By Lem 4.28: g_0 = c * x, c ∈ fixedPoints, x ∈ actionCommutator
    have h_top : g_0 ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
      rw [fixedPoints_sup_actionCommutator_eq_top hCop hSolv]
      exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_right] at h_top
    obtain ⟨c, hc_fix, x, hx_ac, h_eq⟩ := h_top
    -- h_eq : c * x = g_0
    have h_fix : (φ a) c = c := hc_fix a
    -- ⁅inl c, inr a⁆ = 1 (c ∈ fixedPoints ⇒ inl c commutes with inr a)
    have h_commute_ca : Commute (SemidirectProduct.inl c : G ⋊[φ] A)
        (SemidirectProduct.inr a) := by
      -- inl c · inr a = inr a · inl c iff (φ a) c = c (which holds by h_fix)
      change (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
          SemidirectProduct.inr a * SemidirectProduct.inl c
      -- inr a * inl c * inr a⁻¹ = inl((φ a) c) = inl c (by inl_aut + h_fix)
      have h_aut := SemidirectProduct.inl_aut (φ := φ) a c
      rw [h_fix] at h_aut
      -- h_aut : inl c = inr a * inl c * inr a⁻¹
      -- Want: inl c * inr a = inr a * inl c
      -- From h_aut: inl c * inr a = (inr a * inl c * inr a⁻¹) * inr a
      --           = inr a * inl c * (inr a⁻¹ * inr a) = inr a * inl c
      have h_inv_eq : (SemidirectProduct.inr a⁻¹ : G ⋊[φ] A) =
          (SemidirectProduct.inr a)⁻¹ := map_inv SemidirectProduct.inr a
      rw [h_inv_eq] at h_aut
      rw [show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
            (SemidirectProduct.inr a * SemidirectProduct.inl c * (SemidirectProduct.inr a)⁻¹) *
              SemidirectProduct.inr a from by rw [← h_aut]]
      group
    have h_comm_ca_eq_one : ⁅(SemidirectProduct.inl c : G ⋊[φ] A),
        SemidirectProduct.inr a⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr h_commute_ca
    -- Goal: ⁅inl g_0, inr a⁆ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- g_0 = c * x, so inl g_0 = inl c * inl x. Use commutator identity.
    rw [← h_eq, map_mul SemidirectProduct.inl]
    -- Goal: ⁅inl c * inl x, inr a⁆ ∈ ...
    -- Identity: ⁅cx, a⁆ = c · ⁅x, a⁆ · c⁻¹ · ⁅c, a⁆
    have h_id : ⁅(SemidirectProduct.inl c * SemidirectProduct.inl x : G ⋊[φ] A),
        (SemidirectProduct.inr a : G ⋊[φ] A)⁆ =
        (SemidirectProduct.inl c : G ⋊[φ] A) *
          ⁅(SemidirectProduct.inl x : G ⋊[φ] A), SemidirectProduct.inr a⁆ *
          (SemidirectProduct.inl c)⁻¹ *
          ⁅(SemidirectProduct.inl c : G ⋊[φ] A), SemidirectProduct.inr a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h_id, h_comm_ca_eq_one, mul_one]
    -- Goal: inl c * ⁅inl x, inr a⁆ * (inl c)⁻¹ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- = ⁅inl c · inl x · (inl c)⁻¹, inl c · inr a · (inl c)⁻¹⁆ (conjugate_commutatorElement)
    -- inl c · inr a · (inl c)⁻¹ = inr a (commute)
    rw [conjugate_commutatorElement]
    have h_conj_ca : (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a *
        (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inr a := by
      rw [show (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inr a =
          SemidirectProduct.inr a * SemidirectProduct.inl c from h_commute_ca]
      group
    rw [h_conj_ca]
    -- Goal: ⁅inl c * inl x * (inl c)⁻¹, inr a⁆ ∈ ⁅⁅XG, YA⁆, YA⁆
    -- inl c * inl x * (inl c)⁻¹ = inl(c * x * c⁻¹) ∈ inl(actionCommutator) = ⁅XG, YA⁆
    have h_lift : (SemidirectProduct.inl c : G ⋊[φ] A) * SemidirectProduct.inl x *
        (SemidirectProduct.inl c)⁻¹ = SemidirectProduct.inl (c * x * c⁻¹) := by
      have h_inv : ((SemidirectProduct.inl c : G ⋊[φ] A))⁻¹ = SemidirectProduct.inl c⁻¹ :=
        (map_inv SemidirectProduct.inl c).symm
      rw [h_inv, ← map_mul, ← map_mul]
    rw [h_lift]
    -- c * x * c⁻¹ ∈ actionCommutator (G-normal)
    have : (actionCommutator φ).Normal := actionCommutator.normal φ
    have h_cxc_ac : c * x * c⁻¹ ∈ actionCommutator φ :=
      ‹(actionCommutator φ).Normal›.conj_mem _ hx_ac c
    -- inl(c * x * c⁻¹) ∈ (actionCommutator).map inl = ⁅XG, YA⁆ (= I1)
    have h_in_I1 : (SemidirectProduct.inl (c * x * c⁻¹) : G ⋊[φ] A) ∈ ⁅XG, YA⁆ := by
      have := actionCommutator_map_inl (φ := φ)
      rw [← this]
      exact ⟨c * x * c⁻¹, h_cxc_ac, rfl⟩
    exact Subgroup.commutator_mem_commutator h_in_I1 ⟨a, rfl⟩

/-- **Fitting product hom** `θ : G →* G` defined by `θ(g) = ∏ a : A, (φ a) g`.

Well-defined hom for abelian G (使用 Finset.prod_mul_distrib). 教科書 (Isaacs p.140) の
Thm 4.34 証明の核. -/
noncomputable def fittingProductHom {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    (φ : A →* MulAut G) : G →* G where
  toFun g := ∏ a : A, (φ a) g
  map_one' := by simp
  map_mul' x y := by
    simp_rw [map_mul]
    exact Finset.prod_mul_distrib

/-- **`fittingProductHom` of A-fixed element**: c ∈ C_G(A) ⇒ θ c = c^|A|. -/
lemma fittingProductHom_apply_of_fixed {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    {φ : A →* MulAut G} {c : G} (hc : ∀ a : A, (φ a) c = c) :
    fittingProductHom φ c = c ^ Nat.card A := by
  change ∏ a : A, (φ a) c = c ^ Nat.card A
  have h_eq : ∏ a : A, (φ a) c = ∏ _a : A, c :=
    Finset.prod_congr rfl (fun a _ => hc a)
  rw [h_eq, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **`fittingProductHom` of action-image**: For g ∈ G, a ∈ A,
`θ ((φ a) g) = θ g` (using `b ↦ b * a` is a permutation of A). -/
lemma fittingProductHom_apply_of_smul {A G : Type*} [CommGroup G] [Group A] [Fintype A]
    {φ : A →* MulAut G} (g : G) (a : A) :
    fittingProductHom φ ((φ a) g) = fittingProductHom φ g := by
  change ∏ b : A, (φ b) ((φ a) g) = ∏ b : A, (φ b) g
  -- Rewrite (φ b) ∘ (φ a) = φ (b * a) using map_mul
  have h_compose : ∀ b : A, (φ b) ((φ a) g) = (φ (b * a)) g := fun b => by
    rw [← MulAut.mul_apply, ← map_mul]
  rw [Finset.prod_congr (rfl : (Finset.univ : Finset A) = Finset.univ)
        (fun b _ => h_compose b)]
  -- ∏ b : A, (φ (b * a)) g = ∏ b' : A, (φ b') g (b' = b * a is a bijection)
  exact Finset.prod_bijective (fun b => b * a) (Group.mulRight_bijective a)
    (fun b => by simp) (fun _ _ => rfl)

/-- **`actionCommutator` is in `ker (fittingProductHom)`** (G abelian).

For each generator `g * (φ a) g⁻¹` of `actionCommutator`: `θ (g * (φ a) g⁻¹) = θ g * θ ((φ a) g)⁻¹
= θ g * (θ g)⁻¹ = 1` (using θ hom + `fittingProductHom_apply_of_smul` + map_inv on φ a). -/
lemma actionCommutator_le_ker_fittingProductHom
    {A G : Type*} [CommGroup G] [Group A] [Fintype A] (φ : A →* MulAut G) :
    actionCommutator φ ≤ (fittingProductHom φ).ker := by
  rw [actionCommutator, Subgroup.closure_le]
  rintro _ ⟨g, a, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  -- Goal: θ (g * (φ a) g⁻¹) = 1
  -- (φ a) g⁻¹ = (φ a)(g⁻¹) = ((φ a) g)⁻¹
  have h_inv_eq : (φ a) g⁻¹ = ((φ a) g)⁻¹ := map_inv (φ a) g
  rw [h_inv_eq, map_mul, map_inv, fittingProductHom_apply_of_smul]
  exact mul_inv_cancel _

/-- **Isaacs Theorem 4.34** ⭐ (Fitting, = BG Prop 1.6(d)):
G abelian + A 作用 + coprime (|A|, |G|) ⇒
`fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥` (intersection trivial,
combined with Lem 4.28 sup = ⊤ gives internal direct product `G = C_G(A) × [G, A]`).

**証明** (Isaacs p.140): θ : G →* G, `θ g = ∏ a : A, (φ a) g`.
- For c ∈ C_G(A): `θ c = c^|A|`.
- `actionCommutator ⊆ ker θ` (各生成元 `[g, a] ↦ 1`).
- So `c ∈ C_G(A) ∩ actionCommutator ⇒ θ c = c^|A| = 1`. Combined with `c^|G| = 1`
  (Lagrange) + coprime ⇒ `c = 1` (Bezout: ∃ s t, s|A| + t|G| = 1, c = c^1 = ...). -/
theorem fixedPoints_inf_actionCommutator_eq_bot_of_abelian
    {A G : Type*} [CommGroup G] [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  obtain ⟨hc_fix, hc_ac⟩ := Subgroup.mem_inf.mp hc
  -- c is A-fixed
  have hc_fixed : ∀ a : A, (φ a) c = c := hc_fix
  -- c ∈ ker θ via actionCommutator ⊆ ker θ
  have : Fintype A := Fintype.ofFinite A
  have hc_ker : fittingProductHom φ c = 1 :=
    actionCommutator_le_ker_fittingProductHom φ hc_ac
  -- θ c = c^|A| from hc_fixed
  have hc_pow_A : c ^ Nat.card A = 1 := by
    rw [← fittingProductHom_apply_of_fixed hc_fixed]; exact hc_ker
  -- c^|G| = 1 (Lagrange)
  have hc_pow_G : c ^ Nat.card G = 1 := pow_card_eq_one'
  -- Bezout: ∃ s t, s|A| + t|G| = 1 (coprime), then c = c^(s|A| + t|G|) = 1
  have h_one : c = 1 := by
    have h_gcd : Nat.gcd (Nat.card A) (Nat.card G) = 1 := hCop
    -- Use orderOf c ∣ Nat.card A and orderOf c ∣ Nat.card G ⇒ orderOf c ∣ gcd = 1 ⇒ c = 1
    have h_ord_A : orderOf c ∣ Nat.card A := orderOf_dvd_of_pow_eq_one hc_pow_A
    have h_ord_G : orderOf c ∣ Nat.card G := orderOf_dvd_of_pow_eq_one hc_pow_G
    have h_ord_gcd : orderOf c ∣ Nat.gcd (Nat.card A) (Nat.card G) :=
      Nat.dvd_gcd h_ord_A h_ord_G
    rw [h_gcd] at h_ord_gcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h_ord_gcd)
  exact h_one

/-- **Isaacs Corollary 4.35** ⭐ (= BG Prop 1.6(e), **FT クリティカル**):
G is abelian p-群, A is p'-group (i.e., p ∤ |A|), A acts on G via automorphisms.
If A fixes every element of order p (i.e., every g with `g^p = 1`), then
`actionCommutator φ = ⊥` (A acts trivially on G).

**証明** (Isaacs p.141):
- Coprime: p ∤ |A| + G p-group ⇒ |A| coprime |G|.
- G abelian + coprime ⇒ Thm 4.34: `fixedPoints ⊓ actionCommutator = ⊥`.
- Suppose [G, A] = actionCommutator ≠ ⊥. Then nontrivial subgroup of p-group G.
- Cauchy: ∃ g ∈ [G, A] with orderOf g = p. So `g^p = 1`, `g ≠ 1`.
- Hypothesis: A fixes g, i.e., g ∈ fixedPoints.
- So g ∈ fixedPoints ⊓ [G, A] = ⊥, contradicting g ≠ 1. -/
theorem actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    {A G : Type*} [Group A] [CommGroup G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (φ : A →* MulAut G) (hG : IsPGroup p G)
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ := by
  -- Coprime |A|, |G|: G is p-group ⇒ |G| = p^n. p ∤ |A| ⇒ gcd = 1.
  have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
    rw [hn]
    exact (Nat.Coprime.pow_right n
      (Nat.coprime_comm.mp (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hA_p')))
  -- Apply Thm 4.34: fixedPoints ⊓ actionCommutator = ⊥
  have h_inf_bot := fixedPoints_inf_actionCommutator_eq_bot_of_abelian φ hCop
  -- Suppose actionCommutator ≠ ⊥, get contradiction via Cauchy
  by_contra h_ne_bot
  -- ∃ g ∈ actionCommutator with g ≠ 1
  obtain ⟨g_elem, hg_in, hg_ne⟩ : ∃ g ∈ actionCommutator φ, g ≠ 1 := by
    by_contra h
    push Not at h
    apply h_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    exact h
  -- actionCommutator is nontrivial subgroup of p-group ⇒ has order-p element
  have hG_AC : IsPGroup p (actionCommutator φ) := hG.to_subgroup _
  have : Nontrivial (actionCommutator φ) := ⟨⟨g_elem, hg_in⟩, 1, by
    intro h
    apply hg_ne
    exact (Subtype.ext_iff.mp h)⟩
  obtain ⟨n, hn_pos, hn_card⟩ := hG_AC.nontrivial_iff_card.mp inferInstance
  -- |actionCommutator| = p^n with n ≥ 1, so p ∣ |actionCommutator|
  have hp_dvd : p ∣ Nat.card (actionCommutator φ) := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  -- Cauchy: ∃ g ∈ actionCommutator with orderOf g = p
  obtain ⟨g, hg_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  -- Convert orderOf inside subgroup ⇒ orderOf in G via subtype is preserved
  have h_ord_eq : orderOf (g : G) = orderOf g := by
    exact (orderOf_injective (actionCommutator φ).subtype
      (Subgroup.subtype_injective _) g)
  have h_ord_g : orderOf (g : G) = p := h_ord_eq.trans hg_ord
  -- g^p = 1 in G
  have hg_pow : (g : G) ^ p = 1 := by
    rw [← h_ord_g]; exact pow_orderOf_eq_one _
  -- g is fixed by A (hypothesis)
  have hg_fixed : ∀ a : A, (φ a) (g : G) = g := h_fix g hg_pow
  -- So g ∈ fixedPointsOfMulAut ⊓ actionCommutator = ⊥
  have hg_in_inf : (g : G) ∈ Subgroup.fixedPointsOfMulAut φ ⊓ actionCommutator φ :=
    Subgroup.mem_inf.mpr ⟨hg_fixed, g.2⟩
  rw [h_inf_bot, Subgroup.mem_bot] at hg_in_inf
  -- hg_in_inf : (g : G) = 1, but orderOf g = p > 1, contradiction
  have : orderOf (g : G) = 1 := by rw [hg_in_inf, orderOf_one]
  rw [h_ord_g] at this
  exact hp.out.one_lt.ne' this

end

end OddOrder.Isaacs.Ch04


