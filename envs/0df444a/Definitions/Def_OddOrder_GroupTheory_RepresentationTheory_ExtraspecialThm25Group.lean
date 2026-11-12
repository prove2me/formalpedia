-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25Group
-- name    : OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25Group
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:00.790338+00:00
-- url     : https://prove2.me/theorems/625984dd-1d35-415f-b674-102458e28de2
-- title:
--   BG Theorem 2.5 at the group level (divisibility part)
-- statement:
--   Wires the (2.11) keystone and the Proposition 2.4 counting into the group-level divisibility conclusion of Theorem 2.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: for a class-at-most-2 $p$-group $P\trianglelefteq G$ with a faithful irreducible representation and an element $x$ of order $h$ acting fixed-point-freely on $P/Z(P)$, $h\mid(\dim V)\pm 1$. It supplies the group-theoretic setup wiring.
--
--   The main declaration: `conjAutOfNormal` (The automorphism of a normal subgroup `P` induced by conjugation by `x ∈ G`).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ExtraspecialThm25Group.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ExtraspecialThm25Group.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialKeystone
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03

namespace OddOrder.RepresentationTheory

open Representation Module EigenspaceUnderCyclicAction

open OddOrder.Isaacs.Ch03 (IsAInvariant)

variable {G : Type*} [Group G]

/-- The automorphism of a normal subgroup `P` induced by conjugation by `x ∈ G`. -/
noncomputable def conjAutOfNormal (P : Subgroup G) [P.Normal] (x : G) : P ≃* P :=
  (MulEquiv.subgroupMap (MulAut.conj x) P).trans
    (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self x P))

@[simp]
theorem conjAutOfNormal_apply_coe (P : Subgroup G) [P.Normal] (x : G) (p : P) :
    (conjAutOfNormal P x p : G) = x * (p : G) * x⁻¹ := rfl

/-- Iterating: `(φ^k p : G) = x^k · p · x^{-k}`. -/
theorem conjAutOfNormal_pow_apply_coe (P : Subgroup G) [P.Normal] (x : G) (k : ℕ) (p : P) :
    (((conjAutOfNormal P x) ^ k) p : G) = x ^ k * (p : G) * (x ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, conjAutOfNormal_apply_coe, ih]
    group

/-- If `x^h = 1` then `φ^h = 1`. -/
theorem conjAutOfNormal_pow_eq_one (P : Subgroup G) [P.Normal] {x : G} {h : ℕ} (hx : x ^ h = 1) :
    (conjAutOfNormal P x) ^ h = 1 := by
  ext p
  rw [conjAutOfNormal_pow_apply_coe, hx]
  simp

/-- **BG Proposition 1.5** (the `hcent` input to `finrank_modEq_of_faithful_irreducible`).  In the
Theorem 2.5 setup, `x ∈ G` has order `h` coprime to `|P|` and for every nontrivial power `xᵏ` the
centralizer `C_P(xᵏ)` is contained in `Z(P)` (BG's hypothesis `C_P(x) = Z(P)` for `x ∈ H^#`, stated
here as the fixed points of the conjugation automorphism `(conjAutOfNormal P x)^k` lying in `Z(P)`).
Then `x` acts **fixed-point-freely on `P/Z(P)`**: the only coset fixed by a nontrivial power of the
induced automorphism `σ = quotientCenterCongr (conjAutOfNormal P x)` is the identity.

The proof lifts a fixed coset to a genuine fixed point via the coprime fixed-point theorem (Isaacs
Cor 3.28, `coprime_fixedPoints_quotient_of_coprime_normal`): the cyclic group `⟨φᵏ⟩`
(`φ = conjAutOfNormal P x`) acts on `P` with `Z(P)` an invariant subgroup, and
`(|⟨φᵏ⟩|, |Z(P)|) = 1` since `|⟨φᵏ⟩| ∣ h`,
`|Z(P)| ∣ |P|`, and `(h, |P|) = 1`.  The lifted fixed point lies in `C_P(xᵏ) ⊆ Z(P)`, so the coset
is trivial. -/
theorem quotientCenter_fixedFree_of_centralizer_le_center
    [Finite G] (P : Subgroup G) [P.Normal]
    (x : G) {h : ℕ} (hxh : x ^ h = 1) (hcop : Nat.Coprime h (Nat.card P))
    (hCP : ∀ k : ZMod h, k ≠ 0 → ∀ p : P,
        (conjAutOfNormal P x ^ k.val) p = p → p ∈ Subgroup.center P) :
    ∀ k : ZMod h, k ≠ 0 → ∀ c : P ⧸ Subgroup.center P,
        ((quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c) = c → c = 1 := by
  classical
  intro k hk c hfix
  set φ₀ : P ≃* P := conjAutOfNormal P x with hφ₀
  -- a fixed point of `t` is fixed by every power of `t`
  have hiter : ∀ (t : (P ⧸ Subgroup.center P) ≃* (P ⧸ Subgroup.center P)) (d) (m : ℕ),
      t d = d → (t ^ m) d = d := by
    intro t d m ht
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, MulAut.mul_apply, ht]; exact ih
  -- a coset representative of `c`
  set g : P := Quotient.out c with hg
  have hgc : (g : P ⧸ Subgroup.center P) = c := by rw [hg]; exact Quotient.out_eq' c
  -- `φ₀^k` has order dividing `h`, hence `(|⟨φ₀^k⟩|, |Z(P)|) = 1`
  have hωh : (φ₀ ^ k.val) ^ h = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hφ₀, conjAutOfNormal_pow_eq_one P hxh, one_pow]
  have hAcard : Nat.card (Subgroup.zpowers (φ₀ ^ k.val)) ∣ h := by
    rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hωh
  have hCopN : Nat.Coprime (Nat.card (Subgroup.zpowers (φ₀ ^ k.val)))
      (Nat.card (Subgroup.center P)) :=
    (hcop.coprime_dvd_left hAcard).coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
  have hSolv : Group.IsSolvable ↥(Subgroup.zpowers (φ₀ ^ k.val)) ∨
      Group.IsSolvable ↥(Subgroup.center P) :=
    Or.inr (Group.isSolvable_of_comm fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp a.2 b.1).symm)
  have hN_inv : IsAInvariant (Subgroup.zpowers (φ₀ ^ k.val)).subtype (Subgroup.center P) :=
    IsAInvariant.center _
  -- the coset `gZ` is invariant under all powers of `φ₀^k` (since `σ^k` fixes `c`)
  have hg_fix : ∀ a : Subgroup.zpowers (φ₀ ^ k.val),
      ∃ n ∈ Subgroup.center P, (Subgroup.zpowers (φ₀ ^ k.val)).subtype a g = g * n := by
    intro a
    obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr a.2
    have key : (Subgroup.zpowers (φ₀ ^ k.val)).subtype a g = (φ₀ ^ (k.val * m)) g := by
      rw [show (Subgroup.zpowers (φ₀ ^ k.val)).subtype a = (φ₀ ^ k.val) ^ m from hm.symm,
        ← pow_mul]
    have hquot : ((Subgroup.zpowers (φ₀ ^ k.val)).subtype a g : P ⧸ Subgroup.center P) = c := by
      rw [key, ← quotientCenterCongr_pow_mk, hgc, pow_mul]
      exact hiter ((quotientCenterCongr φ₀) ^ k.val) c m hfix
    refine ⟨g⁻¹ * (Subgroup.zpowers (φ₀ ^ k.val)).subtype a g, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgc, hquot,
      inv_mul_cancel]
  -- lift the fixed coset to a genuine fixed point of `φ₀^k`
  obtain ⟨w, hw_fix, n, hn, hwn⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      hCopN hSolv hN_inv hg_fix
  have hωw : (φ₀ ^ k.val) w = w := hw_fix ⟨φ₀ ^ k.val, Subgroup.mem_zpowers _⟩
  have hw_center : w ∈ Subgroup.center P := hCP k hk w hωw
  -- `g = w * n⁻¹ ∈ Z(P)`, so `c = ⟦g⟧ = 1`
  have hg_center : g ∈ Subgroup.center P := by
    have hgwn : g = w * n⁻¹ := by rw [hwn]; group
    rw [hgwn]; exact Subgroup.mul_mem _ hw_center (Subgroup.inv_mem _ hn)
  rw [← hgc, QuotientGroup.eq_one_iff]
  exact hg_center

/-- **Shared keystone data for BG Theorem 2.5 (group level).** From the Theorem 2.5 setup
(`P ⊴ G` of class `≤ 2`, faithful `ρ` over alg-closed `F`, `char ∤ |P|`, `x^h = 1`, `ε` primitive
`h`-th root, `char ∤ h`, `V_P` irreducible, `x` fixed-point-free on `P/Z`), the conjugation
operator `T = ρ x` on `End_F V` has: the eigenspace decomposition `hV`, the keystone multiplicities
`dim E₀ = dim E_m + 1` (BG (2.11) via `finrank_cyclicEndConjEigenspaceFin_succ`), and
`∑ dim Vᵢ = dim V`.  Both conclusions of Theorem 2.5 (divisibility and `C_V(H)`) consume this. -/
private theorem cyclicEndConj_keystoneData_of_faithful_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite G]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hVP : Representation.IsIrreducible (ρ.comp P.subtype))
    (hcent : ∀ k : ZMod h, k ≠ 0 → ∀ c : P ⧸ Subgroup.center P,
        ((quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c) = c → c = 1) :
    DirectSum.IsInternal (cyclicEigenspaceFinFamily ε (ρ.asGroupHom x : Module.End F V) h) ∧
    (∀ m : Fin h, m ≠ 0 →
      Module.finrank F (cyclicEndConjEigenspaceFin ε (ρ.asGroupHom x) (0 : Fin h))
        = Module.finrank F (cyclicEndConjEigenspaceFin ε (ρ.asGroupHom x) m) + 1) ∧
    (∑ i : Fin h, cyclicEigenspaceFinDim ε (ρ.asGroupHom x : Module.End F V) i
        = Module.finrank F V) := by
  classical
  set ρP : Representation F P V := ρ.comp P.subtype with hρP
  have : Representation.IsIrreducible ρP := hVP
  set φ : P ≃* P := conjAutOfNormal P x with hφ
  set T : LinearMap.GeneralLinearGroup F V := ρ.asGroupHom x with hT
  -- `↑T = ρ x`
  have hTcoe : (T : Module.End F V) = ρ x := by rw [hT]; exact MonoidHom.coe_toHomUnits ρ x
  -- restriction is faithful
  have hfP : Function.Injective ρP := fun a b hab => Subtype.ext (hf hab)
  -- intertwining relation
  have hint : ∀ p : P, (T : Module.End F V) * ρP p = ρP (φ p) * (T : Module.End F V) := by
    intro p
    rw [hTcoe]
    change ρ x * ρ (p : G) = ρ ((φ p : P) : G) * ρ x
    rw [conjAutOfNormal_apply_coe, ← map_mul, ← map_mul]
    congr 1
    group
  -- `φ^h = 1`, `T^h = 1`
  have hφh : φ ^ h = 1 := conjAutOfNormal_pow_eq_one P hxh
  have hTEnd_h : (T : Module.End F V) ^ h = 1 := by
    rw [hTcoe, ← map_pow, hxh, map_one]
  -- eigenspace decomposition of `V` under `T`
  have hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily ε (T : Module.End F V) h) :=
    cyclicEigenspaceFin_isInternal_of_pow_eq_one hprim hTEnd_h
  -- the keystone supplies `hEdim`
  have hEdim := finrank_cyclicEndConjEigenspaceFin_succ ρP hfP hcl φ T hint hφh hprim hh hcent
  -- `∑ dim Vᵢ = dim V`
  have hsumV : ∑ i : Fin h, cyclicEigenspaceFinDim ε (T : Module.End F V) i
      = Module.finrank F V := by
    rw [← (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily ε (T : Module.End F V) h)) hV).finrank_eq,
      Module.finrank_directSum]
  exact ⟨hV, hEdim, hsumV⟩

/-- **BG Theorem 2.5, `C_V(H)` part (group level).** Same setup as the divisibility theorem
`finrank_modEq_of_faithful_irreducible`;
in addition assume `dim V ≥ 2` and that `x` has no nonzero fixed vector, i.e. the fixed space
`C_V(H) = C_V(x) = V₀` is trivial (`cyclicEigenspaceFinDim ε (ρ x) 0 = 0`).  Then `dim V = h - 1`,
i.e. `h = dim V + 1`.  Equivalently (contrapositive), if `h ≠ dim V + 1` then `C_V(H) ≠ 0` — the
half of Theorem 2.5 used in the even/odd contradiction of Theorem 3.4. -/
theorem finrank_eq_sub_one_of_faithful_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite G]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hVP : Representation.IsIrreducible (ρ.comp P.subtype))
    (hcent : ∀ k : ZMod h, k ≠ 0 → ∀ c : P ⧸ Subgroup.center P,
        ((quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c) = c → c = 1)
    (hV2 : 2 ≤ Module.finrank F V)
    (hCV : cyclicEigenspaceFinDim ε (ρ.asGroupHom x : Module.End F V) (0 : Fin h) = 0) :
    (Module.finrank F V : ℤ) = (h : ℤ) - 1 := by
  obtain ⟨hV, hEdim, hsumV⟩ :=
    cyclicEndConj_keystoneData_of_faithful_irreducible P ρ hf hcl x hxh hprim hh hVP hcent
  have hq : 2 ≤ ∑ i : Fin h,
      (cyclicEigenspaceFinDim ε (ρ.asGroupHom x : Module.End F V) i : ℤ) := by
    rw [← Nat.cast_sum, hsumV]; exact_mod_cast hV2
  have hsub := sum_eigenspaceFinDim_eq_sub_one_of_finrank_cyclicEndConjEigenspace
    hprim hV hh2 hEdim hq hCV
  rw [← hsub, ← Nat.cast_sum, hsumV]

/-- **BG Theorem 2.5, `C_V(H)` part**, with the abstract `hcent` replaced by the BG-faithful
centralizer condition `(h, |P|) = 1` + `C_P(xᵏ) ⊆ Z(P)` (cf.
`finrank_modEq_of_faithful_irreducible_of_centralizer`). -/
theorem finrank_eq_sub_one_of_faithful_irreducible_of_centralizer
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite G]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hcop : Nat.Coprime h (Nat.card P))
    (hVP : Representation.IsIrreducible (ρ.comp P.subtype))
    (hCP : ∀ k : ZMod h, k ≠ 0 → ∀ p : P,
        (conjAutOfNormal P x ^ k.val) p = p → p ∈ Subgroup.center P)
    (hV2 : 2 ≤ Module.finrank F V)
    (hCV : cyclicEigenspaceFinDim ε (ρ.asGroupHom x : Module.End F V) (0 : Fin h) = 0) :
    (Module.finrank F V : ℤ) = (h : ℤ) - 1 :=
  finrank_eq_sub_one_of_faithful_irreducible P ρ hf hcl x hxh hh2 hprim hh hVP
    (quotientCenter_fixedFree_of_centralizer_le_center P x hxh hcop hCP) hV2 hCV

end OddOrder.RepresentationTheory


