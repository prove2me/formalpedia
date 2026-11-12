-- Prove2me | Definitions.Def_OddOrder_BG_AppA_PStabilityBasic
-- name    : OddOrder_BG_AppA_PStabilityBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:43:58.172778+00:00
-- url     : https://prove2.me/theorems/1f644ebf-df71-4879-9823-ba0cbb590add
-- title:
--   Bender–Glauberman Appendix A: $p$-stability basics
-- statement:
--   The basic part of Bender–Glauberman Appendix A on $p$-stability (A.1, A.2, the definition of $p$-stable, and A.3), following Gorenstein (1968).
--
--   Main definitions: `IsPStable` ($p$-stability, as defined in Gorenstein 1968 p. 105), with lemmas `representation_conj_sub_one` ($\rho(gxg^{-1})-1=\rho(g)(\rho(x)-1)\rho(g)^{-1}$), `representation_conj_quadratic` (conjugates satisfy the same quadratic minimal polynomial) and `representation_conj_ne_one` (conjugates of non-identity elements stay non-identity).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppA_PStabilityBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppA_PStabilityBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_Representations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PGroupFixedVector
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CoprimeActionTrivial
import Definitions.Def_OddOrder_GroupTheory_ChiefFactor
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Order.OrderIsoNat

namespace OddOrder.BG.AppA

open Representation Module Function LinearMap Submodule

universe uF uG uV

variable {p : ℕ} [Fact p.Prime]

variable {F : Type uF} [Field F] [CharP F p]

variable {V : Type uV} [AddCommGroup V] [Module F V] [Module.Finite F V]

variable {G : Type uG} [Group G]

section ThmA1

/-- **BG Theorem A.1** (mmd L4460-4464): `V` 2-dim faithful irreducible over
`F` (char `p`), `|G|` odd ⇒ `p ∤ |G|`.

証明: BG Thm 2.6 で Sylow-`p` `P` が abelian かつ `G' ≤ P` を得, 後者から
`P ⊴ G` (`Subgroup.Normal.of_commutator_le`). `P` 正規 `p`-群なので
`PGroupFixedVector` の固定点 `C_V(P) ≠ ⊥` は `G`-不変. 既約で `C_V(P) = ⊤`,
すなわち `P` 全要素が `V` 上自明作用. 忠実より `P = ⊥`. しかし `p ∣ |G|`
なら `Sylow.ne_bot_of_dvd_card` で `P ≠ ⊥`, 矛盾. -/
theorem thmA1
    [Finite G] (hodd : Odd (Nat.card G))
    (hdim : Module.finrank F V = 2)
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hirr : ∀ U : Submodule F V,
      (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) :
    ¬ p ∣ Nat.card G := by
  intro hp_dvd
  -- 1. Get a Sylow p subgroup
  obtain ⟨P⟩ : Nonempty (Sylow p G) := Sylow.nonempty
  -- 2. BG Thm 2.6: P abelian + commutator G ≤ P
  obtain ⟨_hP_comm, hG'_le_P⟩ :=
    OddOrder.BG.Ch1.S02.odd_two_dim_sylow_abelian hodd hdim ρ hfaithful hp_dvd ‹CharP F p› P
  -- 3. P normal in G (commutator G ≤ P)
  have hP_normal : (P : Subgroup G).Normal := by
    apply Subgroup.Normal.of_commutator_le (H := (P : Subgroup G))
    exact hG'_le_P
  -- 4. P is a p-group
  have hP_pgroup : IsPGroup p (↥(P : Subgroup G)) := P.isPGroup'
  -- 5. V is nontrivial (dim = 2)
  have hV_nontriv : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := F) (M := V) (by rw [hdim]; norm_num)
  -- 6. ⊤ ≠ ⊥ in Submodule F V
  have hV_ne_bot : (⊤ : Submodule F V) ≠ ⊥ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have hv_top : v ∈ (⊤ : Submodule F V) := Submodule.mem_top
    rw [h] at hv_top
    exact (Submodule.mem_bot _).mp hv_top
  -- 7. ρ restricted to P is a representation of P
  let ρ_P : Representation F (↥(P : Subgroup G)) V := ρ.comp (P : Subgroup G).subtype
  -- 8. C_V(P) := ρ_P.invariants ≠ ⊥ (PGroupFixedVector)
  have hC_ne_bot : ρ_P.invariants ≠ ⊥ := hP_pgroup.invariants_ne_bot ρ_P hV_ne_bot
  -- 9. C_V(P) is G-invariant (since P is normal)
  have hC_inv : ∀ g : G, ∀ v ∈ ρ_P.invariants, ρ g v ∈ ρ_P.invariants := by
    intro g v hv
    rw [Representation.mem_invariants] at hv ⊢
    rintro ⟨q, hq⟩
    -- want ρ_P ⟨q, hq⟩ (ρ g v) = ρ g v, i.e., ρ q (ρ g v) = ρ g v
    change ρ q (ρ g v) = ρ g v
    have hconj : g⁻¹ * q * g ∈ (P : Subgroup G) := hP_normal.conj_mem' q hq g
    have h_fix : ρ (g⁻¹ * q * g) v = v := by
      have := hv ⟨g⁻¹ * q * g, hconj⟩
      simpa [ρ_P] using this
    calc ρ q (ρ g v)
        = (ρ q * ρ g) v := by rw [Module.End.mul_apply]
      _ = ρ (q * g) v := by rw [← map_mul]
      _ = ρ (g * (g⁻¹ * q * g)) v := by congr 1; group
      _ = (ρ g * ρ (g⁻¹ * q * g)) v := by rw [map_mul]
      _ = ρ g (ρ (g⁻¹ * q * g) v) := by rw [Module.End.mul_apply]
      _ = ρ g v := by rw [h_fix]
  -- 10. C_V(P) = ⊤ by irreducibility
  have hC_top : ρ_P.invariants = ⊤ :=
    (hirr ρ_P.invariants hC_inv).resolve_left hC_ne_bot
  -- 11. ρ q = 1 for all q ∈ P
  have h_triv : ∀ q ∈ (P : Subgroup G), ρ q = (1 : Module.End F V) := by
    intro q hq
    ext v
    have hv_inv : v ∈ ρ_P.invariants := by rw [hC_top]; exact Submodule.mem_top
    have hv_fix := (Representation.mem_invariants ρ_P v).mp hv_inv ⟨q, hq⟩
    -- hv_fix : ρ_P ⟨q, hq⟩ v = v; ρ_P ⟨q, hq⟩ = ρ q definitionally
    rw [Module.End.one_apply]
    simpa [ρ_P] using hv_fix
  -- 12. P = ⊥ (by faithful)
  have hP_bot : (P : Subgroup G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    apply hfaithful
    rw [h_triv q hq, map_one]
  -- 13. Contradiction: P ≠ ⊥ (Sylow + p ∣ |G|)
  exact P.ne_bot_of_dvd_card hp_dvd hP_bot

end ThmA1

section DimReduction

/-- **BG Thm A.2 の dim reduction lemma** (= Gorenstein Ch.3 §8 Thm 8.1
weakening, mmd L2204-L2240). `F` alg-closed char `p` 上, `V` finite-dim
nontrivial, `G = ⟨x, y⟩` 忠実既約作用, `x, y` が二次最小多項式の `p`-元
⇒ `dim V = 2`.

証明: 5 step (Gorenstein 8.1 翻訳, Step 4 を eigenvector 1 個に精密化).
詳細 [`notes/bg/appA_pstability.md`](../../notes/bg/appA_pstability.md)
「★ 2026-05-28 (late PM) 追補」, issue #0041. -/
theorem quadratic_two_generated_irreducible_finrank_eq_two
    [IsAlgClosed F] [Nontrivial V]
    (ρ : Representation F G V) (_hfaithful : Function.Injective ρ)
    (hirr : ∀ U : Submodule F V,
      (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (x y : G) (hgen : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hx : ((ρ x : Module.End F V) - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : ((ρ y : Module.End F V) - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    Module.finrank F V = 2 := by
  -- Setup: V_i = ker(ρ x_i - 1), W_i = range(ρ x_i - 1)
  set Tx : Module.End F V := (ρ x : Module.End F V) - 1 with hTx_def
  set Ty : Module.End F V := (ρ y : Module.End F V) - 1 with hTy_def
  set V_1 : Submodule F V := LinearMap.ker Tx with hV1_def
  set V_2 : Submodule F V := LinearMap.ker Ty with hV2_def
  set W_1 : Submodule F V := LinearMap.range Tx with hW1_def
  set W_2 : Submodule F V := LinearMap.range Ty with hW2_def
  -- Step 1: W_i ⊆ V_i (since (ρ x_i - 1)^2 = 0)
  have hW1_le_V1 : W_1 ≤ V_1 := by
    rw [hW1_def, hV1_def, LinearMap.range_le_ker_iff]
    -- Goal: Tx ∘ₗ Tx = 0, equivalently Tx * Tx = 0, equivalently Tx^2 = 0
    have : Tx * Tx = 0 := by
      have : Tx ^ 2 = 0 := hx
      simpa [pow_two] using this
    exact this
  have hW2_le_V2 : W_2 ≤ V_2 := by
    rw [hW2_def, hV2_def, LinearMap.range_le_ker_iff]
    have : Ty * Ty = 0 := by
      have : Ty ^ 2 = 0 := hy
      simpa [pow_two] using this
    exact this
  -- Step 1: rank-nullity ⇒ d = dim V ≤ 2 dim V_i
  have h_rn_x : Module.finrank F W_1 + Module.finrank F V_1 = Module.finrank F V :=
    LinearMap.finrank_range_add_finrank_ker Tx
  have h_rn_y : Module.finrank F W_2 + Module.finrank F V_2 = Module.finrank F V :=
    LinearMap.finrank_range_add_finrank_ker Ty
  have hd_le_2d1 : Module.finrank F V ≤ 2 * Module.finrank F V_1 := by
    have hW1_le := Submodule.finrank_mono hW1_le_V1
    omega
  have hd_le_2d2 : Module.finrank F V ≤ 2 * Module.finrank F V_2 := by
    have hW2_le := Submodule.finrank_mono hW2_le_V2
    omega
  -- Helpers: x acts trivially on V_1 = ker(ρx - 1), y on V_2 = ker(ρy - 1)
  have hx_triv_V1 : ∀ v ∈ V_1, ρ x v = v := by
    intro v hv
    have h : Tx v = 0 := hv
    have e : Tx v = ρ x v - v := by
      simp [hTx_def, LinearMap.sub_apply, Module.End.one_apply]
    rw [e] at h
    exact sub_eq_zero.mp h
  have hy_triv_V2 : ∀ v ∈ V_2, ρ y v = v := by
    intro v hv
    have h : Ty v = 0 := hv
    have e : Ty v = ρ y v - v := by
      simp [hTy_def, LinearMap.sub_apply, Module.End.one_apply]
    rw [e] at h
    exact sub_eq_zero.mp h
  -- Step 2: V_1 ∩ V_2 = ⊥
  -- (Otherwise both x, y act trivially on W := V_1 ∩ V_2 ⇒ G acts trivially on W
  -- ⇒ W = ⊤ by irreducibility ⇒ ρ x = 1, contradicts hxne)
  have hV12_inter_bot : V_1 ⊓ V_2 = ⊥ := by
    by_contra hne
    -- ∀ g ∈ G, ρ g v = v for v ∈ V_1 ⊓ V_2 (via closure_induction)
    have h_triv_all : ∀ g : G, ∀ v ∈ V_1 ⊓ V_2, ρ g v = v := by
      intro g v hv
      have hg_mem : g ∈ Subgroup.closure ({x, y} : Set G) := by rw [hgen]; trivial
      induction hg_mem using Subgroup.closure_induction with
      | mem h hh =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
        rcases hh with h_eq | h_eq
        · subst h_eq
          exact hx_triv_V1 v (Submodule.mem_inf.mp hv).1
        · subst h_eq
          exact hy_triv_V2 v (Submodule.mem_inf.mp hv).2
      | one => rw [map_one, Module.End.one_apply]
      | mul a b _ _ ihA ihB =>
        rw [map_mul, Module.End.mul_apply, ihB, ihA]
      | inv a _ ihA =>
        -- ρ a v = v ⇒ ρ a⁻¹ v = v via ρ (a⁻¹ * a) = ρ 1 = 1
        have : ρ a⁻¹ (ρ a v) = ρ a⁻¹ v := by rw [ihA]
        rw [← this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
    -- W := V_1 ⊓ V_2 is G-invariant
    have hW_inv : ∀ g : G, ∀ v ∈ V_1 ⊓ V_2, ρ g v ∈ V_1 ⊓ V_2 := by
      intro g v hv
      rw [h_triv_all g v hv]; exact hv
    -- Apply hirr ⇒ W = ⊥ or ⊤; ≠ ⊥, so = ⊤
    rcases hirr (V_1 ⊓ V_2) hW_inv with h_bot | h_top
    · exact hne h_bot
    · -- W = ⊤ ⇒ every v ∈ V is in V_1 ⊓ V_2 ⊆ V_1 ⇒ ρ x = 1, contradicts hxne
      apply hxne
      ext v
      rw [Module.End.one_apply]
      have hv1 : v ∈ V_1 := by
        have : v ∈ V_1 ⊓ V_2 := by rw [h_top]; exact Submodule.mem_top
        exact (Submodule.mem_inf.mp this).1
      exact hx_triv_V1 v hv1
  -- Step 4 prep: V_2 ≠ ⊥ (else (ρ y - 1) injective ⇒ surjective ⇒ W_2 = ⊤,
  -- but W_2 ⊆ V_2 = ⊥, ⊥ ≠ ⊤ since V Nontrivial)
  have hV2_ne_bot : V_2 ≠ ⊥ := by
    intro h
    have hW2_le : W_2 ≤ ⊥ := hW2_le_V2.trans h.le
    have hW2_bot : W_2 = ⊥ := le_bot_iff.mp hW2_le
    have hTy_zero : Ty = 0 := LinearMap.range_eq_bot.mp hW2_bot
    apply hyne
    have : (ρ y : Module.End F V) - 1 = 0 := hTy_zero
    exact sub_eq_zero.mp this
  -- Step 4: T := (Ty * Tx) : V_2 → V_2 well-defined (well-typed restriction)
  have hT_maps : ∀ v ∈ V_2, ((Ty * Tx : Module.End F V)) v ∈ V_2 := by
    intro v _
    change Ty (Tx v) ∈ V_2
    exact hW2_le_V2 ⟨Tx v, rfl⟩
  have hV2_fd : FiniteDimensional F V_2 := inferInstance
  have hV2_nontriv : Nontrivial (V_2 : Submodule F V) :=
    Submodule.nontrivial_iff_ne_bot.mpr hV2_ne_bot
  let T : V_2 →ₗ[F] V_2 := (Ty * Tx : Module.End F V).restrict hT_maps
  -- T has eigenvalue μ
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v_sub, hv_sub_mem, hv_sub_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  -- T v_sub = μ • v_sub
  have hT_eq : T v_sub = μ • v_sub := by
    rwa [Module.End.mem_eigenspace_iff] at hv_sub_mem
  -- v := v_sub.val ∈ V is the eigenvector lifted to V; u_1 := v, u_2 := Tx v
  set v : V := v_sub.val with hv_def
  -- u_1 = v ≠ 0
  have hu_1_ne : v ≠ 0 := by
    intro h
    apply hv_sub_ne
    ext
    exact h
  -- u_2 := Tx v ∈ V_1 (since Tx v ∈ W_1 ⊆ V_1)
  have hu_2_V1 : Tx v ∈ V_1 := hW1_le_V1 ⟨v, rfl⟩
  -- T injectivity argument: T v_sub = 0 ⇒ Ty (Tx v) = 0 ⇒ Tx v ∈ V_1 ∩ V_2 = ⊥ ⇒ Tx v = 0
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w_sub hw_ker
    have h_val_zero : (Ty * Tx : Module.End F V) w_sub.val = 0 := by
      have h := congr_arg Subtype.val (hw_ker : T w_sub = 0)
      simpa [T] using h
    have hTyTx : Ty (Tx w_sub.val) = 0 := by
      rw [Module.End.mul_apply] at h_val_zero; exact h_val_zero
    -- Tx w_sub.val ∈ V_2 (from Ty (Tx w_sub.val) = 0 = kernel of Ty)
    have hTxw_V2 : Tx w_sub.val ∈ V_2 := hTyTx
    have hTxw_V1 : Tx w_sub.val ∈ V_1 := hW1_le_V1 ⟨w_sub.val, rfl⟩
    have hTxw_zero : Tx w_sub.val = 0 := by
      have : Tx w_sub.val ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hTxw_V1, hTxw_V2⟩
      rw [hV12_inter_bot] at this
      exact (Submodule.mem_bot _).mp this
    -- w_sub.val ∈ V_1 (from Tx w_sub.val = 0)
    have hw_V1 : w_sub.val ∈ V_1 := hTxw_zero
    have : w_sub.val ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hw_V1, w_sub.prop⟩
    rw [hV12_inter_bot] at this
    exact Subtype.ext ((Submodule.mem_bot _).mp this)
  -- μ ≠ 0 (else T v_sub = 0 ⇒ v_sub = 0 by T injective)
  have hμ_ne : μ ≠ 0 := by
    intro hμ_zero
    apply hv_sub_ne
    apply hT_inj
    rw [hT_eq, hμ_zero, zero_smul, LinearMap.map_zero]
  -- u_2 = Tx v ≠ 0 (else v ∈ V_1 ∩ V_2 = ⊥)
  have hu_2_ne : Tx v ≠ 0 := by
    intro hu_2_zero
    have hv_V1 : v ∈ V_1 := hu_2_zero
    have : v ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hv_V1, v_sub.prop⟩
    rw [hV12_inter_bot] at this
    exact hu_1_ne ((Submodule.mem_bot _).mp this)
  -- Step 5: U := span {v, Tx v}; show U is x,y-invariant, hence G-invariant, hence = ⊤
  -- ρ x v = v + Tx v, ρ x (Tx v) = Tx v, ρ y v = v, ρ y (Tx v) = Tx v + μ • v
  have hxv : ρ x v = v + Tx v := by
    have h : Tx v = ρ x v - v := by
      simp [hTx_def, LinearMap.sub_apply, Module.End.one_apply]
    rw [h]; abel
  have hxTxv : ρ x (Tx v) = Tx v := hx_triv_V1 (Tx v) hu_2_V1
  have hyv : ρ y v = v := hy_triv_V2 v v_sub.prop
  have hyTxv : ρ y (Tx v) = Tx v + μ • v := by
    have hTyTxv : Ty (Tx v) = μ • v := by
      -- (Ty * Tx) v = (T v_sub).val; T v_sub = μ • v_sub; (μ • v_sub).val = μ • v
      have h1 : (Ty * Tx : Module.End F V) v = (T v_sub).val := by
        change (Ty * Tx : Module.End F V) v_sub.val = (T v_sub).val
        simp [T]
      rw [Module.End.mul_apply] at h1
      rw [h1, hT_eq]
      rfl
    have h_diff : ρ y (Tx v) - Tx v = μ • v := by
      have e : Ty (Tx v) = ρ y (Tx v) - Tx v := by
        simp [hTy_def, LinearMap.sub_apply, Module.End.one_apply]
      rw [e] at hTyTxv; exact hTyTxv
    rw [← h_diff]; abel
  -- U := span F {v, Tx v}
  set U : Submodule F V := Submodule.span F {v, Tx v} with hU_def
  -- v ∈ U, Tx v ∈ U
  have hv_in_U : v ∈ U := Submodule.subset_span (Set.mem_insert _ _)
  have hTxv_in_U : Tx v ∈ U := Submodule.subset_span (by simp)
  -- "g preserves U" forms a subgroup; contains x, y; ⟨x, y⟩ = ⊤ ⇒ all g preserve U
  have hU_fd : FiniteDimensional F U := inferInstance
  -- Build the "stabilizer" subgroup
  let stab : Subgroup G :=
    { carrier := { g | ∀ u ∈ U, ρ g u ∈ U }
      one_mem' := by intro u hu; rw [map_one, Module.End.one_apply]; exact hu
      mul_mem' := by
        intro a b ha hb u hu
        rw [map_mul, Module.End.mul_apply]; exact ha _ (hb _ hu)
      inv_mem' := by
        intro a ha u hu
        -- Restrict ρ a to U → U, then it's injective (ρ a inj on V) + finite-dim ⇒ surjective
        let f : U →ₗ[F] U := LinearMap.restrict (ρ a) (fun w hw => ha w hw)
        have hρa_inj : Function.Injective ((ρ a) : V → V) := by
          intro p q hpq
          have : ρ a⁻¹ (ρ a p) = ρ a⁻¹ (ρ a q) := congr_arg _ hpq
          have heq : (ρ a⁻¹ * ρ a : Module.End F V) = 1 := by
            rw [← map_mul, inv_mul_cancel, map_one]
          rwa [show (ρ a⁻¹ : V → V) (ρ a p) = (ρ a⁻¹ * ρ a : Module.End F V) p
            from rfl,
            show (ρ a⁻¹ : V → V) (ρ a q) = (ρ a⁻¹ * ρ a : Module.End F V) q
            from rfl,
            heq, Module.End.one_apply, Module.End.one_apply] at this
        have hf_inj : Function.Injective f := by
          intro p q hpq
          apply Subtype.ext
          have := congr_arg Subtype.val hpq
          simpa [f] using hρa_inj this
        have hf_surj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf_inj
        obtain ⟨w, hw⟩ := hf_surj ⟨u, hu⟩
        have h_val : ρ a w.val = u := by
          have := congr_arg Subtype.val hw
          simpa [f] using this
        have : ρ a⁻¹ u = w.val := by
          rw [← h_val]
          have heq : (ρ a⁻¹ * ρ a : Module.End F V) = 1 := by
            rw [← map_mul, inv_mul_cancel, map_one]
          change (ρ a⁻¹ * ρ a : Module.End F V) w.val = w.val
          rw [heq, Module.End.one_apply]
        rw [this]; exact w.prop }
  -- stab = ⊤ (since x, y ∈ stab and ⟨x, y⟩ = ⊤)
  have hStab_top : stab = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    change ∀ u ∈ U, ρ g u ∈ U
    -- Use span_induction
    rcases hg with rfl | rfl
    · -- g = x
      intro u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · rw [hxv]
          exact U.add_mem hv_in_U hTxv_in_U
        · rw [hxTxv]; exact hTxv_in_U
      | zero => rw [map_zero]; exact U.zero_mem
      | add a b _ _ iha ihb => rw [map_add]; exact U.add_mem iha ihb
      | smul s a _ iha => rw [map_smul]; exact U.smul_mem s iha
    · -- g = y
      intro u hu
      induction hu using Submodule.span_induction with
      | mem w hw =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · rw [hyv]; exact hv_in_U
        · rw [hyTxv]
          exact U.add_mem hTxv_in_U (U.smul_mem μ hv_in_U)
      | zero => rw [map_zero]; exact U.zero_mem
      | add a b _ _ iha ihb => rw [map_add]; exact U.add_mem iha ihb
      | smul s a _ iha => rw [map_smul]; exact U.smul_mem s iha
  -- U is G-invariant: every g ∈ G is in stab = ⊤
  have hU_G_inv : ∀ g : G, ∀ u ∈ U, ρ g u ∈ U := fun g => by
    have : g ∈ stab := by rw [hStab_top]; trivial
    exact this
  -- U ≠ ⊥ (v ∈ U, v ≠ 0)
  have hU_ne_bot : U ≠ ⊥ := by
    intro h
    apply hu_1_ne
    have : v ∈ (⊥ : Submodule F V) := h ▸ hv_in_U
    exact (Submodule.mem_bot _).mp this
  -- By irreducibility, U = ⊤
  have hU_top : U = ⊤ := (hirr U hU_G_inv).resolve_left hU_ne_bot
  -- u_1 = v, u_2 = Tx v are linearly independent
  have h_lin_ind : LinearIndependent F ![v, Tx v] := by
    rw [LinearIndependent.pair_iff' hu_1_ne]
    intro a heq
    -- heq : a • v = Tx v; we show contradiction with hu_2_ne (or get Tx v = 0)
    -- a • v ∈ V_2 (V_2 contains v); Tx v ∈ V_1; so Tx v ∈ V_1 ∩ V_2 = ⊥ ⇒ Tx v = 0
    have hav_V2 : a • v ∈ V_2 := V_2.smul_mem a v_sub.prop
    have hTxv_V2 : Tx v ∈ V_2 := heq ▸ hav_V2
    have : Tx v ∈ V_1 ⊓ V_2 := Submodule.mem_inf.mpr ⟨hu_2_V1, hTxv_V2⟩
    rw [hV12_inter_bot] at this
    exact hu_2_ne ((Submodule.mem_bot _).mp this)
  -- {v, Tx v} is a basis of V (lin ind + spans top)
  have h_setrange : Set.range ![v, Tx v] = ({v, Tx v} : Set V) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    · rintro h
      rcases h with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hSpan_top : Submodule.span F (Set.range ![v, Tx v]) = ⊤ := by
    rw [h_setrange]; exact hU_top
  let B : Module.Basis (Fin 2) F V := Basis.mk h_lin_ind hSpan_top.ge
  -- dim V = card (Fin 2) = 2
  rw [Module.finrank_eq_card_basis B]
  simp

end DimReduction

section ThmA2

/-- **BG Theorem A.2** (mmd L4468-4472): `F` alg-closed char `p` (odd) 上,
`V` finite-dim nontrivial, `G = ⟨x, y⟩` 忠実既約作用, `x, y` が二次最小
多項式の `p`-元 ⇒ `|G|` 偶 (i.e., `¬ Odd |G|`).

証明: dim reduction で `dim V = 2`. `x` (or `y`) は `p`-element で `≠ 1` ⇒
`p ∣ |G|`. もし `|G|` 奇なら A.1 で `p ∤ |G|`, 矛盾. -/
theorem thmA2
    [Finite G] [IsAlgClosed F] [Nontrivial V]
    (_hp_odd : p ≠ 2)
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hirr : ∀ U : Submodule F V,
      (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (x y : G) (hgen : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hx : ((ρ x : Module.End F V) - 1) ^ 2 = 0) (hxne : ρ x ≠ 1)
    (hy : ((ρ y : Module.End F V) - 1) ^ 2 = 0) (hyne : ρ y ≠ 1) :
    ¬ Odd (Nat.card G) := by
  intro hodd
  -- Step 1: dim V = 2 (from dim reduction lemma)
  have hdim : Module.finrank F V = 2 :=
    quadratic_two_generated_irreducible_finrank_eq_two ρ hfaithful hirr
      x y hgen hx hxne hy hyne
  -- Step 2: (ρ x)^p = 1 via Frobenius
  have : CharP (Module.End F V) p := IsPGroup.charP_End_of_field
  have hp_prime : p.Prime := Fact.out
  -- (ρ x - 1)^p = (ρ x - 1)^(p-2) * (ρ x - 1)^2 = (ρ x - 1)^(p-2) * 0 = 0
  have hN_p_zero : ((ρ x : Module.End F V) - 1) ^ p = 0 := by
    have hp_two : 2 ≤ p := hp_prime.two_le
    calc ((ρ x : Module.End F V) - 1) ^ p
        = ((ρ x : Module.End F V) - 1) ^ (p - 2) * ((ρ x : Module.End F V) - 1) ^ 2 := by
          rw [← pow_add]; congr 1; omega
      _ = ((ρ x : Module.End F V) - 1) ^ (p - 2) * 0 := by rw [hx]
      _ = 0 := mul_zero _
  -- (ρ x - 1)^p = (ρ x)^p - 1^p (Frobenius); = 0 ⇒ (ρ x)^p = 1
  have hρx_p : (ρ x : Module.End F V) ^ p = 1 := by
    have h1 : ((ρ x : Module.End F V) - 1) ^ p =
        (ρ x : Module.End F V) ^ p - (1 : Module.End F V) ^ p :=
      sub_pow_char_of_commute p (Commute.one_right _)
    rw [hN_p_zero, one_pow, eq_comm, sub_eq_zero] at h1
    exact h1
  -- Step 3: x has order dividing p; ≠ 1 ⇒ order = p (p prime); so p ∣ |G|
  have hxp_one : x ^ p = 1 := by
    apply hfaithful
    rw [map_pow, map_one]; exact hρx_p
  have hox_dvd_p : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp_one
  have hx_ne_one : x ≠ 1 := fun h => hxne (by rw [h, map_one])
  have hox_ne_one : orderOf x ≠ 1 := fun h => hx_ne_one (orderOf_eq_one_iff.mp h)
  have hox_eq_p : orderOf x = p := by
    rcases hp_prime.eq_one_or_self_of_dvd (orderOf x) hox_dvd_p with h | h
    · exact absurd h hox_ne_one
    · exact h
  have hp_dvd : p ∣ Nat.card G := hox_eq_p ▸ orderOf_dvd_natCard x
  -- Step 4: A.1 (|G| odd ⇒ p ∤ |G|) で矛盾
  exact thmA1 hodd hdim ρ hfaithful hirr hp_dvd

end ThmA2

section PStability

omit [Module.Finite F V] in
/-- `ρ (g * x * g⁻¹) - 1 = ρg * (ρx - 1) * ρg⁻¹` (conjugation factorization). -/
lemma representation_conj_sub_one
    (ρ : Representation F G V) (x g : G) :
    (ρ (g * x * g⁻¹) : Module.End F V) - 1
      = ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹ := by
  have hgg : (ρ g : Module.End F V) * ρ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, hgg]

omit [Module.Finite F V] in
/-- 共役元は同じ quadratic minimal polynomial を持つ: `(ρ x - 1)² = 0 ⇒ (ρ(gxg⁻¹) - 1)² = 0`.
A.3 で `y = gxg⁻¹` ∈ K (conjugacy class of x) も quadratic を持つことに使用. -/
lemma representation_conj_quadratic
    (ρ : Representation F G V) (x g : G)
    (hxsq : ((ρ x : Module.End F V) - 1) ^ 2 = 0) :
    ((ρ (g * x * g⁻¹) : Module.End F V) - 1) ^ 2 = 0 := by
  have hgg' : (ρ g⁻¹ : Module.End F V) * ρ g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [representation_conj_sub_one ρ x g]
  -- (ρg * A * ρg⁻¹)^2 = ρg * A * (ρg⁻¹ * ρg) * A * ρg⁻¹ = ρg * A² * ρg⁻¹ = 0
  calc (ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹) ^ 2
      = ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹
          * (ρ g * ((ρ x : Module.End F V) - 1) * ρ g⁻¹) := by rw [sq]
    _ = ρ g * ((ρ x : Module.End F V) - 1) * (ρ g⁻¹ * ρ g)
          * ((ρ x : Module.End F V) - 1) * ρ g⁻¹ := by
            simp only [mul_assoc]
    _ = ρ g * ((ρ x : Module.End F V) - 1) * 1
          * ((ρ x : Module.End F V) - 1) * ρ g⁻¹ := by rw [hgg']
    _ = ρ g * (((ρ x : Module.End F V) - 1)
          * ((ρ x : Module.End F V) - 1)) * ρ g⁻¹ := by
            simp only [mul_one, mul_assoc]
    _ = ρ g * ((ρ x : Module.End F V) - 1) ^ 2 * ρ g⁻¹ := by rw [← sq]
    _ = ρ g * 0 * ρ g⁻¹ := by rw [hxsq]
    _ = 0 := by rw [mul_zero, zero_mul]

omit [Module.Finite F V] in
/-- 共役元は `ρ` 上 `≠ 1` を保つ: `ρ x ≠ 1 ⇒ ρ(gxg⁻¹) ≠ 1`. -/
lemma representation_conj_ne_one
    (ρ : Representation F G V) (x g : G) (hxne : ρ x ≠ 1) :
    ρ (g * x * g⁻¹) ≠ 1 := by
  intro h
  apply hxne
  -- ρ(gxg⁻¹) = ρg ρx ρg⁻¹ = 1 ⇒ ρx = ρg⁻¹ * 1 * ρg = 1
  have hgg : (ρ g : Module.End F V) * ρ g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hg'g : (ρ g⁻¹ : Module.End F V) * ρ g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h1 : (ρ g : Module.End F V) * ρ x * ρ g⁻¹ = 1 := by
    rw [← map_mul, ← map_mul]; exact h
  -- ρx = ρg⁻¹ * (ρg * ρx * ρg⁻¹) * ρg = ρg⁻¹ * 1 * ρg = 1
  have : (ρ x : Module.End F V)
       = ρ g⁻¹ * (ρ g * ρ x * ρ g⁻¹) * ρ g := by
    calc (ρ x : Module.End F V)
        = 1 * ρ x * 1 := by rw [one_mul, mul_one]
      _ = (ρ g⁻¹ * ρ g) * ρ x * (ρ g⁻¹ * ρ g) := by rw [hg'g]
      _ = ρ g⁻¹ * (ρ g * ρ x * ρ g⁻¹) * ρ g := by
            simp only [mul_assoc]
  rw [this, h1, mul_one, hg'g]

/-- 共役元は p-element を保つ: `IsPGroup p (zpowers x) ⇒ IsPGroup p (zpowers (gxg⁻¹))`.
証明: `SemiconjBy g x (gxg⁻¹)` ⇒ `orderOf x = orderOf (gxg⁻¹)`, IsPGroup は orderOf
で特徴付け. -/
lemma isPGroup_zpowers_conj [Finite G]
    (x g : G) (hxp : IsPGroup p (Subgroup.zpowers x)) :
    IsPGroup p (Subgroup.zpowers (g * x * g⁻¹)) := by
  have hp_prime : p.Prime := Fact.out
  -- SemiconjBy g x (gxg⁻¹): g * x = (g * x * g⁻¹) * g
  have hsemi : SemiconjBy g x (g * x * g⁻¹) := by
    unfold SemiconjBy
    group
  have horder : orderOf x = orderOf (g * x * g⁻¹) := hsemi.orderOf_eq g
  -- IsPGroup p (zpowers a) ↔ ∃ n, |zpowers a| = p^n; |zpowers a| = orderOf a (mathlib)
  rw [IsPGroup.iff_card] at hxp ⊢
  rw [Nat.card_zpowers, ← horder, ← Nat.card_zpowers]
  exact hxp

/-- **p-stability** (Gorenstein 1968 p.105 definition, BG App.A 用途).

`G` が `p`-stable とは: `F` の alg-closed char `p` 上の有限次元 nontrivial vector space
`V` への **忠実な representation** `ρ : G →* End F V` で、任意の `p`-element `x : G` が
**quadratic minimal polynomial** `(X - 1)²` を持つ(= `(ρ x - 1)² = 0` ∧ `ρ x ≠ 1`)
ことは無い、というもの.

Gorenstein は `GF(p^n)` 上の faithful rep で定義するが、`GF(p^n) → F` 拡張 (= base change)
で alg closure に持ち上がり同値. Lean では alg closure 版で statement.

**注意**: Gorenstein の p-stability は通常「`G` has no nontrivial normal `p`-subgroups」
かつ `p` odd の context で定義する. 本 def はそれらを前提に組み込まず、`IsPStable` を
使う側の定理 (A.3, A.4) で hypothesis として渡す方針 (def シンプル + 整合性).

下流: A.3, A.4(a) で使用. -/
def IsPStable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ ⦃F : Type*⦄ [Field F] [CharP F p] [IsAlgClosed F]
    ⦃V : Type*⦄ [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    (ρ : Representation F G V), Function.Injective ρ →
    ∀ x : G, IsPGroup p (Subgroup.zpowers x) →
      ((ρ x : Module.End F V) - 1) ^ 2 = 0 → ρ x = 1

/-- **BG Theorem A.3** (mmd L4476, = Gorenstein Ch.3 §8 Thm 8.3 weakening,
mmd L2288): `p` odd, `G` に非自明な正規 `p`-部分群が無く (= `O_p(G) = 1`),
`G` が `p`-stable でないなら `|G|` は偶.

**証明 (= Gorenstein 8.3 翻訳, A.2 を 8.1 の代わりに使う, mmd L2290-L2310)**:
1. `¬ IsPStable p G` ⇒ ∃ ρ faithful, ∃ x p-element with quadratic minpoly.
2. `K := x` の conjugacy class. 全 K の元は同じ性質.
3. **Baer-Suzuki (Gorenstein 8.2)** で `O_p(G) = 1` + K で全 pair p-群を生成」が
   不可能 ⇒ ∃ y ∈ K, `H := ⟨x, y⟩` は p-群でない.
4. H-invariant chain `V ⊃ V_2 ⊃ ... ⊃ 0` で H が各 quotient 上既約.
5. `N_i := ker(H → End(V_i/V_{i+1}))`. ∃ i, `N_i ⊊ H` (反例: 全 N_i = H ⇒ H の
   p'-部分群は全 quotient 上自明 → V 上自明 (coprime action) → faithful より = 1 ⇒
   H p-群、矛盾).
6. `H/N_i` faithful irreducible action on `V_i/V_{i+1}`, x̄, ȳ quadratic minpoly.
7. **A.2 (`quadratic_two_generated_irreducible_finrank_eq_two` + closure_eq via x̄, ȳ
   generators)** で `|H/N_i|` 偶.
8. `2 ∣ |H/N_i| ∣ |H| ∣ |G|` ⇒ `|G|` 偶. ∎

依存:
- ✅ `OddOrder.Isaacs.Ch01.opCore` (= `O_p(G)`)
- ✅ `OddOrder.Isaacs.Ch02.baerSuzuki_pCore` (Baer-Suzuki 単一元 form)
- ✅ `quadratic_two_generated_irreducible_finrank_eq_two` (= A.2)
- ❌ H-invariant chain + quotient representation (新規)
- ❌ p'-element trivial on quotients ⇒ trivial on V (coprime action 結果)

詳細・着手順は issue [#0043](../../issues/0043-bg-appa-a3-pstability.md). -/
theorem thmA3 [Finite G] (_hp_odd : p ≠ 2)
    (h_Op_trivial : OddOrder.Isaacs.Ch01.opCore p G = ⊥)
    (h_not_pstable : ¬ IsPStable p G) :
    ¬ Odd (Nat.card G) := by
  intro hodd
  -- ## Step 1: ¬ IsPStable を unfold + push Not で証人を取り出す
  unfold IsPStable at h_not_pstable
  push Not at h_not_pstable
  obtain ⟨F, _, _, _, V, _, _, _, _, ρ, hfaithful, x, hxp, hxsq, hxne⟩ :=
    h_not_pstable
  -- ## Step 2: Baer-Suzuki で ⟨x, gxg⁻¹⟩ が非 p-群となる g を取得
  -- x ≠ 1 (ρ x ≠ 1 + faithful)
  have hx_ne_one : x ≠ 1 := by
    intro h; apply hxne; rw [h, map_one]
  -- x ∉ O_p(G) (= ⊥ なので x ≠ 1 から)
  have hx_not_in_Op : x ∉ OddOrder.Isaacs.Ch01.opCore p G := by
    rw [h_Op_trivial]
    intro h
    exact hx_ne_one (Subgroup.mem_bot.mp h)
  -- baerSuzuki_pCore.mpr の対偶で ∃ g, ⟨x, gxg⁻¹⟩ 非 p-群
  have h_exists_g : ∃ g : G,
      ¬ IsPGroup p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
    by_contra h_all
    push Not at h_all
    exact hx_not_in_Op
      ((OddOrder.Isaacs.Ch02.baerSuzuki_pCore x).mpr h_all)
  obtain ⟨g, h_pair_not_pgroup⟩ := h_exists_g
  -- ## Step 3: `y := g x g⁻¹` ∈ K (= conjugacy class of x) も同じ性質を持つ
  set y : G := g * x * g⁻¹ with hy_def
  -- y は p-element, ρ y は quadratic で ≠ 1
  have hysq : ((ρ y : Module.End F V) - 1) ^ 2 = 0 :=
    representation_conj_quadratic ρ x g hxsq
  have hyne : ρ y ≠ 1 := representation_conj_ne_one ρ x g hxne
  have hyp : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_conj x g hxp
  -- H := ⟨x, y⟩ ≤ G は非 p-群
  set H : Subgroup G := Subgroup.closure ({x, y} : Set G) with hH_def
  have hH_not_pgroup : ¬ IsPGroup p H := h_pair_not_pgroup
  -- x ∈ H, y ∈ H
  have hxH : x ∈ H := Subgroup.subset_closure (by simp)
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  -- ## Steps 4-8 (Gorenstein 8.3 mmd L2293-L2298): 合成列 + coprime action + A.2
  -- 残りの目標 = `2 ∣ |G|`. これを出せば `hodd : Odd |G|` と矛盾.
  --
  -- 4. H-invariant 合成列 `V = V_1 ⊋ V_2 ⊋ ... ⊋ V_{m+1} = 0` を構成
  --    (V finite-dim + 再帰的に H-irreducible quotient を取得).
  --    mathlib: `RingTheory.SimpleModule` / `Order.JordanHolder.CompositionSeries`.
  --
  -- 5. N_i := ker(H → End_F (V_i/V_{i+1})). 全 i で N_i = H と仮定すると
  --    H に nontrivial p'-subgroup Q が存在 (H not p-group, Cauchy + IsPGroup
  --    否定). Q は全 V_i/V_{i+1} 上自明 ⇒ **coprime action (Gorenstein Thm 3.4
  --    翻訳)** で Q は V 上自明 ⇒ ρ|_Q = 1
  --    ⇒ ρ faithful + Q ≠ 1 と矛盾. ∴ ∃ i, N_i ⊊ H.
  --
  -- 6. その i で H̄ := H/N_i, ρ̄ : H̄ → End_F (V_i/V_{i+1}) faithful + irreducible.
  --    H̄ = ⟨x̄, ȳ⟩ (closure 商).
  --
  -- 7. x̄, ȳ ≠ 1: もし x̄ = 1 なら H̄ = ⟨ȳ⟩ は p-group (ȳ p-element, `hyp` 使用).
  --    H̄ p-group + alg-closed char p faithful irreducible は不可能
  --    (= Gorenstein Thm 1.2 = repo `PGroupFixedVector.invariants_ne_bot` 系)
  --    ⇒ H̄ = 1 ⇒ N_i = H, 矛盾. 同様に ȳ ≠ 1.
  --
  -- 8. A.2 (`thmA2`) を H̄ ↷ V_i/V_{i+1} に適用 (closure_eq via x̄, ȳ 生成元)
  --    ⇒ ¬ Odd |H̄| ⇒ 2 ∣ |H̄|. 2 ∣ |H̄| ∣ |H| ∣ |G| (Lagrange) で 2 ∣ |G|. ∎
  --
  -- 使う主要補題 (issue #0043 + notes/bg/appA_pstability.md):
  --   * H-invariant `CompositionSeries` of `V` as `F[H]`-module
  --   * `coprime_action_trivial_of_trivial_on_quotients` (= Gorenstein Thm 3.4)
  --   * `IsPGroup.faithful_irreducible_in_charP_trivial` (= Gorenstein Thm 1.2)
  --   * Quotient representation `H → H/N_i → End_F (V_i/V_{i+1})`
  have h_two_dvd : 2 ∣ Nat.card G := by
    -- ## Step 5: Set up ρ_H : Representation F ↥H V via subgroup restriction
    let ρ_H : Representation F ↥H V := ρ.comp H.subtype
    have hρH_faithful : Function.Injective ρ_H :=
      fun a b hab => Subtype.ext (hfaithful hab)
    -- Well-foundedness for `Subrepresentation ρ_H` via toSubmodule embedding.
    -- `Submodule F V` has WF (both directions) for finite-dim V.
    have hwf_LT : WellFoundedLT (Subrepresentation ρ_H) := by
      apply StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule)
      intros a b hab
      exact lt_of_le_of_ne hab.le
        (fun h => hab.ne (Subrepresentation.toSubmodule_injective h))
    have hwf_GT : WellFoundedGT (Subrepresentation ρ_H) := by
      apply StrictMono.wellFoundedGT (f := Subrepresentation.toSubmodule)
      intros a b hab
      exact lt_of_le_of_ne hab.le
        (fun h => hab.ne (Subrepresentation.toSubmodule_injective h))
    have : Nonempty (Subrepresentation ρ_H) := ⟨⊥⟩
    -- Get covBy chain in `Subrepresentation ρ_H`
    obtain ⟨a, h_min, n, h_max, h_cov⟩ :=
      exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (Subrepresentation ρ_H)
    -- Translate to Submodule chain
    have h_a0_bot : (a 0).toSubmodule = ⊥ := by
      have h_eq : a 0 = ⊥ := h_min.eq_bot
      rw [h_eq]; rfl
    have h_an_top : (a n).toSubmodule = ⊤ := by
      have h_eq : a n = ⊤ := h_max.eq_top
      rw [h_eq]; rfl
    -- ## Step 6: 分岐 — H が全 quotient で自明か否か
    by_cases h_all_triv : ∀ i : ℕ, i < n → ∀ (h : ↥H) (v : V),
        v ∈ (a (i + 1)).toSubmodule → ρ_H h v - v ∈ (a i).toSubmodule
    · -- Case A: 全 quotient 自明 ⇒ coprime action chain で矛盾
      exfalso
      -- A.1: ∃ prime r ≠ p with r ∣ |↥H| (H not p-group + 素因数分解)
      have hH_card_pos : 0 < Nat.card ↥H := Nat.card_pos
      have hH_card_ne_zero : Nat.card ↥H ≠ 0 := hH_card_pos.ne'
      have h_not_pow : ¬ ∃ k : ℕ, Nat.card ↥H = p ^ k := by
        intro hc; exact hH_not_pgroup (IsPGroup.iff_card.mpr hc)
      obtain ⟨r, hr_prime, hr_dvd, hr_ne_p⟩ :
          ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card ↥H ∧ r ≠ p := by
        by_contra h_no
        push Not at h_no
        apply h_not_pow
        have hall : ∀ q ∈ (Nat.card ↥H).primeFactorsList, q = p := by
          intro q hq
          rw [Nat.mem_primeFactorsList hH_card_ne_zero] at hq
          exact h_no q hq.1 hq.2
        refine ⟨(Nat.card ↥H).primeFactorsList.length, ?_⟩
        rw [← List.prod_replicate, ← List.eq_replicate_of_mem hall,
          Nat.prod_primeFactorsList hH_card_ne_zero]
      -- A.2: Cauchy で q ∈ ↥H, orderOf q = r
      have : Fact r.Prime := ⟨hr_prime⟩
      obtain ⟨q, hq_order⟩ : ∃ q : ↥H, orderOf q = r :=
        exists_prime_orderOf_dvd_card' r hr_dvd
      -- q ≠ 1
      have hq_ne_one : q ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hq_order
        -- hq_order : 1 = r, and hr_prime.one_lt : 1 < r ⇒ 1 ≠ r
        exact hr_prime.one_lt.ne hq_order
      have hqG_ne_one : (q : G) ≠ 1 := by
        intro h
        exact hq_ne_one (Subtype.ext h)
      -- A.3: Q := zpowers q (as Subgroup ↥H) — work entirely in ↥H
      let Q : Subgroup ↥H := Subgroup.zpowers q
      let ρ_Q : Representation F ↥Q V := ρ_H.comp Q.subtype
      -- Cardinality of Q is r
      have hQ_card : Nat.card ↥Q = r := by
        rw [Nat.card_zpowers]; exact hq_order
      -- (Nat.card ↥Q : F) ≠ 0 since r ≠ p = char F
      have hQ_nezero : NeZero ((Nat.card ↥Q : F)) := by
        constructor
        intro h_zero
        rw [hQ_card] at h_zero
        have hp_dvd_r : p ∣ r := by
          rwa [CharP.cast_eq_zero_iff F p r] at h_zero
        have hp_prime : p.Prime := Fact.out
        rcases hr_prime.eq_one_or_self_of_dvd p hp_dvd_r with h1 | h2
        · exact hp_prime.one_lt.ne' h1
        · exact hr_ne_p h2.symm
      have : Finite ↥Q := inferInstance
      -- A.4: Apply coprime_action_trivial_chain to ρ_Q
      have h_Q_triv : ∀ (g : ↥Q) (v : V), ρ_Q g v = v := by
        apply OddOrder.GroupTheory.RepresentationTheory.coprime_action_trivial_chain
          ρ_Q (s := fun i : Fin (n + 1) => (a (i : ℕ)).toSubmodule)
        · -- s 0 = ⊥ (= h_a0_bot via beta + Fin cast)
          simpa using h_a0_bot
        · -- s (Fin.last n) = ⊤
          have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := by simp
          change (a ((Fin.last n : Fin (n + 1)) : ℕ)).toSubmodule = ⊤
          rw [hlast]; exact h_an_top
        · -- h_triv_quot
          intro g_q i v hv
          have h_eq : ρ_Q g_q v = ρ_H (g_q : ↥H) v := rfl
          change ρ_Q g_q v - v ∈ (a ((i.castSucc : Fin (n + 1)) : ℕ)).toSubmodule
          rw [h_eq]
          have hcastSucc : ((i.castSucc : Fin (n + 1)) : ℕ) = i.val := by simp
          have hsucc : ((i.succ : Fin (n + 1)) : ℕ) = i.val + 1 := by simp
          rw [hcastSucc]
          have hv' : v ∈ (a (i.val + 1)).toSubmodule := by
            have hv_in : v ∈ (a ((i.succ : Fin (n + 1)) : ℕ)).toSubmodule := hv
            rwa [hsucc] at hv_in
          exact h_all_triv i.val i.isLt (g_q : ↥H) v hv'
      -- A.5: ρ q = 1 (via ρ_Q at ⟨q, mem_zpowers_self⟩)
      have h_ρq_one : ρ (q : G) = 1 := by
        ext v
        rw [Module.End.one_apply]
        have hself : q ∈ Subgroup.zpowers q := Subgroup.mem_zpowers q
        have h_app := h_Q_triv ⟨q, hself⟩ v
        -- ρ_Q ⟨q, hself⟩ v = ρ_H q v = ρ (q : G) v
        change ρ (q : G) v = v at h_app
        exact h_app
      -- A.6: 矛盾 — q = 1 (by faithful) と q ≠ 1
      have hq_eq_one : (q : G) = 1 := by
        apply hfaithful
        rw [h_ρq_one, map_one]
      exact hqG_ne_one hq_eq_one
    · -- Case B: ∃ i, action non-trivial. Apply A.2.
      push Not at h_all_triv
      obtain ⟨i, hi_lt_n, q_witness, v_witness, hv_witness, h_not_triv_witness⟩ :=
        h_all_triv
      -- Step 7a: N_i := {h ∈ ↥H | h acts trivially on a(i+1)/a i}
      let N_i : Subgroup ↥H :=
        { carrier := { h | ∀ v ∈ (a (i + 1)).toSubmodule,
                            ρ_H h v - v ∈ (a i).toSubmodule }
          one_mem' := by
            intro v _
            change ρ_H 1 v - v ∈ (a i).toSubmodule
            simp [map_one, Module.End.one_apply]
          mul_mem' := by
            intro h₁ h₂ hh₁ hh₂ v hv
            change ρ_H (h₁ * h₂) v - v ∈ (a i).toSubmodule
            have h_decomp : ρ_H (h₁ * h₂) v - v
                = ρ_H h₁ (ρ_H h₂ v - v) + (ρ_H h₁ v - v) := by
              rw [map_mul, Module.End.mul_apply, map_sub]
              abel
            rw [h_decomp]
            exact (a i).toSubmodule.add_mem
              ((a i).apply_mem_toSubmodule h₁ (hh₂ v hv)) (hh₁ v hv)
          inv_mem' := by
            intro h hh v hv
            change ρ_H h⁻¹ v - v ∈ (a i).toSubmodule
            -- key: ρ_H h⁻¹ v - v = ρ_H h⁻¹ (-(ρ_H h v - v))
            have h_apply : ρ_H h⁻¹ (-(ρ_H h v - v)) = ρ_H h⁻¹ v - v := by
              rw [map_neg, map_sub]
              have hh_inv : ρ_H h⁻¹ (ρ_H h v) = v := by
                rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                  Module.End.one_apply]
              rw [hh_inv]; abel
            rw [← h_apply]
            exact (a i).apply_mem_toSubmodule h⁻¹
              ((a i).toSubmodule.neg_mem (hh v hv)) }
      -- Step 7b: witness ∉ N_i
      have h_q_notin_Ni : q_witness ∉ N_i := by
        intro h_in
        exact h_not_triv_witness (h_in v_witness hv_witness)
      -- Step 7c: N_i.Normal
      have hN_i_normal : N_i.Normal := by
        constructor
        intro n hn g v hv
        change ρ_H (g * n * g⁻¹) v - v ∈ (a i).toSubmodule
        -- ρ_H (g n g⁻¹) v = ρ_H g (ρ_H n (ρ_H g⁻¹ v))
        -- v = ρ_H g (ρ_H g⁻¹ v)
        -- so diff = ρ_H g (ρ_H n (ρ_H g⁻¹ v) - ρ_H g⁻¹ v)
        have h_inv_v : ρ_H g (ρ_H g⁻¹ v) = v := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply]
        have h_compute : ρ_H (g * n * g⁻¹) v - v
            = ρ_H g (ρ_H n (ρ_H g⁻¹ v) - ρ_H g⁻¹ v) := by
          rw [map_sub]
          congr 1
          · rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
          · exact h_inv_v.symm
        rw [h_compute]
        have hgv_in : ρ_H g⁻¹ v ∈ (a (i + 1)).toSubmodule :=
          (a (i + 1)).apply_mem_toSubmodule g⁻¹ hv
        have h_n_act : ρ_H n (ρ_H g⁻¹ v) - ρ_H g⁻¹ v ∈ (a i).toSubmodule :=
          hn (ρ_H g⁻¹ v) hgv_in
        exact (a i).apply_mem_toSubmodule g h_n_act
      -- Step 7d: V_quot setup
      let aip1_top : Submodule F V := (a (i + 1)).toSubmodule
      let ai_in_aip1 : Submodule F ↥aip1_top :=
        (a i).toSubmodule.comap aip1_top.subtype
      -- a i ⋖ a (i+1) ⇒ a i < a (i+1) as Submodule
      have h_ai_lt_aip1 : (a i).toSubmodule < aip1_top := by
        have h_lt : a i < a (i + 1) := (h_cov i hi_lt_n).lt
        change (a i).toSubmodule < (a (i + 1)).toSubmodule
        exact lt_of_le_of_ne h_lt.le
          (fun h_eq => h_lt.ne (Subrepresentation.toSubmodule_injective h_eq))
      have h_ai_in_aip1_ne_top : ai_in_aip1 ≠ ⊤ := by
        intro h_eq
        apply h_ai_lt_aip1.ne
        apply le_antisymm h_ai_lt_aip1.le
        intro w hw
        have hw_subt : (⟨w, hw⟩ : ↥aip1_top) ∈ ai_in_aip1 := by rw [h_eq]; trivial
        exact hw_subt
      have hV_quot_nontriv : Nontrivial (↥aip1_top ⧸ ai_in_aip1) := by
        rw [Submodule.Quotient.nontrivial_iff]
        exact h_ai_in_aip1_ne_top
      have hV_quot_finite : Module.Finite F (↥aip1_top ⧸ ai_in_aip1) :=
        Module.Finite.of_surjective ai_in_aip1.mkQ ai_in_aip1.mkQ_surjective
      -- Step 7e: ρ_quot : Representation F ↥H (↥aip1_top ⧸ ai_in_aip1)
      have h_inv_aip1 : ∀ g : ↥H,
          ai_in_aip1 ≤ ai_in_aip1.comap ((a (i + 1)).toRepresentation g) := by
        intro g w hw
        change ((a (i + 1)).toRepresentation g w).val ∈ (a i).toSubmodule
        change ρ_H g w.val ∈ (a i).toSubmodule
        exact (a i).apply_mem_toSubmodule g hw
      let ρ_quot : Representation F ↥H (↥aip1_top ⧸ ai_in_aip1) :=
        Representation.quotient (a (i + 1)).toRepresentation ai_in_aip1 h_inv_aip1
      -- Step 7f: N_i acts trivially on V_quot (= IsTrivial ρ_quot.comp N_i.subtype)
      have hN_i_triv :
          Representation.IsTrivial (ρ_quot.comp N_i.subtype) := by
        constructor
        intro n
        apply LinearMap.ext
        intro v_q
        refine Quotient.inductionOn' v_q (fun w => ?_)
        -- Goal: ρ_quot ↑n (Quotient.mk' w) = 1 (Quotient.mk' w)
        change Submodule.Quotient.mk ((a (i + 1)).toRepresentation
                (N_i.subtype n) w) = Submodule.Quotient.mk w
        rw [Submodule.Quotient.eq]
        change ρ_H (N_i.subtype n) w.val - w.val ∈ (a i).toSubmodule
        exact n.property w.val w.property
      -- Step 7g: ρ_bar : Representation F (↥H ⧸ N_i) (V_quot)
      have := hN_i_normal
      let ρ_bar : Representation F (↥H ⧸ N_i) (↥aip1_top ⧸ ai_in_aip1) :=
        Representation.ofQuotient ρ_quot N_i
      -- Step 7h: ρ_bar faithful
      have hρ_bar_faithful : Function.Injective ρ_bar := by
        rw [injective_iff_map_eq_one]
        intro hbar
        refine Quotient.inductionOn' hbar (fun h => ?_)
        intro hh_eq
        rw [QuotientGroup.eq_one_iff]
        intro v hv
        have h_quot_h_eq : ρ_quot h = 1 := by
          apply LinearMap.ext
          intro v_q
          refine Quotient.inductionOn' v_q (fun w => ?_)
          -- Goal: ρ_quot h (Quotient.mk'' w) = 1 (Quotient.mk'' w)
          -- Rewrite ρ_quot via ρ_bar:
          have h_app : ρ_quot h (Submodule.Quotient.mk w) =
              ρ_bar (QuotientGroup.mk h) (Submodule.Quotient.mk w) :=
            (Representation.ofQuotient_coe_apply ρ_quot N_i h _).symm
          -- mk equals: Submodule.Quotient.mk w = Quotient.mk'' w
          have h_mk_eq : (Submodule.Quotient.mk w : ↥aip1_top ⧸ ai_in_aip1) =
              Quotient.mk'' w := rfl
          rw [← h_mk_eq, h_app]
          -- ρ_bar (QuotientGroup.mk h) = ρ_bar (Quotient.mk'' h) = 1
          have h_eq_qbar : (QuotientGroup.mk h : ↥H ⧸ N_i) = Quotient.mk'' h := rfl
          rw [h_eq_qbar, hh_eq]
        have h_app_v : ρ_quot h (Submodule.Quotient.mk ⟨v, hv⟩)
            = Submodule.Quotient.mk ⟨v, hv⟩ := by
          rw [h_quot_h_eq, Module.End.one_apply]
        change Submodule.Quotient.mk ((a (i + 1)).toRepresentation h ⟨v, hv⟩)
            = Submodule.Quotient.mk ⟨v, hv⟩ at h_app_v
        rw [Submodule.Quotient.eq] at h_app_v
        change ρ_H h v - v ∈ (a i).toSubmodule
        exact h_app_v
      -- Step 7i: ρ_bar irreducible
      have hρ_bar_irr : ∀ U : Submodule F (↥aip1_top ⧸ ai_in_aip1),
          (∀ g : ↥H ⧸ N_i, ∀ v ∈ U, ρ_bar g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
        intro U hU_inv
        -- W := comap mkQ U : Submodule of aip1_top, contains ai_in_aip1
        let W : Submodule F ↥aip1_top := Submodule.comap ai_in_aip1.mkQ U
        have hW_ge : ai_in_aip1 ≤ W := Submodule.le_comap_mkQ ai_in_aip1 U
        -- W invariant under (a(i+1)).toRepresentation
        have hW_inv : ∀ h : ↥H, ∀ w ∈ W, (a (i + 1)).toRepresentation h w ∈ W := by
          intro h w hw_W
          change ai_in_aip1.mkQ ((a (i + 1)).toRepresentation h w) ∈ U
          have h_step : ai_in_aip1.mkQ ((a (i + 1)).toRepresentation h w) =
              ρ_quot h (ai_in_aip1.mkQ w) := rfl
          rw [h_step]
          have hw_U : ai_in_aip1.mkQ w ∈ U := hw_W
          -- ρ_bar (QuotientGroup.mk h) (ai_in_aip1.mkQ w) = ρ_quot h (...)
          have h_eq : ρ_quot h (ai_in_aip1.mkQ w) =
              ρ_bar (QuotientGroup.mk h) (ai_in_aip1.mkQ w) :=
            (Representation.ofQuotient_coe_apply ρ_quot N_i h _).symm
          rw [h_eq]
          exact hU_inv (QuotientGroup.mk h) (ai_in_aip1.mkQ w) hw_U
        -- Build σ : Subrepresentation ρ_H with σ.toSubmodule = Submodule.map subtype W
        let σ : Subrepresentation ρ_H :=
          { toSubmodule := Submodule.map aip1_top.subtype W
            apply_mem_toSubmodule := by
              intro g v hv
              obtain ⟨⟨w, hw_aip1⟩, hw_W, hval_eq⟩ := hv
              refine ⟨(a (i + 1)).toRepresentation g ⟨w, hw_aip1⟩,
                hW_inv g ⟨w, hw_aip1⟩ hw_W, ?_⟩
              rw [← hval_eq]; rfl }
        -- a i ≤ σ
        have hai_le_σ : a i ≤ σ := by
          intro v hv
          have h_in_aip1 : v ∈ aip1_top := (h_cov i hi_lt_n).le hv
          refine ⟨⟨v, h_in_aip1⟩, ?_, rfl⟩
          change (⟨v, h_in_aip1⟩ : ↥aip1_top) ∈ W
          exact hW_ge hv
        -- σ ≤ a (i+1)
        have hσ_le_aip1 : σ ≤ a (i + 1) := by
          intro v hv
          obtain ⟨⟨w, hw_aip1⟩, _, hval_eq⟩ := hv
          rw [← hval_eq]; exact hw_aip1
        -- By covering: σ = a i or σ = a (i+1)
        have h_covby : a i ⋖ a (i + 1) := h_cov i hi_lt_n
        rcases h_covby.eq_or_eq hai_le_σ hσ_le_aip1 with hσ_eq_ai | hσ_eq_aip1
        · -- σ = a i ⇒ U = ⊥
          left
          rw [eq_bot_iff]
          intro u hu_U
          obtain ⟨w, rfl⟩ := ai_in_aip1.mkQ_surjective u
          have hw_W : w ∈ W := hu_U
          have hwval_σ : w.val ∈ σ.toSubmodule := ⟨w, hw_W, rfl⟩
          have hσ_eq : σ.toSubmodule = (a i).toSubmodule :=
            congr_arg Subrepresentation.toSubmodule hσ_eq_ai
          rw [hσ_eq] at hwval_σ
          have hw_ai : w ∈ ai_in_aip1 := hwval_σ
          change (ai_in_aip1.mkQ w : ↥aip1_top ⧸ ai_in_aip1) ∈
            (⊥ : Submodule F (↥aip1_top ⧸ ai_in_aip1))
          rw [Submodule.mem_bot, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero]
          exact hw_ai
        · -- σ = a (i+1) ⇒ U = ⊤
          right
          rw [eq_top_iff]
          intro u _
          obtain ⟨w, rfl⟩ := ai_in_aip1.mkQ_surjective u
          change w ∈ W
          have hwval_aip1 : w.val ∈ aip1_top := w.property
          have hσ_eq : σ.toSubmodule = (a (i + 1)).toSubmodule :=
            congr_arg Subrepresentation.toSubmodule hσ_eq_aip1
          have hwval_σ : w.val ∈ σ.toSubmodule := by
            rw [hσ_eq]; exact hwval_aip1
          obtain ⟨⟨w', hw'_aip1⟩, hw'_W, hval_eq⟩ := hwval_σ
          have h_eq_w : w = ⟨w', hw'_aip1⟩ := Subtype.ext hval_eq.symm
          rw [h_eq_w]; exact hw'_W
      -- Step 7j: closure {x_bar, y_bar} = ⊤ in ↥H ⧸ N_i
      let x_subt : ↥H := ⟨x, hxH⟩
      let y_subt : ↥H := ⟨y, hyH⟩
      let x_bar : ↥H ⧸ N_i := QuotientGroup.mk x_subt
      let y_bar : ↥H ⧸ N_i := QuotientGroup.mk y_subt
      -- closure {x_subt, y_subt} = ⊤ in ↥H
      have h_gen_subt : Subgroup.closure ({x_subt, y_subt} : Set ↥H) = ⊤ := by
        apply Subgroup.map_injective H.subtype_injective
        rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, H.range_subtype]
        congr 1
        ext g
        constructor
        · rintro ⟨a, ha_mem, rfl⟩
          rcases ha_mem with rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ rfl
        · rintro (rfl | rfl)
          · exact ⟨x_subt, Set.mem_insert _ _, rfl⟩
          · exact ⟨y_subt, Set.mem_insert_of_mem _ rfl, rfl⟩
      -- closure {x_bar, y_bar} = ⊤ in ↥H ⧸ N_i
      have h_gen_bar : Subgroup.closure ({x_bar, y_bar} : Set (↥H ⧸ N_i)) = ⊤ := by
        have h_eq : ({x_bar, y_bar} : Set (↥H ⧸ N_i)) =
            (QuotientGroup.mk' N_i) '' ({x_subt, y_subt} : Set ↥H) := by
          ext z
          constructor
          · rintro (rfl | rfl)
            · exact ⟨x_subt, Set.mem_insert _ _, rfl⟩
            · exact ⟨y_subt, Set.mem_insert_of_mem _ rfl, rfl⟩
          · rintro ⟨a, ha_mem, rfl⟩
            rcases ha_mem with rfl | rfl
            · exact Set.mem_insert _ _
            · exact Set.mem_insert_of_mem _ rfl
        rw [h_eq, ← MonoidHom.map_closure, h_gen_subt,
          ← MonoidHom.range_eq_map]
        exact MonoidHom.range_eq_top_of_surjective _
          (QuotientGroup.mk'_surjective N_i)
      -- Step 7k: (ρ_bar x_bar - 1)² = 0 and similarly for y_bar
      have h_lift_sq : ∀ (z_subt : ↥H)
          (hzsq : ((ρ_H z_subt : Module.End F V) - 1) ^ 2 = 0),
          ((ρ_bar (QuotientGroup.mk z_subt) :
              Module.End F (↥aip1_top ⧸ ai_in_aip1)) - 1) ^ 2 = 0 := by
        intro z_subt hzsq
        apply LinearMap.ext
        intro v_q
        refine Quotient.inductionOn' v_q (fun w => ?_)
        -- Goal: ((ρ_bar (mk z_subt) - 1) ^ 2) (mk w) = 0 (mk w)
        -- Key fact: applying ρ_bar via ofQuotient_coe_apply: lifts to (a(i+1)).toRep z_subt
        -- (ρ_bar (mk z_subt) - 1) (mk u) = mk ((a(i+1)).toRep z_subt u - u) for any u
        have h_step : ∀ (u : ↥aip1_top),
            ((ρ_bar (QuotientGroup.mk z_subt) - 1)
              (Submodule.Quotient.mk u : ↥aip1_top ⧸ ai_in_aip1)) =
            Submodule.Quotient.mk ((a (i + 1)).toRepresentation z_subt u - u) := by
          intro u
          rw [LinearMap.sub_apply, Module.End.one_apply]
          have h_app : ρ_bar (QuotientGroup.mk z_subt) (Submodule.Quotient.mk u) =
              Submodule.Quotient.mk ((a (i + 1)).toRepresentation z_subt u) :=
            Representation.ofQuotient_coe_apply ρ_quot N_i z_subt _
          rw [h_app]; rfl
        set M : Module.End F (↥aip1_top ⧸ ai_in_aip1) :=
          (ρ_bar (QuotientGroup.mk z_subt) - 1) ^ 2 with hM_def
        have h_sq_app : M (Quotient.mk'' w) =
            Submodule.Quotient.mk ((a (i + 1)).toRepresentation z_subt
              ((a (i + 1)).toRepresentation z_subt w - w) -
              ((a (i + 1)).toRepresentation z_subt w - w)) := by
          change M (Submodule.Quotient.mk w) = _
          rw [hM_def, pow_two, Module.End.mul_apply, h_step, h_step]
        rw [h_sq_app]
        -- The inner argument equals 0 in ↥aip1_top.
        have h_inner_zero : (a (i + 1)).toRepresentation z_subt
            ((a (i + 1)).toRepresentation z_subt w - w) -
            ((a (i + 1)).toRepresentation z_subt w - w) = (0 : ↥aip1_top) := by
          apply Subtype.ext
          -- Compute .val
          have h_act : ∀ (u' : ↥aip1_top),
              ((a (i + 1)).toRepresentation z_subt u' : ↥aip1_top).val =
              ρ_H z_subt u'.val := fun _ => rfl
          change ((((a (i + 1)).toRepresentation z_subt
              ((a (i + 1)).toRepresentation z_subt w - w) -
              ((a (i + 1)).toRepresentation z_subt w - w)) : ↥aip1_top).val) =
              (0 : ↥aip1_top).val
          -- Step-by-step value computation
          rw [show ((((a (i + 1)).toRepresentation z_subt
                  ((a (i + 1)).toRepresentation z_subt w - w) -
                  ((a (i + 1)).toRepresentation z_subt w - w)) : ↥aip1_top).val) =
              (((a (i + 1)).toRepresentation z_subt
                  ((a (i + 1)).toRepresentation z_subt w - w)) : ↥aip1_top).val -
              (((a (i + 1)).toRepresentation z_subt w - w) : ↥aip1_top).val from rfl]
          rw [show ((((a (i + 1)).toRepresentation z_subt w - w) : ↥aip1_top).val) =
              ((a (i + 1)).toRepresentation z_subt w : ↥aip1_top).val - w.val from rfl]
          rw [h_act ((a (i + 1)).toRepresentation z_subt w - w), h_act w]
          change ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val - w.val)
              = (0 : V)
          -- (ρ_H z_subt - 1)² w.val = ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val -
          -- w.val)
          have h_at_val :
              ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val - w.val) = 0 := by
            have h := congr_arg (· w.val) hzsq
            simp only [LinearMap.zero_apply] at h
            rw [pow_two, Module.End.mul_apply,
              LinearMap.sub_apply, LinearMap.sub_apply,
              Module.End.one_apply, Module.End.one_apply] at h
            -- h : ρ_H z_subt (ρ_H z_subt w.val - w.val) - (ρ_H z_subt w.val - w.val) = 0
            exact h
          exact h_at_val
        rw [h_inner_zero, Submodule.Quotient.mk_zero]
        rfl
      have hx_bar_sq : ((ρ_bar x_bar : Module.End F _) - 1) ^ 2 = 0 := by
        have h_eq : ρ_H x_subt = ρ x := rfl
        exact h_lift_sq x_subt (by rw [h_eq]; exact hxsq)
      have hy_bar_sq : ((ρ_bar y_bar : Module.End F _) - 1) ^ 2 = 0 := by
        have h_eq : ρ_H y_subt = ρ y := rfl
        exact h_lift_sq y_subt (by rw [h_eq]; exact hysq)
      -- Step 7l: x_bar ≠ 1 and y_bar ≠ 1 (PGroupFixedVector argument)
      -- Helper: if z_subt ∈ N_i, then ↥H/N_i = ⟨other_bar⟩ p-group ⇒ contradiction
      -- We'll show: x_subt ∉ N_i and y_subt ∉ N_i.
      -- Argument structure (for x_subt):
      --   Suppose x_subt ∈ N_i. Then ↥H/N_i = closure {1, y_bar} = ⟨y_bar⟩.
      --   y_bar = image of y_subt (p-element) ⇒ y_bar is p-element ⇒ ⟨y_bar⟩ p-group.
      --   ⇒ ↥H/N_i p-group. ρ_bar faithful irreducible on V_quot in char p.
      --   PGroupFixedVector ⇒ ρ_bar.invariants ≠ ⊥, irreducibility ⇒ = ⊤
      --   ⇒ ρ_bar acts trivially ⇒ ↥H/N_i = 1 ⇒ q_witness ∈ N_i, 矛盾.
      have h_HN_not_pgroup_via : ∀ (z : G) (z_subt : ↥H) (hz_eq : (z_subt : G) = z)
          (hzp : IsPGroup p (Subgroup.zpowers z)),
          (Subgroup.zpowers (QuotientGroup.mk z_subt : ↥H ⧸ N_i)
            = (⊤ : Subgroup (↥H ⧸ N_i))) → False := by
        intro z z_subt hz_eq hzp h_top_zpow
        -- z_bar is p-element (via order divides z's order)
        have h_HN_pgroup : IsPGroup p (↥H ⧸ N_i) := by
          rw [IsPGroup.iff_card] at hzp
          obtain ⟨n, hn⟩ := hzp
          rw [Nat.card_zpowers] at hn
          have h_ord_z_subt : orderOf z_subt = orderOf z := by
            have h := orderOf_injective H.subtype Subtype.coe_injective z_subt
            simp only [Subgroup.coe_subtype] at h
            rw [hz_eq] at h
            exact h.symm
          have h_pow_mk : (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ^ (p ^ n) = 1 := by
            have h_pow : z_subt ^ (p ^ n) = 1 := by
              rw [← h_ord_z_subt] at hn
              rw [← hn, pow_orderOf_eq_one]
            have h_eq : (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ^ (p ^ n)
                = (QuotientGroup.mk (z_subt ^ (p ^ n)) : ↥H ⧸ N_i) := by
              change ((QuotientGroup.mk' N_i) z_subt) ^ (p ^ n) =
                (QuotientGroup.mk' N_i) (z_subt ^ (p ^ n))
              rw [map_pow]
            rw [h_eq, h_pow]; rfl
          have h_ord_mk_dvd : orderOf (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ∣ p ^ n :=
            orderOf_dvd_of_pow_eq_one h_pow_mk
          obtain ⟨m, _, h_ord_mk⟩ := (Nat.dvd_prime_pow Fact.out).mp h_ord_mk_dvd
          -- Now ↥H ⧸ N_i = zpowers (mk z_subt) (by h_top_zpow), so card = orderOf mk z_subt
          intro g
          have h_g_in : g ∈ Subgroup.zpowers (QuotientGroup.mk z_subt : ↥H ⧸ N_i) := by
            rw [h_top_zpow]; trivial
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h_g_in
          -- g = (mk z_subt)^k. Order of g divides order of mk z_subt = p^m.
          refine ⟨m, ?_⟩
          have h_pow_g : g ^ (p ^ m) = 1 := by
            rw [← hk]
            rw [show ((QuotientGroup.mk z_subt : ↥H ⧸ N_i)^k)^(p^m)
                = ((QuotientGroup.mk z_subt : ↥H ⧸ N_i)^(p^m))^k by group]
            have : (QuotientGroup.mk z_subt : ↥H ⧸ N_i) ^ (p ^ m) = 1 := by
              rw [← h_ord_mk, pow_orderOf_eq_one]
            rw [this, one_zpow]
          exact h_pow_g
        -- ρ_bar.invariants ≠ ⊥
        have hHN_finite : Finite (↥H ⧸ N_i) := inferInstance
        have h_VQ_top_ne_bot : (⊤ : Submodule F (↥aip1_top ⧸ ai_in_aip1)) ≠ ⊥ := by
          intro h_bot
          obtain ⟨v, hv⟩ := exists_ne (0 : ↥aip1_top ⧸ ai_in_aip1)
          apply hv
          have : v ∈ (⊥ : Submodule F (↥aip1_top ⧸ ai_in_aip1)) := h_bot ▸ Submodule.mem_top
          exact (Submodule.mem_bot _).mp this
        have h_inv_ne_bot : ρ_bar.invariants ≠ ⊥ :=
          h_HN_pgroup.invariants_ne_bot ρ_bar h_VQ_top_ne_bot
        -- Irreducibility: invariants is ↥H/N_i-invariant
        have h_inv_subm_inv : ∀ g : ↥H ⧸ N_i, ∀ v ∈ ρ_bar.invariants,
            ρ_bar g v ∈ ρ_bar.invariants := by
          intro g v hv
          rw [Representation.mem_invariants] at hv ⊢
          intro h
          calc ρ_bar h (ρ_bar g v) = (ρ_bar h * ρ_bar g) v := by
                rw [Module.End.mul_apply]
            _ = ρ_bar (h * g) v := by rw [← map_mul]
            _ = ρ_bar g (ρ_bar (g⁻¹ * h * g) v) := by
                rw [show h * g = g * (g⁻¹ * h * g) by group, map_mul, Module.End.mul_apply]
            _ = ρ_bar g v := by rw [hv (g⁻¹ * h * g)]
        rcases hρ_bar_irr ρ_bar.invariants h_inv_subm_inv with h_bot | h_top
        · exact h_inv_ne_bot h_bot
        · -- ρ_bar.invariants = ⊤ ⇒ ρ_bar acts trivially
          have h_triv : ∀ g : ↥H ⧸ N_i, ρ_bar g = 1 := by
            intro g
            apply LinearMap.ext
            intro v
            have hv_inv : v ∈ ρ_bar.invariants := by rw [h_top]; exact Submodule.mem_top
            have := (Representation.mem_invariants ρ_bar v).mp hv_inv g
            rw [Module.End.one_apply]
            exact this
          -- ρ_bar = 1 ⇒ ↥H/N_i = 1 (faithful)
          have h_HN_trivial : ∀ g : ↥H ⧸ N_i, g = 1 := by
            intro g
            apply hρ_bar_faithful
            rw [h_triv g, map_one]
          -- But q_witness has nontrivial image in ↥H/N_i (since q_witness ∉ N_i)
          have h_q_bar_ne_one : (QuotientGroup.mk q_witness : ↥H ⧸ N_i) ≠ 1 := by
            intro h_eq; apply h_q_notin_Ni
            exact (QuotientGroup.eq_one_iff _).mp h_eq
          exact h_q_bar_ne_one (h_HN_trivial _)
      have hx_bar_ne : ρ_bar x_bar ≠ 1 := by
        intro h_eq
        have hx_bar_one : x_bar = 1 := hρ_bar_faithful (h_eq.trans (map_one ρ_bar).symm)
        -- closure {x_bar, y_bar} = ⊤; x_bar = 1 ⇒ ⟨y_bar⟩ = ⊤
        have h_zpow_y : Subgroup.zpowers y_bar = (⊤ : Subgroup (↥H ⧸ N_i)) := by
          apply le_antisymm le_top
          rw [← h_gen_bar]
          rw [Subgroup.closure_le]
          intro z hz
          rcases hz with hz | hz
          · subst hz; rw [hx_bar_one]; exact one_mem _
          · subst hz; exact Subgroup.mem_zpowers _
        exact h_HN_not_pgroup_via y y_subt rfl hyp h_zpow_y
      have hy_bar_ne : ρ_bar y_bar ≠ 1 := by
        intro h_eq
        have hy_bar_one : y_bar = 1 := hρ_bar_faithful (h_eq.trans (map_one ρ_bar).symm)
        have h_zpow_x : Subgroup.zpowers x_bar = (⊤ : Subgroup (↥H ⧸ N_i)) := by
          apply le_antisymm le_top
          rw [← h_gen_bar]
          rw [Subgroup.closure_le]
          intro z hz
          rcases hz with hz | hz
          · subst hz; exact Subgroup.mem_zpowers _
          · subst hz; rw [hy_bar_one]; exact one_mem _
        exact h_HN_not_pgroup_via x x_subt rfl hxp h_zpow_x
      -- Step 8: Apply thmA2 + Lagrange
      have : Finite (↥H ⧸ N_i) := inferInstance
      have h_HN_even : ¬ Odd (Nat.card (↥H ⧸ N_i)) :=
        thmA2 _hp_odd ρ_bar hρ_bar_faithful hρ_bar_irr x_bar y_bar h_gen_bar
          hx_bar_sq hx_bar_ne hy_bar_sq hy_bar_ne
      have h_2_dvd_HN : 2 ∣ Nat.card (↥H ⧸ N_i) := by
        rcases Nat.even_or_odd (Nat.card (↥H ⧸ N_i)) with h_even | h_odd
        · exact h_even.two_dvd
        · exact absurd h_odd h_HN_even
      -- Lagrange: |↥H ⧸ N_i| ∣ |↥H| ∣ |G|
      have h_HN_dvd_H : Nat.card (↥H ⧸ N_i) ∣ Nat.card ↥H := by
        rw [← Subgroup.index_eq_card]
        exact ⟨Nat.card N_i, N_i.index_mul_card.symm⟩
      have h_H_dvd_G : Nat.card ↥H ∣ Nat.card G := H.card_subgroup_dvd_card
      exact h_2_dvd_HN.trans (h_HN_dvd_H.trans h_H_dvd_G)
  exact hodd.not_two_dvd_nat h_two_dvd

end PStability

end OddOrder.BG.AppA


