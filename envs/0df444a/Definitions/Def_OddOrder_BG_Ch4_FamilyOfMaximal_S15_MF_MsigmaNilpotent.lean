-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_MsigmaNilpotent
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_MsigmaNilpotent
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:00:02.959995+00:00
-- url     : https://prove2.me/theorems/b049c04d-79ec-4c9b-96b4-0d18722f8f08
-- title:
--   BG §15: $M_\sigma$ nilpotent (Theorem 15.2 lifting lemmas)
-- statement:
--   A part of the Theorem 15.2 development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §15, split from the Corollary 15.5 file. It contains coprime lifting over a normal $D$-invariant subgroup (independent of §14), the 'lift' of Theorem 15.2 step 3(ii) from Proposition 1.5(d), and step 4, the fixed-point-free fact $C_{\bar Q}(D)=1$.
--
--   Main declarations: `le_sup_inf_centralizer_of_commutator_le`; `fpf_of_centralizer_inf_le`; `fpf_of_centralizer_inf_le_general`; `mem_centralizer_of_centralizes_quotient`.
--
--   The bundle also proves 21 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/MsigmaNilpotent.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/MsigmaNilpotent.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Helpers

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Ambient nilpotent Hall splitting**: for a finite nilpotent subgroup `H`, the ambient
realizations of `O_π(H)` and `O_{π'}(H)` join to all of `H`.  (Image under `H.subtype` of the
`↥H`-internal `O_π(↥H) ⊔ O_{π'}(↥H) = ⊤`.)  Combined with `opiCoreInG_commutator_compl_eq_bot`
and `inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl`, this is the direct-product splitting
`H = O_π(H) × O_{π'}(H)` of a nilpotent group into its Hall `π`/`π'` parts. -/
theorem opiCoreInG_sup_compl_eq_of_isNilpotent [Finite G] (π : Set ℕ) {H : Subgroup G}
    [Group.IsNilpotent ↥H] :
    opiCoreInG π H ⊔ opiCoreInG πᶜ H = H := by
  refine le_antisymm (sup_le (opiCoreInG_le π H) (opiCoreInG_le πᶜ H)) ?_
  have htop : (Ch03.oPiCore π ↥H ⊔ Ch03.oPiCore {p | p ∉ π} ↥H).map H.subtype =
      opiCoreInG π H ⊔ opiCoreInG πᶜ H := by
    rw [Subgroup.map_sup]; rfl
  calc H = (⊤ : Subgroup ↥H).map H.subtype := by
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ ≤ (Ch03.oPiCore π ↥H ⊔ Ch03.oPiCore {p | p ∉ π} ↥H).map H.subtype :=
        Subgroup.map_mono
          (OddOrder.BG.Ch3.S10.top_le_oPiCore_sup_compl_of_isNilpotent (K := ↥H) π)
    _ = opiCoreInG π H ⊔ opiCoreInG πᶜ H := htop

/-- **Normalizing a subgroup normalizes its centralizer** (`§14`-independent, reusable):
`N_G(H) ≤ N_G(C_G(H))`.  If `g` normalizes `H`, conjugation by `g` permutes the elements of `H`,
hence preserves the set of elements commuting with all of `H`. -/
theorem normalizer_le_normalizer_centralizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (Subgroup.centralizer (H : Set G)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ {z : G}, z ∈ Subgroup.normalizer (H : Set G) →
      ∀ c, c ∈ Subgroup.centralizer (H : Set G) →
        z * c * z⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
    intro z hz c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : z⁻¹ * x * z ∈ H := (Subgroup.mem_normalizer_iff''.mp hz x).mp hx
    have hcx : (z⁻¹ * x * z) * c = c * (z⁻¹ * x * z) :=
      Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (z * c * z⁻¹) = z * ((z⁻¹ * x * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * x * z)) * z⁻¹ := by rw [hcx]
      _ = (z * c * z⁻¹) * x := by group
  intro c
  refine ⟨fun hc => key hg c hc, fun hc => ?_⟩
  have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normalizer (H : Set G)).inv_mem hg
  have := key hginv (g * c * g⁻¹) hc
  simpa [mul_assoc] using this

/-- **Commuting nilpotent join is nilpotent** (`§14`-independent, reusable): if two subgroups
`A`, `B` are each nilpotent and elementwise commute (`⁅A, B⁆ = ⊥`), then `A ⊔ B` is nilpotent.
The join is the range of the homomorphism `↥A × ↥B → G`, `(a, b) ↦ a · b` (well-defined since
`A`, `B` commute), so it is a quotient image of the nilpotent direct product `↥A × ↥B`. -/
theorem isNilpotent_sup_of_commutator_eq_bot {A B : Subgroup G}
    [Group.IsNilpotent ↥A] [Group.IsNilpotent ↥B] (hcomm : ⁅A, B⁆ = ⊥) :
    Group.IsNilpotent ↥(A ⊔ B) := by
  have hAcB : A ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcomm' : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := by
    intro a b
    exact (Subgroup.mem_centralizer_iff.mp (hAcB a.2) (b : G) b.2).symm
  set f : ↥A × ↥B →* G := (A.subtype).noncommCoprod (B.subtype) hcomm' with hf
  have hrange : f.range = A ⊔ B := by
    rw [hf, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have : Group.IsNilpotent ↥(f.range) :=
    Group.nilpotent_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact hrange ▸ this

/-- **`C_Q(D) ⊊ Q` for a non-nilpotent would-be-commuting join** (`§14`-independent, reusable): if
`Q` and `D` are nilpotent but `Q ⊔ D` is not, then `D` does not centralize `Q`, i.e.
`Q ⊓ C_G(D) ≠ Q`.  (Otherwise `Q ≤ C_G(D)` gives `⁅Q, D⁆ = ⊥`, making `Q ⊔ D` nilpotent by
`isNilpotent_sup_of_commutator_eq_bot`.)

In Theorem 15.2's step 3 (mmd L4194) this is `Q₀ = C_Q(D) ⊊ Q` for the `K`-invariant complement
`D` of `Q` in `M_σ` (`Q ⊔ D = M_σ` non-nilpotent, `Q` the `q`-Sylow, `D` nilpotent by
`complement_isNilpotent_of_inputs`): the proper subgroup that starts the minimal-normal `Q̄`
analysis. -/
theorem inf_centralizer_ne_self_of_sup_not_nilpotent {Q D : Subgroup G}
    [Group.IsNilpotent ↥Q] [Group.IsNilpotent ↥D]
    (hnot : ¬ Group.IsNilpotent ↥(Q ⊔ D)) :
    Q ⊓ Subgroup.centralizer (D : Set G) ≠ Q := fun hQ0 =>
  hnot (isNilpotent_sup_of_commutator_eq_bot
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hQ0 ▸ inf_le_right)))

/-- **`Q₀ = C_Q(D)` is `KD`-invariant** (`§14`-independent, reusable): if `K` and `D` each
normalize `Q`, and `K` normalizes `D`, then `K ⊔ D` normalizes `Q ⊓ C_G(D)`.  (`D` always
normalizes its own centralizer and `Q`; `K` normalizes `C_G(D)` because it normalizes `D`
[`normalizer_le_normalizer_centralizer`]; both then normalize the intersection
[`le_normalizer_inf`].)

In Theorem 15.2's step 3 (mmd L4194) this makes `Q₀ = C_Q(D)` a `KD`-invariant subgroup of `Q`,
so that `K` and `D` act on `N_M(Q₀)/Q₀` (whence the minimal normal `Q₁/Q₀`). -/
theorem sup_le_normalizer_centralizer_inf {Q D K : Subgroup G}
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hKD : K ≤ Subgroup.normalizer (D : Set G)) :
    K ⊔ D ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
  sup_le
    (le_normalizer_inf hKQ (hKD.trans (normalizer_le_normalizer_centralizer D)))
    (le_normalizer_inf hDQ (Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer D)))

/-- **Strict normalizer growth, intersected form** (`§14`-independent, reusable): for a proper
subgroup `Q0 < Q` of a nilpotent `Q`, a witness normalizing `Q0` lies *inside* `Q`, so
`Q0 < Q ⊓ N_G(Q0) = N_Q(Q0)`.  Sharper than `lt_normalizer_of_lt_of_isNilpotent` (which keeps only
`Q0 < N_G(Q0)`, dropping the `≤ Q` containment): the strict step is obtained inside `↥Q` and pushed
back through `Q.subtype` (`map_lt_map_iff_of_injective` + `subgroupOf_map_subtype`).

In Theorem 15.2's brick D (mmd L4194) this furnishes the nontrivial chain top `Q1 < N_Q(Q1)` handed
to `exists_minimal_normalOver` (ambient `N_M(Q1)`, `T = N_Q(Q1) ≤ Q`) to build the next chief
factor `Q2/Q1` with `Q1 < Q2 ≤ Q`. -/
theorem lt_inf_normalizer_of_lt_of_isNilpotent {Q Q0 : Subgroup G} [Group.IsNilpotent ↥Q]
    (hQ0Q : Q0 < Q) :
    Q0 < Q ⊓ Subgroup.normalizer (Q0 : Set G) := by
  have hQ0le : Q0 ≤ Q := hQ0Q.le
  have hlt : Q0.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top, ne_eq, Subgroup.subgroupOf_eq_top]; exact hQ0Q.2
  have h := OddOrder.Isaacs.Ch01.lt_normalizer_of_isNilpotent_of_lt_top (G := ↥Q) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hQ0le] at h
  -- `h : Q0.subgroupOf Q < (N_G Q0).subgroupOf Q`; map back to `G` along the injective `Q.subtype`.
  have hmap := (Subgroup.map_lt_map_iff_of_injective Q.subtype_injective).mpr h
  rw [Subgroup.map_subgroupOf_eq_of_le hQ0le, Subgroup.subgroupOf_map_subtype] at hmap
  rwa [inf_comm] at hmap

/-- **Minimal `N`-normal subgroup over `Q₀`** (`§14`-independent, reusable): given a nontrivial
`N`-normal subgroup `T` strictly above `Q₀`, there is a minimal `N`-normal subgroup `Q₁` with
`Q₀ < Q₁ ≤ T` (no `N`-normal subgroup lies strictly between `Q₀` and `Q₁`).  This is the
subgroup-lattice (quotient-free) form of "the quotient `N/Q₀` has a minimal normal subgroup inside
`T/Q₀`", obtained from finiteness of the subgroup lattice (`Set.Finite.exists_minimal`).

In Theorem 15.2's step 3 (mmd L4194) `N = N_M(Q₀)` and `T = N_Q(Q₀) = Q ⊓ N_M(Q₀)` (nontrivial over
`Q₀` by `lt_normalizer_of_lt_of_isNilpotent`), giving the minimal normal `Q₁/Q₀` with `Q₁ ≤ Q`. -/
theorem exists_minimal_normalOver [Finite G] {N Q0 T : Subgroup G}
    (hQ0T : Q0 < T) (hTnorm : (T.subgroupOf N).Normal) :
    ∃ Q1 : Subgroup G, Q0 < Q1 ∧ Q1 ≤ T ∧ (Q1.subgroupOf N).Normal ∧
      ∀ H : Subgroup G, Q0 < H → H ≤ Q1 → (H.subgroupOf N).Normal → Q1 ≤ H := by
  let S : Set (Subgroup G) := {H | Q0 < H ∧ H ≤ T ∧ (H.subgroupOf N).Normal}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_ne : S.Nonempty := ⟨T, hQ0T, le_refl T, hTnorm⟩
  obtain ⟨Q1, ⟨hQ0Q1, hQ1T, hQ1norm⟩, hQ1min⟩ := hS_fin.exists_minimal hS_ne
  exact ⟨Q1, hQ0Q1, hQ1T, hQ1norm, fun H hQ0H hHQ1 hHnorm =>
    hQ1min ⟨hQ0H, hHQ1.trans hQ1T, hHnorm⟩ hHQ1⟩

/-- **Chief factor over `Q₁` normalized by `D` and `K₁`** (Theorem 15.2 brick D construction,
mmd L4194).  If `Q₁ < Q` with `Q` nilpotent, `Q ⊴ M` (`Q ≤ M ≤ N_G(Q)`), and `D, K₁ ≤ M ⊓ N_G(Q₁)`,
then there is a chief factor `Q₂/Q₁` with `Q₁ < Q₂ ≤ Q` whose `Q₂` is normalized by `D` and `K₁`
and itself normalizes `Q₁`.

Ambient `N = M ⊓ N_G(Q₁)` contains `D` and `K₁` and normalizes `T = N_Q(Q₁) = Q ⊓ N_G(Q₁) ≤ Q`
(`N ≤ N_G(Q)` since `N ≤ M ≤ N_G(Q)`, and `N ≤ N_G(N_G(Q₁))` by `le_normalizer`, so `N ≤ N_G(T)` by
`le_normalizer_inf`).  `lt_inf_normalizer_of_lt_of_isNilpotent` gives the nontrivial top
`Q₁ < N_Q(Q₁)`; `exists_minimal_normalOver` then produces the minimal `N`-normal `Q₂` over `Q₁`
inside `T`, and `Q₂ ⊴ N` transfers to `D, K₁ ≤ N_G(Q₂)`. -/
theorem exists_chiefFactor_over_normalized [Finite G]
    {M Q Q1 D K1 : Subgroup G} [Group.IsNilpotent ↥Q]
    (hQ1Q : Q1 < Q) (hQM : Q ≤ M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hDN : D ≤ M ⊓ Subgroup.normalizer (Q1 : Set G))
    (hK1N : K1 ≤ M ⊓ Subgroup.normalizer (Q1 : Set G)) :
    ∃ Q2 : Subgroup G, Q1 < Q2 ∧ Q2 ≤ Q ∧
      D ≤ Subgroup.normalizer (Q2 : Set G) ∧
      K1 ≤ Subgroup.normalizer (Q2 : Set G) ∧
      Q2 ≤ Subgroup.normalizer (Q1 : Set G) := by
  -- Nontrivial chain top `Q₁ < N_Q(Q₁) = Q ⊓ N_G(Q₁)`.
  have hQ1T : Q1 < Q ⊓ Subgroup.normalizer (Q1 : Set G) :=
    lt_inf_normalizer_of_lt_of_isNilpotent hQ1Q
  -- `T = N_Q(Q₁) ≤ N = N_M(Q₁)`.
  have hTN : Q ⊓ Subgroup.normalizer (Q1 : Set G) ≤ M ⊓ Subgroup.normalizer (Q1 : Set G) :=
    inf_le_inf hQM le_rfl
  -- `N` normalizes `T` (it normalizes `Q` via `M ≤ N_G(Q)` and `N_G(Q₁)` via `le_normalizer`).
  have hN_normT : M ⊓ Subgroup.normalizer (Q1 : Set G) ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.normalizer (Q1 : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf (inf_le_left.trans hMQ) (inf_le_right.trans Subgroup.le_normalizer)
  have hTnorm : ((Q ⊓ Subgroup.normalizer (Q1 : Set G)).subgroupOf
      (M ⊓ Subgroup.normalizer (Q1 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr hN_normT
  -- Minimal `N`-normal subgroup over `Q₁` inside `T`.
  obtain ⟨Q2, hQ1Q2, hQ2T, hQ2norm, _⟩ := exists_minimal_normalOver hQ1T hTnorm
  have hQ2Q : Q2 ≤ Q := hQ2T.trans inf_le_left
  have hQ2Q1norm : Q2 ≤ Subgroup.normalizer (Q1 : Set G) := hQ2T.trans inf_le_right
  -- `Q₂ ⊴ N`, so `N`—and hence `D`, `K₁`—normalizes `Q₂`.
  have hN_normQ2 : M ⊓ Subgroup.normalizer (Q1 : Set G) ≤ Subgroup.normalizer (Q2 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQ2T.trans hTN)).mp hQ2norm
  exact ⟨Q2, hQ1Q2, hQ2Q, hDN.trans hN_normQ2, hK1N.trans hN_normQ2, hQ2Q1norm⟩

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Coprime lifting over a normal `D`-invariant subgroup** (`§14`-independent, reusable; the
practical non-abelian form of `N = ⁅N,D⁆·C_N(D)` instantiated at a *given* normal subgroup `M₀`
containing `⁅N,D⁆`).  If `D` normalizes `N`, `M₀ ≤ N` is normalized by both `N` and `D`,
`⁅N, D⁆ ≤ M₀`, and `(|D|, |N|) = 1` (with `D` or `N` solvable), then `N = M₀·C_N(D)`, i.e.
`N ≤ M₀ ⊔ (N ⊓ C_G(D))`.

Quotienting by the *normal* `M₀` sidesteps the (not-free) `⁅N,D⁆ ⊴ N`: since `⁅N,D⁆ ⊆ M₀`, `D` acts
trivially on `N/M₀`, so the quotient fixed points are `⊤`; the coprime fixed-point lifting
`fixedPointsOfMulAut_quotientMulAutHom_eq_map` (BG Proposition 1.5(d)) rewrites them as the
push-forward `C_N(D)·M₀/M₀`, whence `N = C_N(D)·M₀`.  The conjugation action of `D` on `↥N` is
`(normalizerMonoidHom N).comp (inclusion hDN)`, matching the `S06`/`S03h` bridges
(`actionCommutator_conj_map_subtype`, `fixedPointsOfMulAut_conj_map_subtype`).

In Theorem 15.2's step 3 part (ii) (mmd L4194): with `N = Q₁`, `M₀ = Q₀ = C_Q(D)`, an extra
`C_{Q₁}(D) ⊆ Q₀` forces `Q₁ ⊆ Q₀`, contradicting `Q₀ < Q₁`. -/
theorem le_sup_inf_centralizer_of_commutator_le [Finite G]
    {N M₀ D : Subgroup G}
    (hM₀N : M₀ ≤ N)
    (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hN_M₀ : N ≤ Subgroup.normalizer (M₀ : Set G))
    (hDM₀ : D ≤ Subgroup.normalizer (M₀ : Set G))
    (hcomm : ⁅N, D⁆ ≤ M₀)
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥N))
    (hSolv : Group.IsSolvable ↥D ∨ Group.IsSolvable ↥N) :
    N ≤ M₀ ⊔ (N ⊓ Subgroup.centralizer (D : Set G)) := by
  -- The conjugation action of `D` on `↥N` (`D ≤ N_G(N)`).
  set φ : ↥D →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom N).comp (Subgroup.inclusion hDN) with hφ
  -- `M₀.subgroupOf N` is normal in `↥N` and `D`-invariant.
  have hM₀N_normal : (M₀.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM₀N).mpr hN_M₀
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (M₀.subgroupOf N) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change (a : G) * (x : G) * (a : G)⁻¹ ∈ M₀
    exact (Subgroup.mem_normalizer_iff.mp (hDM₀ a.2) (x : G)).mp hx
  -- `actionCommutator φ ≤ M₀.subgroupOf N` (from `⁅N,D⁆ ⊆ M₀`).
  have hac_map : (OddOrder.Isaacs.Ch04.actionCommutator φ).map N.subtype = ⁅N, D⁆ :=
    OddOrder.BG.Ch1.S06.actionCommutator_conj_map_subtype hDN
  have hac_le : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ M₀.subgroupOf N := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have : (N.subtype y) ∈ (OddOrder.Isaacs.Ch04.actionCommutator φ).map N.subtype :=
      ⟨y, hy, rfl⟩
    rw [hac_map] at this
    exact hcomm this
  -- `D` acts trivially on `N/M₀`: the quotient fixed points are `⊤`.
  have htop : Subgroup.fixedPointsOfMulAut
      (quotientMulAutHom hMinv) = ⊤ := by
    have hbot : OddOrder.Isaacs.Ch04.actionCommutator
        (quotientMulAutHom hMinv) = ⊥ := by
      rw [OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map, Subgroup.map_eq_bot_iff,
        QuotientGroup.ker_mk']
      exact hac_le
    rw [Subgroup.eq_top_iff']
    intro g
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    exact (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hbot a g
  -- Proposition 1.5(d): quotient fixed points are the push-forward of `C_N(D)`.
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hSolv hMinv
  rw [htop] at hmap
  -- `C_N(D) ⊔ M₀ = ⊤` in `↥N`.
  have hsup : Subgroup.fixedPointsOfMulAut φ ⊔ M₀.subgroupOf N = ⊤ := by
    have hcme := Subgroup.comap_map_eq (f := QuotientGroup.mk' (M₀.subgroupOf N))
      (Subgroup.fixedPointsOfMulAut φ)
    rw [QuotientGroup.ker_mk', ← hmap, Subgroup.comap_top] at hcme
    exact hcme.symm
  -- Map back to `G`: `(C_G(D) ⊓ N) ⊔ M₀ = N`.
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map N.subtype =
      Subgroup.centralizer (D : Set G) ⊓ N :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hDN
  have hmapN := congrArg (Subgroup.map N.subtype) hsup
  rw [Subgroup.map_sup, hbridge, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM₀N,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapN
  refine le_of_eq ?_
  calc N = Subgroup.centralizer (D : Set G) ⊓ N ⊔ M₀ := hmapN.symm
    _ = M₀ ⊔ (N ⊓ Subgroup.centralizer (D : Set G)) := by rw [inf_comm, sup_comm]

/-- **General collapse** (Theorem 15.2 step 3(ii)): `⁅N,D⁆ ≤ M₀` and `N ⊓ C_G(D) ≤ M₀` give
`N ≤ M₀` (the lifting `le_sup_inf_centralizer_of_commutator_le` plus the centralizer cap).
Generalizes `le_of_commutator_le_centralizerCap` by taking the cap directly, so it also applies to
brick D's `(Q₁, Q₂)` step where `M₀ = Q₁ ≠ C_Q(D)`. -/
theorem le_of_commutator_le_of_inf_centralizer_le [Finite G] {N M₀ D : Subgroup G}
    (hM₀N : M₀ ≤ N) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hN_M₀ : N ≤ Subgroup.normalizer (M₀ : Set G))
    (hDM₀ : D ≤ Subgroup.normalizer (M₀ : Set G))
    (hcomm : ⁅N, D⁆ ≤ M₀) (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥N))
    (hSolv : Group.IsSolvable ↥D ∨ Group.IsSolvable ↥N)
    (hcap : N ⊓ Subgroup.centralizer (D : Set G) ≤ M₀) :
    N ≤ M₀ :=
  (le_sup_inf_centralizer_of_commutator_le hM₀N hDN hN_M₀ hDM₀ hcomm hcop hSolv).trans
    (sup_le le_rfl hcap)

/-- **Nilpotent ⟹ coprime normal `q`-part centralizes `q′`-part** (`§14`-independent, reusable): in
a nilpotent finite group, a normal `q`-subgroup `A` (`q` prime) and a `q′`-subgroup `B` satisfy
`⁅A, B⁆ = ⊥`.  `B` lies in the normal Hall `q′`-subgroup `O_{q′} = opiCoreInG {q}ᶜ ⊤` (nilpotency,
`piGroup_le_opiCoreInG_of_nilpotent`), which is normal of order coprime to the `q`-group `A`, so
`⁅A, B⁆ ≤ ⁅A, O_{q′}⁆ ≤ A ⊓ O_{q′} = ⊥`.

This is the kernel of Theorem 15.2 step 3(ii): the nilpotent quotient `DQ₁/Q₀` (from Theorem 3.7
on the regular `K`-action) has the `q′`-image of `D` centralizing the normal `q`-subgroup `Q₁/Q₀`,
i.e. `⁅Q₁, D⁆ ⊆ Q₀` after pulling back. -/
theorem commutator_eq_bot_of_isNilpotent_of_normal_isPGroup
    {𝓗 : Type*} [Group 𝓗] [Finite 𝓗] [Group.IsNilpotent 𝓗]
    {q : ℕ} [Fact q.Prime] {A B : Subgroup 𝓗} [A.Normal] (hA : IsPGroup q A)
    (hB : q ∉ (Nat.card ↥B).primeFactors) :
    ⁅A, B⁆ = ⊥ := by
  have : Group.IsNilpotent ↥(⊤ : Subgroup 𝓗) :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
  have hOnorm : (opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗)).Normal :=
    opiCoreInG_normal ({q}ᶜ : Set ℕ)
  -- `B ≤ O_{q′}` (a `q′`-subgroup of a nilpotent group).
  have hBO : B ≤ opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) := by
    refine piGroup_le_opiCoreInG_of_nilpotent (fun r hr => ?_) le_top
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hB hr
  -- `A ⊓ O_{q′} = ⊥` (`q`-group vs `q′`-group).
  have hAO : A ⊓ opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) = ⊥ := by
    apply Disjoint.eq_bot
    refine Subgroup.disjoint_of_coprime_natCard
      (coprime_of_forall_prime_not_dvd (fun r hr hrA hrO => ?_))
    have hrq : r = q := by
      have hπA : Subgroup.IsPiSubgroup ({q} : Set ℕ) A :=
        Subgroup.isPiSubgroup_of_isPGroup_of_mem hA rfl
      exact hπA r (Nat.mem_primeFactors.mpr ⟨hr, hrA, Nat.card_pos.ne'⟩)
    rw [hrq] at hr hrO
    exact (isPiSubgroup_opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) q
      (Nat.mem_primeFactors.mpr ⟨hr, hrO, Nat.card_pos.ne'⟩)) rfl
  rw [eq_bot_iff]
  have hmono : ⁅A, B⁆ ≤ ⁅A, opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗)⁆ :=
    Subgroup.commutator_mono le_rfl hBO
  have hinf : ⁅A, opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗)⁆ ≤
      A ⊓ opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗) :=
    Subgroup.commutator_le_inf A (opiCoreInG ({q}ᶜ : Set ℕ) (⊤ : Subgroup 𝓗))
  exact (hmono.trans hinf).trans hAO.le

/-- **B1 of Theorem 15.2 step 3(ii)** (`§14`-independent, reusable): if the quotient `N/Q₀'` is
nilpotent, `A₀ ⊴ N` is a `q`-group (`q` prime) and `B₀ ≤ N` is a `q′`-group, then `⁅A₀, B₀⁆ ≤ Q₀'`.
The images `Ā₀ = A₀·Q₀'/Q₀'` (normal `q`-group) and `B̄₀` (`q′`-group) of the nilpotent quotient
satisfy `⁅Ā₀, B̄₀⁆ = ⊥` (`commutator_eq_bot_of_isNilpotent_of_normal_isPGroup`); since
`⁅Ā₀, B̄₀⁆ = ⁅A₀, B₀⁆·Q₀'/Q₀'` (`map_commutator`), the commutator lands in `ker = Q₀'`.

For the regular-action contradiction (mmd L4194): with `N = ↥(D ⊔ Q₁)`, `Q₀' = Q₀.subgroupOf`,
`A₀ = Q₁.subgroupOf`, `B₀ = D.subgroupOf`, once `DQ₁/Q₀` is nilpotent (Theorem 3.7) this gives
`⁅Q₁, D⁆ ⊆ Q₀`, feeding `le_of_commutator_le_centralizerCap` for the contradiction. -/
theorem commutator_le_of_quotient_isNilpotent {N : Type*} [Group N] [Finite N]
    {q : ℕ} [Fact q.Prime] {Q0' A0 B0 : Subgroup N} [Q0'.Normal] [A0.Normal]
    (hNilp : Group.IsNilpotent (N ⧸ Q0'))
    (hA0 : IsPGroup q A0) (hB0 : q ∉ (Nat.card ↥B0).primeFactors) :
    ⁅A0, B0⁆ ≤ Q0' := by
  have := hNilp
  have : (A0.map (QuotientGroup.mk' Q0')).Normal :=
    ‹A0.Normal›.map _ (QuotientGroup.mk'_surjective Q0')
  have hAq : IsPGroup q (A0.map (QuotientGroup.mk' Q0')) := hA0.map _
  have hBq' : q ∉ (Nat.card ↥(B0.map (QuotientGroup.mk' Q0'))).primeFactors := fun hq =>
    hB0 (Nat.primeFactors_mono (Subgroup.card_map_dvd (H := B0) _) Nat.card_pos.ne' hq)
  have hbot : ⁅A0.map (QuotientGroup.mk' Q0'), B0.map (QuotientGroup.mk' Q0')⁆ = ⊥ :=
    commutator_eq_bot_of_isNilpotent_of_normal_isPGroup hAq hBq'
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

/-- **Brick B2 core of Theorem 15.2 step 3(ii)** (mmd L4194, regular-action ⟹ nilpotent step):
if `K₁` (prime order) acts regularly on `DQ₁/Q₀` — the preimage fixed-point-free condition `hFPF`
(`k` fixes `x` mod `Q₀` only when `x ∈ Q₀`) — then `↥(D ⊔ Q₁) / Q₀.subgroupOf _` is nilpotent.

Ambient `P = D ⊔ Q₁ ⊔ K₁` (so `Q₀ ⊴ P`), `Γ = ↥P / Q₀`; push `D ⊔ Q₁`, `K₁` into `Γ` via
`ψ, ρ = π ∘ inclusion`.  Theorem 3.7 on the images `N̄ = ψ.range`, `R̄ = ρ.range` gives
`IsNilpotent ↥N̄`; Noether's first isomorphism (`quotientKerEquivRange ψ`, kernel `Q₀.subgroupOf _`)
transfers it to the quotient.  Feeds `commutator_le_of_quotient_isNilpotent` (B1). -/
theorem isNilpotent_DQ1_quotient_of_regular [Finite G]
    {D Q1 K1 Q0 : Subgroup G} [(Q0.subgroupOf (D ⊔ Q1)).Normal]
    (hPsolv : Group.IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hdisj : Disjoint (D ⊔ Q1) K1)
    (hK1Q0disj : Disjoint K1 Q0)
    (hQ0lt : Q0 < D ⊔ Q1)
    (hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0) :
    Group.IsNilpotent (↥(D ⊔ Q1) ⧸ (Q0.subgroupOf (D ⊔ Q1))) := by
  have hDQ1P : D ⊔ Q1 ≤ D ⊔ Q1 ⊔ K1 := le_sup_left
  have hK1P : K1 ≤ D ⊔ Q1 ⊔ K1 := le_sup_right
  have hQ0P_normal : (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPQ0
  set π : ↥(D ⊔ Q1 ⊔ K1) →* ↥(D ⊔ Q1 ⊔ K1) ⧸ (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)) :=
    QuotientGroup.mk' _ with hπ
  set ψ : ↥(D ⊔ Q1) →* ↥(D ⊔ Q1 ⊔ K1) ⧸ (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)) :=
    π.comp (Subgroup.inclusion hDQ1P) with hψ
  set ρ : ↥K1 →* ↥(D ⊔ Q1 ⊔ K1) ⧸ (Q0.subgroupOf (D ⊔ Q1 ⊔ K1)) :=
    π.comp (Subgroup.inclusion hK1P) with hρ
  have := hPsolv
  -- Kernels of `ψ`, `ρ` and the "trivial image ⟺ lies in `Q₀`" criteria.
  have hkerψ : ψ.ker = Q0.subgroupOf (D ⊔ Q1) := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hkerρ : ρ.ker = Q0.subgroupOf K1 := by
    rw [hρ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hψ1 : ∀ b : ↥(D ⊔ Q1), ψ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerψ, Subgroup.mem_subgroupOf]
  have hρ1 : ∀ b : ↥K1, ρ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerρ, Subgroup.mem_subgroupOf]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, hkerρ, Subgroup.subgroupOf_eq_bot]
    exact hK1Q0disj.symm
  -- Quotient-equality criterion and the values of `ψ`, `ρ`.
  have hπeq : ∀ u v : ↥(D ⊔ Q1 ⊔ K1), π u = π v ↔ (u : G)⁻¹ * (v : G) ∈ Q0 := by
    intro u v
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hψval : ∀ b : ↥(D ⊔ Q1), ψ b = π (Subgroup.inclusion hDQ1P b) := fun b => rfl
  have hρval : ∀ c : ↥K1, ρ c = π (Subgroup.inclusion hK1P c) := fun c => rfl
  have : Group.IsSolvable ↥(ψ.range ⊔ ρ.range) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  -- `ψ.range` is normal in `Γ`: `P = D ⊔ Q₁ ⊔ K₁ ≤ N_G(D ⊔ Q₁)` (as `K₁` normalizes `D ⊔ Q₁`).
  have hψrange : ψ.range = ((D ⊔ Q1).subgroupOf (D ⊔ Q1 ⊔ K1)).map π := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hNPnormal : ((D ⊔ Q1).subgroupOf (D ⊔ Q1 ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hK1DQ1)
  have hψrange_normal : (ψ.range).Normal := by
    rw [hψrange]; exact hNPnormal.map π (QuotientGroup.mk'_surjective _)
  have hNilpN : Group.IsNilpotent ↥(ψ.range) := by
    refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      (N := ψ.range) (R := ρ.range) ?_ ?_ ?_ ?_ ?_ ?_
    · -- `ρ.range ≤ N(ψ.range) = ⊤` since `ψ.range ⊴ Γ`.
      exact le_top.trans_eq (Subgroup.normalizer_eq_top_iff.mpr hψrange_normal).symm
    · -- `Disjoint ψ.range ρ.range`: a common image lifts to `(D ⊔ Q₁) ⊓ K₁ = ⊥`.
      rw [Subgroup.disjoint_def]
      intro y hyψ hyρ
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hyψ
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hyρ
      have hbc : (b : G)⁻¹ * (c : G) ∈ Q0 :=
        (hπeq (Subgroup.inclusion hDQ1P b) (Subgroup.inclusion hK1P c)).mp
          (by rw [← hψval, ← hρval]; exact hc.symm)
      have hcDQ1 : (c : G) ∈ D ⊔ Q1 := by
        have hrw : (c : G) = (b : G) * ((b : G)⁻¹ * (c : G)) := by group
        rw [hrw]
        exact (D ⊔ Q1).mul_mem b.2 (hQ0lt.le hbc)
      have hmem : (c : G) ∈ (D ⊔ Q1) ⊓ K1 := ⟨hcDQ1, c.2⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
      rw [← hc, show c = 1 from Subtype.ext hmem, map_one]
    · -- `ψ.range ≠ ⊥`: the image of an `x ∈ (D ⊔ Q₁) ∖ Q₀` is nontrivial.
      obtain ⟨x, hxDQ1, hxQ0⟩ := SetLike.exists_of_lt hQ0lt
      intro hbot
      refine hxQ0 ((hψ1 ⟨x, hxDQ1⟩).mp ?_)
      have hmem : ψ ⟨x, hxDQ1⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    · -- `ρ.range ≠ ⊥`: `K₁` is nontrivial and meets `Q₀` trivially.
      obtain ⟨p, hp, hcard⟩ := hK1prime
      have : Nontrivial ↥K1 :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
      obtain ⟨k, hk1⟩ := exists_ne (1 : ↥K1)
      intro hbot
      refine hk1 (Subtype.ext ?_)
      have hρk : ρ k = 1 := by
        have hmem : ρ k ∈ ρ.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at hmem
      have hmem : (k : G) ∈ K1 ⊓ Q0 := ⟨k.2, (hρ1 k).mp hρk⟩
      rw [hK1Q0disj.eq_bot, Subgroup.mem_bot] at hmem
      exact hmem
    · -- `card ρ.range = card K₁ = p` (`ρ` injective).
      obtain ⟨p, hp, hcard⟩ := hK1prime
      exact ⟨p, hp,
        by rw [← hcard]; exact Nat.card_congr (MonoidHom.ofInjective hρinj).symm.toEquiv⟩
    · -- Fixed-point-free: a fixed nontrivial image contradicts `hFPF` (`k` fixes `x` mod `Q₀`).
      intro r hr hr1 n hn hn1 heq
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hn
      have hk1 : (a : G) ≠ 1 := fun h => hr1 (by
        rw [hρval, show Subgroup.inclusion hK1P a = 1 from Subtype.ext h, map_one])
      have hconj : ρ a * ψ b * (ρ a)⁻¹ = π (Subgroup.inclusion hK1P a *
          Subgroup.inclusion hDQ1P b * (Subgroup.inclusion hK1P a)⁻¹) := by
        rw [hρval, hψval, map_mul, map_mul, map_inv]
      rw [hconj, hψval b] at heq
      have hmem := (hπeq _ _).mp heq
      refine hn1 ((hψ1 b).mpr (hFPF (a : G) a.2 hk1 (b : G) b.2 ?_))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_rev,
        inv_inv, mul_assoc] using hmem
  have e : (↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1)) ≃* ↥(ψ.range) :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  exact Group.nilpotent_of_mulEquiv e.symm

/-- **Regular-action ⟹ quotient nilpotent, single-subgroup form** (`§14`-independent, reusable;
generalises `isNilpotent_DQ1_quotient_of_regular` from `N = D ⊔ Q₁` to an arbitrary `N`).  If a
prime-order subgroup `K₁` acts on `N/Q₀` (`Q₀ ⊴ N`, `Q₀ < N`, `K₁ ≤ N_G(N)`, `K₁ ⊓ N = ⊥`,
`K₁ ⊓ Q₀ = ⊥`) fixed-point-freely on preimages — `k·x⁻¹·k⁻¹·x ∈ Q₀ ⟹ x ∈ Q₀` for `1 ≠ k ∈ K₁`,
`x ∈ N` — then `↥N / Q₀.subgroupOf N` is nilpotent.

Ambient `P = N ⊔ K₁`, `Γ = ↥P / Q₀`; the images `N̄ = ψ.range`, `K̄₁ = ρ.range` form a Frobenius
group (Theorem 3.7), making `N̄` nilpotent, and Noether's first isomorphism transfers it to the
quotient.  Used in Theorem 15.2 step (c)(d) with `N = M_σ`, `Q₀ = Q`, to prove `M_σ/Q` nilpotent
("`K` acts regularly on `M_σ/Q`", since `C_{M_σ}(K) = K* ⊆ Q`). -/
theorem isNilpotent_quotient_of_regular_general [Finite G]
    {N K1 Q0 : Subgroup G} [(Q0.subgroupOf N).Normal]
    (hPsolv : Group.IsSolvable ↥(N ⊔ K1))
    (hPQ0 : N ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1N : K1 ≤ Subgroup.normalizer (N : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hdisj : Disjoint N K1)
    (hK1Q0disj : Disjoint K1 Q0)
    (hQ0lt : Q0 < N)
    (hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ N, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0) :
    Group.IsNilpotent (↥N ⧸ (Q0.subgroupOf N)) := by
  have hNP : N ≤ N ⊔ K1 := le_sup_left
  have hK1P : K1 ≤ N ⊔ K1 := le_sup_right
  have hQ0P_normal : (Q0.subgroupOf (N ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPQ0
  set π : ↥(N ⊔ K1) →* ↥(N ⊔ K1) ⧸ (Q0.subgroupOf (N ⊔ K1)) :=
    QuotientGroup.mk' _ with hπ
  set ψ : ↥N →* ↥(N ⊔ K1) ⧸ (Q0.subgroupOf (N ⊔ K1)) :=
    π.comp (Subgroup.inclusion hNP) with hψ
  set ρ : ↥K1 →* ↥(N ⊔ K1) ⧸ (Q0.subgroupOf (N ⊔ K1)) :=
    π.comp (Subgroup.inclusion hK1P) with hρ
  have := hPsolv
  have hkerψ : ψ.ker = Q0.subgroupOf N := by
    rw [hψ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hkerρ : ρ.ker = Q0.subgroupOf K1 := by
    rw [hρ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']; rfl
  have hψ1 : ∀ b : ↥N, ψ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerψ, Subgroup.mem_subgroupOf]
  have hρ1 : ∀ b : ↥K1, ρ b = 1 ↔ (b : G) ∈ Q0 := fun b => by
    rw [← MonoidHom.mem_ker, hkerρ, Subgroup.mem_subgroupOf]
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, hkerρ, Subgroup.subgroupOf_eq_bot]
    exact hK1Q0disj.symm
  have hπeq : ∀ u v : ↥(N ⊔ K1), π u = π v ↔ (u : G)⁻¹ * (v : G) ∈ Q0 := by
    intro u v
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hψval : ∀ b : ↥N, ψ b = π (Subgroup.inclusion hNP b) := fun b => rfl
  have hρval : ∀ c : ↥K1, ρ c = π (Subgroup.inclusion hK1P c) := fun c => rfl
  have : Group.IsSolvable ↥(ψ.range ⊔ ρ.range) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  have hψrange : ψ.range = (N.subgroupOf (N ⊔ K1)).map π := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hNPnormal : (N.subgroupOf (N ⊔ K1)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hK1N)
  have hψrange_normal : (ψ.range).Normal := by
    rw [hψrange]; exact hNPnormal.map π (QuotientGroup.mk'_surjective _)
  have hNilpN : Group.IsNilpotent ↥(ψ.range) := by
    refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
      (N := ψ.range) (R := ρ.range) ?_ ?_ ?_ ?_ ?_ ?_
    · exact le_top.trans_eq (Subgroup.normalizer_eq_top_iff.mpr hψrange_normal).symm
    · rw [Subgroup.disjoint_def]
      intro y hyψ hyρ
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hyψ
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hyρ
      have hbc : (b : G)⁻¹ * (c : G) ∈ Q0 :=
        (hπeq (Subgroup.inclusion hNP b) (Subgroup.inclusion hK1P c)).mp
          (by rw [← hψval, ← hρval]; exact hc.symm)
      have hcN : (c : G) ∈ N := by
        have hrw : (c : G) = (b : G) * ((b : G)⁻¹ * (c : G)) := by group
        rw [hrw]
        exact N.mul_mem b.2 (hQ0lt.le hbc)
      have hmem : (c : G) ∈ N ⊓ K1 := ⟨hcN, c.2⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
      rw [← hc, show c = 1 from Subtype.ext hmem, map_one]
    · obtain ⟨x, hxN, hxQ0⟩ := SetLike.exists_of_lt hQ0lt
      intro hbot
      refine hxQ0 ((hψ1 ⟨x, hxN⟩).mp ?_)
      have hmem : ψ ⟨x, hxN⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    · obtain ⟨p, hp, hcard⟩ := hK1prime
      have : Nontrivial ↥K1 :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hp.one_lt)
      obtain ⟨k, hk1⟩ := exists_ne (1 : ↥K1)
      intro hbot
      refine hk1 (Subtype.ext ?_)
      have hρk : ρ k = 1 := by
        have hmem : ρ k ∈ ρ.range := MonoidHom.mem_range.mpr ⟨k, rfl⟩
        rwa [hbot, Subgroup.mem_bot] at hmem
      have hmem : (k : G) ∈ K1 ⊓ Q0 := ⟨k.2, (hρ1 k).mp hρk⟩
      rw [hK1Q0disj.eq_bot, Subgroup.mem_bot] at hmem
      exact hmem
    · obtain ⟨p, hp, hcard⟩ := hK1prime
      exact ⟨p, hp,
        by rw [← hcard]; exact Nat.card_congr (MonoidHom.ofInjective hρinj).symm.toEquiv⟩
    · intro r hr hr1 n hn hn1 heq
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hr
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hn
      have hk1 : (a : G) ≠ 1 := fun h => hr1 (by
        rw [hρval, show Subgroup.inclusion hK1P a = 1 from Subtype.ext h, map_one])
      have hconj : ρ a * ψ b * (ρ a)⁻¹ = π (Subgroup.inclusion hK1P a *
          Subgroup.inclusion hNP b * (Subgroup.inclusion hK1P a)⁻¹) := by
        rw [hρval, hψval, map_mul, map_mul, map_inv]
      rw [hconj, hψval b] at heq
      have hmem := (hπeq _ _).mp heq
      refine hn1 ((hψ1 b).mpr (hFPF (a : G) a.2 hk1 (b : G) b.2 ?_))
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, mul_inv_rev,
        inv_inv, mul_assoc] using hmem
  have e : (↥N ⧸ Q0.subgroupOf N) ≃* ↥(ψ.range) :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  exact Group.nilpotent_of_mulEquiv e.symm

/-- **Brick A "core" of Theorem 15.2 step 3(ii)** (mmd L4194): under the `K*`-condition, the fixed
points of `k` (with prime-manner action `C_{M_σ}(k) = K*`) inside `D ⊔ Q₁` land in `Q₀`.
`C(k) ⊓ (D ⊔ Q₁) ⊆ C(k) ⊓ M_σ = K*`; since `K* ≤ Q` and `Q ⊓ (D ⊔ Q₁) = Q₁` (Dedekind, `D ⊓ Q = ⊥`,
`C(k) ⊓ (D ⊔ Q₁) ⊆ C(k) ⊓ M_σ = K*`; since `K* ≤ Q` and `Q ⊓ (D ⊔ Q₁) = Q₁` (Dedekind, `D ⊓ Q = ⊥`,
`D ≤ N_G(Q₁)`), the fixed points lie in `K* ⊓ Q₁`, which is `≤ Q₀` (if `K* ≤ Q₀`) or trivial (if
`K* ⊄ Q₁`, as `|K*|` is prime).  Supplies `C_{DQ₁}(k) ⊆ Q₀` to brick A's Prop 1.5(d) lift. -/
theorem centralizer_inf_DQ1_le_Q0 [Finite G]
    {Mσ D Q Q1 Q0 Kstar : Subgroup G} {k : G}
    (hKstar : Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hDQ1Mσ : D ⊔ Q1 ≤ Mσ)
    (hQ1Q : Q1 ≤ Q) (hDQ : Disjoint D Q)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hcond : Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1)
    (hprime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q) :
    Subgroup.centralizer ({k} : Set G) ⊓ (D ⊔ Q1) ≤ Q0 := by
  have hDed : (Q1 ⊔ D) ⊓ Q = Q1 :=
    Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot hQ1Q hDQ.eq_bot hDnormQ1
  have hsub : Subgroup.centralizer ({k} : Set G) ⊓ (D ⊔ Q1) ≤ Kstar ⊓ Q1 := by
    intro y hy
    obtain ⟨hyC, hyDQ1⟩ := Subgroup.mem_inf.mp hy
    have hyKstar : y ∈ Kstar := hKstar ▸ Subgroup.mem_inf.mpr ⟨hyC, hDQ1Mσ hyDQ1⟩
    refine Subgroup.mem_inf.mpr ⟨hyKstar, ?_⟩
    have hmem : y ∈ (Q1 ⊔ D) ⊓ Q := ⟨by rw [sup_comm]; exact hyDQ1, hKstarQ hyKstar⟩
    rwa [hDed] at hmem
  refine hsub.trans ?_
  rcases hcond with hc | hc
  · exact inf_le_left.trans hc
  · have hbot : Kstar ⊓ Q1 = ⊥ := by
      obtain ⟨q, hq, hcard⟩ := hprime
      have hdvd : Nat.card ↥(Kstar ⊓ Q1) ∣ Nat.card ↥Kstar := Subgroup.card_dvd_of_le inf_le_left
      rw [hcard] at hdvd
      rcases (Nat.dvd_prime hq).mp hdvd with h1 | hqq
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd ((Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [hcard]; exact hqq.symm.le)) ▸ inf_le_right) hc
    rw [hbot]; exact bot_le

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Brick A "lift" of Theorem 15.2 step 3(ii)** (Prop 1.5(d)): from `C(k) ⊓ (D ⊔ Q₁) ≤ Q₀`
(brick A-core) and the coprime conjugation action of `⟨k⟩` on `D ⊔ Q₁`, `k` acts fixed-point-freely
on `(D ⊔ Q₁)/Q₀` — i.e. `k·x⁻¹·k⁻¹·x ∈ Q₀ ⟹ x ∈ Q₀`.  The quotient fixed points push forward from
`C_{D⊔Q₁}(⟨k⟩) = C(k) ⊓ (D ⊔ Q₁) ⊆ Q₀` (`fixedPointsOfMulAut_quotientMulAutHom_eq_map`), so they
are trivial; a `k`-fixed `x̄` is `⟨k⟩`-fixed (generator argument), hence `1`. -/
theorem fpf_of_centralizer_inf_le [Finite G]
    {D Q1 Q0 : Subgroup G} {k : G}
    (hk_norm : k ∈ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hk_normQ0 : k ∈ Subgroup.normalizer (Q0 : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hsolv : Group.IsSolvable ↥(Subgroup.zpowers k) ∨ Group.IsSolvable ↥(D ⊔ Q1))
    (hCk : Subgroup.centralizer ({k} : Set G) ⊓ (D ⊔ Q1) ≤ Q0) :
    ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0 := by
  have hkz : Subgroup.zpowers k ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hk_norm
  have hkzQ0 : Subgroup.zpowers k ≤ Subgroup.normalizer (Q0 : Set G) :=
    Subgroup.zpowers_le.mpr hk_normQ0
  set φ : ↥(Subgroup.zpowers k) →* MulAut ↥(D ⊔ Q1) :=
    (Subgroup.normalizerMonoidHom (D ⊔ Q1)).comp (Subgroup.inclusion hkz) with hφ
  have hQ0_normal : (Q0.subgroupOf (D ⊔ Q1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0DQ1).mpr hDQ1Q0
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf (D ⊔ Q1)) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change (a : G) * (x : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hkzQ0 a.2) (x : G)).mp hx
  -- Prop 1.5(d) + brick A-core: the quotient fixed points are trivial.
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map (D ⊔ Q1).subtype =
      Subgroup.centralizer ((Subgroup.zpowers k : Subgroup G) : Set G) ⊓ (D ⊔ Q1) :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hkz
  have hfp_le : Subgroup.fixedPointsOfMulAut φ ≤ Q0.subgroupOf (D ⊔ Q1) := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hym : ((D ⊔ Q1).subtype y) ∈ (Subgroup.fixedPointsOfMulAut φ).map (D ⊔ Q1).subtype :=
      ⟨y, hy, rfl⟩
    rw [hbridge] at hym
    obtain ⟨hcent, _⟩ := Subgroup.mem_inf.mp hym
    exact hCk (Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers k)) hcent, y.2⟩)
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hsolv hMinv
  have hfpbot : Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) = ⊥ := by
    rw [hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hfp_le
  intro x hx hpre
  -- A `MulAut` fixing `y` fixes `y` under all its `zpowers` (stabilizer is a subgroup).
  have hpow : ∀ (f : MulAut (↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1)))
      (y : ↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1)), f y = y → ∀ i : ℤ, (f ^ i) y = y :=
    fun f y hf i => MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (MulAut (↥(D ⊔ Q1) ⧸ Q0.subgroupOf (D ⊔ Q1))) y).zpow_mem
        (MulAction.mem_stabilizer_iff.mpr hf) i)
  -- The generator `k` fixes `x̄` (the premise `k·x⁻¹·k⁻¹·x ∈ Q₀`).
  have hkbar : quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩
      (QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩) =
      QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩ := by
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change (k * x * k⁻¹)⁻¹ * x ∈ Q0
    have heq : (k * x * k⁻¹)⁻¹ * x = k * x⁻¹ * k⁻¹ * x := by group
    rw [heq]; exact hpre
  -- Hence `x̄` is fixed by all of `⟨k⟩`, so lies in the trivial fixed-point set.
  have hxbar : QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩ ∈
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) := by
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have ha : a = ⟨k, Subgroup.mem_zpowers k⟩ ^ i := Subtype.ext (by rw [← hi, Subgroup.coe_zpow])
    rw [ha, map_zpow]
    exact hpow (quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩)
      (QuotientGroup.mk' (Q0.subgroupOf (D ⊔ Q1)) ⟨x, hx⟩) hkbar i
  rw [hfpbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hxbar
  exact hxbar

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Single-subgroup form of `fpf_of_centralizer_inf_le`** (`§14`-independent, reusable): the
Prop 1.5(d) fixed-point lift for an arbitrary subgroup `A` (not just `D ⊔ Q₁`).  If `k` normalizes
`A` and the normal `Q₀ ≤ A`, acts coprimely (`(|⟨k⟩|, |A|) = 1`, one-sided solvable), and
`C_G(k) ⊓ A ≤ Q₀`, then `k` acts fixed-point-freely on `A/Q₀`: `k·x⁻¹·k⁻¹·x ∈ Q₀ ⟹ x ∈ Q₀` for
`x ∈ A`.  Used in Theorem 15.2 step (c)(d) with `A = M_σ`, `Q₀ = Q` (the regular `K`-action on
`M_σ/Q` from `C_{M_σ}(k) = K* ⊆ Q`). -/
theorem fpf_of_centralizer_inf_le_general [Finite G]
    {A Q0 : Subgroup G} {k : G}
    (hk_norm : k ∈ Subgroup.normalizer (A : Set G))
    (hk_normQ0 : k ∈ Subgroup.normalizer (Q0 : Set G))
    (hAQ0 : A ≤ Subgroup.normalizer (Q0 : Set G))
    (hQ0A : Q0 ≤ A)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥A))
    (hsolv : Group.IsSolvable ↥(Subgroup.zpowers k) ∨ Group.IsSolvable ↥A)
    (hCk : Subgroup.centralizer ({k} : Set G) ⊓ A ≤ Q0) :
    ∀ x ∈ A, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0 := by
  have hkz : Subgroup.zpowers k ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.zpowers_le.mpr hk_norm
  have hkzQ0 : Subgroup.zpowers k ≤ Subgroup.normalizer (Q0 : Set G) :=
    Subgroup.zpowers_le.mpr hk_normQ0
  set φ : ↥(Subgroup.zpowers k) →* MulAut ↥A :=
    (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hkz) with hφ
  have hQ0_normal : (Q0.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0A).mpr hAQ0
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf A) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    change (a : G) * (x : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hkzQ0 a.2) (x : G)).mp hx
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map A.subtype =
      Subgroup.centralizer ((Subgroup.zpowers k : Subgroup G) : Set G) ⊓ A :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hkz
  have hfp_le : Subgroup.fixedPointsOfMulAut φ ≤ Q0.subgroupOf A := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hym : (A.subtype y) ∈ (Subgroup.fixedPointsOfMulAut φ).map A.subtype := ⟨y, hy, rfl⟩
    rw [hbridge] at hym
    obtain ⟨hcent, _⟩ := Subgroup.mem_inf.mp hym
    exact hCk (Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers k)) hcent, y.2⟩)
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hsolv hMinv
  have hfpbot : Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) = ⊥ := by
    rw [hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hfp_le
  intro x hx hpre
  have hpow : ∀ (f : MulAut (↥A ⧸ Q0.subgroupOf A)) (y : ↥A ⧸ Q0.subgroupOf A),
      f y = y → ∀ i : ℤ, (f ^ i) y = y :=
    fun f y hf i => MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (MulAut (↥A ⧸ Q0.subgroupOf A)) y).zpow_mem
        (MulAction.mem_stabilizer_iff.mpr hf) i)
  have hkbar : quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩
      (QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩) =
      QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩ := by
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change (k * x * k⁻¹)⁻¹ * x ∈ Q0
    have heq : (k * x * k⁻¹)⁻¹ * x = k * x⁻¹ * k⁻¹ * x := by group
    rw [heq]; exact hpre
  have hxbar : QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩ ∈
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) := by
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have ha : a = ⟨k, Subgroup.mem_zpowers k⟩ ^ i := Subtype.ext (by rw [← hi, Subgroup.coe_zpow])
    rw [ha, map_zpow]
    exact hpow (quotientMulAutHom hMinv ⟨k, Subgroup.mem_zpowers k⟩)
      (QuotientGroup.mk' (Q0.subgroupOf A) ⟨x, hx⟩) hkbar i
  rw [hfpbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hxbar
  exact hxbar

/-- **Brick A assembled** (Theorem 15.2 step 3(ii)): the `K*`-condition gives the regular/FPF
condition `hFPF` for every `k ∈ K₁^#`, by composing brick A-core (`centralizer_inf_DQ1_le_Q0`,
the `C(k)⊓(D⊔Q₁) ⊆ Q₀` step) with brick A-lift (`fpf_of_centralizer_inf_le`, the Prop 1.5(d)
fixed-point lift).  Per-`k` normalizer/coprimality data is drawn from the `K₁`-level hypotheses.

This is general over `(Q₀, Q₁)` (it does *not* require `Q₀ = C_Q(D)`), so it serves both the
`(Q₀, Q₁)` application and brick D's re-application with `(Q₁, Q₂)`. -/
theorem hFPF_of_kstar_condition [Finite G]
    {Mσ D Q Q1 Q0 Kstar K1 : Subgroup G}
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hDQ1Mσ : D ⊔ Q1 ≤ Mσ)
    (hQ1Q : Q1 ≤ Q) (hDQ : Disjoint D Q)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hcond : Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1)
    (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hK1Q0 : K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1)
    (hcop : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hsolv : Group.IsSolvable ↥(D ⊔ Q1)) :
    ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0 := by
  intro k hk hk1
  have hCk := centralizer_inf_DQ1_le_Q0 (hprime_manner k hk hk1) hKstarQ hDQ1Mσ hQ1Q hDQ hDnormQ1
    hcond hKstar_prime
  exact fpf_of_centralizer_inf_le (hK1DQ1 hk) (hK1Q0 hk) hDQ1Q0 hQ0DQ1 (hcop k hk)
    (Or.inr hsolv) hCk

/-- **Part-(ii) contradiction core** (Theorem 15.2 step 3(ii)): from the regular condition `hFPF`,
the chain `B2-core → B1` gives `⁅Q₁, D⁆ ⊆ Q₀`.  `isNilpotent_DQ1_quotient_of_regular` makes
`(D ⊔ Q₁)/Q₀` nilpotent; `commutator_le_of_quotient_isNilpotent` (normal `q`-subgroup `Q₁`,
`q′`-subgroup `D`) gives `⁅Q₁, D⁆ ≤ Q₀` inside `↥(D ⊔ Q₁)`, pushed back to `G` via the subtype
(`map_commutator` + `subgroupOf_map_subtype`).  Composed with `hFPF_of_kstar_condition` and a
collapse, this yields the `K*`-condition contradiction. -/
theorem commutator_le_Q0_of_fpf [Finite G]
    {D Q1 K1 Q0 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf (D ⊔ Q1)).Normal] [(Q1.subgroupOf (D ⊔ Q1)).Normal]
    (hPsolv : Group.IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hdisj : Disjoint (D ⊔ Q1) K1) (hK1Q0disj : Disjoint K1 Q0)
    (hQ0lt : Q0 < D ⊔ Q1)
    (hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)))
    (hDq' : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors)
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1)
    (hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ D ⊔ Q1, k * x⁻¹ * k⁻¹ * x ∈ Q0 → x ∈ Q0) :
    ⁅Q1, D⁆ ≤ Q0 := by
  have hNilp := isNilpotent_DQ1_quotient_of_regular hPsolv hPQ0 hK1DQ1 hK1prime hdisj hK1Q0disj
    hQ0lt hFPF
  have hB1 := commutator_le_of_quotient_isNilpotent (q := q) hNilp hQ1q hDq'
  have hmap := Subgroup.map_mono (f := (D ⊔ Q1).subtype) hB1
  simp only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (le_sup_right : Q1 ≤ D ⊔ Q1), inf_eq_left.mpr (le_sup_left : D ≤ D ⊔ Q1),
    inf_eq_left.mpr hQ0DQ1] at hmap
  exact hmap

/-- **Part-(ii) regular-action contradiction engine** (Theorem 15.2 step 3(ii), mmd L4194): the
`K*`-condition `Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1` is contradictory with the chief chain `Q0 < Q1 ≤ Q` and
the type-`P` structural data.  Composes the three landed bricks:
`hFPF_of_kstar_condition` (the regular `K₁`-action `hFPF` from the prime-manner centralizer
`C_{M_σ}(k) = K*`), `commutator_le_Q0_of_fpf` (`B2-core → B1`: `⁅Q₁, D⁆ ≤ Q₀`) and the collapse
`le_of_commutator_le_of_inf_centralizer_le` (`Q₁ ≤ Q₀`), against `Q₀ < Q₁`.

Invoked twice in Theorem 15.2.  With `(Q₀, Q₁) = (C_Q(D), minimal normal over Q₀)` it refutes the
`K*`-condition, forcing `K* ⊄ Q₀ ∧ K* ⊆ Q₁`.  For brick D, with `(Q₁, Q₂)` (a chief factor over the
already-established `Q₁`), the left disjunct `K* ⊆ Q₁` holds, so the engine fires and forces
`Q₁ = Q`. -/
theorem false_of_kstar_condition_of_lt [Finite G]
    {Mσ D Q Q1 Q0 Kstar K1 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf (D ⊔ Q1)).Normal] [(Q1.subgroupOf (D ⊔ Q1)).Normal]
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hDQ1Mσ : D ⊔ Q1 ≤ Mσ) (hQ1Q : Q1 ≤ Q)
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1) (hQ0lt : Q0 < Q1)
    (hDQ : Disjoint D Q) (hdisj : Disjoint (D ⊔ Q1) K1) (hK1Q0disj : Disjoint K1 Q0)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)))
    (hDq' : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors)
    (hcopZ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hcopDQ1 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q1))
    (hsolvDQ1 : Group.IsSolvable ↥(D ⊔ Q1)) (hPsolv : Group.IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hcond : Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1)
    (hcap : Q1 ⊓ Subgroup.centralizer (D : Set G) ≤ Q0) :
    False := by
  -- Regular `K₁`-action on `(D ⊔ Q₁)/Q₀` from the `K*`-condition (brick A).
  have hFPF := hFPF_of_kstar_condition hprime_manner hKstarQ hDQ1Mσ hQ1Q hDQ hDnormQ1 hcond
    hKstar_prime hK1DQ1 (le_sup_right.trans hPQ0) hDQ1Q0 hQ0DQ1 hcopZ hsolvDQ1
  -- `⁅Q₁, D⁆ ≤ Q₀` (brick B: B2-core → transfer → B1).
  have hcomm := commutator_le_Q0_of_fpf (q := q) hPsolv hPQ0 hK1DQ1 hK1prime hdisj hK1Q0disj
    (hQ0lt.trans_le le_sup_right) hQ1q hDq' hQ0DQ1 hFPF
  -- `Q₁ ≤ Q₀` (collapse), contradicting `Q₀ < Q₁`.
  have := hsolvDQ1
  have hsolvQ1 : Group.IsSolvable ↥Q1 :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
        (le_sup_right : Q1 ≤ D ⊔ Q1))
  have hle := le_of_commutator_le_of_inf_centralizer_le hQ0lt.le hDnormQ1
    (le_sup_right.trans hDQ1Q0) (le_sup_left.trans hDQ1Q0) hcomm hcopDQ1 (Or.inr hsolvQ1) hcap
  exact absurd (lt_of_lt_of_le hQ0lt hle) (lt_irrefl Q0)

/-- **Step 1 of Theorem 15.2 part (ii)** (mmd L4194): the `K*`-condition is *false*, hence
`K* ⊆ Q₁` and `K* ⊄ Q₀`.  Direct contrapositive of `false_of_kstar_condition_of_lt`: were either
disjunct of `Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1` to hold, the regular `K₁`-action would collapse `Q₁ ≤ Q₀`,
against `Q₀ < Q₁`.  Supplies the `Kstar ≤ Q₁` premise that brick D feeds back into the engine at the
next chief factor `(Q₁, Q₂)`. -/
theorem kstar_le_Q1_of_inputs [Finite G]
    {Mσ D Q Q1 Q0 Kstar K1 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf (D ⊔ Q1)).Normal] [(Q1.subgroupOf (D ⊔ Q1)).Normal]
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hDQ1Mσ : D ⊔ Q1 ≤ Mσ) (hQ1Q : Q1 ≤ Q)
    (hQ0DQ1 : Q0 ≤ D ⊔ Q1) (hQ0lt : Q0 < Q1)
    (hDQ : Disjoint D Q) (hdisj : Disjoint (D ⊔ Q1) K1) (hK1Q0disj : Disjoint K1 Q0)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G))
    (hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)))
    (hDq' : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors)
    (hcopZ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)))
    (hcopDQ1 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q1))
    (hsolvDQ1 : Group.IsSolvable ↥(D ⊔ Q1)) (hPsolv : Group.IsSolvable ↥(D ⊔ Q1 ⊔ K1))
    (hcap : Q1 ⊓ Subgroup.centralizer (D : Set G) ≤ Q0) :
    ¬ Kstar ≤ Q0 ∧ Kstar ≤ Q1 := by
  have hkey : ¬ (Kstar ≤ Q0 ∨ ¬ Kstar ≤ Q1) := fun hcond =>
    false_of_kstar_condition_of_lt hprime_manner hKstarQ hKstar_prime hDQ1Mσ hQ1Q hQ0DQ1 hQ0lt
      hDQ hdisj hK1Q0disj hDnormQ1 hK1DQ1 hDQ1Q0 hPQ0 hK1prime hQ1q hDq' hcopZ hcopDQ1 hsolvDQ1
      hPsolv hcond hcap
  rw [not_or, not_not] at hkey
  exact hkey

/-- **Brick D of Theorem 15.2 part (ii)** (mmd L4194): once step 1 has established `K* ⊆ Q₁`, the
chief factor `Q₁` is in fact all of `Q`.  Were `Q₁ < Q`, `exists_chiefFactor_over_normalized` builds
the next chief factor `Q₂/Q₁` (with `Q₁ < Q₂ ≤ Q`, normalized by `D` and `K₁`); the regular-action
engine `false_of_kstar_condition_of_lt` then fires at `(Q₁, Q₂)` — its `K*`-condition holds via the
*left* disjunct `K* ⊆ Q₁` — giving `Q₂ ≤ Q₁`, against `Q₁ < Q₂`.  Hence `Q₁ = Q`.

The `(Q₁, Q₂)`-level engine hypotheses are mechanically derived from the global structural data:
order/coprimality facts descend along `Q₂ ≤ Q` (monotonicity of `Disjoint`, `Nat.Coprime`,
`IsPGroup`, `card_dvd_of_le`); normalization comes from `Q₂`'s construction; the centralizer cap
`Q₂ ⊓ C(D) ≤ Q₁` factors through `Q ⊓ C(D) ≤ Q₁`. -/
theorem Q1_eq_Q_of_inputs [Finite G]
    {M Mσ D Q Q1 Kstar K1 : Subgroup G} {q : ℕ} [Fact q.Prime] [Group.IsNilpotent ↥Q]
    (hprime_manner : ∀ k ∈ K1, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar)
    (hKstarQ : Kstar ≤ Q) (hKstar_prime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥Kstar = q)
    (hDQMσ : D ⊔ Q ≤ Mσ) (hDQ : Disjoint D Q)
    (hDQK1disj : Disjoint (D ⊔ Q) K1) (hK1Qdisj : Disjoint K1 Q)
    (hK1normD : K1 ≤ Subgroup.normalizer (D : Set G))
    (hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p)
    (hQ_pg : IsPGroup q Q) (hD_q' : q ∉ (Nat.card ↥D).primeFactors)
    (hcopZ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q)))
    (hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q)) (hsolv : Group.IsSolvable ↥(D ⊔ Q ⊔ K1))
    (hcap : Q ⊓ Subgroup.centralizer (D : Set G) ≤ Q1)
    (hQM : Q ≤ M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hDM : D ≤ M) (hK1M : K1 ≤ M)
    (hQ1Q : Q1 ≤ Q) (hKstarQ1 : Kstar ≤ Q1)
    (hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G))
    (hK1normQ1 : K1 ≤ Subgroup.normalizer (Q1 : Set G)) :
    Q1 = Q := by
  by_contra hne
  have hQ1ltQ : Q1 < Q := lt_of_le_of_ne hQ1Q hne
  obtain ⟨Q2, hQ1Q2, hQ2Q, hDnormQ2, hK1normQ2, hQ2normQ1⟩ :=
    exists_chiefFactor_over_normalized hQ1ltQ hQM hMnormQ (le_inf hDM hDnormQ1)
      (le_inf hK1M hK1normQ1)
  -- (Q₁, Q₂)-level engine hypotheses, descended from the global data.
  have hDQ2Mσ : D ⊔ Q2 ≤ Mσ := (sup_le_sup_left hQ2Q D).trans hDQMσ
  have hQ1DQ2 : Q1 ≤ D ⊔ Q2 := hQ1Q2.le.trans le_sup_right
  have hdisj2 : Disjoint (D ⊔ Q2) K1 := hDQK1disj.mono_left (sup_le_sup_left hQ2Q D)
  have hK1Q1disj : Disjoint K1 Q1 := hK1Qdisj.mono_right hQ1Q
  have hK1DQ2 : K1 ≤ Subgroup.normalizer ((D ⊔ Q2 : Subgroup G) : Set G) :=
    le_normalizer_sup hK1normD hK1normQ2
  have hDQ2normQ1 : D ⊔ Q2 ≤ Subgroup.normalizer (Q1 : Set G) := sup_le hDnormQ1 hQ2normQ1
  have hPnormQ1 : D ⊔ Q2 ⊔ K1 ≤ Subgroup.normalizer (Q1 : Set G) := sup_le hDQ2normQ1 hK1normQ1
  have hcardD : Nat.card ↥(D.subgroupOf (D ⊔ Q2)) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : D ≤ D ⊔ Q2)).toEquiv
  have hDq'2 : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q2))).primeFactors := by rw [hcardD]; exact hD_q'
  have hQ2_pg : IsPGroup q (Q2.subgroupOf (D ⊔ Q2)) := (hQ_pg.to_le hQ2Q).comap_subtype
  have hcopZ2 : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q2)) :=
    fun k hk => (hcopZ k hk).coprime_dvd_right (Subgroup.card_dvd_of_le (sup_le_sup_left hQ2Q D))
  have hcopDQ2 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q2) :=
    hcopDQ.coprime_dvd_right (Subgroup.card_dvd_of_le hQ2Q)
  have := hsolv
  have hsolv2 : Group.IsSolvable ↥(D ⊔ Q2) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      ((sup_le_sup_left hQ2Q D).trans (le_sup_left : D ⊔ Q ≤ D ⊔ Q ⊔ K1)))
  have hPsolv2 : Group.IsSolvable ↥(D ⊔ Q2 ⊔ K1) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (sup_le_sup_right (sup_le_sup_left hQ2Q D) K1))
  have hcap2 : Q2 ⊓ Subgroup.centralizer (D : Set G) ≤ Q1 := (inf_le_inf_right _ hQ2Q).trans hcap
  have : (Q1.subgroupOf (D ⊔ Q2)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ1DQ2).mpr hDQ2normQ1
  have : (Q2.subgroupOf (D ⊔ Q2)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hDnormQ2 Subgroup.le_normalizer)
  exact false_of_kstar_condition_of_lt hprime_manner hKstarQ hKstar_prime hDQ2Mσ hQ2Q hQ1DQ2
    hQ1Q2 hDQ hdisj2 hK1Q1disj hDnormQ2 hK1DQ2 hDQ2normQ1 hPnormQ1 hK1prime hQ2_pg hDq'2
    hcopZ2 hcopDQ2 hsolv2 hPsolv2 (Or.inl hKstarQ1) hcap2

/-- **BG Theorem 15.2 step 3, the chief-factor construction `Q₀ = C_Q(D) ⊴ M`** (mmd L4194).
Given the type-`P₁` data with the `K`-invariant complement `D` of `Q = O_q(M)` in `M_σ`
(`exists_kInvariant_qComplement`), this assembles the minimal chief factor: `Q₀ = C_Q(D)` is
proper in `Q` (`M_σ` not nilpotent), and the minimal normal subgroup `Q₁/Q₀` of `N_M(Q₀)/Q₀`
inside `Q` is shown to equal `Q` (`Q₁_eq_Q_of_inputs`), giving:

* **`M ≤ N_G(Q₀)`** (conjuncts (e)/13-14): `Q = Q₁ ≤ N_G(Q₀)` (the chief factor lives in `N_M(Q₀)`)
  and `K, D ≤ N_G(Q₀)` (`Q₀` is `KD`-invariant), so `M = M_σ K = (Q ⊔ D) ⊔ K ≤ N_G(Q₀)`;
* **`¬ K* ≤ Q₀`** (`kstar_le_Q1_of_inputs`, the regular-action dichotomy);
* **`Q₀ < Q`** (`inf_centralizer_ne_self_of_sup_not_nilpotent`);
* the **lattice-minimality** of `Q` over `Q₀` among `M`-normal subgroups (feeds the elementary
  abelian chief-factor `Q̄ = Q/Q₀` and the chief-factor engine).

The `§14`-gated inputs are folded into the type-`P₁` hypotheses (`hP1`, `hKstar`); `hMσnotnil`
(`M_σ` not nilpotent) is the Theorem 15.2 hypothesis `M_F ≠ M_σ`, `hDq'` (`q ∤ |D|`) the Sylow
fact from `q_not_dvd_index_of_msigma_quotient_isNilpotent`. -/
theorem chiefFactor_Q0_normal_minimal_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q D : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (_hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKne : K ≠ ⊥) (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)))
    (hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M))
    (hDq' : q ∉ (Nat.card ↥D).primeFactors)
    (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M) (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hQDdisj : Disjoint Q D)
    (hcomplD : Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
      (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hDnil : Group.IsNilpotent ↥D) (_hDne : D ≠ ⊥) :
    M ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
      ¬ Kstar ≤ (Q ⊓ Subgroup.centralizer (D : Set G)) ∧
      (Q ⊓ Subgroup.centralizer (D : Set G)) < Q ∧
      (∀ H : Subgroup G, (Q ⊓ Subgroup.centralizer (D : Set G)) < H → H ≤ Q →
        (H.subgroupOf M).Normal → Q ≤ H) := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  set Q0 : Subgroup G := Q ⊓ Subgroup.centralizer (D : Set G) with hQ0def
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have : Group.IsSolvable ↥Mσ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMσM)
  have hQpg : IsPGroup q ↥Q := by rw [hQ]; exact isPGroup_opiCoreInG_singleton M
  have hQnil : Group.IsNilpotent ↥Q := hQpg.isNilpotent
  have hDM : D ≤ M := hDMσ.trans hMσM
  have hQM : Q ≤ M := hQMσ.trans hMσM
  -- `Q ⊔ D = M_σ` (complement), so `M_σ` not nilpotent gives `Q₀ = C_Q(D) ⊊ Q`.
  have hQDsup : Q ⊔ D = Mσ := by
    have : (Q ⊔ D).subgroupOf Mσ = ⊤ := by
      rw [Subgroup.subgroupOf_sup hQMσ hDMσ]; exact hcomplD.sup_eq_top
    exact le_antisymm (sup_le hQMσ hDMσ) (Subgroup.subgroupOf_eq_top.mp this)
  have hQDnotnil : ¬ Group.IsNilpotent ↥(Q ⊔ D) := by rw [hQDsup]; exact hMσnotnil
  have hQ0ltQ : Q0 < Q :=
    lt_of_le_of_ne inf_le_left (inf_centralizer_ne_self_of_sup_not_nilpotent hQDnotnil)
  have hQ0le : Q0 ≤ Q := hQ0ltQ.le
  -- `Q₀ = C_Q(D)` is `KD`-invariant: `K, D ≤ N_G(Q₀)`.
  have hKNQ : K ≤ Subgroup.normalizer (Q : Set G) := hKM.trans hMnormQ
  have hDNQ : D ≤ Subgroup.normalizer (Q : Set G) := hDM.trans hMnormQ
  have hKDNQ0 : K ⊔ D ≤ Subgroup.normalizer (Q0 : Set G) :=
    sup_le_normalizer_centralizer_inf hKNQ hDNQ hKnormD
  have hKNQ0 : K ≤ Subgroup.normalizer (Q0 : Set G) := le_sup_left.trans hKDNQ0
  have hDNQ0 : D ≤ Subgroup.normalizer (Q0 : Set G) := le_sup_right.trans hKDNQ0
  -- a prime-order subgroup `K₁ ≤ K` and the prime-manner action.
  have hprime := actsPrimeManner_of_typeP hG hM hP1.1 hKM hK hKstar
  have hKcard1 : Nat.card ↥K ≠ 1 := fun hc => hKne (Subgroup.card_eq_one.mp hc)
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hKcard1
  have : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hr_dvd
  set K1 : Subgroup G := Subgroup.zpowers (c : G) with hK1
  have hcK : (c : G) ∈ K := c.2
  have hK1K : K1 ≤ K := by rw [hK1]; exact Subgroup.zpowers_le.mpr hcK
  have hK1M : K1 ≤ M := hK1K.trans hKM
  have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
  have hcardK1 : Nat.card ↥K1 = r := by rw [hK1, Nat.card_zpowers, hord_coe]
  have hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p := ⟨r, hr_prime, hcardK1⟩
  have hK1normD : K1 ≤ Subgroup.normalizer (D : Set G) := hK1K.trans hKnormD
  have hK1NQ0 : K1 ≤ Subgroup.normalizer (Q0 : Set G) := hK1K.trans hKNQ0
  -- the prime-manner action restricted to `K₁`.
  have hprimeK1 : ∀ k ∈ K1, k ≠ 1 →
      Subgroup.centralizer ({k} : Set G) ⊓ Mσ = Kstar := fun k hk => hprime k (hK1K hk)
  have hKstar_prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥Kstar = p :=
    ⟨Nat.card ↥Kstar, kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar, rfl⟩
  -- `q ∤ |D|`, hence `Coprime |D| |Q|` (`Q` a `q`-group).
  have hqD : ¬ q ∣ Nat.card ↥D := fun hdvd =>
    hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hqD).symm
  -- coprimality of cyclic `⟨k⟩ ≤ K` with `|M_σ|`, restricted along `D ⊔ Q ≤ M_σ`.
  have hcopKMσ : ∀ k ∈ K, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k))
      (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := fun k hk =>
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hk))
  -- set up the ambient `N = M ⊓ N_G(Q₀)` and the nontrivial chain top `T = N_Q(Q₀)`.
  set N : Subgroup G := M ⊓ Subgroup.normalizer (Q0 : Set G) with hNdef
  have hQ0T : Q0 < Q ⊓ Subgroup.normalizer (Q0 : Set G) :=
    lt_inf_normalizer_of_lt_of_isNilpotent hQ0ltQ
  have hTN : Q ⊓ Subgroup.normalizer (Q0 : Set G) ≤ N := inf_le_inf hQM le_rfl
  have hNnormT : N ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.normalizer (Q0 : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf (inf_le_left.trans hMnormQ) (inf_le_right.trans Subgroup.le_normalizer)
  have hTnorm : ((Q ⊓ Subgroup.normalizer (Q0 : Set G)).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr hNnormT
  obtain ⟨Q1, hQ0Q1, hQ1T, hQ1normalN, hQ1min⟩ := exists_minimal_normalOver hQ0T hTnorm
  have hQ1Q : Q1 ≤ Q := hQ1T.trans inf_le_left
  have hQ1NQ0 : Q1 ≤ Subgroup.normalizer (Q0 : Set G) := hQ1T.trans inf_le_right
  -- `D, K₁ ≤ N` and `N ≤ N_G(Q₁)`.
  have hDN : D ≤ N := le_inf hDM hDNQ0
  have hK1N : K1 ≤ N := le_inf hK1M hK1NQ0
  have hNnormQ1 : N ≤ Subgroup.normalizer (Q1 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hQ1T.trans hTN)).mp hQ1normalN
  have hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G) := hDN.trans hNnormQ1
  have hK1normQ1 : K1 ≤ Subgroup.normalizer (Q1 : Set G) := hK1N.trans hNnormQ1
  -- structural facts shared by `kstar_le_Q1_of_inputs` and `Q1_eq_Q_of_inputs`.
  have hDQ : Disjoint D Q := hQDdisj.symm
  have hDQMσ : D ⊔ Q ≤ Mσ := sup_le hDMσ hQMσ
  have hDQ1Mσ : D ⊔ Q1 ≤ Mσ := sup_le hDMσ (hQ1Q.trans hQMσ)
  have hQ0DQ1 : Q0 ≤ D ⊔ Q1 := hQ0Q1.le.trans le_sup_right
  have hdisjQ1 : Disjoint (D ⊔ Q1) K1 :=
    (hKMσdisj.symm.mono_left hDQ1Mσ).mono_right hK1K
  have hK1Q0disj : Disjoint K1 Q0 := (hKMσdisj.mono_left hK1K).mono_right (hQ0le.trans hQMσ)
  have hK1DQ1 : K1 ≤ Subgroup.normalizer ((D ⊔ Q1 : Subgroup G) : Set G) :=
    le_normalizer_sup hK1normD hK1normQ1
  have hDQ1Q0 : D ⊔ Q1 ≤ Subgroup.normalizer (Q0 : Set G) := sup_le hDNQ0 hQ1NQ0
  have hPQ0 : D ⊔ Q1 ⊔ K1 ≤ Subgroup.normalizer (Q0 : Set G) := sup_le hDQ1Q0 hK1NQ0
  have hQ1q : IsPGroup q (Q1.subgroupOf (D ⊔ Q1)) := (hQpg.to_le hQ1Q).comap_subtype
  have hcardD1 : Nat.card ↥(D.subgroupOf (D ⊔ Q1)) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : D ≤ D ⊔ Q1)).toEquiv
  have hDq'1 : q ∉ (Nat.card ↥(D.subgroupOf (D ⊔ Q1))).primeFactors := by rw [hcardD1]; exact hDq'
  have hcopZ1 : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q1)) :=
    fun k hk => (hcopKMσ k (hK1K hk)).coprime_dvd_right
      (Subgroup.card_dvd_of_le (le_trans hDQ1Mσ le_rfl))
  have hcopDQ1 : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q1) :=
    hcopDQ.coprime_dvd_right (Subgroup.card_dvd_of_le hQ1Q)
  have hsolvDQ1 : Group.IsSolvable ↥(D ⊔ Q1) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hDQ1Mσ.trans hMσM))
  have hPsolvQ1 : Group.IsSolvable ↥(D ⊔ Q1 ⊔ K1) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (sup_le (hDQ1Mσ.trans hMσM) hK1M))
  have hcapQ1 : Q1 ⊓ Subgroup.centralizer (D : Set G) ≤ Q0 := by
    rw [hQ0def]; exact inf_le_inf_right _ hQ1Q
  have hQ0normDQ1 : (Q0.subgroupOf (D ⊔ Q1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0DQ1).mpr hDQ1Q0
  have hQ1normDQ1 : (Q1.subgroupOf (D ⊔ Q1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right)).mpr
      (sup_le hDnormQ1 Subgroup.le_normalizer)
  -- `¬ K* ≤ Q₀` and `K* ≤ Q₁`.
  obtain ⟨hKstarNotQ0, hKstarQ1⟩ := kstar_le_Q1_of_inputs hprimeK1 hKstarQ hKstar_prime hDQ1Mσ hQ1Q
    hQ0DQ1 hQ0Q1 hDQ hdisjQ1 hK1Q0disj hDnormQ1 hK1DQ1 hDQ1Q0 hPQ0 hK1prime hQ1q hDq'1
    hcopZ1 hcopDQ1 hsolvDQ1 hPsolvQ1 hcapQ1
  -- `Q₁ = Q` (brick D).
  have hcopZQ : ∀ k ∈ K1, Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥(D ⊔ Q)) :=
    fun k hk => (hcopKMσ k (hK1K hk)).coprime_dvd_right
      (Subgroup.card_dvd_of_le (hDQMσ.trans le_rfl))
  have hsolvDQK1 : Group.IsSolvable ↥(D ⊔ Q ⊔ K1) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (sup_le (hDQMσ.trans hMσM) hK1M))
  have hcapQ : Q ⊓ Subgroup.centralizer (D : Set G) ≤ Q1 := by rw [← hQ0def]; exact hQ0Q1.le
  have hQ1eqQ : Q1 = Q :=
    Q1_eq_Q_of_inputs hprimeK1 hKstarQ hKstar_prime hDQMσ hDQ
      ((hKMσdisj.symm.mono_left hDQMσ).mono_right hK1K) (hKMσdisj.mono_left hK1K |>.mono_right hQMσ)
      hK1normD hK1prime hQpg hDq' hcopZQ hcopDQ hsolvDQK1 hcapQ hQM hMnormQ hDM hK1M hQ1Q hKstarQ1
      hDnormQ1 hK1normQ1
  -- `Q ≤ N_G(Q₀)` (from `Q = Q₁`), hence `M = M_σ K ≤ N_G(Q₀)`.
  have hQNQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQ1eqQ ▸ hQ1NQ0
  have hMσNQ0 : Mσ ≤ Subgroup.normalizer (Q0 : Set G) := by
    rw [← hQDsup]; exact sup_le hQNQ0 hDNQ0
  -- `M = M_σ ⊔ K` (type-`P₁` complement, `M_σ = M'`).
  have hMσderived : Mσ = derivedInG M := typeP1_msigma_eq_derivedInG hG hM hP1 hKM hK hKstar
  obtain ⟨hcomplK, _, _⟩ := S14.typeP_duality hG hM hP1.1 hKM hK hKstar
  have hMeq : Mσ ⊔ K = M := by
    have hsup : (Mσ.subgroupOf M) ⊔ (K.subgroupOf M) = ⊤ := by
      rw [hMσderived]; exact hcomplK.sup_eq_top
    have h := congrArg (Subgroup.map M.subtype) hsup
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hMσM, inf_eq_left.mpr hKM, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  have hMNQ0 : M ≤ Subgroup.normalizer (Q0 : Set G) := by
    rw [← hMeq]; exact sup_le hMσNQ0 hKNQ0
  -- minimality of `Q` over `Q₀` among `M`-normal subgroups (from `Q₁ = Q`, `N = M`).
  have hNeqM : N = M := by rw [hNdef]; exact inf_eq_left.mpr hMNQ0
  refine ⟨hMNQ0, hKstarNotQ0, hQ0ltQ, ?_⟩
  intro H hH1 hH2 hH3
  have hH3' : (H.subgroupOf N).Normal := by rw [hNeqM]; exact hH3
  have := hQ1min H hH1 (hQ1eqQ ▸ hH2) hH3'
  rwa [hQ1eqQ] at this

/-- **BG Theorem 15.2 step 3, the elementary abelian chief factor `Q̄ = Q/Q₀`** (mmd L4194-4196,
"`Q̄` is a minimal normal subgroup of `M/Q₀` and is elementary abelian of order `q^p`").  Given the
lattice-minimality of `Q` over `Q₀` among `M`-normal subgroups (output of
`chiefFactor_Q0_normal_minimal_of_inputs`) with `Q ⊴ M`, `Q₀ ⊴ M`, `Q₀ < Q` and `Q` a `q`-group,
the chief factor `Q/Q₀` is elementary abelian (and nontrivial).

Proof: the image `E = Q/Q₀` of `Q` in the solvable quotient `M/Q₀` is a *minimal normal* subgroup —
the lattice-minimality `hmin` transfers along the correspondence `comap (mk' Q₀)` — so by Isaacs
Theorem 3.11 (`minimal_normal_isElementaryAbelian_of_isSolvable`) it is elementary abelian for some
prime; the first isomorphism theorem (`quotientKerEquivRange` of `↥Q → M/Q₀`) identifies `E` with
`↥Q ⧸ Q₀.subgroupOf Q`, and as a quotient of the `q`-group `Q` that prime is `q`.

Discharges the `hEA`/`hNT` hypotheses of `chiefFactor_card_and_commutator_of_inputs`. -/
theorem isElementaryAbelian_chiefFactor_of_minimalNormal [Finite G]
    {M Q Q0 : Subgroup G} {q : ℕ} [Fact q.Prime] [Group.IsSolvable ↥M] [(Q0.subgroupOf Q).Normal]
    (hQ0Q : Q0 < Q) (hQM : Q ≤ M) (hQpg : IsPGroup q ↥Q)
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMnormQ0 : M ≤ Subgroup.normalizer (Q0 : Set G))
    (hmin : ∀ H : Subgroup G, Q0 < H → H ≤ Q → (H.subgroupOf M).Normal → Q ≤ H) :
    OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q) ∧
      Nontrivial (↥Q ⧸ Q0.subgroupOf Q) := by
  classical
  have hQ0M : Q0 ≤ M := hQ0Q.le.trans hQM
  have hQ0nM : (Q0.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0M).mpr hMnormQ0
  have hQnM : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
  -- `Nontrivial Q̄` (`Q₀ < Q`).
  obtain ⟨x0, hx0Q, hx0Q0⟩ := (SetLike.lt_iff_le_and_exists.mp hQ0Q).2
  have hNT : Nontrivial (↥Q ⧸ Q0.subgroupOf Q) := by
    refine ⟨QuotientGroup.mk ⟨x0, hx0Q⟩, 1, ?_⟩
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hx0Q0
  -- ambient quotient `M/Q₀` and the chief-factor image `E = (Q ↾ M)·Q₀ / Q₀`.
  set N0 : Subgroup ↥M := Q0.subgroupOf M with hN0def
  set E : Subgroup (↥M ⧸ N0) := (Q.subgroupOf M).map (QuotientGroup.mk' N0) with hEdef
  have hN0QM : N0 ≤ Q.subgroupOf M := by rw [hN0def]; exact Subgroup.comap_mono hQ0Q.le
  -- `E` is minimal normal in the solvable `M/Q₀`.
  have hEmin : OddOrder.Isaacs.Ch02.IsMinimalNormal E := by
    refine ⟨hQnM.map (QuotientGroup.mk' N0) (QuotientGroup.mk'_surjective N0), ?_, ?_⟩
    · -- `E ≠ ⊥`.
      intro hEbot
      rw [hEdef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hEbot
      have hQle : Q ≤ Q0 := by
        intro x hxQ
        have hxM : x ∈ M := hQM hxQ
        have hmem : (⟨x, hxM⟩ : ↥M) ∈ Q0.subgroupOf M :=
          hEbot (Subgroup.mem_subgroupOf.mpr hxQ)
        exact Subgroup.mem_subgroupOf.mp hmem
      exact hQ0Q.ne (le_antisymm hQ0Q.le hQle)
    · -- minimality via the correspondence.
      intro N' hN'norm hN'E
      have := hN'norm
      set N'' : Subgroup ↥M := Subgroup.comap (QuotientGroup.mk' N0) N' with hN''def
      have hN0N'' : N0 ≤ N'' := QuotientGroup.le_comap_mk' N0 N'
      have hN''QM : N'' ≤ Q.subgroupOf M := by
        have hsub : N'' ≤ Subgroup.comap (QuotientGroup.mk' N0) E := Subgroup.comap_mono hN'E
        rwa [hEdef, QuotientGroup.comap_map_mk', sup_eq_right.mpr hN0QM] at hsub
      set H : Subgroup G := N''.map M.subtype with hHdef
      have hHsubM : H.subgroupOf M = N'' :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective N''
      have hQ0H : Q0 ≤ H := by
        rw [hHdef]
        intro y hy
        have hyM : y ∈ M := hQ0M hy
        exact ⟨⟨y, hyM⟩, hN0N'' (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
      have hHQ : H ≤ Q := by
        rw [hHdef]
        rintro _ ⟨w, hwN'', rfl⟩
        exact (Subgroup.mem_subgroupOf.mp (hN''QM hwN''))
      have hHnorm : (H.subgroupOf M).Normal := by rw [hHsubM]; infer_instance
      have hN'eq : N' = N''.map (QuotientGroup.mk' N0) := by
        rw [hN''def, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N0)]
      rcases eq_or_lt_of_le hQ0H with hHeq | hHlt
      · -- `H = Q₀`, so `N'' = N0`, `N' = ⊥`.
        left
        have hHQ0 : H = Q0 := hHeq.symm
        have hN''N0 : N'' = N0 := by rw [← hHsubM, hHQ0]
        rw [hN'eq, hN''N0, Subgroup.map_eq_bot_iff]
        exact (QuotientGroup.ker_mk' N0).ge
      · -- `Q₀ < H`, so `hmin` forces `H = Q`, `N'' = Q.subgroupOf M`, `N' = E`.
        right
        have hHeqQ : H = Q := le_antisymm hHQ (hmin H hHlt hHQ hHnorm)
        have hN''QMeq : N'' = Q.subgroupOf M := by rw [← hHsubM, hHeqQ]
        rw [hN'eq, hN''QMeq, hEdef]
  -- elementary abelian for some prime `p`.
  obtain ⟨p, hp_prime, hEAp⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hEmin
  -- the first isomorphism `↥Q ⧸ Q₀ ≃* ↥E`.
  set f : ↥Q →* (↥M ⧸ N0) := (QuotientGroup.mk' N0).comp (Subgroup.inclusion hQM) with hfdef
  have hfker : f.ker = Q0.subgroupOf Q := by
    ext z
    rw [hfdef, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN0def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hfrange : f.range = E := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.inclusion_range, hEdef]
  let e : (↥Q ⧸ Q0.subgroupOf Q) ≃* ↥E :=
    (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange))
  -- transport elementary abelian to `Q̄`, and identify the prime as `q`.
  have hEAp' : OddOrder.GroupTheory.IsElementaryAbelian p (↥Q ⧸ Q0.subgroupOf Q) :=
    OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv e.symm hEAp
  have hpgp : IsPGroup p (↥Q ⧸ Q0.subgroupOf Q) := hEAp'.isPGroup
  have hpgq : IsPGroup q (↥Q ⧸ Q0.subgroupOf Q) := hQpg.to_quotient (Q0.subgroupOf Q)
  have : Finite (↥Q ⧸ Q0.subgroupOf Q) := inferInstance
  have : Fact p.Prime := ⟨hp_prime⟩
  have hpq : p = q := by
    obtain ⟨a, ha⟩ := hpgp.exists_card_eq
    obtain ⟨b, hb⟩ := hpgq.exists_card_eq
    have hqdvd : q ∣ Nat.card (↥Q ⧸ Q0.subgroupOf Q) := by
      rw [hb]
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0, pow_zero] at hb
        exact absurd hb (Finite.one_lt_card_iff_nontrivial.mpr hNT).ne'
      · exact dvd_pow_self q h0.ne'
    rw [ha] at hqdvd
    exact ((Nat.prime_dvd_prime_iff_eq Fact.out hp_prime).mp
      ((Fact.out : q.Prime).dvd_of_dvd_pow hqdvd)).symm
  exact ⟨hpq ▸ hEAp', hNT⟩

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
open scoped commutatorElement in
/-- **Theorem 15.2 step 4, the fixed-point-free fact `C_{Q̄}(D) = 1`** (Proposition 1.5(d), mmd
L4196).  With `Q₀ = C_Q(D)` and `D` acting coprimely on `Q` (`D ≤ N_G(Q)`, `Q, D ≤ N_G(Q₀)`), `D`
acts fixed-point-freely on `Q̄ = Q/Q₀`: any `x ∈ Q` whose class is centralized by `D`
(`⁅d, x⁆ ∈ Q₀` for every `d ∈ D`) already lies in `Q₀`.

This is the `C_M(U) = 1` hypothesis (`hCU`) of BG Theorem 3.10
(`prime_card_complement_of_frobenius_conj`) in the `M = Q̄`, `U = D̄` instantiation that yields
`|K|` prime (Theorem 15.2 conjunct (f)): a class of `Q̄` centralizing `D̄` lifts to a representative
`x` with `⁅d, x⁆ ∈ Q₀` for all `d ∈ D`, forced by this lemma into `Q₀`, i.e. the class is trivial.

Proof (mirrors `fpf_of_centralizer_inf_le`, but the fixed-point source is the *definitional*
`C_Q(D) = Q₀` rather than a separate centralizer bound, and no generator lift is needed since the
whole group `D` acts): the `D`-fixed points of `Q/Q₀` push forward from `C_{↥Q}(D) = Q₀`
(`fixedPointsOfMulAut_quotientMulAutHom_eq_map`, Proposition 1.5(d)), hence are trivial.  The
bracket conversion `⁅a, x⁻¹⁆ = x⁻¹ ⁅a, x⁆⁻¹ x` uses `x ∈ Q ≤ N_G(Q₀)`. -/
theorem mem_centralizer_of_centralizes_quotient [Finite G]
    {Q D Q0 : Subgroup G} (hQ0 : Q0 = Q ⊓ Subgroup.centralizer (D : Set G))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hDQ0 : D ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q))
    (hSolv : Group.IsSolvable ↥D ∨ Group.IsSolvable ↥Q)
    {x : G} (hxQ : x ∈ Q) (hfix : ∀ d ∈ D, ⁅d, x⁆ ∈ Q0) :
    x ∈ Q0 := by
  have hQ0Q : Q0 ≤ Q := by rw [hQ0]; exact inf_le_left
  set φ : ↥D →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hDQ) with hφ
  have hQ0_normal : (Q0.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0Q).mpr hQQ0
  -- `Q₀.subgroupOf Q` is `D`-invariant.
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf Q) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    change (a : G) * (y : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hDQ0 a.2) (y : G)).mp hy
  -- Proposition 1.5(d): the quotient fixed points push forward from `C_{↥Q}(D) = Q₀`, hence `⊥`.
  have hbridge : (Subgroup.fixedPointsOfMulAut φ).map Q.subtype =
      Subgroup.centralizer (D : Set G) ⊓ Q :=
    OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hDQ
  have hfp_le : Subgroup.fixedPointsOfMulAut φ ≤ Q0.subgroupOf Q := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hym : (Q.subtype y) ∈ (Subgroup.fixedPointsOfMulAut φ).map Q.subtype := ⟨y, hy, rfl⟩
    rw [hbridge] at hym
    obtain ⟨hcent, _⟩ := Subgroup.mem_inf.mp hym
    rw [hQ0]; exact Subgroup.mem_inf.mpr ⟨y.2, hcent⟩
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hSolv hMinv
  have hfpbot : Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) = ⊥ := by
    rw [hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hfp_le
  -- The class of `x` is `D`-fixed (each `a ∈ D` fixes it, by the premise), hence trivial.
  have hxN : x ∈ Subgroup.normalizer (Q0 : Set G) := hQQ0 hxQ
  have hxbar : QuotientGroup.mk' (Q0.subgroupOf Q) ⟨x, hxQ⟩ ∈
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv) := by
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change ((a : G) * x * (a : G)⁻¹)⁻¹ * x ∈ Q0
    have h1 : ⁅(a : G), x⁆ ∈ Q0 := hfix a a.2
    have h2 : ((a : G) * x * (a : G)⁻¹)⁻¹ * x = x⁻¹ * ⁅(a : G), x⁆⁻¹ * (x⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN)
      (⁅(a : G), x⁆⁻¹)).mp (Q0.inv_mem h1)
  rw [hfpbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hxbar
  exact hxbar

end OddOrder.BG.Ch4.S15


