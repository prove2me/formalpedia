-- Prove2me | Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
-- name    : KrohnRhodes_Foundations_KrasnerKaloujnine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:53:58.876393+00:00
-- url     : https://prove2.me/theorems/1e6b33db-1ca0-4eca-a5b7-b9c50a97be1f
-- title:
--   Krasner Kaloujnine
-- statement:
--   Definitions and structural lemmas for Krasner Kaloujnine, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Foundations/KrasnerKaloujnine.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Mathlib
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.RegularWreathProduct
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedDecidableInType false
namespace KrohnRhodes
universe u
variable {G : Type u} [Group G]
section Krasner
variable (N : Subgroup G) [N.Normal]
noncomputable def section_ : G ⧸ N → G :=
  Function.surjInv (QuotientGroup.mk'_surjective N)
theorem section_apply (q : G ⧸ N) :
    QuotientGroup.mk' N (section_ N q) = q :=
  Function.surjInv_eq _ _
noncomputable def krasnerLeftRaw (g : G) (q : G ⧸ N) : G :=
  (section_ N q)⁻¹ * g * section_ N ((QuotientGroup.mk' N g)⁻¹ * q)
theorem krasnerLeftRaw_mem (g : G) (q : G ⧸ N) :
    krasnerLeftRaw N g q ∈ N := by
  -- N = ker(QuotientGroup.mk' N), so it suffices to show mk' applied to the element is 1.
  -- Compute: π(s(q)⁻¹ * g * s(π(g)⁻¹ * q)) = q⁻¹ * π(g) * (π(g)⁻¹ * q) = 1.
  have hone : QuotientGroup.mk' N (krasnerLeftRaw N g q) = 1 := by
    unfold krasnerLeftRaw
    rw [map_mul, map_mul, map_inv, section_apply, section_apply]
    group
  exact (QuotientGroup.eq_one_iff _).mp hone
noncomputable def krasnerLeft (g : G) (q : G ⧸ N) : N :=
  ⟨krasnerLeftRaw N g q, krasnerLeftRaw_mem N g q⟩
noncomputable def krasnerKaloujnineFun (g : G) : N ≀ᵣ (G ⧸ N) :=
  ⟨krasnerLeft N g, QuotientGroup.mk' N g⟩
theorem krasnerKaloujnine_map_mul (g₁ g₂ : G) :
    krasnerKaloujnineFun N (g₁ * g₂) =
      krasnerKaloujnineFun N g₁ * krasnerKaloujnineFun N g₂ := by
  -- Right component:  π(g₁ g₂) = π(g₁) * π(g₂).
  -- Left component (pointwise at q):
  --   n_{g₁ g₂}(q) = s(q)⁻¹ * g₁ * g₂ * s(π(g₁)⁻¹ π(g₂)⁻¹ q)
  -- = s(q)⁻¹ * g₁ * s(π(g₁)⁻¹ q) * s(π(g₁)⁻¹ q)⁻¹ * g₂ * s(π(g₂)⁻¹ π(g₁)⁻¹ q)
  -- = n_{g₁}(q) * n_{g₂}(π(g₁)⁻¹ q)
  -- Mathlib's regular wreath multiplication: (a * b).left = a.left * (λx, b.left (a.right⁻¹ * x))
  refine RegularWreathProduct.ext ?_ ?_
  · -- left component
    funext q
    apply Subtype.ext
    change krasnerLeftRaw N (g₁ * g₂) q
        = krasnerLeftRaw N g₁ q * krasnerLeftRaw N g₂ ((QuotientGroup.mk' N g₁)⁻¹ * q)
    -- Manual rewriting to avoid timeouts.
    change (section_ N q)⁻¹ * (g₁ * g₂) *
        section_ N ((QuotientGroup.mk' N (g₁ * g₂))⁻¹ * q) =
      ((section_ N q)⁻¹ * g₁ * section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q)) *
      ((section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q))⁻¹ * g₂ *
        section_ N ((QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q)))
    have hquot :
        (QuotientGroup.mk' N (g₁ * g₂))⁻¹ * q =
        (QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q) := by
      rw [map_mul, mul_inv_rev]
      group
    rw [hquot]
    -- Now both sides have the same `section_` arguments.
    set a : G := section_ N q
    set b : G := section_ N ((QuotientGroup.mk' N g₁)⁻¹ * q)
    set c : G := section_ N ((QuotientGroup.mk' N g₂)⁻¹ * ((QuotientGroup.mk' N g₁)⁻¹ * q))
    change a⁻¹ * (g₁ * g₂) * c = (a⁻¹ * g₁ * b) * (b⁻¹ * g₂ * c)
    group
  · -- right component
    change QuotientGroup.mk' N (g₁ * g₂) = QuotientGroup.mk' N g₁ * QuotientGroup.mk' N g₂
    exact map_mul (QuotientGroup.mk' N) g₁ g₂
theorem krasnerKaloujnine_map_one :
    krasnerKaloujnineFun N 1 = 1 := by
  refine RegularWreathProduct.ext ?_ ?_
  · funext q
    apply Subtype.ext
    change (section_ N q)⁻¹ * 1 * section_ N ((QuotientGroup.mk' N 1)⁻¹ * q) = 1
    rw [map_one, inv_one, one_mul, mul_one]
    rw [inv_mul_cancel]
  · change QuotientGroup.mk' N 1 = 1
    exact map_one _
noncomputable def krasnerKaloujnine_hom :
    G →* (N ≀ᵣ (G ⧸ N)) where
  toFun := krasnerKaloujnineFun N
  map_one' := krasnerKaloujnine_map_one N
  map_mul' := krasnerKaloujnine_map_mul N
end Krasner
end KrohnRhodes


