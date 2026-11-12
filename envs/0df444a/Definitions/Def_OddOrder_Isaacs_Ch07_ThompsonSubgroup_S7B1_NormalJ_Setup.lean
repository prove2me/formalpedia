-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
-- name    : OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B1_NormalJ_Setup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:48:36.535204+00:00
-- url     : https://prove2.me/theorems/c5c44a5d-3cdf-44ba-83db-aacdd99810e0
-- title:
--   Isaacs FGT Ch. 7: the normal-$J$ theorem (Thm 7.6), Steps 1-5 and the $V$-setup
-- statement:
--   Isaacs, *Finite Group Theory*, Chapter 7, Theorem 7.6, pp. 209-214: the infrastructure layer of the eight-step normal-$J$ argument, covering the Hall–Higman 3.21 corollaries (Step 1), the core $L=O_{p',p}(G)$ and its bridges (Steps 2-4), and the subgroup $V=\Omega_1(Z(O_p(G)))$.
--
--   Main definitions: `opPpPrimeCore` ($L=O_{p',p}(G)$ as a preimage along the quotient map), `zCenterOpCoreSubgroup` ($Z(O_p(G))$ viewed in $G$), `omega1ZCenterOpCore` ($V=\Omega_1(Z(O_p(G)))$) and its `CommGroup` structure, with normality instances.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B1_NormalJ_Setup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `L = O_{p',p}(G)` defined as the preimage of `L̅ = O_{p'}(G̅)` along
the quotient map `G →* G/(O_p(G))`.  This is the second term of the lower
`p`-radical series of `G` (with `O_p` first, `O_{p'}` second). -/
noncomputable def opPpPrimeCore (G : Type*) [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] : Subgroup G :=
  (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)).comap
    (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))

/-- `L = O_{p',p}(G)` is `G`-normal (comap of normal subgroup is normal). -/
instance opPpPrimeCore_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] : (opPpPrimeCore G p).Normal := by
  unfold opPpPrimeCore
  infer_instance

/-- **Isaacs Thm 7.6 Step 4** (mmd L3858): `Z(O_p(G))` is `G`-normal (and `G`-characteristic).

The `Subgroup.center` of a characteristic subgroup is itself characteristic in the
ambient group.  In particular `Subgroup.center` of `O_p(G)`, viewed as the image
of `Subgroup.center (opCore p G)` in `G`, is `G`-normal. -/
private theorem center_opCore_map_normal {G : Type*} [Group G] {p : ℕ} :
    ((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨⟨z, hz_L⟩, hz_center, rfl⟩ g
  -- g * z * g⁻¹ ∈ opCore p G  (since opCore is normal)
  have hLnorm : (OddOrder.Isaacs.Ch01.opCore p G).Normal := inferInstance
  have hgz : g * z * g⁻¹ ∈ OddOrder.Isaacs.Ch01.opCore p G :=
    hLnorm.conj_mem z hz_L g
  refine ⟨⟨g * z * g⁻¹, hgz⟩, ?_, rfl⟩
  -- Show ⟨g*z*g⁻¹, _⟩ ∈ Subgroup.center (opCore p G).
  change (⟨g * z * g⁻¹, hgz⟩ : OddOrder.Isaacs.Ch01.opCore p G) ∈
    Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  rintro ⟨h, hh_L⟩
  -- ⟨h, hh_L⟩ * ⟨g*z*g⁻¹, hgz⟩ = ⟨g*z*g⁻¹, hgz⟩ * ⟨h, hh_L⟩,
  -- i.e., h * (g*z*g⁻¹) = (g*z*g⁻¹) * h.
  have hgh : g⁻¹ * h * g ∈ OddOrder.Isaacs.Ch01.opCore p G := by
    have := hLnorm.conj_mem h hh_L g⁻¹
    simpa [mul_assoc] using this
  have hcomm : (⟨g⁻¹ * h * g, hgh⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨z, hz_L⟩
      = ⟨z, hz_L⟩ * ⟨g⁻¹ * h * g, hgh⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  have hcomm_G : (g⁻¹ * h * g) * z = z * (g⁻¹ * h * g) := congr_arg Subtype.val hcomm
  apply Subtype.ext
  calc h * (g * z * g⁻¹)
      = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm_G]
    _ = (g * z * g⁻¹) * h := by group

/-- Local notation shorthand inside §7B: the underlying subgroup of `Z(O_p(G))`
viewed inside `G` (i.e., the image of `Subgroup.center (opCore p G)` under
the inclusion `opCore p G ↪ G`). -/
def zCenterOpCoreSubgroup (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  (Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
    (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype

private theorem zCenterOpCoreSubgroup_comm
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x ∈ zCenterOpCoreSubgroup G p,
      ∀ y ∈ zCenterOpCoreSubgroup G p, x * y = y * x := by
  rintro _ ⟨⟨x, hx_L⟩, hx_center, rfl⟩ _ ⟨⟨y, hy_L⟩, hy_center, rfl⟩
  -- ⟨x, _⟩ ∈ Z(L) so commutes with ⟨y, _⟩ in L; project to G.
  -- mem_center_iff: x ∈ center ↔ ∀ g, g * x = x * g.
  have hcomm :
      (⟨y, hy_L⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨x, hx_L⟩ =
        ⟨x, hx_L⟩ * ⟨y, hy_L⟩ :=
    Subgroup.mem_center_iff.mp hx_center _
  exact (congr_arg Subtype.val hcomm).symm

/-- **V := Ω₁(Z(O_p(G)))** as a subgroup of `G`.

The set `{g ∈ Z(O_p(G)) | g^p = 1}`, viewed inside `G`.  Since `Z(O_p(G))`
is abelian, this is a subgroup of `G` directly (no closure required).

This is the `V` of **Isaacs Thm 7.6 Step 7 sub-session (A)**: the bottom
layer `Ω₁` of the center of the `p`-core, on which the action of
`A ∈ E(P)` will be analyzed via Cor 4.35. -/
def omega1ZCenterOpCore (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  OddOrder.GroupTheory.omega1OfAbelian G (zCenterOpCoreSubgroup G p) p
    zCenterOpCoreSubgroup_comm

/-- Membership characterization for `V := Ω₁(Z(O_p(G)))`. -/
theorem mem_omega1ZCenterOpCore {G : Type*} [Group G] {p : ℕ} {g : G} :
    g ∈ omega1ZCenterOpCore G p ↔
      g ∈ zCenterOpCoreSubgroup G p ∧ g ^ p = 1 := by
  unfold omega1ZCenterOpCore
  exact OddOrder.GroupTheory.mem_omega1OfAbelian

/-- `V ≤ Z(O_p(G))` (the bottom layer is contained in the center it sits in). -/
theorem omega1ZCenterOpCore_le_zCenterOpCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ zCenterOpCoreSubgroup G p :=
  OddOrder.GroupTheory.omega1OfAbelian_le

/-- **Isaacs Thm 7.6 Step 7 sub-session (A)**: `V := Ω₁(Z(O_p(G)))` is normal in `G`.

Proof: `Z(O_p(G))` (as `zCenterOpCoreSubgroup`) is normal in `G` (already in
`center_opCore_map_normal`).  Conjugation by `g ∈ G` preserves the power map
`x ↦ x^p`, so it sends `{z ∈ Z(O_p(G)) | z^p = 1}` to itself. -/
instance omega1ZCenterOpCore_normal {G : Type*} [Group G] {p : ℕ} :
    (omega1ZCenterOpCore G p).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [mem_omega1ZCenterOpCore] at hn ⊢
  refine ⟨?_, ?_⟩
  · -- Z(O_p(G)) is normal (center_opCore_map_normal).
    have h_norm : (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal
    exact h_norm.conj_mem _ hn.1 g
  · -- (g * n * g⁻¹) ^ p = g * n^p * g⁻¹ = g * 1 * g⁻¹ = 1.
    calc (g * n * g⁻¹) ^ p
        = g * n ^ p * g⁻¹ := by rw [conj_pow]
      _ = g * 1 * g⁻¹ := by rw [hn.2]
      _ = 1 := by group

/-- The elements of `V := Ω₁(Z(O_p(G)))` commute pairwise (V is abelian).

Inherited from the fact that they sit in `Z(O_p(G))`. -/
theorem omega1ZCenterOpCore_comm {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(omega1ZCenterOpCore G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  have hx : (x : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore x.2
  have hy : (y : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore y.2
  exact zCenterOpCoreSubgroup_comm _ hx _ hy

/-- `V := Ω₁(Z(O_p(G)))` as a `CommGroup`.

The pairwise-commutativity from `omega1ZCenterOpCore_comm` upgrades the
ambient `Group ↥V` structure to `CommGroup`. -/
@[reducible] def omega1ZCenterOpCore_commGroup (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(omega1ZCenterOpCore G p) :=
  { (inferInstance : Group ↥(omega1ZCenterOpCore G p)) with
    mul_comm := omega1ZCenterOpCore_comm }

/-- `Z(U) = Z(O_p(G))` is `G`-normal: it is the image of the center
of the (`G`-normal) `O_p(G)`, transported up via `center_opCore_map_normal`. -/
instance zCenterOpCoreSubgroup_normal
    {G : Type*} [Group G] {p : ℕ} :
    (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal

/-- The conjugation action of an arbitrary subgroup `Q ≤ G` on `Z(U) = Z(O_p(G))`:
`Q →* MulAut Z(U)` via `MulAut.conjNormal ∘ Q.subtype`.

Used in Step 6: `Q` (a Sylow `q`-subgroup of `K = C_G(V)`, `q ≠ p`) acts on
`Z(U)` by conjugation; combined with `Q` fixing `V = Ω₁ Z(U)` (from `Q ⊆ K`),
Cor 4.35 yields `Q` acts trivially on `Z(U)`. -/
noncomputable def conjActionOnZCenterOpCoreSubgroup
    {G : Type*} [Group G] {p : ℕ} (Q : Subgroup G) :
    Q →* MulAut ↥(zCenterOpCoreSubgroup G p) :=
  MulAut.conjNormal.comp Q.subtype

/-- Pairwise commutativity on the subtype ↥(Z(U)). -/
theorem zCenterOpCoreSubgroup_comm_subtype
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(zCenterOpCoreSubgroup G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  exact zCenterOpCoreSubgroup_comm _ x.2 _ y.2

/-- `Z(U)` as a `CommGroup`. -/
@[reducible] def zCenterOpCoreSubgroup_commGroup
    (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(zCenterOpCoreSubgroup G p) :=
  { (inferInstance : Group ↥(zCenterOpCoreSubgroup G p)) with
    mul_comm := zCenterOpCoreSubgroup_comm_subtype }

/-- Generic: a subgroup-level `IsElementaryAbelian p H` upgrades the ambient
`Group ↥H` to a `CommGroup ↥H` using the commutativity component.  Local
construction used when applying CommGroup-requiring lemmas (e.g., index
calculations) on elementary abelian subgroups. -/
@[reducible] def isElementaryAbelian_commGroup
    {G : Type*} [Group G] {p : ℕ} {H : Subgroup G} (hH : H.IsElementaryAbelian p) :
    CommGroup ↥H :=
  { (inferInstance : Group ↥H) with mul_comm := hH.1 }

/-- **Isaacs Thm 7.6 Step 6 setup** (mmd L3879): `K := C_G(V)` (where
`V = Ω₁(Z(O_p(G)))`) is `G`-normal.  Trivial: centralizers of normal subgroups
are normal. -/
instance centralizer_omega1ZCenterOpCore_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).Normal :=
  Subgroup.normal_centralizer

end OddOrder.Isaacs.Ch07


