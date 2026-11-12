-- Prove2me | Definitions.Def_OddOrder_GroupTheory_CoprimeAction
-- name    : OddOrder_GroupTheory_CoprimeAction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:34:58.939034+00:00
-- url     : https://prove2.me/theorems/3152d7c9-8f24-405a-83ae-524e5d138f36
-- title:
--   Coprime actions and Glauberman's lemma (setup)
-- statement:
--   Basic tools for coprime actions. Main definitions: compatibility of the actions of $A$ and $G$ on $\Omega$ via $\varphi:A\to\mathrm{Aut}(G)$, the action of the semidirect product $G\rtimes_\varphi A$ on $\Omega$, and a carrier for Peterfalvi (9.1): a coprime action of a Frobenius group $L=UE$ together with the fixed-point subgroups $C_H(UE)$, $C_H(E)$, $C_H(U)$.
--
--   Main declarations: `IsCompatibleAction`; `gammaMulAction` (The action of the semidirect product `G ⋊[φ] A` on `Ω`, built from compatible G- and A-actions); `CoprimeFrobeniusAction`; `fixedByUE` (`C_H(UE) = C_H(L)`: the points of `H` fixed by the whole Frobenius group `L = UE`); and 2 more.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/CoprimeAction.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/CoprimeAction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_GroupTheory_FixedSubgroup
import Definitions.Def_OddOrder_Mathlib_SchurZassenhausConj
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SemidirectProduct

namespace OddOrder.GroupTheory

section CompatibleAction

variable {A G Ω : Type*} [Group A] [Group G]

variable [MulAction G Ω] [MulAction A Ω]

/-- **Compatibility** between A and G actions on Ω via `φ : A → Aut(G)`:
`a • (g • ω) = (φ a g) • (a • ω)` for all `a ∈ A, g ∈ G, ω ∈ Ω`.

Isaacs PDF p.97 の (★) 条件 (right-action 表記での `(α·g)·a = (α·a)·g^a` の left-action 翻訳). -/
def IsCompatibleAction (φ : A →* MulAut G) : Prop :=
  ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (φ a g) • (a • ω)

end CompatibleAction

section GammaAction

variable {A G Ω : Type*} [Group A] [Group G]

variable [MulAction G Ω] [MulAction A Ω]

variable {φ : A →* MulAut G}

/-- The action of the semidirect product `G ⋊[φ] A` on `Ω`, built from compatible
G- and A-actions. `(g, a) • ω := g • (a • ω)`.

これは `def` であって `instance` ではない (compatibility は `Prop` で typeclass で
推論不能). 使用側は `letI := gammaMulAction hCompat` で局所 instance 化. -/
@[reducible] def gammaMulAction (hCompat : @IsCompatibleAction A G Ω _ _ _ _ φ) :
    MulAction (G ⋊[φ] A) Ω where
  smul x ω := x.left • (x.right • ω)
  one_smul ω := by
    change (1 : G ⋊[φ] A).left • ((1 : G ⋊[φ] A).right • ω) = ω
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, one_smul, one_smul]
  mul_smul x y ω := by
    rcases x with ⟨gx, ax⟩
    rcases y with ⟨gy, ay⟩
    change (gx * φ ax gy) • ((ax * ay) • ω) = gx • (ax • (gy • (ay • ω)))
    rw [mul_smul (gx) (φ ax gy), mul_smul ax ay, ← hCompat ax gy (ay • ω)]

end GammaAction

section WielandtFixedPoint

variable {L H : Type*} [Group L] [Group H]

/-- A carrier for **Peterfalvi (9.1)**: a coprime action `φ` of a Frobenius group
`L = U ⋊ E` (kernel `U`, complement `E`) on a finite solvable group `H`.

The three fixed-point subgroups `C_H(UE)`, `C_H(E)`, `C_H(U)` of Wielandt's formula are
*derived* from the action (see `fixedByUE`, `fixedByE`, `fixedByU`), not stored, so the
formula below is a genuine statement about the action. -/
structure CoprimeFrobeniusAction (L H : Type*) [Group L] [Group H] where
  U : Subgroup L
  E : Subgroup L
  frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup L U E
  H_solvable : Group.IsSolvable H
  /-- The action of the Frobenius group `L = U ⋊ E` on `H` by automorphisms. -/
  φ : L →* MulAut H
  coprime_order : Nat.Coprime (Nat.card H) (Nat.card L)

namespace CoprimeFrobeniusAction

/-- `C_H(UE) = C_H(L)`: the points of `H` fixed by the whole Frobenius group `L = UE`. -/
def fixedByUE (act : CoprimeFrobeniusAction L H) : Subgroup H := fixedSubgroup act.φ ⊤

/-- `C_H(E)`: the points of `H` fixed by the Frobenius complement `E`. -/
def fixedByE (act : CoprimeFrobeniusAction L H) : Subgroup H := fixedSubgroup act.φ act.E

/-- `C_H(U)`: the points of `H` fixed by the Frobenius kernel `U`. -/
def fixedByU (act : CoprimeFrobeniusAction L H) : Subgroup H := fixedSubgroup act.φ act.U

theorem fixedByUE_le_fixedByE (act : CoprimeFrobeniusAction L H) :
    act.fixedByUE ≤ act.fixedByE := fixedSubgroup_antitone act.φ le_top

theorem fixedByUE_le_fixedByU (act : CoprimeFrobeniusAction L H) :
    act.fixedByUE ≤ act.fixedByU := fixedSubgroup_antitone act.φ le_top

end CoprimeFrobeniusAction

end WielandtFixedPoint

section FrobeniusCentralizer

open OddOrder.Isaacs

variable {L : Type*} [Group L] [Finite L] {N A : Subgroup L}

/-- **A non-kernel element centralizes nothing nontrivial in the Frobenius kernel.**  In a finite
Frobenius group with kernel `N`, if `g ∉ N` then `C_L(g) ⊓ N = 1`: any `x ∈ N` commuting with `g`
would put `g ∈ C_L(x) ≤ N` (`centralizer_kernel_le`).  Reusable; the engine of the fixed-point-free
action in Peterfalvi (9.1)/(13.17.b). -/
theorem IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem
    (h : Ch06.IsFrobeniusGroup L N A) {g : L} (hg : g ∉ N) :
    Subgroup.centralizer ({g} : Set L) ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxc, hxN⟩ := Subgroup.mem_inf.mp hx
  by_contra hxne
  rw [Subgroup.mem_bot] at hxne
  refine hg (h.centralizer_kernel_le x hxN hxne ?_)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm

/-- **Ambient-`G` form of `frobeniusGroup_sup_of_invariant_le_kernel`.**  For a finite Frobenius
group `Lsub ≤ G` with kernel `H` (`H ≤ Lsub`, `H.subgroupOf Lsub` normal), a nontrivial subgroup
`P ≤ H` normalized by a nontrivial `A ≤ Lsub` meeting the kernel trivially (`A ⊓ H = ⊥`) yields the
sub-Frobenius group `P ⊔ A = P ⋊ A` with kernel `P`, phrased in the ambient `G` (subgroups
`P.subgroupOf (P ⊔ A)`, `A.subgroupOf (P ⊔ A)`) so it feeds the ambient Wielandt engine
`frobenius_kernel_centralizes_of_complement_fpf` with no `subgroupOf` transfer.

The conjugation condition lifts each nontrivial `a ∈ A`, `n ∈ P` into the Frobenius group `↥Lsub`:
`a ∉ H` (as `A ⊓ H = ⊥`), so `centralizer_inf_kernel_eq_bot_of_not_mem` makes `C_{Lsub}(a)` meet
the kernel `H` trivially, hence `a` centralizes no nontrivial `n ∈ P ≤ H`.  Reusable engine for
Peterfalvi's "`P₀A` is a Frobenius group with kernel `P₀`" step (12.11). -/
theorem IsFrobeniusGroup.frobeniusGroup_sup_of_invariant_le_kernel_ambient
    {G : Type*} [Group G] [Finite G] {Lsub H P A : Subgroup G} (hHL : H ≤ Lsub)
    (hFrobL : ∃ C : Subgroup ↥Lsub, Ch06.IsFrobeniusGroup ↥Lsub (H.subgroupOf Lsub) C)
    (hPH : P ≤ H) (hPne : P ≠ ⊥) (hAL : A ≤ Lsub) (hAH : A ⊓ H = ⊥) (hAne : A ≠ ⊥)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    Ch06.IsFrobeniusGroup ↥(P ⊔ A) (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) := by
  classical
  obtain ⟨C, hFrobA⟩ := hFrobL
  have hPle : P ≤ P ⊔ A := le_sup_left
  have hAle : A ≤ P ⊔ A := le_sup_right
  have hPnormal : (P.subgroupOf (P ⊔ A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPle]
    exact sup_le Subgroup.le_normalizer hAP
  have hPA_bot : P ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    calc P ⊓ A ≤ H ⊓ A := inf_le_inf_right A hPH
      _ = A ⊓ H := inf_comm ..
      _ = ⊥ := hAH
  have hdisj : Disjoint (P.subgroupOf (P ⊔ A)) (A.subgroupOf (P ⊔ A)) := by
    rw [disjoint_iff, show P.subgroupOf (P ⊔ A) ⊓ A.subgroupOf (P ⊔ A)
        = (P ⊓ A).subgroupOf (P ⊔ A) from (Subgroup.comap_inf P A (P ⊔ A).subtype).symm,
      hPA_bot, Subgroup.bot_subgroupOf]
  have htop : P.subgroupOf (P ⊔ A) ⊔ A.subgroupOf (P ⊔ A) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPle hAle, Subgroup.subgroupOf_self]
  refine
    { isNormal := hPnormal
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
    rw [← Subgroup.normal_mul, htop, Subgroup.coe_top]
  · intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hPne (le_bot_iff.mp (by simpa [inf_of_le_left hPle] using hbot.le_bot))
  · intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hAne (le_bot_iff.mp (by simpa [inf_of_le_left hAle] using hbot.le_bot))
  · intro a ha ha1 n hn hn1 hconj
    rw [Subgroup.mem_subgroupOf] at ha hn
    have haL_ne : (a : G) ≠ 1 := fun hh => ha1 (Subtype.ext (by simpa using hh))
    have hnL_ne : (n : G) ≠ 1 := fun hh => hn1 (Subtype.ext (by simpa using hh))
    have haH : (a : G) ∉ H := fun haHmem =>
      haL_ne (Subgroup.disjoint_def.mp (disjoint_iff.mpr hAH) ha haHmem)
    have hnH : (n : G) ∈ H := hPH hn
    have hconjG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := Subtype.ext_iff.mp hconj
      push_cast at this
      simpa using this
    have haLsub : (a : G) ∈ Lsub := hAL ha
    have hnLsub : (n : G) ∈ Lsub := hHL hnH
    have hk_notmem : (⟨(a : G), haLsub⟩ : ↥Lsub) ∉ H.subgroupOf Lsub :=
      fun hh => haH (Subgroup.mem_subgroupOf.mp hh)
    have hcb := IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem hFrobA hk_notmem
    have hcomm : (a : G) * (n : G) = (n : G) * (a : G) := mul_inv_eq_iff_eq_mul.mp hconjG
    have hn_cent : (⟨(n : G), hnLsub⟩ : ↥Lsub) ∈
        Subgroup.centralizer ({(⟨(a : G), haLsub⟩ : ↥Lsub)} : Set ↥Lsub) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm.symm
    have hn_in : (⟨(n : G), hnLsub⟩ : ↥Lsub) ∈
        Subgroup.centralizer ({(⟨(a : G), haLsub⟩ : ↥Lsub)} : Set ↥Lsub) ⊓ H.subgroupOf Lsub :=
      ⟨hn_cent, Subgroup.mem_subgroupOf.mpr hnH⟩
    exact hnL_ne (congrArg Subtype.val (Subgroup.mem_bot.mp (hcb.le hn_in)))

/-- **Isaacs Lemma 6.1 for an invariant subgroup of a Frobenius kernel (ambient form)**: in the
setting of `frobeniusGroup_sup_of_invariant_le_kernel_ambient` — a finite Frobenius group
`Lsub ≤ G` with kernel `H`, a nontrivial `P ≤ H` normalized by a nontrivial `A ≤ Lsub` meeting the
kernel trivially — the sub-Frobenius group `P ⋊ A` yields the congruence `|P| ≡ 1 (mod |A|)`.

Reusable counting engine for Peterfalvi's "an order-`q` element acts fixed-point-freely on
`Ω₁(P)`, hence `q ∣ p^k - 1`" steps ((12.10) case (8.3.b), (12.12)). -/
theorem IsFrobeniusGroup.card_modEq_one_of_invariant_le_kernel_ambient
    {G : Type*} [Group G] [Finite G] {Lsub H P A : Subgroup G} (hHL : H ≤ Lsub)
    (hFrobL : ∃ C : Subgroup ↥Lsub, Ch06.IsFrobeniusGroup ↥Lsub (H.subgroupOf Lsub) C)
    (hPH : P ≤ H) (hPne : P ≠ ⊥) (hAL : A ≤ Lsub) (hAH : A ⊓ H = ⊥) (hAne : A ≠ ⊥)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    Nat.card ↥P ≡ 1 [MOD Nat.card ↥A] := by
  have hFrob := IsFrobeniusGroup.frobeniusGroup_sup_of_invariant_le_kernel_ambient
    hHL hFrobL hPH hPne hAL hAH hAne hAP
  have h1 := hFrob.card_kernel_modEq_one
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ P ⊔ A)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ P ⊔ A)).toEquiv] at h1

end FrobeniusCentralizer

end OddOrder.GroupTheory


