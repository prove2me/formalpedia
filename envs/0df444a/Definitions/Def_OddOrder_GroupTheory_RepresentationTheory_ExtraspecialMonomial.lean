-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialMonomial
-- name    : OddOrder_GroupTheory_RepresentationTheory_ExtraspecialMonomial
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:54:10.669541+00:00
-- url     : https://prove2.me/theorems/46a15313-c952-46f6-a269-72ddab1c8c70
-- title:
--   The monomial action of an intertwiner on the Burnside basis (BG (2.11))
-- statement:
--   In the setting of Theorem 2.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, an element $x$ of $G=P\rtimes\langle x\rangle$ normalizes the extraspecial subgroup $P$ and acts on $\mathrm{End}_F V$ by conjugation. This file shows that this conjugation permutes the Burnside basis $\{\rho(\mathrm{out}\,c)\}$ up to nonzero scalars (a monomial action), because conjugation by $x$ induces an automorphism of $P$ and hence of $P/Z$.
--
--   Main declarations: `quotientCenterCongr` (The automorphism of `P/Z(P)` induced by an automorphism `φ` of `P`); `gl_mul_invEnd_eq_one`; `cyclicEndConj_representation` (Conjugation realises the intertwiner as `ρ ∘ φ`); `cyclicEndConj_pow_representation` (Iterated conjugation: `(c_x)^k (ρ p) = ρ (φ^k p)`).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ExtraspecialMonomial.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ExtraspecialMonomial.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BurnsideBasis
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_EigenspaceUnderCyclicAction

namespace OddOrder.RepresentationTheory

open Representation Module EigenspaceUnderCyclicAction

variable {F : Type*} [Field F] [IsAlgClosed F]

variable {P : Type*} [Group P] {V : Type*} [AddCommGroup V] [Module F V]

/-- An automorphism of `P` maps the center onto the center (the center is characteristic). -/
theorem center_map_eq_of_mulEquiv (φ : P ≃* P) :
    (Subgroup.center P).map (φ : P →* P) = Subgroup.center P := by
  have hmem : ∀ (e : P ≃* P) (z : P), z ∈ Subgroup.center P → e z ∈ Subgroup.center P := by
    intro e z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, hz, rfl⟩; exact hmem φ z hz
  · intro y hy
    exact ⟨φ.symm y, hmem φ.symm y hy, by simp⟩

/-- The automorphism of `P/Z(P)` induced by an automorphism `φ` of `P`. -/
noncomputable def quotientCenterCongr (φ : P ≃* P) :
    (P ⧸ Subgroup.center P) ≃* (P ⧸ Subgroup.center P) :=
  QuotientGroup.congr (Subgroup.center P) (Subgroup.center P) φ (center_map_eq_of_mulEquiv φ)

@[simp]
theorem quotientCenterCongr_mk (φ : P ≃* P) (g : P) :
    quotientCenterCongr φ (g : P ⧸ Subgroup.center P) = (φ g : P ⧸ Subgroup.center P) :=
  rfl

/-- Iterating the induced quotient automorphism: `σ^k ⟦g⟧ = ⟦φ^k g⟧`. -/
theorem quotientCenterCongr_pow_mk (φ : P ≃* P) (k : ℕ) (g : P) :
    ((quotientCenterCongr φ) ^ k) (g : P ⧸ Subgroup.center P)
      = ((φ ^ k) g : P ⧸ Subgroup.center P) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, quotientCenterCongr_mk, ih, pow_succ]; rfl

omit [IsAlgClosed F] in
/-- For a `GL` element `T`, conjugation `cyclicEndConj T` followed by `T⁻¹` collapses: as
endomorphisms, `(T : End) * (T⁻¹) = 1`. -/
private theorem gl_mul_invEnd_eq_one (T : LinearMap.GeneralLinearGroup F V) :
    (T : Module.End F V) * (T.toLinearEquiv.symm : Module.End F V) = 1 := by
  ext v
  rw [Module.End.mul_apply, Module.End.one_apply]
  change T.toLinearEquiv (T.toLinearEquiv.symm v) = v
  exact T.toLinearEquiv.apply_symm_apply v

omit [IsAlgClosed F] in
/-- **Conjugation realises the intertwiner as `ρ ∘ φ`.** If `T · ρ p = ρ (φ p) · T` for all `p`,
then `cyclicEndConj T (ρ p) = ρ (φ p)`. -/
theorem cyclicEndConj_representation (ρ : Representation F P V) (φ : P ≃* P)
    (T : LinearMap.GeneralLinearGroup F V)
    (hint : ∀ p : P, (T : Module.End F V) * ρ p = ρ (φ p) * (T : Module.End F V)) (p : P) :
    cyclicEndConj T (ρ p) = ρ (φ p) := by
  change (T : Module.End F V) * ρ p * (T.toLinearEquiv.symm : Module.End F V) = ρ (φ p)
  rw [hint p, mul_assoc, gl_mul_invEnd_eq_one, mul_one]

omit [IsAlgClosed F] in
/-- **Iterated conjugation**: `(c_x)^k (ρ p) = ρ (φ^k p)`. -/
theorem cyclicEndConj_pow_representation (ρ : Representation F P V) (φ : P ≃* P)
    (T : LinearMap.GeneralLinearGroup F V)
    (hint : ∀ p : P, (T : Module.End F V) * ρ p = ρ (φ p) * (T : Module.End F V)) :
    ∀ (k : ℕ) (p : P), ((cyclicEndConj T) ^ k) (ρ p) = ρ ((φ ^ k) p) := by
  intro k
  induction k with
  | zero => intro p; simp
  | succ k ih =>
    intro p
    rw [pow_succ, Module.End.mul_apply, cyclicEndConj_representation ρ φ T hint p, ih (φ p)]
    congr 1

/-- **`(c_x)^h = 1`** when `φ^h = 1`: the iterate agrees with `id` on the Burnside spanning set
`{ρ p}` (`(c_x)^h (ρ p) = ρ (φ^h p) = ρ p`), and `{ρ p}` spans `End_F V`. -/
theorem cyclicEndConj_pow_eq_one [FiniteDimensional F V] (ρ : Representation F P V)
    [ρ.IsIrreducible] (φ : P ≃* P) (T : LinearMap.GeneralLinearGroup F V)
    (hint : ∀ p : P, (T : Module.End F V) * ρ p = ρ (φ p) * (T : Module.End F V))
    {h : ℕ} (hφh : φ ^ h = 1) :
    (cyclicEndConj T) ^ h = 1 := by
  refine LinearMap.ext_on (span_range_representation_eq_top ρ) ?_
  rintro _ ⟨g, rfl⟩
  rw [cyclicEndConj_pow_representation ρ φ T hint h g, hφh]
  simp

/-- **The monomial action of `(c_x)^k` on the Burnside basis** (BG (2.11)): `(c_x)^k (b c)` is a
scalar multiple of `b (σ^k c)`, where `σ = quotientCenterCongr φ`. (`(c_x)^k (ρ(t c)) = ρ(φ^k(t c))`
by `cyclicEndConj_pow_representation`, and `φ^k(t c)`, `t(σ^k c)` lie in the same central coset.)
This is the monomial action of the cyclic group `⟨c_x⟩` on the basis — input to the orbit count. -/
theorem cyclicEndConj_pow_burnsideBasisOfSection [Finite P] [Invertible (Nat.card P : F)]
    [FiniteDimensional F V] (ρ : Representation F P V) [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P) (φ : P ≃* P) (T : LinearMap.GeneralLinearGroup F V)
    (hint : ∀ p : P, (T : Module.End F V) * ρ p = ρ (φ p) * (T : Module.End F V))
    (t : P ⧸ Subgroup.center P → P) (ht : ∀ c, (↑(t c) : P ⧸ Subgroup.center P) = c)
    (k : ℕ) (c : P ⧸ Subgroup.center P) :
    ∃ a : F, ((cyclicEndConj T) ^ k) (burnsideBasisOfSection ρ hf hcl t ht c)
      = a • burnsideBasisOfSection ρ hf hcl t ht (((quotientCenterCongr φ) ^ k) c) := by
  have hcoset : (φ ^ k) (t c) * (t (((quotientCenterCongr φ) ^ k) c))⁻¹ ∈ Subgroup.center P := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht,
      ← quotientCenterCongr_pow_mk, ht]
    exact mul_inv_cancel _
  obtain ⟨a, ha⟩ := center_isScalar ρ hcoset
  refine ⟨a, ?_⟩
  rw [burnsideBasisOfSection_apply, burnsideBasisOfSection_apply,
    cyclicEndConj_pow_representation ρ φ T hint k (t c)]
  have hsplit : (φ ^ k) (t c)
      = ((φ ^ k) (t c) * (t (((quotientCenterCongr φ) ^ k) c))⁻¹)
        * t (((quotientCenterCongr φ) ^ k) c) := by group
  rw [hsplit, map_mul, ha, ← Module.End.one_eq_id, smul_mul_assoc, one_mul]

end OddOrder.RepresentationTheory


