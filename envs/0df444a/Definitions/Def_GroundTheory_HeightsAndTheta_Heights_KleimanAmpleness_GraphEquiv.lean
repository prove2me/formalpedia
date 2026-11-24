-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GraphEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:58.390999+00:00
-- url     : https://prove2.me/theorems/31ea26e4-2914-4f4d-8298-9610bfe9edac
-- title:
--   Graph Equiv
-- statement:
--   Definitions and structural lemmas for Graph Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/GraphEquiv.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KerAltSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace Staircase
structure DblData (R : Type) [CommRing R] where
  D : ℕ → ℕ → Type
  [gD : ∀ p q, AddCommGroup (D p q)]
  [mD : ∀ p q, Module R (D p q)]
  v : ∀ p q, D p q →ₗ[R] D (p + 1) q
  h : ∀ p q, D p q →ₗ[R] D p (q + 1)
  comm : ∀ p q, (v p (q + 1)).comp (h p q) = (h (p + 1) q).comp (v p q)
  A : ℕ → Type
  [gA : ∀ p, AddCommGroup (A p)]
  [mA : ∀ p, Module R (A p)]
  dA : ∀ p, A p →ₗ[R] A (p + 1)
  a : ∀ p, A p →ₗ[R] D p 0
  C : ℕ → Type
  [gC : ∀ q, AddCommGroup (C q)]
  [mC : ∀ q, Module R (C q)]
  dC : ∀ q, C q →ₗ[R] C (q + 1)
  c : ∀ q, C q →ₗ[R] D 0 q
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type} [CommRing R]
structure DblData.Good (X : DblData R) : Prop where
  ha : ∀ p, (X.a (p + 1)).comp (X.dA p) = (X.v p 0).comp (X.a p)
  hc : ∀ q, (X.c (q + 1)).comp (X.dC q) = (X.h 0 q).comp (X.c q)
  ka : ∀ p, LinearMap.ker (X.a p) = ⊥
  ra : ∀ p, LinearMap.ker (X.h p 0) = LinearMap.range (X.a p)
  rh : ∀ p q, LinearMap.ker (X.h p (q + 1)) = LinearMap.range (X.h p q)
  kc : ∀ q, LinearMap.ker (X.c q) = ⊥
  rc : ∀ q, LinearMap.ker (X.v 0 q) = LinearMap.range (X.c q)
  rv : ∀ p q, LinearMap.ker (X.v (p + 1) q) = LinearMap.range (X.v p q)
namespace DblData
theorem comm_apply (X : DblData R) (p q : ℕ) (z : X.D p q) :
    X.v p (q + 1) (X.h p q z) = X.h (p + 1) q (X.v p q z) :=
  LinearMap.congr_fun (X.comm p q) z
def shift (X : DblData R) : DblData R where
  D p q := X.D (p + 1) q
  v p q := X.v (p + 1) q
  h p q := X.h (p + 1) q
  comm p q := X.comm (p + 1) q
  A p := X.A (p + 1)
  dA p := X.dA (p + 1)
  a p := X.a (p + 1)
  C q := LinearMap.range (X.v 0 q)
  dC q := (X.h 1 q).restrict (fun x hx => by
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨X.h 0 q z, X.comm_apply 0 q z⟩)
  c q := (LinearMap.range (X.v 0 q)).subtype
def up (X : DblData R) (n : ℕ) : X.D 0 n →ₗ[R] X.shift.C n := (X.v 0 n).rangeRestrict
namespace Good
theorem shift {X : DblData R} (hX : X.Good) : X.shift.Good where
  ha p := hX.ha (p + 1)
  hc q := LinearMap.ext fun _ => rfl
  ka p := hX.ka (p + 1)
  ra p := hX.ra (p + 1)
  rh p q := hX.rh (p + 1) q
  kc q := Submodule.ker_subtype _
  rc q := by
    show LinearMap.ker (X.v 1 q) = LinearMap.range (LinearMap.range (X.v 0 q)).subtype
    rw [Submodule.range_subtype]
    exact hX.rv 0 q
  rv p q := hX.rv (p + 1) q
end Good
def Rel : (n : ℕ) → (X : DblData R) → X.A n → X.C n → Prop
  | 0, X => fun x y => X.a 0 x = X.c 0 y
  | n + 1, X => fun x y => ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z)
theorem rel_zero {X : DblData R} {x : X.A 0} {y : X.C 0} : Rel 0 X x y ↔ X.a 0 x = X.c 0 y := Iff.rfl
theorem rel_succ {n : ℕ} {X : DblData R} {x : X.A (n + 1)} {y : X.C (n + 1)} :
    Rel (n + 1) X x y ↔ ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z) :=
  Iff.rfl
theorem Rel.zero : ∀ (n : ℕ) (X : DblData R), Rel n X 0 0
  | 0, X => rel_zero.mpr (by rw [map_zero, map_zero])
  | n + 1, X => rel_succ.mpr ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; exact Rel.zero n X.shift⟩
theorem Rel.add : ∀ (n : ℕ) (X : DblData R) {x₁ x₂ : X.A n} {y₁ y₂ : X.C n},
    Rel n X x₁ y₁ → Rel n X x₂ y₂ → Rel n X (x₁ + x₂) (y₁ + y₂)
  | 0, X, _, _, _, _, h₁, h₂ => rel_zero.mpr (by rw [map_add, map_add, rel_zero.mp h₁, rel_zero.mp h₂])
  | n + 1, X, _, _, _, _, h₁, h₂ => by
      obtain ⟨z₁, e₁, r₁⟩ := rel_succ.mp h₁
      obtain ⟨z₂, e₂, r₂⟩ := rel_succ.mp h₂
      refine rel_succ.mpr ⟨z₁ + z₂, by rw [map_add, map_add, e₁, e₂], ?_⟩
      rw [map_add]
      exact Rel.add n X.shift r₁ r₂
theorem Rel.smul : ∀ (n : ℕ) (X : DblData R) (r : R) {x : X.A n} {y : X.C n},
    Rel n X x y → Rel n X (r • x) (r • y)
  | 0, X, r, _, _, h₁ => rel_zero.mpr (by rw [map_smul, map_smul, rel_zero.mp h₁])
  | n + 1, X, r, _, _, h₁ => by
      obtain ⟨z, e, r₁⟩ := rel_succ.mp h₁
      refine rel_succ.mpr ⟨r • z, by rw [map_smul, map_smul, e], ?_⟩
      rw [map_smul]
      exact Rel.smul n X.shift r r₁
def relSub (n : ℕ) (X : DblData R) : Submodule R (X.A n × X.C n) where
  carrier := {p | Rel n X p.1 p.2}
  add_mem' h₁ h₂ := Rel.add n X h₁ h₂
  zero_mem' := Rel.zero n X
  smul_mem' r _ hp := Rel.smul n X r hp
end DblData
namespace DblData
end DblData
end Staircase
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


