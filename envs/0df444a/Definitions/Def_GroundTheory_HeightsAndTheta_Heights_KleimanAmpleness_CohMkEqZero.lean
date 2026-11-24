-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:02.13443+00:00
-- url     : https://prove2.me/theorems/7ff7bbc2-e0a3-4dcd-98e4-7f0df605a43b
-- title:
--   Coh Mk Eq Zero
-- statement:
--   Definitions and structural lemmas for Coh Mk Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
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
noncomputable section
namespace EulerSES
open Module
section Generic
variable {F : Type} [Field F] {X Y : ℕ → Type} [∀ n, AddCommGroup (X n)] [∀ n, Module F (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module F (Y n)]
theorem mem_cyc {CX : ∀ n, Submodule F (X n)} {dX : ∀ n, X n →ₗ[F] X (n + 1)} {n : ℕ} {x : X n} :
    x ∈ cyc CX dX n ↔ x ∈ CX n ∧ dX n x = 0 := by
  simp [cyc, Submodule.mem_inf, LinearMap.mem_ker]
theorem mem_bnd_zero {CX : ∀ n, Submodule F (X n)} {dX : ∀ n, X n →ₗ[F] X (n + 1)} {x : X 0} :
    x ∈ bnd CX dX 0 ↔ x = 0 :=
  Submodule.mem_bot F
theorem mem_bnd_succ {CX : ∀ n, Submodule F (X n)} {dX : ∀ n, X n →ₗ[F] X (n + 1)} {n : ℕ} {x : X (n + 1)} :
    x ∈ bnd CX dX (n + 1) ↔ ∃ w ∈ CX n, dX n w = x :=
  Submodule.mem_map
theorem coh_mk_eq_zero {CX : ∀ n, Submodule F (X n)} {dX : ∀ n, X n →ₗ[F] X (n + 1)} {n : ℕ}
    (x : cyc CX dX n) : (Submodule.Quotient.mk x : coh CX dX n) = 0 ↔ (x : X n) ∈ bnd CX dX n :=
  Submodule.Quotient.mk_eq_zero _
theorem d_of_mem_bnd {CX : ∀ n, Submodule F (X n)} {dX : ∀ n, X n →ₗ[F] X (n + 1)}
    (hdd : ∀ n, ∀ x ∈ CX n, dX (n + 1) (dX n x) = 0) {n : ℕ} {x : X n} (hx : x ∈ bnd CX dX n) :
    dX n x = 0 := by
  rcases n with _ | n
  · rw [mem_bnd_zero.1 hx, map_zero]
  · obtain ⟨w, hw, rfl⟩ := mem_bnd_succ.1 hx
    exact hdd n w hw
variable (CX : ∀ n, Submodule F (X n)) (dX : ∀ n, X n →ₗ[F] X (n + 1))
  (CY : ∀ n, Submodule F (Y n)) (dY : ∀ n, Y n →ₗ[F] Y (n + 1)) (h : ∀ n, X n →ₗ[F] Y n)
theorem map_mem_cyc (hC : ∀ n, ∀ x ∈ CX n, h n x ∈ CY n)
    (hd : ∀ n, ∀ x ∈ CX n, dY n (h n x) = h (n + 1) (dX n x)) (n : ℕ) :
    ∀ x ∈ cyc CX dX n, h n x ∈ cyc CY dY n := by
  intro x hx
  rw [mem_cyc] at hx ⊢
  exact ⟨hC n x hx.1, by rw [hd n x hx.1, hx.2, map_zero]⟩
theorem map_mem_bnd (hC : ∀ n, ∀ x ∈ CX n, h n x ∈ CY n)
    (hd : ∀ n, ∀ x ∈ CX n, dY n (h n x) = h (n + 1) (dX n x)) (n : ℕ) :
    ∀ x ∈ bnd CX dX n, h n x ∈ bnd CY dY n := by
  intro x hx
  rcases n with _ | n
  · rw [mem_bnd_zero] at hx ⊢
    rw [hx, map_zero]
  · obtain ⟨w, hw, rfl⟩ := mem_bnd_succ.1 hx
    exact mem_bnd_succ.2 ⟨h n w, hC n w hw, hd n w hw⟩
def cohMap (hC : ∀ n, ∀ x ∈ CX n, h n x ∈ CY n)
    (hd : ∀ n, ∀ x ∈ CX n, dY n (h n x) = h (n + 1) (dX n x)) (n : ℕ) :
    coh CX dX n →ₗ[F] coh CY dY n :=
  Submodule.mapQ _ _ ((h n).restrict (map_mem_cyc CX dX CY dY h hC hd n))
    (fun x hx => map_mem_bnd CX dX CY dY h hC hd n x hx)
end Generic
section SES
variable {F : Type} [Field F] {A B C : ℕ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)]
  [∀ n, AddCommGroup (B n)] [∀ n, Module F (B n)] [∀ n, AddCommGroup (C n)] [∀ n, Module F (C n)]
structure IsSES (CA : ∀ n, Submodule F (A n)) (CB : ∀ n, Submodule F (B n)) (CC : ∀ n, Submodule F (C n))
    (dA : ∀ n, A n →ₗ[F] A (n + 1)) (dB : ∀ n, B n →ₗ[F] B (n + 1)) (dC : ∀ n, C n →ₗ[F] C (n + 1))
    (f : ∀ n, A n →ₗ[F] B n) (g : ∀ n, B n →ₗ[F] C n) : Prop where
  dA_mem : ∀ n, ∀ x ∈ CA n, dA n x ∈ CA (n + 1)
  dB_mem : ∀ n, ∀ x ∈ CB n, dB n x ∈ CB (n + 1)
  dC_mem : ∀ n, ∀ x ∈ CC n, dC n x ∈ CC (n + 1)
  dA_dA : ∀ n, ∀ x ∈ CA n, dA (n + 1) (dA n x) = 0
  dB_dB : ∀ n, ∀ x ∈ CB n, dB (n + 1) (dB n x) = 0
  dC_dC : ∀ n, ∀ x ∈ CC n, dC (n + 1) (dC n x) = 0
  f_mem : ∀ n, ∀ x ∈ CA n, f n x ∈ CB n
  g_mem : ∀ n, ∀ y ∈ CB n, g n y ∈ CC n
  f_d : ∀ n, ∀ x ∈ CA n, dB n (f n x) = f (n + 1) (dA n x)
  g_d : ∀ n, ∀ y ∈ CB n, dC n (g n y) = g (n + 1) (dB n y)
  f_inj : ∀ n, ∀ x ∈ CA n, f n x = 0 → x = 0
  g_f : ∀ n, ∀ x ∈ CA n, g n (f n x) = 0
  ker_g : ∀ n, ∀ y ∈ CB n, g n y = 0 → ∃ x ∈ CA n, f n x = y
  g_onto : ∀ n, ∀ z ∈ CC n, ∃ y ∈ CB n, g n y = z
def liftSp (CB : ∀ n, Submodule F (B n)) (dC : ∀ n, C n →ₗ[F] C (n + 1)) (g : ∀ n, B n →ₗ[F] C n) (n : ℕ) :
    Submodule F (B n) :=
  CB n ⊓ LinearMap.ker ((dC n).comp (g n))
theorem mem_liftSp {CB : ∀ n, Submodule F (B n)} {dC : ∀ n, C n →ₗ[F] C (n + 1)} {g : ∀ n, B n →ₗ[F] C n}
    {n : ℕ} {y : B n} : y ∈ liftSp CB dC g n ↔ y ∈ CB n ∧ dC n (g n y) = 0 := by
  simp [liftSp, Submodule.mem_inf, LinearMap.mem_ker]
variable {CA : ∀ n, Submodule F (A n)} {CB : ∀ n, Submodule F (B n)} {CC : ∀ n, Submodule F (C n)}
  {dA : ∀ n, A n →ₗ[F] A (n + 1)} {dB : ∀ n, B n →ₗ[F] B (n + 1)} {dC : ∀ n, C n →ₗ[F] C (n + 1)}
  {f : ∀ n, A n →ₗ[F] B n} {g : ∀ n, B n →ₗ[F] C n}
namespace IsSES
variable (H : IsSES CA CB CC dA dB dC f g)
include H
def iA (n : ℕ) : coh CA dA n →ₗ[F] coh CB dB n := cohMap CA dA CB dB f H.f_mem H.f_d n
def pB (n : ℕ) : coh CB dB n →ₗ[F] coh CC dC n := cohMap CB dB CC dC g H.g_mem H.g_d n
theorem g_mem_cyc (n : ℕ) : ∀ y ∈ liftSp CB dC g n, g n y ∈ cyc CC dC n := by
  intro y hy
  rw [mem_liftSp] at hy
  exact mem_cyc.2 ⟨H.g_mem n y hy.1, hy.2⟩
def toCohC (n : ℕ) : liftSp CB dC g n →ₗ[F] coh CC dC n :=
  Submodule.mkQ _ ∘ₗ (g n).restrict (H.g_mem_cyc n)
theorem toCohC_apply (n : ℕ) (y : liftSp CB dC g n) :
    H.toCohC n y = Submodule.Quotient.mk ⟨g n y, H.g_mem_cyc n y y.2⟩ :=
  rfl
theorem fInj (n : ℕ) : Function.Injective ((f n).domRestrict (CA n)) :=
  (injective_iff_map_eq_zero ((f n).domRestrict (CA n))).2 fun x hx => Subtype.ext (H.f_inj n x x.2 hx)
def fEquiv (n : ℕ) : CA n ≃ₗ[F] LinearMap.range ((f n).domRestrict (CA n)) :=
  LinearEquiv.ofInjective _ (H.fInj n)
theorem dB_mem_range (n : ℕ) (y : liftSp CB dC g n) :
    dB n y ∈ LinearMap.range ((f (n + 1)).domRestrict (CA (n + 1))) := by
  have hy := mem_liftSp.1 y.2
  obtain ⟨x, hx, hfx⟩ :=
    H.ker_g (n + 1) (dB n y) (H.dB_mem n y hy.1) (by rw [← H.g_d n y hy.1]; exact hy.2)
  exact LinearMap.mem_range.2 ⟨⟨x, hx⟩, hfx⟩
def liftB (n : ℕ) : liftSp CB dC g n →ₗ[F] CA (n + 1) :=
  (H.fEquiv (n + 1)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ ((dB n).domRestrict (liftSp CB dC g n)) (H.dB_mem_range n)
theorem f_liftB (n : ℕ) (y : liftSp CB dC g n) : f (n + 1) (H.liftB n y : A (n + 1)) = dB n y :=
  LinearEquiv.ofInjective_symm_apply (f := (f (n + 1)).domRestrict (CA (n + 1))) (h := H.fInj (n + 1)) _
theorem liftB_mem_cyc (n : ℕ) (y : liftSp CB dC g n) : (H.liftB n y : A (n + 1)) ∈ cyc CA dA (n + 1) := by
  have hy := mem_liftSp.1 y.2
  have hx := (H.liftB n y).2
  refine mem_cyc.2 ⟨hx, H.f_inj (n + 1 + 1) _ (H.dA_mem (n + 1) _ hx) ?_⟩
  rw [← H.f_d (n + 1) _ hx, H.f_liftB n y, H.dB_dB n y hy.1]
def toCohA (n : ℕ) : liftSp CB dC g n →ₗ[F] coh CA dA (n + 1) :=
  Submodule.mkQ _ ∘ₗ
    LinearMap.codRestrict (cyc CA dA (n + 1)) ((CA (n + 1)).subtype ∘ₗ H.liftB n) (H.liftB_mem_cyc n)
theorem toCohA_apply (n : ℕ) (y : liftSp CB dC g n) :
    H.toCohA n y = Submodule.Quotient.mk ⟨H.liftB n y, H.liftB_mem_cyc n y⟩ :=
  rfl
theorem toCohC_surj (n : ℕ) : Function.Surjective (H.toCohC n) := by
  intro q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hz := mem_cyc.1 z.2
  obtain ⟨y, hy, hgy⟩ := H.g_onto n z hz.1
  refine ⟨⟨y, mem_liftSp.2 ⟨hy, by rw [hgy]; exact hz.2⟩⟩, ?_⟩
  rw [toCohC_apply]
  congr 1
  exact Subtype.ext hgy
theorem lift_bnd (n : ℕ) (y : B n) (hy : y ∈ CB n) (hgy : g n y ∈ bnd CC dC n) :
    ∃ x ∈ CA n, y - f n x ∈ bnd CB dB n := by
  rcases n with _ | n
  · obtain ⟨x, hx, hfx⟩ := H.ker_g 0 y hy (mem_bnd_zero.1 hgy)
    exact ⟨x, hx, by rw [hfx, sub_self]; exact zero_mem _⟩
  · obtain ⟨z, hz, hdz⟩ := mem_bnd_succ.1 hgy
    obtain ⟨y', hy', rfl⟩ := H.g_onto n z hz
    have hmem : y - dB n y' ∈ CB (n + 1) := sub_mem hy (H.dB_mem n y' hy')
    obtain ⟨x, hx, hfx⟩ := H.ker_g (n + 1) _ hmem (by rw [map_sub, ← H.g_d n y' hy', hdz, sub_self])
    refine ⟨x, hx, mem_bnd_succ.2 ⟨y', hy', ?_⟩⟩
    rw [hfx, sub_sub_cancel]
theorem ker_toCohC_le (n : ℕ) : LinearMap.ker (H.toCohC n) ≤ LinearMap.ker (H.toCohA n) := by
  intro y hy
  rw [LinearMap.mem_ker, toCohC_apply, coh_mk_eq_zero] at hy
  rw [LinearMap.mem_ker, toCohA_apply, coh_mk_eq_zero]
  have hyl := mem_liftSp.1 y.2
  obtain ⟨x, hx, hb⟩ := H.lift_bnd n y hyl.1 hy
  have hxb : (H.liftB n y : A (n + 1)) = dA n x := by
    have h1 := d_of_mem_bnd H.dB_dB hb
    rw [map_sub, sub_eq_zero, H.f_d n x hx] at h1
    exact congrArg Subtype.val (H.fInj (n + 1) (a₁ := H.liftB n y) (a₂ := ⟨dA n x, H.dA_mem n x hx⟩)
      (by show f (n + 1) (H.liftB n y : A (n + 1)) = f (n + 1) (dA n x); rw [H.f_liftB]; exact h1))
  show (H.liftB n y : A (n + 1)) ∈ bnd CA dA (n + 1)
  rw [hxb]
  exact mem_bnd_succ.2 ⟨x, hx, rfl⟩
def delta (n : ℕ) : coh CC dC n →ₗ[F] coh CA dA (n + 1) :=
  (LinearMap.ker (H.toCohC n)).liftQ (H.toCohA n) (H.ker_toCohC_le n) ∘ₗ
    ((H.toCohC n).quotKerEquivOfSurjective (H.toCohC_surj n)).symm.toLinearMap
variable (hfa : ∀ n, FiniteDimensional F (coh CA dA n)) (hfb : ∀ n, FiniteDimensional F (coh CB dB n))
  (hfc : ∀ n, FiniteDimensional F (coh CC dC n))
end IsSES
end SES
end EulerSES
open EulerSES
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


