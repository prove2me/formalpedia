-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnimodGenus
-- name    : Formalism_PeriodIntegrals_UnimodGenus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:52.249441+00:00
-- url     : https://prove2.me/theorems/ac0e40b7-d0e5-4e12-b185-2c2e7a6ae6bb
-- title:
--   Unimod Genus
-- statement:
--   Definitions and structural lemmas for Unimod Genus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnimodGenus.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.UG
section Defs
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
def isom (h : V →ₗ⋆[K] V →ₗ[K] K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change h (a (b x)) (a (b y)) = h x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha (a.symm x) (a.symm y)
    change h (a.symm x) (a.symm y) = h x y
    simpa using this.symm
def gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : Submodule R V :=
  L.map ((g : V →ₗ[K] V).restrictScalars R)
def dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (1 : Submodule R K).comap ((h y).restrictScalars R)
def IsUnimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  dual h L = L
def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx
def hcompl (p : Ideal R) : Submonoid R :=
  Submonoid.closure {s | s ∉ p ∧ ∀ t : R, algebraMap R K t = star (algebraMap R K s) → t ∉ p}
def loc {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) (L : Submodule R W) :
    Submodule R W :=
  locS (hcompl (K := K) p) L
def SameGenus (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) : Prop :=
  ∀ p : Ideal R, p.IsMaximal → ∃ g ∈ isom h, gmap g (loc (K := K) p L) = loc (K := K) p M
end Defs
abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E
def hStd (E : Type) [Field E] [StarRing E] (n : ℕ) : Sp E n →ₗ⋆[E] Sp E n →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => ∑ i, star (x i) * y i)
    (by intro x y z; simp [add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_left_comm])
def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)
def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P
end PI.UG
namespace PI
open PI.UG
def UnimodGenus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), IsCMUnram E →
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
      SameGenus (hStd E n) (stdLat E n) N
end PI


