-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivationOfSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:54.73682+00:00
-- url     : https://prove2.me/theorems/e14e9d21-af6a-4646-b803-8c17305d9d8b
-- title:
--   Derivation Of Surjective
-- statement:
--   Definitions and structural lemmas for Derivation Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivationOfSurjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
variable {k S T : Type*} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]
theorem map_derivation_eq_of_map_eq (f : S →ₐ[k] T) (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom)
    {s s' : S} (h : f s = f s') : f (D s) = f (D s') := by
  have hker : s - s' ∈ RingHom.ker f.toRingHom := by
    simp [RingHom.mem_ker, h]
  have hD' := hD _ hker
  rw [RingHom.mem_ker, map_sub D s s'] at hD'
  have h2 : f (D s) - f (D s') = 0 := by
    rw [← map_sub f (D s) (D s')]
    exact hD'
  exact eq_of_sub_eq_zero h2
noncomputable def derivationOfSurjectiveFun (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S) : T → T :=
  fun t => f (D (Function.surjInv hf t))
theorem derivationOfSurjectiveFun_apply (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) (s : S) :
    derivationOfSurjectiveFun f hf D (f s) = f (D s) := by
  have h : f (Function.surjInv hf (f s)) = f s := Function.surjInv_eq hf (f s)
  exact map_derivation_eq_of_map_eq f D hD h
theorem derivationOfSurjectiveFun_add (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    ∀ t t' : T, derivationOfSurjectiveFun f hf D (t + t')
      = derivationOfSurjectiveFun f hf D t + derivationOfSurjectiveFun f hf D t' := by
  intro t t'
  obtain ⟨a, rfl⟩ := hf t
  obtain ⟨b, rfl⟩ := hf t'
  rw [← map_add f a b]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [map_add D a b, map_add f (D a) (D b)]
theorem derivationOfSurjectiveFun_smul (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    ∀ (c : k) (t : T), derivationOfSurjectiveFun f hf D (c • t) = c • derivationOfSurjectiveFun f hf D t := by
  intro c t
  obtain ⟨a, rfl⟩ := hf t
  have h1 : f (c • a) = c • f a := map_smul f c a
  have h2 : D (c • a) = c • D a := by
    simp
  have h3 : f (c • D a) = c • f (D a) := map_smul f c (D a)
  rw [← h1]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [h2]
  exact h3
noncomputable def derivationOfSurjectiveLinearMap (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) : T →ₗ[k] T where
  toFun := derivationOfSurjectiveFun f hf D
  map_add' := derivationOfSurjectiveFun_add f hf D hD
  map_smul' := derivationOfSurjectiveFun_smul f hf D hD
theorem derivationOfSurjectiveFun_one (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    derivationOfSurjectiveFun f hf D 1 = 0 := by
  have h : (1 : T) = f 1 := (map_one f).symm
  rw [h]
  rw [derivationOfSurjectiveFun_apply f hf D hD, D.map_one_eq_zero, map_zero]
theorem derivationOfSurjectiveFun_mul (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    ∀ a b : T, derivationOfSurjectiveFun f hf D (a * b)
      = a • derivationOfSurjectiveFun f hf D b + b • derivationOfSurjectiveFun f hf D a := by
  intro a b
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  rw [← map_mul f x y]
  simp only [derivationOfSurjectiveFun_apply f hf D hD]
  rw [D.leibniz]
  simp [smul_eq_mul]
noncomputable def derivationOfSurjective (f : S →ₐ[k] T) (hf : Function.Surjective f)
    (D : Derivation k S S)
    (hD : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom) :
    Derivation k T T where
  toLinearMap := derivationOfSurjectiveLinearMap f hf D hD
  map_one_eq_zero' := derivationOfSurjectiveFun_one f hf D hD
  leibniz' := derivationOfSurjectiveFun_mul f hf D hD
end FunctorialResolution.EmbeddedResolution


