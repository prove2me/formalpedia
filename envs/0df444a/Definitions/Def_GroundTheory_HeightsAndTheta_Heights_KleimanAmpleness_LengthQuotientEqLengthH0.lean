-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:11.531233+00:00
-- url     : https://prove2.me/theorems/ed08bb92-7ac6-5bca-b0a2-b67f99e3c3a7
-- title:
--   Length Quotient Eq Length H0
-- statement:
--   Definitions and structural lemmas for Length Quotient Eq Length H0, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LengthQuotientEqLengthH0.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace QuotientH0Length
section CechH
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]
def toH0OfCocycle (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) : M →ₗ[R] Cech.H G ρ 0 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker (Cech.d G ρ 0)) φ
    (fun m => LinearMap.mem_ker.mpr (hφ m))
end CechH
section Quot
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
theorem mem_sub_of_mem_secs {F : SubSystem S x Ω} {t : Ω} (ht : t ∈ F.secs) (I : Chart x) :
    t ∈ F.sub I :=
  (Submodule.mem_iInf _).mp ht I
def secsTo (F₁ F₂ : SubSystem S x Ω) (I : Chart x) :
    F₁.secs →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mkQ ∘ₗ
    { toFun := fun t => ⟨t.1, mem_sub_of_mem_secs t.2 I⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def toCochain (F₁ F₂ : SubSystem S x Ω) :
    F₁.secs →ₗ[S] Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0 :=
  LinearMap.pi fun I : Cech.Idx (support x) 0 => secsTo F₁ F₂ I.1
def sing {a : Fin (N + 1)} (ha : a ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩, Finset.card_singleton a⟩
end Quot
end QuotientH0Length
end
end GroundTheory.Heights₂.Heights.Kleiman


