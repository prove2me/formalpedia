-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:44.17242+00:00
-- url     : https://prove2.me/theorems/77193ea5-4401-4b97-bf28-dd1acee32afa
-- title:
--   PRestr Len Restrict
-- statement:
--   Definitions and structural lemmas for PRestr Len Restrict, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartRing_sub_locAt_a84ca9ba7312
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_add_75c3baa8859e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_algebraMap_ad6f57dcffae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_mul_614d2e1fada9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_one_d19ae30e21d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locAt_zero_68297b898f07

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
namespace RestrLenRestrict
section CechH
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]
def cochainOf (σ : ∀ I : Cell U, M →ₗ[R] G I) : M →ₗ[R] Cech.Cochain G 0 :=
  LinearMap.pi fun I : Cech.Idx U 0 => σ I.1
def toH0OfCocycle (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) : M →ₗ[R] Cech.H G ρ 0 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker (Cech.d G ρ 0)) φ
    (fun m => LinearMap.mem_ker.mpr (hφ m))
end CechH
section Quot
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type w} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
theorem mem_sub_of_mem_secs {F : SubSystem S x E} {t : E} (ht : t ∈ F.secs) (I : Chart x) :
    t ∈ F.sub I :=
  (Submodule.mem_iInf _).mp ht I
def secsTo (F₁ F₂ : SubSystem S x E) (I : Chart x) :
    F₁.secs →ₗ[S] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mkQ ∘ₗ
    { toFun := fun t => ⟨t.1, mem_sub_of_mem_secs t.2 I⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
def qres (F₁ F₂ : SubSystem S x E) (I J : Chart x) (h : I.1 ⊆ J.1) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) →ₗ[S] (F₁.sub J ⧸ SubSystem.quotSub F₁ F₂ J) :=
  SubSystem.quotRes F₁ F₂ I J h
def toCochain (F₁ F₂ : SubSystem S x E) :=
  cochainOf (R := S) (G := fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (fun I => secsTo F₁ F₂ I)
def sing {a : Fin (N + 1)} (ha : a ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{a}, Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha⟩, Finset.card_singleton a⟩
end Quot
section Compose
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {K' K'' : Type w}
  [Field K'] [Algebra S K'] [Field K''] [Algebra S K''] {N : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {z : Fin (N + 1) → K''}
end Compose
section Red
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
def redHom (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    {j : Fin (N + 1)} (hyj : y j ≠ 0) :
    chartRing k x (singleChart (hxy j hyj)) →ₐ[k] chartRing k y (singleChart hyj) where
  toFun a := ⟨redAt k x y a, (chartRing_sub_locAt hsp hxy (singleChart hyj) a.2).2⟩
  map_one' := Subtype.ext (locAt_one hsp).2
  map_mul' a b := Subtype.ext (locAt_mul hsp (chartRing_sub_locAt hsp hxy (singleChart hyj) a.2).1
    (chartRing_sub_locAt hsp hxy (singleChart hyj) b.2).1).2
  map_zero' := Subtype.ext (locAt_zero hsp).2
  map_add' a b := Subtype.ext (locAt_add hsp (chartRing_sub_locAt hsp hxy (singleChart hyj) a.2).1
    (chartRing_sub_locAt hsp hxy (singleChart hyj) b.2).1).2
  commutes' c := Subtype.ext (locAt_algebraMap hsp c).2
end Red
end RestrLenRestrict
end
end GroundTheory.Heights₂.Heights.Kleiman


