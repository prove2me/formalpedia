-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c9530685-f073-591f-8d4d-051ab6920cf6

import Mathlib
import Theorems.Thm_LinearMap_exists_linearEquiv_extQuot_forall_comp_eq_of_surjective
import Theorems.Thm_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafSectionsLinearRes
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry Opposite

namespace EP3Alg

open LinearMap

section Defs

variable {B : Type u} [CommRing B]

abbrev EQ {M : Type v} [AddCommGroup M] [Module B M] {r : ℕ} (p : (Fin r → B) →ₗ[B] M)
    (N : Type v) [AddCommGroup N] [Module B N] : Type (max u v) :=
  (↥(LinearMap.ker p) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p).subtype)

variable {M : Type v} [AddCommGroup M] [Module B M] {M' : Type v} [AddCommGroup M'] [Module B M']

noncomputable def presBC (B' : Type u) [CommRing B'] [Algebra B B'] [Module B' M'] [IsScalarTower B B' M']
    (μ : M →ₗ[B] M') {r : ℕ} (p : (Fin r → B) →ₗ[B] M) : (Fin r → B') →ₗ[B'] M' :=
  Fintype.linearCombination B' (fun i : Fin r => μ (p (Pi.single i 1)))

theorem presBC_apply (B' : Type u) [CommRing B'] [Algebra B B'] [Module B' M'] [IsScalarTower B B' M']
    (μ : M →ₗ[B] M') {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (v : Fin r → B') :
    presBC B' μ p v = ∑ i, v i • μ (p (Pi.single i 1)) := by
  simp [presBC, Fintype.linearCombination_apply]

theorem presBC_apply_algebraMap (B' : Type u) [CommRing B'] [Algebra B B'] [Module B' M'] [IsScalarTower B B' M']
    (μ : M →ₗ[B] M') {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (v : Fin r → B) :
    presBC B' μ p (fun i => algebraMap B B' (v i)) = μ (p v) := by
  rw [presBC_apply]
  simp_rw [algebraMap_smul, ← map_smul]
  rw [← map_sum, ← map_sum]
  congr 2
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

end Defs

section Linz

variable {B : Type u} [CommRing B] {B' : Type u} [CommRing B'] [Algebra B B']
  {X : Type v} [AddCommGroup X] [Module B' X]

noncomputable def linz {r : ℕ} (g : (Fin r → B) →+ X) : (Fin r → B') →ₗ[B'] X :=
  Fintype.linearCombination B' (fun i : Fin r => g (Pi.single i 1))

theorem single_eq_algebraMap_single {r : ℕ} (i : Fin r) :
    (Pi.single i (1 : B') : Fin r → B') = fun j => algebraMap B B' ((Pi.single i (1 : B) : Fin r → B) j) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single, Function.update, h]

theorem linz_algebraMap {r : ℕ} (g : (Fin r → B) →+ X)
    (hg : ∀ (a : B) (v : Fin r → B), g (a • v) = algebraMap B B' a • g v) (v : Fin r → B) :
    linz g (fun i => algebraMap B B' (v i)) = g v := by
  rw [linz, Fintype.linearCombination_apply]
  simp_rw [← hg]
  rw [← map_sum]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

end Linz

section Phi

variable {B : Type u} [CommRing B] {M N : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

noncomputable def Phi {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) : EQ p₂ N ≃ₗ[B] EQ p₁ N :=
  Classical.choose (LinearMap.exists_linearEquiv_extQuot_forall_comp_eq_of_surjective (N := N) p₁ p₂ hp₁ hp₂)

theorem Phi_mk {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂)
    (g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B)) (hg : p₂ ∘ₗ g = p₁)
    (g' : ↥(LinearMap.ker p₁) →ₗ[B] ↥(LinearMap.ker p₂))
    (hg' : ∀ s : ↥(LinearMap.ker p₁), ((g' s : ↥(LinearMap.ker p₂)) : Fin r₂ → B) = g (s : Fin r₁ → B))
    (δ : ↥(LinearMap.ker p₂) →ₗ[B] N) :
    Phi (N := N) p₁ p₂ hp₁ hp₂ (Submodule.Quotient.mk δ) = Submodule.Quotient.mk (δ ∘ₗ g') :=
  (Classical.choose_spec (LinearMap.exists_linearEquiv_extQuot_forall_comp_eq_of_surjective (N := N) p₁ p₂ hp₁ hp₂))
    g hg g' hg' δ

theorem exists_lift {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₂ : Function.Surjective p₂) : ∃ g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B), p₂ ∘ₗ g = p₁ := by
  classical
  choose σ hσ using fun i : Fin r₁ => hp₂ (p₁ (Pi.basisFun B (Fin r₁) i))
  refine ⟨(Pi.basisFun B (Fin r₁)).constr B σ, (Pi.basisFun B (Fin r₁)).ext fun i => ?_⟩
  rw [LinearMap.comp_apply, Module.Basis.constr_basis, hσ]

def kerLift {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B)) (hg : p₂ ∘ₗ g = p₁) :
    ↥(LinearMap.ker p₁) →ₗ[B] ↥(LinearMap.ker p₂) :=
  g.restrict (p := LinearMap.ker p₁) (q := LinearMap.ker p₂) fun x hx => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hg]; exact hx

theorem kerLift_coe {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B)) (hg : p₂ ∘ₗ g = p₁) (s : ↥(LinearMap.ker p₁)) :
    ((kerLift p₁ p₂ g hg s : ↥(LinearMap.ker p₂)) : Fin r₂ → B) = g (s : Fin r₁ → B) := rfl

theorem Phi_mk' {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂)
    (g : (Fin r₁ → B) →ₗ[B] (Fin r₂ → B)) (hg : p₂ ∘ₗ g = p₁) (δ : ↥(LinearMap.ker p₂) →ₗ[B] N) :
    Phi (N := N) p₁ p₂ hp₁ hp₂ (Submodule.Quotient.mk δ) = Submodule.Quotient.mk (δ ∘ₗ kerLift p₁ p₂ g hg) :=
  Phi_mk p₁ p₂ hp₁ hp₂ g hg (kerLift p₁ p₂ g hg) (fun _ => rfl) δ

theorem Phi_trans {r₁ r₂ r₃ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M) (p₃ : (Fin r₃ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) (hp₃ : Function.Surjective p₃) (x : EQ p₃ N) :
    Phi (N := N) p₁ p₂ hp₁ hp₂ (Phi (N := N) p₂ p₃ hp₂ hp₃ x) = Phi (N := N) p₁ p₃ hp₁ hp₃ x := by
  obtain ⟨g, hg⟩ := exists_lift p₁ p₂ hp₂
  obtain ⟨h, hh⟩ := exists_lift p₂ p₃ hp₃
  have hhg : p₃ ∘ₗ (h ∘ₗ g) = p₁ := by rw [← LinearMap.comp_assoc, hh, hg]
  induction x using Submodule.Quotient.induction_on with
  | H δ =>
    rw [Phi_mk' p₂ p₃ hp₂ hp₃ h hh, Phi_mk' p₁ p₂ hp₁ hp₂ g hg, Phi_mk' p₁ p₃ hp₁ hp₃ (h ∘ₗ g) hhg]
    rfl

theorem Phi_self {r₁ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (hp₁ : Function.Surjective p₁) (x : EQ p₁ N) :
    Phi (N := N) p₁ p₁ hp₁ hp₁ x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H δ =>
    rw [Phi_mk' p₁ p₁ hp₁ hp₁ LinearMap.id (LinearMap.comp_id p₁)]
    rfl

theorem Phi_Phi {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) (x : EQ p₁ N) :
    Phi (N := N) p₁ p₂ hp₁ hp₂ (Phi (N := N) p₂ p₁ hp₂ hp₁ x) = x := by
  rw [Phi_trans, Phi_self]

theorem Phi_symm_apply {r₁ r₂ : ℕ} (p₁ : (Fin r₁ → B) →ₗ[B] M) (p₂ : (Fin r₂ → B) →ₗ[B] M)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) (x : EQ p₁ N) :
    (Phi (N := N) p₁ p₂ hp₁ hp₂).symm x = Phi (N := N) p₂ p₁ hp₂ hp₁ x := by
  apply (Phi (N := N) p₁ p₂ hp₁ hp₂).injective
  rw [LinearEquiv.apply_symm_apply, Phi_Phi]

end Phi

section T

variable {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
  {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
  {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
  {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']

theorem presBC_surjective (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p) : Function.Surjective (presBC B' μ p) :=
  (LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective μ hμ μ hμ p hp (presBC B' μ p)
    (presBC_apply_algebraMap B' μ p)).1

noncomputable def gBC (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p) :
    ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker (presBC B' μ p)) :=
  Classical.choose (LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective μ hμ ν hν p hp (presBC B' μ p)
    (presBC_apply_algebraMap B' μ p)).2

theorem gBC_coe (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    (s : ↥(LinearMap.ker p)) (i : Fin r) :
    ((gBC μ hμ ν hν p hp s : ↥(LinearMap.ker (presBC B' μ p))) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i) :=
  (Classical.choose_spec (Classical.choose_spec (LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective μ hμ ν hν p hp
    (presBC B' μ p) (presBC_apply_algebraMap B' μ p)).2)).1 s i

noncomputable def Tmap (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p) :
    EQ p N →ₗ[B] EQ (presBC B' μ p) N' :=
  Classical.choose (Classical.choose_spec (LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective μ hμ ν hν p hp
    (presBC B' μ p) (presBC_apply_algebraMap B' μ p)).2)

theorem Tmap_isBaseChange (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p) :
    IsBaseChange B' (Tmap μ hμ ν hν p hp) :=
  (Classical.choose_spec (Classical.choose_spec (LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective μ hμ ν hν p hp
    (presBC B' μ p) (presBC_apply_algebraMap B' μ p)).2)).2.1

theorem Tmap_exists_compat (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    (δ : ↥(LinearMap.ker p) →ₗ[B] N) :
    ∃ δ' : ↥(LinearMap.ker (presBC B' μ p)) →ₗ[B'] N', ∀ s : ↥(LinearMap.ker p), δ' (gBC μ hμ ν hν p hp s) = ν (δ s) :=
  (Classical.choose_spec (Classical.choose_spec (LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective μ hμ ν hν p hp
    (presBC B' μ p) (presBC_apply_algebraMap B' μ p)).2)).2.2.1 δ

theorem Tmap_mk (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    (δ : ↥(LinearMap.ker p) →ₗ[B] N) (δ' : ↥(LinearMap.ker (presBC B' μ p)) →ₗ[B'] N')
    (h : ∀ s : ↥(LinearMap.ker p), δ' (gBC μ hμ ν hν p hp s) = ν (δ s)) :
    Tmap μ hμ ν hν p hp (Submodule.Quotient.mk δ) = Submodule.Quotient.mk δ' :=
  (Classical.choose_spec (Classical.choose_spec (LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective μ hμ ν hν p hp
    (presBC B' μ p) (presBC_apply_algebraMap B' μ p)).2)).2.2.2 δ δ' h

end T

section Rho

variable {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
  {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
  {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
  {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']

noncomputable def rho (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p') :
    EQ p N →ₗ[B] EQ p' N' :=
  ((Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp').symm.toLinearMap.restrictScalars B) ∘ₗ
    Tmap μ hμ ν hν p hp

theorem Phi_rho (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p') (x : EQ p N) :
    Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp' (rho μ hμ ν hν p hp p' hp' x) =
      Tmap μ hμ ν hν p hp x := by
  show Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp'
    ((Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp').symm (Tmap μ hμ ν hν p hp x)) = _
  rw [LinearEquiv.apply_symm_apply]

theorem rho_mk (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p')
    (g : (Fin r → B) →+ (Fin r' → B'))
    (hg : ∀ (a : B) (v : Fin r → B), g (a • v) = algebraMap B B' a • g v)
    (hgp : ∀ v : Fin r → B, p' (g v) = μ (p v))
    (δ : ↥(LinearMap.ker p) →ₗ[B] N) (δ' : ↥(LinearMap.ker p') →ₗ[B'] N')
    (hδ : ∀ (s : ↥(LinearMap.ker p)) (hs : g (s : Fin r → B) ∈ LinearMap.ker p'), δ' ⟨g (s : Fin r → B), hs⟩ = ν (δ s)) :
    rho μ hμ ν hν p hp p' hp' (Submodule.Quotient.mk δ) = Submodule.Quotient.mk δ' := by
  classical
  let G : (Fin r → B') →ₗ[B'] (Fin r' → B') := linz g
  have hG : ∀ v : Fin r → B, G (fun i => algebraMap B B' (v i)) = g v := linz_algebraMap g hg
  have hGp : p' ∘ₗ G = presBC B' μ p := by
    refine (Pi.basisFun B' (Fin r)).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, single_eq_algebraMap_single (B := B) i, hG,
      presBC_apply_algebraMap, hgp]
  apply (Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp').injective
  rw [Phi_rho, Phi_mk' _ _ _ _ G hGp]
  apply Tmap_mk
  intro s
  have hcoe : ((kerLift (presBC B' μ p) p' G hGp (gBC μ hμ ν hν p hp s) : ↥(LinearMap.ker p')) : Fin r' → B')
      = g (s : Fin r → B) := by
    rw [kerLift_coe]
    have : ((gBC μ hμ ν hν p hp s : ↥(LinearMap.ker (presBC B' μ p))) : Fin r → B')
        = fun i => algebraMap B B' ((s : Fin r → B) i) := funext (gBC_coe μ hμ ν hν p hp s)
    rw [this, hG]
  have hs : g (s : Fin r → B) ∈ LinearMap.ker p' :=
    hcoe ▸ (kerLift (presBC B' μ p) p' G hGp (gBC μ hμ ν hν p hp s)).2
  rw [LinearMap.comp_apply]
  have : kerLift (presBC B' μ p) p' G hGp (gBC μ hμ ν hν p hp s) = ⟨g (s : Fin r → B), hs⟩ := Subtype.ext hcoe
  rw [this, hδ s hs]

theorem rho_smul (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p') (b : B) (x : EQ p N) :
    rho μ hμ ν hν p hp p' hp' (b • x) = algebraMap B B' b • rho μ hμ ν hν p hp p' hp' x := by
  rw [map_smul, algebraMap_smul]

theorem Tmap_Phi (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r₂ : ℕ} (p₂ : (Fin r₂ → B) →ₗ[B] M) (hp₂ : Function.Surjective p₂) (y : EQ p₂ N) :
    Tmap μ hμ ν hν p hp (Phi (N := N) p p₂ hp hp₂ y) =
      Phi (N := N') (presBC B' μ p) (presBC B' μ p₂) (presBC_surjective μ hμ p hp) (presBC_surjective μ hμ p₂ hp₂)
        (Tmap μ hμ ν hν p₂ hp₂ y) := by
  classical
  obtain ⟨g, hg⟩ := exists_lift p p₂ hp₂

  let g'' : (Fin r → B) →+ (Fin r₂ → B') :=
    { toFun := fun v j => algebraMap B B' (g v j)
      map_zero' := by ext j; simp
      map_add' := fun v w => by ext j; simp }
  have hg'' : ∀ (a : B) (v : Fin r → B), g'' (a • v) = algebraMap B B' a • g'' v := by
    intro a v; ext j
    show algebraMap B B' (g (a • v) j) = algebraMap B B' a * algebraMap B B' (g v j)
    rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  let G : (Fin r → B') →ₗ[B'] (Fin r₂ → B') := linz g''
  have hG : ∀ v : Fin r → B, G (fun i => algebraMap B B' (v i)) = fun j => algebraMap B B' (g v j) :=
    linz_algebraMap g'' hg''
  have hGp : presBC B' μ p₂ ∘ₗ G = presBC B' μ p := by
    refine (Pi.basisFun B' (Fin r)).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, single_eq_algebraMap_single (B := B) i, hG,
      presBC_apply_algebraMap, presBC_apply_algebraMap]
    exact congrArg μ (LinearMap.congr_fun hg (Pi.single i 1))
  induction y using Submodule.Quotient.induction_on with
  | H δ₂ =>
    obtain ⟨δ₂', hδ₂'⟩ := Tmap_exists_compat μ hμ ν hν p₂ hp₂ δ₂
    rw [Phi_mk' p p₂ hp hp₂ g hg, Tmap_mk μ hμ ν hν p₂ hp₂ δ₂ δ₂' hδ₂',
      Phi_mk' (N := N') (presBC B' μ p) (presBC B' μ p₂) _ _ G hGp]
    apply Tmap_mk
    intro s
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hδ₂']
    congr 1
    apply Subtype.ext
    rw [kerLift_coe]
    have h1 : ((gBC μ hμ ν hν p hp s : ↥(LinearMap.ker (presBC B' μ p))) : Fin r → B')
        = fun i => algebraMap B B' ((s : Fin r → B) i) := funext (gBC_coe μ hμ ν hν p hp s)
    have h2 : ((gBC μ hμ ν hν p₂ hp₂ (kerLift p p₂ g hg s) : ↥(LinearMap.ker (presBC B' μ p₂))) : Fin r₂ → B')
        = fun j => algebraMap B B' ((kerLift p p₂ g hg s : Fin r₂ → B) j) :=
      funext (gBC_coe μ hμ ν hν p₂ hp₂ (kerLift p p₂ g hg s))
    rw [h1, hG, h2]
    rfl

theorem rho_Phi (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p')
    {r₂ : ℕ} (p₂ : (Fin r₂ → B) →ₗ[B] M) (hp₂ : Function.Surjective p₂) (y : EQ p₂ N) :
    rho μ hμ ν hν p hp p' hp' (Phi (N := N) p p₂ hp hp₂ y) = rho μ hμ ν hν p₂ hp₂ p' hp' y := by
  apply (Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp').injective
  rw [Phi_rho, Tmap_Phi μ hμ ν hν p hp p₂ hp₂ y,
    ← Phi_trans (N := N') (presBC B' μ p) (presBC B' μ p₂) p' (presBC_surjective μ hμ p hp) (presBC_surjective μ hμ p₂ hp₂) hp',
    Phi_rho]

theorem Phi_rho_eq (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p')
    {r₂' : ℕ} (p₂' : (Fin r₂' → B') →ₗ[B'] M') (hp₂' : Function.Surjective p₂') (x : EQ p N) :
    Phi (N := N') p' p₂' hp' hp₂' (rho μ hμ ν hν p hp p₂' hp₂' x) = rho μ hμ ν hν p hp p' hp' x := by
  apply (Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp').injective
  rw [Phi_trans, Phi_rho, Phi_rho]

end Rho

section Comp

variable {B : Type u} [CommRing B] [IsNoetherianRing B]
  {B' : Type u} [CommRing B'] [IsNoetherianRing B'] [Algebra B B'] [Module.Flat B B']
  {B'' : Type u} [CommRing B''] [Algebra B B''] [Algebra B' B''] [IsScalarTower B B' B'']
  [Module.Flat B B''] [Module.Flat B' B'']
  {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
  {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
  {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']
  {M'' : Type v} [AddCommGroup M''] [Module B M''] [Module B' M''] [Module B'' M'']
  [IsScalarTower B B'' M''] [IsScalarTower B' B'' M'']
  {N'' : Type v} [AddCommGroup N''] [Module B N''] [Module B' N''] [Module B'' N'']
  [IsScalarTower B B'' N''] [IsScalarTower B' B'' N'']

theorem rho_comp
    (μ₁₂ : M →ₗ[B] M') (hμ₁₂ : IsBaseChange B' μ₁₂) (ν₁₂ : N →ₗ[B] N') (hν₁₂ : IsBaseChange B' ν₁₂)
    (μ₂₃ : M' →ₗ[B'] M'') (hμ₂₃ : IsBaseChange B'' μ₂₃) (ν₂₃ : N' →ₗ[B'] N'') (hν₂₃ : IsBaseChange B'' ν₂₃)
    (μ₁₃ : M →ₗ[B] M'') (hμ₁₃ : IsBaseChange B'' μ₁₃) (ν₁₃ : N →ₗ[B] N'') (hν₁₃ : IsBaseChange B'' ν₁₃)
    (hμ : ∀ x, μ₁₃ x = μ₂₃ (μ₁₂ x)) (hν : ∀ x, ν₁₃ x = ν₂₃ (ν₁₂ x))
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p')
    {r'' : ℕ} (p'' : (Fin r'' → B'') →ₗ[B''] M'') (hp'' : Function.Surjective p'') (x : EQ p N) :
    rho μ₂₃ hμ₂₃ ν₂₃ hν₂₃ p' hp' p'' hp'' (rho μ₁₂ hμ₁₂ ν₁₂ hν₁₂ p hp p' hp' x) =
      rho μ₁₃ hμ₁₃ ν₁₃ hν₁₃ p hp p'' hp'' x := by
  classical
  have hP12 := presBC_surjective μ₁₂ hμ₁₂ p hp
  have h1 : rho μ₁₂ hμ₁₂ ν₁₂ hν₁₂ p hp p' hp' x =
      Phi (N := N') p' (presBC B' μ₁₂ p) hp' hP12 (Tmap μ₁₂ hμ₁₂ ν₁₂ hν₁₂ p hp x) :=
    Phi_symm_apply _ _ _ _ _
  rw [h1, rho_Phi]
  apply (Phi (N := N'') (presBC B'' μ₁₃ p) p'' (presBC_surjective μ₁₃ hμ₁₃ p hp) hp'').injective
  rw [Phi_rho, ← Phi_trans (N := N'') (presBC B'' μ₁₃ p) (presBC B'' μ₂₃ (presBC B' μ₁₂ p)) p''
    (presBC_surjective μ₁₃ hμ₁₃ p hp) (presBC_surjective μ₂₃ hμ₂₃ _ hP12) hp'', Phi_rho]

  have hQ : presBC B'' μ₂₃ (presBC B' μ₁₂ p) ∘ₗ LinearMap.id = presBC B'' μ₁₃ p := by
    rw [LinearMap.comp_id]
    refine (Pi.basisFun B'' (Fin r)).ext fun i => ?_
    rw [Pi.basisFun_apply, single_eq_algebraMap_single (B := B') i, presBC_apply_algebraMap,
      single_eq_algebraMap_single (B := B) i, presBC_apply_algebraMap]
    have : (fun j => algebraMap B' B'' (algebraMap B B' ((Pi.single i (1 : B) : Fin r → B) j)))
        = fun j => algebraMap B B'' ((Pi.single i (1 : B) : Fin r → B) j) := by
      ext j; rw [← IsScalarTower.algebraMap_apply]
    rw [this, presBC_apply_algebraMap, hμ]
  induction x using Submodule.Quotient.induction_on with
  | H δ =>
    obtain ⟨δ', hδ'⟩ := Tmap_exists_compat μ₁₂ hμ₁₂ ν₁₂ hν₁₂ p hp δ
    obtain ⟨δ'', hδ''⟩ := Tmap_exists_compat μ₂₃ hμ₂₃ ν₂₃ hν₂₃ (presBC B' μ₁₂ p) hP12 δ'
    rw [Tmap_mk μ₁₂ hμ₁₂ ν₁₂ hν₁₂ p hp δ δ' hδ', Tmap_mk μ₂₃ hμ₂₃ ν₂₃ hν₂₃ _ hP12 δ' δ'' hδ'',
      Phi_mk' (N := N'') _ _ _ _ LinearMap.id hQ]
    symm
    apply Tmap_mk
    intro s
    rw [LinearMap.comp_apply, hν, ← hδ', ← hδ'']
    congr 1
    apply Subtype.ext
    rw [kerLift_coe, LinearMap.id_apply]
    funext j
    rw [gBC_coe, gBC_coe, gBC_coe, ← IsScalarTower.algebraMap_apply]

end Comp

theorem rho_isLocalizedModule {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B']
    [Module.Flat B B'] (S : Submonoid B) [IsLocalization S B']
    {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p') :
    IsLocalizedModule S (rho μ hμ ν hν p hp p' hp') := by
  haveI hT : IsLocalizedModule S (Tmap μ hμ ν hν p hp) :=
    (isLocalizedModule_iff_isBaseChange S B' (Tmap μ hμ ν hν p hp)).mpr (Tmap_isBaseChange μ hμ ν hν p hp)
  exact IsLocalizedModule.of_linearEquiv S (Tmap μ hμ ν hν p hp)
    ((Phi (N := N') (presBC B' μ p) p' (presBC_surjective μ hμ p hp) hp').symm.restrictScalars B)

theorem finite_EQ {B : Type u} [CommRing B] [IsNoetherianRing B] {M N : Type v} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] [Module.Finite B N] {r : ℕ} (p : (Fin r → B) →ₗ[B] M) :
    Module.Finite B ((↥(LinearMap.ker p) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p).subtype)) := by

  haveI : Module.Finite B ↥(LinearMap.ker p) := Module.Finite.of_fg (IsNoetherian.noetherian _)
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' B ↥(LinearMap.ker p)
  haveI : Module.Finite B ((Fin n → B) →ₗ[B] N) := Module.Finite.linearMap B B _ _
  haveI : Module.Finite B (↥(LinearMap.ker p) →ₗ[B] N) := by
    refine Module.Finite.of_injective (LinearMap.lcomp B N π) fun f g hfg => ?_
    ext s
    obtain ⟨v, rfl⟩ := hπ s
    exact congrArg (fun φ : (Fin n → B) →ₗ[B] N => φ v) hfg
  exact Module.Finite.quotient B _

theorem flat_of_affineOpens_le {P : Scheme.{u}} (W W' : P.affineOpens) (h : W'.1 ≤ W.1) :
    letI := (P.presheaf.map (homOfLE h).op).hom.toAlgebra
    Module.Flat Γ(P, W.1) Γ(P, W'.1) := by
  have e : W'.1 ≤ (𝟙 P : P ⟶ P) ⁻¹ᵁ W.1 := h
  have h1 : RingHom.Flat ((𝟙 P : P ⟶ P).appLE W.1 W'.1 e).hom :=
    HasRingHomProperty.appLE @Flat (f := 𝟙 P) inferInstance W W' e
  have h2 : (𝟙 P : P ⟶ P).appLE W.1 W'.1 e = P.presheaf.map (homOfLE h).op := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rfl
  rw [h2] at h1
  exact h1

end EP3Alg

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace EP3Geo

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}

abbrev RW (W : P.affineOpens) : Type u := ↑(P.presheaf.obj (op W.1))

theorem noeth [IsLocallyNoetherian P] (W : P.affineOpens) : IsNoetherianRing (RW W) :=
  IsLocallyNoetherian.component_noetherian W

theorem exists_pres (H : OModulePresheaf q) (hHc : H.IsCoherent) (W : P.affineOpens) :
    ∃ (n : ℕ) (f : (Fin n → RW W) →ₗ[RW W] H.obj W.1), Function.Surjective f :=
  @Module.Finite.exists_fin' (RW W) (H.obj W.1) _ _ _ (hHc W)

noncomputable def rk (H : OModulePresheaf q) (hHc : H.IsCoherent) (W : P.affineOpens) : ℕ :=
  (exists_pres H hHc W).choose

noncomputable def pres (H : OModulePresheaf q) (hHc : H.IsCoherent) (W : P.affineOpens) :
    (Fin (rk H hHc W) → RW W) →ₗ[RW W] H.obj W.1 :=
  (exists_pres H hHc W).choose_spec.choose

theorem pres_surjective (H : OModulePresheaf q) (hHc : H.IsCoherent) (W : P.affineOpens) :
    Function.Surjective (pres H hHc W) :=
  (exists_pres H hHc W).choose_spec.choose_spec

abbrev E (H : OModulePresheaf q) (hHc : H.IsCoherent) (K : OModulePresheaf q) (W : P.affineOpens) : Type u :=
  EP3Alg.EQ (pres H hHc W) (K.obj W.1)

@[reducible] noncomputable def modA (H : OModulePresheaf q) (hHc : H.IsCoherent) (K : OModulePresheaf q) (W : P.affineOpens) :
    Module A (E H hHc K W) :=
  Module.compHom (E H hHc K W) (Scheme.TwoAffineOpenCover.algebraOfHom q W.1).algebraMap

@[reducible] noncomputable def algOf {W W' : P.affineOpens} (h : W'.1 ≤ W.1) : Algebra (RW W) (RW W') :=
  (P.presheaf.map (homOfLE h).op).hom.toAlgebra

@[reducible] noncomputable def modOf (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    Module (RW W) (F.obj W'.1) :=
  Module.compHom (F.obj W'.1) (P.presheaf.map (homOfLE h).op).hom

theorem towOf (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h; letI := modOf F h
    IsScalarTower (RW W) (RW W') (F.obj W'.1) :=
  letI := algOf (P := P) h; letI := modOf F h
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable def mu (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := modOf F h
    F.obj W.1 →ₗ[RW W] F.obj W'.1 :=
  F.resₗ h

theorem mu_apply (F : OModulePresheaf q) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) (x : F.obj W.1) :
    letI := modOf F h
    mu F h x = F.res h x := rfl

theorem flatOf {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h
    Module.Flat (RW W) (RW W') :=
  EP3Alg.flat_of_affineOpens_le W W' h

theorem mu_isBaseChange (F : OModulePresheaf q) (hF : F.IsQuasicoherent) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h; letI := modOf F h; letI := towOf F h
    IsBaseChange (RW W') (mu F h) := by
  letI := algOf (P := P) h; letI := modOf F h; letI := towOf F h
  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res F hF W W' h
  exact IsBaseChange.of_equiv β hβ

theorem map_refl (W : P.Opens) (a : Γ(P, W)) : (P.presheaf.map (homOfLE (le_refl W)).op).hom a = a := by
  have : (homOfLE (le_refl W)).op = 𝟙 (op W) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, CategoryTheory.Functor.map_id]; rfl

theorem map_map {W₁ W₂ W₃ : P.Opens} (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃) (a : Γ(P, W₃)) :
    (P.presheaf.map (homOfLE h₁).op).hom ((P.presheaf.map (homOfLE h₂).op).hom a) =
      (P.presheaf.map (homOfLE (h₁.trans h₂)).op).hom a := by
  show ((P.presheaf.map (homOfLE h₂).op) ≫ P.presheaf.map (homOfLE h₁).op).hom a = _
  rw [← Functor.map_comp]; rfl

theorem map_algebraMapA {W W' : P.Opens} (h : W' ≤ W) (r : A) :
    (P.presheaf.map (homOfLE h).op).hom ((Scheme.TwoAffineOpenCover.algebraOfHom q W).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom q W').algebraMap r := by
  show ((q.appLE ⊤ W le_top) ≫ P.presheaf.map (homOfLE h).op).hom _ = (q.appLE ⊤ W' le_top).hom _
  rw [Scheme.Hom.appLE_map]

noncomputable def resΓ [IsLocallyNoetherian P] (H : OModulePresheaf q) (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent)
    (K : OModulePresheaf q) (hKq : K.IsQuasicoherent) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
    E H hHc K W →ₗ[RW W] E H hHc K W' :=
  letI := algOf (P := P) h; letI := modOf H h; letI := towOf H h; letI := modOf K h; letI := towOf K h
  haveI := flatOf (P := P) h; haveI := noeth W
  EP3Alg.rho (mu H h) (mu_isBaseChange H hHq h) (mu K h) (mu_isBaseChange K hKq h)
    (pres H hHc W) (pres_surjective H hHc W) (pres H hHc W') (pres_surjective H hHc W')

theorem resΓ_def [IsLocallyNoetherian P] (H : OModulePresheaf q) (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent)
    (K : OModulePresheaf q) (hKq : K.IsQuasicoherent) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
    resΓ H hHc hHq K hKq h =
      (letI := modOf H h; letI := towOf H h
       haveI := flatOf (P := P) h; haveI := noeth W
       EP3Alg.rho (mu H h) (mu_isBaseChange H hHq h) (mu K h) (mu_isBaseChange K hKq h)
        (pres H hHc W) (pres_surjective H hHc W) (pres H hHc W') (pres_surjective H hHc W')) := rfl

private noncomputable def _root_.EP3Geo.res [IsLocallyNoetherian P] (H : OModulePresheaf q) (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent)
    (K : OModulePresheaf q) (hKq : K.IsQuasicoherent) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) :
    letI := modA H hHc K W; letI := modA H hHc K W'
    E H hHc K W →ₗ[A] E H hHc K W' :=
  letI := modA H hHc K W; letI := modA H hHc K W'
  letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
  { toFun := resΓ H hHc hHq K hKq h
    map_add' := map_add _
    map_smul' := fun r x => by
      show resΓ H hHc hHq K hKq h ((Scheme.TwoAffineOpenCover.algebraOfHom q W.1).algebraMap r • x) =
        (Scheme.TwoAffineOpenCover.algebraOfHom q W'.1).algebraMap r • resΓ H hHc hHq K hKq h x
      rw [map_smul, ← algebraMap_smul (RW W') ((Scheme.TwoAffineOpenCover.algebraOfHom q W.1).algebraMap r),
        ← map_algebraMapA h r]
      rfl }

p2m_export "EP3Geo" "res"
theorem res_apply [IsLocallyNoetherian P] (H : OModulePresheaf q) (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent)
    (K : OModulePresheaf q) (hKq : K.IsQuasicoherent) {W W' : P.affineOpens} (h : W'.1 ≤ W.1) (x : E H hHc K W) :
    letI := modA H hHc K W; letI := modA H hHc K W'
    letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
    res H hHc hHq K hKq h x = resΓ H hHc hHq K hKq h x := rfl

section Feed
variable [IsLocallyNoetherian P] (H : OModulePresheaf q) (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent)
  (K : OModulePresheaf q) (hKc : K.IsCoherent) (hKq : K.IsQuasicoherent)

theorem resΓ_smul {W W' : P.affineOpens} (h : W'.1 ≤ W.1) (a : RW W) (x : E H hHc K W) :
    letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
    resΓ H hHc hHq K hKq h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • resΓ H hHc hHq K hKq h x := by
  letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
  rw [map_smul, ← algebraMap_smul (RW W') a]
  rfl

theorem resΓ_refl (W : P.affineOpens) (x : E H hHc K W) :
    letI := algOf (P := P) (le_refl W.1); letI := modOf K (le_refl W.1); letI := towOf K (le_refl W.1)
    resΓ H hHc hHq K hKq (le_refl W.1) x = x := by
  obtain ⟨δ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  unfold resΓ

  exact @EP3Alg.rho_mk (RW W) _ (noeth W) (RW W) _ (algOf (P := P) (le_refl W.1)) (flatOf (P := P) (le_refl W.1))
    (H.obj W.1) _ _ (K.obj W.1) _ _ (H.obj W.1) _ (modOf H (le_refl W.1)) _ (towOf H (le_refl W.1))
    (K.obj W.1) _ (modOf K (le_refl W.1)) _ (towOf K (le_refl W.1))
    (mu H (le_refl W.1)) (mu_isBaseChange H hHq _) (mu K (le_refl W.1)) (mu_isBaseChange K hKq _)
    _ (pres H hHc W) (pres_surjective H hHc W) _ (pres H hHc W) (pres_surjective H hHc W)
    (AddMonoidHom.id _)
    (fun a v => by
      show a • v = (P.presheaf.map (homOfLE (le_refl W.1)).op).hom a • v
      rw [map_refl])
    (fun v => by
      show pres H hHc W v = H.res (le_refl W.1) (pres H hHc W v)
      rw [H.res_refl_apply])
    δ δ
    (fun s hs => by
      show δ ⟨(s : Fin (rk H hHc W) → RW W), hs⟩ = K.res (le_refl W.1) (δ s)
      rw [K.res_refl_apply])

theorem resΓ_comp {W W' W'' : P.affineOpens} (h : W''.1 ≤ W'.1) (h' : W'.1 ≤ W.1) (x : E H hHc K W) :
    (letI := algOf (P := P) (h.trans h'); letI := modOf K (h.trans h'); letI := towOf K (h.trans h')
     resΓ H hHc hHq K hKq (h.trans h') x) =
    (letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
     letI := algOf (P := P) h'; letI := modOf K h'; letI := towOf K h'
     resΓ H hHc hHq K hKq h (resΓ H hHc hHq K hKq h' x)) := by

  letI i12 := algOf (P := P) h'; letI i23 := algOf (P := P) h; letI i13 := algOf (P := P) (h.trans h')
  letI mH12 := modOf H h'; letI mH23 := modOf H h; letI mH13 := modOf H (h.trans h')
  letI mK12 := modOf K h'; letI mK23 := modOf K h; letI mK13 := modOf K (h.trans h')
  letI := towOf H h'; letI := towOf H h; letI := towOf H (h.trans h')
  letI := towOf K h'; letI := towOf K h; letI := towOf K (h.trans h')
  haveI : IsScalarTower (RW W) (RW W') (RW W'') :=
    IsScalarTower.of_algebraMap_eq fun b => (map_map h h' b).symm
  haveI := flatOf (P := P) h'; haveI := flatOf (P := P) h; haveI := flatOf (P := P) (h.trans h')
  haveI := noeth W; haveI := noeth W'
  rw [resΓ_def, resΓ_def, resΓ_def]
  exact (EP3Alg.rho_comp (mu H h') (mu_isBaseChange H hHq h') (mu K h') (mu_isBaseChange K hKq h')
    (mu H h) (mu_isBaseChange H hHq h) (mu K h) (mu_isBaseChange K hKq h)
    (mu H (h.trans h')) (mu_isBaseChange H hHq (h.trans h')) (mu K (h.trans h')) (mu_isBaseChange K hKq (h.trans h'))
    (fun y => (H.res_res h h' y).symm) (fun y => (K.res_res h h' y).symm)
    (pres H hHc W) (pres_surjective H hHc W) (pres H hHc W') (pres_surjective H hHc W')
    (pres H hHc W'') (pres_surjective H hHc W'') x).symm

theorem resΓ_isLocalizedModule (W : P.affineOpens) (g : RW W) {Wg : P.affineOpens} (hWg : Wg.1 = P.basicOpen g) :
    letI := algOf (P := P) (hWg.trans_le (P.basicOpen_le g)); letI := modOf K (hWg.trans_le (P.basicOpen_le g))
    letI := towOf K (hWg.trans_le (P.basicOpen_le g))
    IsLocalizedModule (Submonoid.powers g) (resΓ H hHc hHq K hKq (hWg.trans_le (P.basicOpen_le g))) := by
  obtain ⟨Ug, hUg⟩ := Wg
  suffices key : ∀ h' : (⟨Ug, hUg⟩ : P.affineOpens).1 ≤ W.1,
      (letI := algOf (P := P) h'; letI := modOf K h'; letI := towOf K h'
       IsLocalizedModule (Submonoid.powers g) (resΓ H hHc hHq K hKq h')) from key _
  intro h'
  change Ug = P.basicOpen g at hWg
  subst hWg
  have h : P.basicOpen g ≤ W.1 := h'
  letI := algOf (P := P) (W' := ⟨P.basicOpen g, hUg⟩) h; letI := modOf H (W' := ⟨P.basicOpen g, hUg⟩) h
  letI := towOf H (W' := ⟨P.basicOpen g, hUg⟩) h
  letI := modOf K (W' := ⟨P.basicOpen g, hUg⟩) h; letI := towOf K (W' := ⟨P.basicOpen g, hUg⟩) h
  haveI := flatOf (P := P) (W' := ⟨P.basicOpen g, hUg⟩) h; haveI := noeth W
  haveI : IsLocalization.Away g (RW ⟨P.basicOpen g, hUg⟩) := W.2.isLocalization_basicOpen g
  rw [resΓ_def]
  exact EP3Alg.rho_isLocalizedModule (Submonoid.powers g) (mu H h) (mu_isBaseChange H hHq h) (mu K h) (mu_isBaseChange K hKq h)
    (pres H hHc W) (pres_surjective H hHc W) (pres H hHc ⟨P.basicOpen g, hUg⟩) (pres_surjective H hHc _)

theorem finite_E (hKc : K.IsCoherent) (W : P.affineOpens) : Module.Finite (RW W) (E H hHc K W) := by
  haveI := noeth W
  haveI : Module.Finite (RW W) (K.obj W.1) := hKc W
  exact EP3Alg.finite_EQ (pres H hHc W)

end Feed

section Main
attribute [local instance] modA

theorem main [IsLocallyNoetherian P] (H K : OModulePresheaf q)
    (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent) (hKc : K.IsCoherent) (hKq : K.IsQuasicoherent) :
    ∃ (X : OModulePresheaf q)
      (e : ∀ W : P.affineOpens, letI := modA H hHc K W; X.obj W.1 ≃ₗ[A] E H hHc K W),
      X.IsCoherent ∧ X.IsQuasicoherent ∧
      (∀ (W : P.affineOpens) (a : RW W) (x : X.obj W.1), e W (a • x) = a • e W x) ∧
      (∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1) (x : X.obj W.1),
        letI := algOf (P := P) h; letI := modOf K h; letI := towOf K h
        e W' (X.res h x) = resΓ H hHc hHq K hKq h (e W x)) := by
  classical

  let B : Set P.affineOpens := Set.univ
  have hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B := fun _ _ _ _ => Set.mem_univ _
  have hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1 := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := x) (U := ⊤) trivial
    exact ⟨⟨U, hU⟩, Set.mem_univ _, hxU⟩

  haveI instT : ∀ W : ↥B, @IsScalarTower A (RW W.1) (E H hHc K W.1)
      (Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1).toSMul inferInstance
      (letI := modA H hHc K W.1; (inferInstance : SMul A (E H hHc K W.1))) := fun W =>
    @IsScalarTower.mk A (RW W.1) (E H hHc K W.1) (Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1).toSMul inferInstance
      (letI := modA H hHc K W.1; (inferInstance : SMul A (E H hHc K W.1)))
      fun r a x => mul_smul ((Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1).algebraMap r) a x

  have hqc : ∀ (W Wg : ↥B) (g : RW W.1) (hWg : Wg.1.1 = P.basicOpen g),
      (∀ y : E H hHc K Wg.1, ∃ (n : ℕ) (x : E H hHc K W.1),
          res H hHc hHq K hKq (hWg.trans_le (P.basicOpen_le g)) x =
            (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
      (∀ x : E H hHc K W.1, res H hHc hHq K hKq (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0) := by
    intro W Wg g hWg
    have h₀ : Wg.1.1 ≤ W.1.1 := hWg.trans_le (P.basicOpen_le g)
    letI := algOf (P := P) h₀; letI := modOf K h₀; letI := towOf K h₀
    haveI hI := resΓ_isLocalizedModule H hHc hHq K hKq W.1 g (Wg := Wg.1) hWg
    refine ⟨fun y => ?_, fun x hx => ?_⟩
    · obtain ⟨⟨x, ⟨s, hs⟩⟩, hxy⟩ := IsLocalizedModule.surj (Submonoid.powers g) (resΓ H hHc hHq K hKq h₀) y
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
      refine ⟨n, x, ?_⟩
      show resΓ H hHc hHq K hKq h₀ x = _
      rw [← hxy, Submonoid.smul_def, ← algebraMap_smul (RW Wg.1)]
      rfl
    · obtain ⟨⟨s, hs⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) (f := resΓ H hHc hHq K hKq h₀)).mp hx
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
      exact ⟨n, hsx⟩
  obtain ⟨X, e, hXc, hXq, he_smul, he_res, -, -⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis q B hdown hcov
      (fun W : ↥B => E H hHc K W.1) (fun {W W'} h => res H hHc hHq K hKq h)
      (fun {W W'} h a x => resΓ_smul H hHc hHq K hKq h a x)
      (fun W x => resΓ_refl H hHc hHq K hKq W.1 x)
      (fun {W W' W''} h h' x => resΓ_comp H hHc hHq K hKq h h' x)
      hqc (fun W => finite_E H hHc K hKc W.1)
  exact ⟨X, fun W => e ⟨W, Set.mem_univ W⟩, hXc, hXq, fun W a x => he_smul ⟨W, Set.mem_univ W⟩ a x,
    fun W W' h x => he_res ⟨W, Set.mem_univ W⟩ ⟨W', Set.mem_univ W'⟩ h x⟩

end Main

end EP3Geo

namespace EP3Clause

open EP3Alg

section Alg

variable {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
  {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
  {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
  {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']

theorem clause_alg (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    {r' : ℕ} (p' : (Fin r' → B') →ₗ[B'] M') (hp' : Function.Surjective p')
    {rW : ℕ} (pW : (Fin rW → B) →ₗ[B] M) (hpW : Function.Surjective pW)
    {rW' : ℕ} (pW' : (Fin rW' → B') →ₗ[B'] M') (hpW' : Function.Surjective pW')
    (g : (Fin r → B) →+ (Fin r' → B'))
    (hg : ∀ (a : B) (v : Fin r → B), g (a • v) = algebraMap B B' a • g v)
    (hgp : ∀ v : Fin r → B, p' (g v) = μ (p v))
    (δ : ↥(LinearMap.ker p) →ₗ[B] N) (δ' : ↥(LinearMap.ker p') →ₗ[B'] N')
    (hδ : ∀ (s : ↥(LinearMap.ker p)) (hs : g (s : Fin r → B) ∈ LinearMap.ker p'), δ' ⟨g (s : Fin r → B), hs⟩ = ν (δ s)) :
    Phi (N := N') p' pW' hp' hpW' (rho μ hμ ν hν pW hpW pW' hpW' ((Phi (N := N) p pW hp hpW).symm (Submodule.Quotient.mk δ))) =
      Submodule.Quotient.mk δ' := by
  have h1 : rho μ hμ ν hν pW hpW pW' hpW' ((Phi (N := N) p pW hp hpW).symm (Submodule.Quotient.mk δ)) =
      rho μ hμ ν hν p hp pW' hpW' (Submodule.Quotient.mk δ) := by
    rw [← rho_Phi μ hμ ν hν p hp pW' hpW' pW hpW, LinearEquiv.apply_symm_apply]
  rw [h1, Phi_rho_eq, rho_mk μ hμ ν hν p hp p' hp' g hg hgp δ δ' hδ]

end Alg

section Upgrade

def upgradeEquiv {R S : Type*} [Semiring R] [Semiring S] {X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y]
    [Module R X] [Module R Y] [Module S X] [Module S Y] (e : X ≃ₗ[R] Y) (h : ∀ (a : S) (x : X), e (a • x) = a • e x) :
    X ≃ₗ[S] Y :=
  { toFun := e, invFun := e.symm, map_add' := e.map_add, map_smul' := h, left_inv := e.left_inv, right_inv := e.right_inv }

theorem upgradeEquiv_apply {R S : Type*} [Semiring R] [Semiring S] {X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y]
    [Module R X] [Module R Y] [Module S X] [Module S Y] (e : X ≃ₗ[R] Y) (h : ∀ (a : S) (x : X), e (a • x) = a • e x) (x : X) :
    upgradeEquiv e h x = e x := rfl

theorem upgradeEquiv_symm_apply {R S : Type*} [Semiring R] [Semiring S] {X Y : Type*} [AddCommMonoid X] [AddCommMonoid Y]
    [Module R X] [Module R Y] [Module S X] [Module S Y] (e : X ≃ₗ[R] Y) (h : ∀ (a : S) (x : X), e (a • x) = a • e x) (y : Y) :
    (upgradeEquiv e h).symm y = e.symm y := rfl

end Upgrade

end EP3Clause

open CategoryTheory AlgebraicGeometry in
set_option maxHeartbeats 8000000 in
theorem solution
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P]
    (H K : OModulePresheaf q)
    (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent) (hKc : K.IsCoherent) (hKq : K.IsQuasicoherent) :
    ∃ (X : OModulePresheaf q)
      (ε : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] H.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] K.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (K.obj W.1) (LinearMap.ker p).subtype)))),
      X.IsCoherent ∧ X.IsQuasicoherent ∧
      ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] H.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] H.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = H.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] K.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] K.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = K.res h (δ s)),
        X.res h ((ε W r p hp).symm (Submodule.Quotient.mk δ)) = (ε W' r' p' hp').symm (Submodule.Quotient.mk δ') := by
  obtain ⟨X, e, hXc, hXq, e_smul, e_res⟩ := EP3Geo.main H K hHc hHq hKc hKq
  letI instA : ∀ W : P.affineOpens, Module A (EP3Geo.E H hHc K W) := fun W => EP3Geo.modA H hHc K W
  refine ⟨X, fun W r p hp => (EP3Clause.upgradeEquiv (e W) (e_smul W)).trans
      (EP3Alg.Phi (N := K.obj W.1) p (EP3Geo.pres H hHc W) hp (EP3Geo.pres_surjective H hHc W)), hXc, hXq, ?_⟩
  intro W W' h r p hp r' p' hp' g hg hgp δ δ' hδ
  haveI := EP3Geo.noeth (P := P) W; haveI := EP3Geo.noeth (P := P) W'
  letI := EP3Geo.algOf (P := P) h; letI := EP3Geo.modOf H h; letI := EP3Geo.modOf K h
  haveI := EP3Geo.towOf H h; haveI := EP3Geo.towOf K h; haveI := EP3Geo.flatOf (P := P) h
  rw [LinearEquiv.eq_symm_apply, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, EP3Clause.upgradeEquiv_apply,
    EP3Clause.upgradeEquiv_symm_apply, e_res, LinearEquiv.apply_symm_apply, EP3Geo.resΓ_def]
  exact EP3Clause.clause_alg (EP3Geo.mu H h) (EP3Geo.mu_isBaseChange H hHq h) (EP3Geo.mu K h) (EP3Geo.mu_isBaseChange K hKq h)
    p hp p' hp' (EP3Geo.pres H hHc W) (EP3Geo.pres_surjective H hHc W) (EP3Geo.pres H hHc W') (EP3Geo.pres_surjective H hHc W')
    g hg hgp δ δ' (fun s hs => hδ s)

end S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent (solution)
