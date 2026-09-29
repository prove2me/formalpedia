-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_ringHom_smul_map_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7e2b0d12-28a5-5cea-96ea-b61a52f44600

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

noncomputable section

namespace DehomSol

open AlgebraicGeometry.GradedOAlgebra AlgebraicGeometry.Scheme.Modules

theorem smul_one_nat (m : ℕ) : m • (1 : ℕ) = m := by simp

theorem map_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U W : X.Opens} (i : W ⟶ U) (x : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U x) = φ.app W (M.presheaf.map i.op x) := by
  have h := congr($(φ.mapPresheaf.naturality i.op) x)
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at h
  exact h.symm

variable {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {L : X.Modules}
    {R : Type u} [CommRing R] [Algebra S R] {𝓡 : ℕ → Submodule S R} [GradedAlgebra 𝓡]
    {ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)} (hR : IsSectionRing f L R 𝓡 ι)
    (τ : 𝓡 1) (V : X.Opens) (hτ : IsFrameOn (ι 1 τ) V)

theorem pow_mem (d : ℕ) : (τ : R) ^ d ∈ 𝓡 d := by
  simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded d τ.2

def τpow (d : ℕ) : 𝓡 d := ⟨(τ : R) ^ d, pow_mem τ d⟩

@[scoped simp] theorem coe_τpow (d : ℕ) : (τpow τ d : R) = (τ : R) ^ d := rfl

theorem τpow_zero : τpow τ 0 = ⟨1, SetLike.GradedOne.one_mem⟩ := Subtype.ext (pow_zero _)

theorem τpow_succ (d : ℕ) :
    τpow τ (d + 1) = ⟨(τpow τ d : R) * (τ : R), SetLike.GradedMul.mul_mem (τpow τ d).2 τ.2⟩ :=
  Subtype.ext (pow_succ _ _)

theorem τpow_add (i j : ℕ) :
    τpow τ (i + j) = ⟨(τpow τ i : R) * (τpow τ j : R), SetLike.GradedMul.mul_mem (τpow τ i).2 (τpow τ j).2⟩ :=
  Subtype.ext (pow_add _ _ _)

include hR hτ in

theorem isFrameOn_pow : ∀ d : ℕ, IsFrameOn (ι d (τpow τ d)) V
  | 0 => by
    rw [τpow_zero, hR.map_one]
    exact isFrameOn_unitSection V
  | d + 1 => by
    rw [τpow_succ, hR.map_mul d 1 (τpow τ d) τ]
    exact ((isFrameOn_pow d).tensorSections_monoidalV2 hτ).map_iso (tensorPowAdd L d 1)

def frameEquiv (d : ℕ) : Γ(X, V) ≃ Γ(L.tensorPow d, V) :=
  Equiv.ofBijective
    (fun g : Γ(X, V) => g • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)))
    (isFrameOn_pow hR τ V hτ d (le_top : V ≤ ⊤) le_rfl)

theorem frameEquiv_apply (d : ℕ) (g : Γ(X, V)) :
    frameEquiv hR τ V hτ d g = g • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)) :=
  rfl

def ψfun (d : ℕ) (s : 𝓡 d) : Γ(X, V) :=
  (frameEquiv hR τ V hτ d).symm ((L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d s))

theorem ψfun_smul (d : ℕ) (s : 𝓡 d) :
    ψfun hR τ V hτ d s • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)) =
      (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d s) := by
  rw [← frameEquiv_apply hR τ V hτ d]
  exact Equiv.apply_symm_apply _ _

theorem eq_ψfun (d : ℕ) (s : 𝓡 d) (g : Γ(X, V))
    (hg : g • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)) =
      (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d s)) :
    g = ψfun hR τ V hτ d s := by
  apply (frameEquiv hR τ V hτ d).injective
  rw [frameEquiv_apply, frameEquiv_apply, hg, ψfun_smul]

def ψ (d : ℕ) : 𝓡 d →+ Γ(X, V) :=
  AddMonoidHom.mk' (ψfun hR τ V hτ d) fun a b => by
    symm
    apply eq_ψfun
    rw [add_smul, ψfun_smul, ψfun_smul, hR.map_add, map_add]

@[scoped simp] theorem ψ_apply (d : ℕ) (s : 𝓡 d) : ψ hR τ V hτ d s = ψfun hR τ V hτ d s := rfl

theorem ψ_one : ψ hR τ V hτ 0 (GradedMonoid.GOne.one (A := fun i => ↥(𝓡 i))) = 1 := by
  rw [ψ_apply]; symm; apply eq_ψfun
  rw [one_smul, τpow_zero]
  rfl

theorem ψ_mul {i j : ℕ} (a : 𝓡 i) (b : 𝓡 j) :
    ψ hR τ V hτ (i + j) (GradedMonoid.GMul.mul (A := fun i => ↥(𝓡 i)) a b) =
      ψ hR τ V hτ i a * ψ hR τ V hτ j b := by
  rw [ψ_apply, ψ_apply, ψ_apply]; symm; apply eq_ψfun
  change _ = (L.tensorPow (i + j)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (ι (i + j) ⟨(a : R) * (b : R), SetLike.GradedMul.mul_mem a.2 b.2⟩)
  rw [τpow_add, hR.map_mul i j (τpow τ i) (τpow τ j), hR.map_mul i j a b, map_app, map_app,
    map_homOfLE_tensorSections, map_homOfLE_tensorSections, ← Scheme.Modules.Hom.app_smul,
    mul_smul, ← tensorSections_smul_right, ← tensorSections_smul_left, ψfun_smul, ψfun_smul]

def φ : R →+* Γ(X, V) :=
  (DirectSum.toSemiring (fun d => ψ hR τ V hτ d) (ψ_one hR τ V hτ) (fun a b => ψ_mul hR τ V hτ a b)).comp
    (DirectSum.decomposeRingEquiv 𝓡).toRingHom

theorem φ_coe (d : ℕ) (s : 𝓡 d) : φ hR τ V hτ (s : R) = ψfun hR τ V hτ d s := by
  simp only [φ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [show DirectSum.decomposeRingEquiv 𝓡 (s : R) = DirectSum.decompose 𝓡 (s : R) from rfl,
    DirectSum.decompose_coe, DirectSum.toSemiring_of, ψ_apply]

theorem φ_algebraMap (a : S) :
    φ hR τ V hτ (algebraMap S R a) = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (baseScalar f a) := by
  have hmem : algebraMap S R a ∈ 𝓡 0 := SetLike.algebraMap_mem_graded 𝓡 a
  rw [show algebraMap S R a = ((⟨algebraMap S R a, hmem⟩ : 𝓡 0) : R) from rfl, φ_coe]
  symm; apply eq_ψfun
  have e : (⟨algebraMap S R a, hmem⟩ : 𝓡 0) = a • (⟨1, SetLike.GradedOne.one_mem⟩ : 𝓡 0) :=
    Subtype.ext (Algebra.algebraMap_eq_smul_one a)
  rw [e, hR.map_smul, Scheme.Modules.map_smul, τpow_zero]

end DehomSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq.DehomSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq.DehomSol"

open DehomSol in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (τ : 𝓡 1) (V : X.Opens) (hτ : AlgebraicGeometry.Scheme.Modules.IsFrameOn (ι 1 τ) V) :
    ∃ φ : R →+* Γ(X, V),
      (∀ a : S, φ (algebraMap S R a) =
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (AlgebraicGeometry.GradedOAlgebra.baseScalar f a)) ∧
      (∀ m : ℕ, AlgebraicGeometry.Scheme.Modules.IsFrameOn
        (ι (m • 1) ⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩) V) ∧
      (∀ (m : ℕ) (s : 𝓡 (m • 1)),
        φ (s : R) • (L.tensorPow (m • 1)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
            (ι (m • 1) ⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩) =
          (L.tensorPow (m • 1)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι (m • 1) s)) := by
  refine ⟨φ hR τ V hτ, φ_algebraMap hR τ V hτ, fun m => ?_, fun m s => ?_⟩
  · have e : (⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩ : 𝓡 (m • 1)) = τpow τ (m • 1) :=
      Subtype.ext (congrArg (fun k => (τ : R) ^ k) (smul_one_nat m)).symm
    rw [e]
    exact isFrameOn_pow hR τ V hτ (m • 1)
  · have e : (⟨(τ : R) ^ m, SetLike.pow_mem_graded m τ.2⟩ : 𝓡 (m • 1)) = τpow τ (m • 1) :=
      Subtype.ext (congrArg (fun k => (τ : R) ^ k) (smul_one_nat m)).symm
    rw [e, φ_coe]
    exact ψfun_smul hR τ V hτ (m • 1) s

end S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq (solution)
