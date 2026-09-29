-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/77a0117f-136c-5647-aa9c-4cab15b77271

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

theorem proj_basicOpen_awayMk (j : Fin (N + 1)) {d : ℕ}
    {g : MvPolynomial (Fin (N + 1)) A} (hg : g ∈ 𝒜 d) :
    (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom
        (HomogeneousLocalization.Away.mk 𝒜 (ProjSpace.X_mem_one A N j) d g (by simpa using hg)))
      = Proj.basicOpen 𝒜 ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) * g) := by
  set z := HomogeneousLocalization.Away.mk 𝒜 (ProjSpace.X_mem_one A N j) d g (by simpa using hg) with hz
  have hkey : ∀ (x : Proj 𝒜) (hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j)),
      IsUnit ((Proj 𝒜).presheaf.germ _ x hxj ((Proj.awayToSection 𝒜 (MvPolynomial.X j)).hom z)) ↔ g ∉ x.asHomogeneousIdeal := by
    intro x hxj
    have hxj' : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl := hxj
    have hgerm := congrArg (fun ψ => CommRingCat.Hom.hom ψ z)
      (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 (MvPolynomial.X j) x hxj)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hgerm
    erw [hgerm]
    haveI : IsLocalHom (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom := isLocalHom_of_isIso _
    refine (isUnit_map_iff (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv.hom _).trans ?_
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]
    have hval : (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hxj') z).val
        = Localization.mk g ⟨(MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ d, pow_mem hxj' d⟩ := by
      simp only [hz, HomogeneousLocalization.Away.mk, HomogeneousLocalization.mapId,
        HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
      rfl
    rw [show Submonoid.powers_le.mpr hxj = Submonoid.powers_le.mpr hxj' from rfl, hval,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact Iff.rfl
  ext x
  simp only [SetLike.mem_coe, Proj.basicOpen_mul, Proj.mem_basicOpen, Opens.mem_inf]
  refine ⟨fun hx => ?_, fun ⟨hxj, hxg⟩ => ?_⟩
  · have hxj : x ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) := Scheme.basicOpen_le _ _ hx
    exact ⟨hxj, (hkey x hxj).mp ((Scheme.mem_basicOpen _ _ x hxj).mp hx)⟩
  · exact (Scheme.mem_basicOpen _ _ x hxj).mpr ((hkey x hxj).mpr hxg)

theorem pullbackOverlap_eq_basicOpen (i j : Fin (N + 1)) :
    pullbackOverlap φ i j = X.basicOpen (frameUnit φ i j) := by
  have h1 : (Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom (ratio A N i j))
      = Proj.basicOpen 𝒜 (MvPolynomial.X i * MvPolynomial.X j) :=
    proj_basicOpen_awayMk (A := A) i (X_mem_one A N j)
  have h2 := Scheme.preimage_basicOpen φ (U := Proj.basicOpen 𝒜 (MvPolynomial.X i))
    ((Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom (ratio A N i j))
  rw [h1] at h2
  exact h2

theorem inf_pullbackChart_eq_basicOpen (i j : Fin (N + 1)) :
    pullbackChart φ i ⊓ pullbackChart φ j = X.basicOpen (frameUnit φ i j) := by
  rw [← pullbackOverlap_eq_inf, pullbackOverlap_eq_basicOpen]

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem restrictFun_injective_of_eq {V W : X.Opens} (hVW : V = W) :
    Function.Injective (restrictFun (le_of_eq hVW) : Γ(X, W) → Γ(X, V)) := by
  subst hVW
  intro x y h
  rwa [restrictFun_refl, restrictFun_refl] at h

theorem frameUnit_cocycle_of_le {W : X.Opens} (i i' j : Fin (N + 1)) (hi : W ≤ pullbackChart φ i) (hi' : W ≤ pullbackChart φ i') :
    restrictFun hi (frameUnit φ i i') * restrictFun hi' (frameUnit φ i' j) = restrictFun hi (frameUnit φ i j) := by
  have hW : W ≤ pullbackOverlap φ i i' := by rw [pullbackOverlap_eq_inf]; exact le_inf hi hi'
  have key := congrArg (restrictFun hW) (frameUnit_cocycle φ i i' j)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  exact key

theorem frameUnit_mul_swap_of_le {W : X.Opens} (i i' : Fin (N + 1)) (hi : W ≤ pullbackChart φ i) (hi' : W ≤ pullbackChart φ i') :
    restrictFun hi (frameUnit φ i i') * restrictFun hi' (frameUnit φ i' i) = 1 := by
  rw [frameUnit_cocycle_of_le φ i i' i hi hi', frameUnit_self, map_one]

section Chart

variable {U : X.Opens} {i₀ : Fin (N + 1)} (hU : U ≤ pullbackChart φ i₀)
include hU

theorem twistObj_eq_of_val_eq {g g' : twistObj π φ m U} (h : g.val i₀ = g'.val i₀) : g = g' := by
  refine twistObj.ext (_root_.funext fun i => ?_)

  have heq : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ = U ⊓ pullbackChart φ i :=
    inf_eq_left.mpr (le_trans inf_le_left hU)
  apply restrictFun_injective_of_eq heq
  have hg := g.compat i i₀
  have hg' := g'.compat i i₀
  rw [restrictFun_irrel (le_of_eq heq) inf_le_left, hg, hg']

  congr 1
  have : restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
      (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ U ⊓ pullbackChart φ i₀) (g.val i₀)
      = restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) (g'.val i₀) := by rw [h]
  exact this

def frameFamily (h : Γ(X, U ⊓ pullbackChart φ i₀)) : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i) :=
  fun i => restrictFun inf_le_right (frameUnit φ i i₀) ^ m
    * restrictFun (le_inf inf_le_left (le_trans inf_le_left hU)) h

theorem frameFamily_compat (h : Γ(X, U ⊓ pullbackChart φ i₀)) : TwistCompat φ m U (frameFamily φ m hU h) := by
  intro i j
  simp only [frameFamily, map_mul, map_pow, restrictFun_restrictFun]

  have hc := frameUnit_cocycle_of_le φ i j i₀
    (le_trans inf_le_left inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ i)
    (inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ j)
  rw [restrictFun_irrel _ (le_trans inf_le_left inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ i),
    ← hc, mul_pow, mul_assoc]

def twistObjOfFun (h : Γ(X, U ⊓ pullbackChart φ i₀)) : twistObj π φ m U :=
  ⟨frameFamily φ m hU h, frameFamily_compat φ m hU h⟩

theorem twistObjOfFun_val_self (h : Γ(X, U ⊓ pullbackChart φ i₀)) : (twistObjOfFun φ π m hU h).val i₀ = h := by
  show restrictFun _ (frameUnit φ i₀ i₀) ^ m * restrictFun _ h = h
  rw [frameUnit_self, map_one, one_pow, one_mul, restrictFun_irrel _ (le_refl _), restrictFun_refl]

theorem twistObjOfFun_val (h : Γ(X, U ⊓ pullbackChart φ i₀)) (i : Fin (N + 1)) :
    (twistObjOfFun φ π m hU h).val i
      = restrictFun inf_le_right (frameUnit φ i i₀) ^ m * restrictFun (le_inf inf_le_left (le_trans inf_le_left hU)) h := rfl

theorem twistObjOfFun_val_eq (g : twistObj π φ m U) : twistObjOfFun φ π m hU (g.val i₀) = g :=
  twistObj_eq_of_val_eq φ π m hU (twistObjOfFun_val_self φ π m hU _)

theorem val_self_injective : Function.Injective fun g : twistObj π φ m U => g.val i₀ :=
  fun _ _ h => twistObj_eq_of_val_eq φ π m hU h

theorem val_self_surjective : Function.Surjective fun g : twistObj π φ m U => g.val i₀ :=
  fun h => ⟨twistObjOfFun φ π m hU h, twistObjOfFun_val_self φ π m hU h⟩

theorem twistObjOfFun_add (h h' : Γ(X, U ⊓ pullbackChart φ i₀)) :
    twistObjOfFun φ π m hU (h + h') = twistObjOfFun φ π m hU h + twistObjOfFun φ π m hU h' :=
  twistObj_eq_of_val_eq φ π m hU (by rw [twistObjOfFun_val_self, twistObj.add_val, Pi.add_apply, twistObjOfFun_val_self,
    twistObjOfFun_val_self])

theorem twistObjOfFun_smul (a : Γ(X, U)) (h : Γ(X, U ⊓ pullbackChart φ i₀)) :
    twistObjOfFun φ π m hU (restrictFun inf_le_left a * h) = a • twistObjOfFun φ π m hU h :=
  twistObj_eq_of_val_eq φ π m hU (by rw [twistObjOfFun_val_self, twistObj.smul_val, twistObjOfFun_val_self])

end Chart

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def interI (I : Finset (Fin (N + 1))) : X.Opens := ⨅ i ∈ I, pullbackChart φ i

theorem interI_le {I : Finset (Fin (N + 1))} {i : Fin (N + 1)} (hi : i ∈ I) : interI φ I ≤ pullbackChart φ i :=
  (iInf_le _ i).trans (iInf_le _ hi)

theorem interI_anti {I J : Finset (Fin (N + 1))} (h : I ⊆ J) : interI φ J ≤ interI φ I :=
  le_iInf fun _ => le_iInf fun hi => interI_le φ (h hi)

def frameProd (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) : Γ(X, pullbackChart φ i₀) := ∏ j ∈ I, frameUnit φ i₀ j

theorem pullbackChart_inf_interI_eq_basicOpen (K : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) :
    pullbackChart φ i₀ ⊓ interI φ K = X.basicOpen (frameProd φ K i₀) := by
  classical
  unfold frameProd interI
  induction K using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    simp only [Finset.notMem_empty, iInf_false, iInf_top, inf_top_eq]
    exact (X.basicOpen_of_isUnit isUnit_one).symm
  | insert k K hkK ih =>
    rw [Finset.prod_insert hkK, Scheme.basicOpen_mul, ← inf_pullbackChart_eq_basicOpen, ← ih, Finset.iInf_insert,
      inf_inf_distrib_left]

theorem interI_eq_basicOpen {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    interI φ I = X.basicOpen (frameProd φ I i₀) := by
  rw [← pullbackChart_inf_interI_eq_basicOpen, eq_comm, inf_eq_right]
  exact interI_le φ hi₀

theorem interI_le_basicOpen {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    interI φ I ≤ X.basicOpen (frameProd φ I i₀) := le_of_eq (interI_eq_basicOpen φ hi₀)

theorem basicOpen_le_interI {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    X.basicOpen (frameProd φ I i₀) ≤ interI φ I := le_of_eq (interI_eq_basicOpen φ hi₀).symm

theorem isAffineOpen_interI [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I) :
    IsAffineOpen (interI φ I) := by
  rw [interI_eq_basicOpen φ hi₀]
  exact (isAffineOpen_pullbackChart φ i₀).basicOpen _

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A))

abbrev uTop (i j : Fin (N + 1)) : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) := restrictFun inf_le_right (frameUnit φ i j)

theorem D_xMul_apply (j : Fin (N + 1)) (f : (twistGradedModule φ π).M) (d : ℤ) (i : Fin (N + 1)) :
    ((twistGradedModule φ π).xMul j f) d i = uTop φ i j * f (d - 1) i := rfl

theorem twistXMul_pow_apply (j : Fin (N + 1)) (k : ℕ) (f : (twistGradedModule φ π).M) (d : ℤ) (i : Fin (N + 1)) :
    (((twistGradedModule φ π).xMul j ^ k) f) d i = uTop φ i j ^ k * f (d - k) i := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, D_xMul_apply, ih, pow_succ', mul_assoc]
    congr 2
    · push_cast; ring_nf

theorem twistMonMul_apply (b : Fin (N + 1) → ℕ) (f : (twistGradedModule φ π).M) (d : ℤ) (i : Fin (N + 1)) :
    (ProjSpaceCech.GradedModule.monMul (twistGradedModule φ π) b f) d i
      = (∏ j, uTop φ i j ^ b j) * f (d - ∑ j, (b j : ℤ)) i := by
  classical

  suffices h : ∀ (s : Finset (Fin (N + 1))) (d : ℤ),
      (ProjSpaceCech.GradedModule.monMul (twistGradedModule φ π) (∑ j ∈ s, Pi.single j (b j)) f) d i
        = (∏ j ∈ s, uTop φ i j ^ b j) * f (d - ∑ j ∈ s, (b j : ℤ)) i by
    have hb : (∑ j ∈ Finset.univ, Pi.single j (b j) : Fin (N + 1) → ℕ) = b := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    simpa [hb] using h Finset.univ d
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro d
    simp [ProjSpaceCech.GradedModule.monMul_zero]
  | insert k s hks ih =>
    intro d
    rw [Finset.sum_insert hks, ProjSpaceCech.GradedModule.monMul_add_apply, ProjSpaceCech.GradedModule.monMul_single,
      twistXMul_pow_apply, ih, Finset.prod_insert hks, Finset.sum_insert hks, mul_assoc]
    congr 2
    ring_nf

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem twistMonMul_shift_apply (k : ℤ) (b : Fin (N + 1) → ℕ) (f : ((twistGradedModule φ π).shift k).M) (d : ℤ) (i : Fin (N + 1)) :
    (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift k) b f) d i
      = (∏ j, uTop φ i j ^ b j) * f (d - ∑ j, (b j : ℤ)) i :=
  twistMonMul_apply φ π b f d i

section Psi

variable {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)

abbrev Wop (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) : X.Opens := interI φ I ⊓ pullbackChart φ i₀

theorem Wop_le_top : Wop φ I i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀ := inf_le_inf_right _ le_top
theorem Wop_le_self : Wop φ I i₀ ≤ pullbackChart φ i₀ := inf_le_right
theorem Wop_le_chart {j : Fin (N + 1)} (hj : j ∈ I) : Wop φ I i₀ ≤ pullbackChart φ j := inf_le_left.trans (interI_le φ hj)

def invProd (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) (a : Fin (N + 1) → ℕ) : Γ(X, Wop φ I i₀) :=
  ∏ j ∈ I.attach, restrictFun (Wop_le_chart φ j.2) (frameUnit φ j i₀) ^ a j

def dirProd (I : Finset (Fin (N + 1))) (i₀ : Fin (N + 1)) (a : Fin (N + 1) → ℕ) : Γ(X, Wop φ I i₀) :=
  ∏ j ∈ I.attach, restrictFun (Wop_le_self φ) (frameUnit φ i₀ j) ^ a j

theorem dirProd_mul_invProd (a : Fin (N + 1) → ℕ) : dirProd φ I i₀ a * invProd φ I i₀ a = 1 := by
  unfold dirProd invProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← mul_pow, frameUnit_mul_swap_of_le φ i₀ j (Wop_le_self φ) (Wop_le_chart φ j.2), one_pow]

theorem invProd_add (a b : Fin (N + 1) → ℕ) : invProd φ I i₀ (a + b) = invProd φ I i₀ a * invProd φ I i₀ b := by
  unfold invProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, pow_add]

theorem dirProd_add (a b : Fin (N + 1) → ℕ) : dirProd φ I i₀ (a + b) = dirProd φ I i₀ a * dirProd φ I i₀ b := by
  unfold dirProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, pow_add]

theorem restrictFun_prod_uTop {a : Fin (N + 1) → ℕ} (ha : ∀ j ∉ I, a j = 0) :
    restrictFun (Wop_le_top φ) (∏ j, uTop φ i₀ j ^ a j) = dirProd φ I i₀ a := by
  classical
  rw [map_prod]
  have h1 : (∏ j, restrictFun (Wop_le_top φ (I := I)) (uTop φ i₀ j ^ a j))
      = ∏ j ∈ I, restrictFun (Wop_le_top φ (I := I)) (uTop φ i₀ j ^ a j) := by
    refine (Finset.prod_subset (Finset.subset_univ I) fun j _ hj => ?_).symm
    rw [ha j hj, pow_zero, map_one]
  rw [h1, dirProd, ← Finset.prod_attach I]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_pow, uTop, restrictFun_restrictFun]

def PsiNum (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift m) I) : Γ(X, Wop φ I i₀) :=
  restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀) * invProd φ I i₀ x.denExp

theorem PsiNum_eq_of_rel {x y : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift m) I}
    (h : ProjSpaceCech.GradedModule.Frac.Rel ((twistGradedModule φ π).shift m) I x y) :
    PsiNum φ π m (i₀ := i₀) x = PsiNum φ π m y := by
  obtain ⟨c, hc, heq⟩ := h

  have key := congrFun (congrFun heq ((∑ j, ((c + y.denExp) j : ℤ)) + ((∑ j, (x.denExp j : ℤ)) + m))) i₀
  rw [twistMonMul_shift_apply, twistMonMul_shift_apply, add_sub_cancel_left] at key
  have hdeg : (∑ j, ((c + y.denExp) j : ℤ)) + ((∑ j, (x.denExp j : ℤ)) + m) - ∑ j, ((c + x.denExp) j : ℤ)
      = (∑ j, (y.denExp j : ℤ)) + m := by
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
  rw [hdeg] at key

  have key' := congrArg (fun t => restrictFun (Wop_le_top φ (I := I)) t * invProd φ I i₀ (c + x.denExp + y.denExp)) key
  simp only [map_mul] at key'
  rw [restrictFun_prod_uTop φ (fun j hj => by simp [Pi.add_apply, hc j hj, y.hden j hj]),
    restrictFun_prod_uTop φ (fun j hj => by simp [Pi.add_apply, hc j hj, x.hden j hj])] at key'

  have e1 : dirProd φ I i₀ (c + y.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp) = invProd φ I i₀ x.denExp := by
    rw [show c + x.denExp + y.denExp = (c + y.denExp) + x.denExp by abel, invProd_add, ← mul_assoc, dirProd_mul_invProd, one_mul]
  have e2 : dirProd φ I i₀ (c + x.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp) = invProd φ I i₀ y.denExp := by
    rw [invProd_add, ← mul_assoc, dirProd_mul_invProd, one_mul]
  calc PsiNum φ π m x
      = restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀)
          * (dirProd φ I i₀ (c + y.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp)) := by rw [e1]; rfl
    _ = restrictFun (Wop_le_top φ) (y.num ((∑ j, (y.denExp j : ℤ)) + m) i₀)
          * (dirProd φ I i₀ (c + x.denExp) * invProd φ I i₀ (c + x.denExp + y.denExp)) := by
        rw [← mul_assoc, ← mul_assoc, mul_comm (restrictFun _ _) (dirProd φ I i₀ (c + y.denExp)),
          mul_comm (restrictFun _ _) (dirProd φ I i₀ (c + x.denExp)), key']
    _ = PsiNum φ π m y := by rw [e2]; rfl

end Psi

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Psi

variable {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)}

theorem PsiNum_add_repr (x y : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I)
    (hnum : ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num + ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num
      ∈ ((twistGradedModule φ π).shift (m : ℤ)).grade (∑ j, ((x.denExp + y.denExp) j : ℤ))) :
    PsiNum φ π m (i₀ := i₀) ⟨x.denExp + y.denExp, ProjSpaceCech.GradedModule.Frac.supp_add I x.hden y.hden,
        ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num + ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num, hnum⟩
      = PsiNum φ π m x + PsiNum φ π m y := by
  unfold PsiNum
  simp only
  have hdeg : (∑ j, ((x.denExp + y.denExp) j : ℤ)) + m
      = (∑ j, (y.denExp j : ℤ)) + ((∑ j, (x.denExp j : ℤ)) + m) := by
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
  have hdeg' : (∑ j, ((x.denExp + y.denExp) j : ℤ)) + m
      = (∑ j, (x.denExp j : ℤ)) + ((∑ j, (y.denExp j : ℤ)) + m) := by
    simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
  rw [show (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num + ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num)
      ((∑ j, ((x.denExp + y.denExp) j : ℤ)) + m) i₀
      = (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) y.denExp x.num) ((∑ j, ((x.denExp + y.denExp) j : ℤ)) + m) i₀
        + (ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) x.denExp y.num) ((∑ j, ((x.denExp + y.denExp) j : ℤ)) + m) i₀ from rfl]
  conv_lhs => rw [hdeg]; arg 1; arg 2; arg 2; rw [← hdeg, hdeg']
  rw [twistMonMul_shift_apply, twistMonMul_shift_apply, add_sub_cancel_left, add_sub_cancel_left, map_add, map_mul, map_mul,
    restrictFun_prod_uTop φ y.hden, restrictFun_prod_uTop φ x.hden, invProd_add, add_mul]
  congr 1
  ·
    calc dirProd φ I i₀ y.denExp * restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀)
          * (invProd φ I i₀ x.denExp * invProd φ I i₀ y.denExp)
        = restrictFun (Wop_le_top φ) (x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀) * invProd φ I i₀ x.denExp
          * (dirProd φ I i₀ y.denExp * invProd φ I i₀ y.denExp) := by ring
      _ = _ := by rw [dirProd_mul_invProd, mul_one]
  · calc dirProd φ I i₀ x.denExp * restrictFun (Wop_le_top φ) (y.num ((∑ j, (y.denExp j : ℤ)) + m) i₀)
          * (invProd φ I i₀ x.denExp * invProd φ I i₀ y.denExp)
        = restrictFun (Wop_le_top φ) (y.num ((∑ j, (y.denExp j : ℤ)) + m) i₀) * invProd φ I i₀ y.denExp
          * (dirProd φ I i₀ x.denExp * invProd φ I i₀ x.denExp) := by ring
      _ = _ := by rw [dirProd_mul_invProd, mul_one]

theorem PsiNum_smul_repr (r : A) (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiNum φ π m (i₀ := i₀) ⟨x.denExp, x.hden, r • x.num, Submodule.smul_mem _ r x.hnum⟩
      = (Scheme.TwoAffineOpenCover.algebraOfHom π (Wop φ I i₀)).algebraMap r * PsiNum φ π m x := by
  unfold PsiNum
  simp only
  rw [show (r • x.num) ((∑ j, (x.denExp j : ℤ)) + m) i₀
      = (Scheme.TwoAffineOpenCover.algebraOfHom π ((⊤ : X.Opens) ⊓ pullbackChart φ i₀)).algebraMap r
        * x.num ((∑ j, (x.denExp j : ℤ)) + m) i₀ from rfl,
    map_mul, restrictFun_algebraMap' π, mul_assoc]

end Psi

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Psi

variable {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)

def PsiFun : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I → Γ(X, Wop φ I i₀) :=
  Quotient.lift (PsiNum φ π m (i₀ := i₀)) fun _ _ h => PsiNum_eq_of_rel φ π m h

theorem PsiFun_mk (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiFun φ π m (i₀ := i₀) (ProjSpaceCech.GradedModule.sec.mk _ I x) = PsiNum φ π m x := rfl

theorem PsiFun_add (s t : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiFun φ π m (i₀ := i₀) (s + t) = PsiFun φ π m s + PsiFun φ π m t := by
  induction s using Quotient.inductionOn with
  | h x =>
    induction t using Quotient.inductionOn with
    | h y => exact PsiNum_add_repr φ π m x y _

theorem PsiFun_smul (r : A) (s : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I) :
    PsiFun φ π m (i₀ := i₀) (r • s) = (Scheme.TwoAffineOpenCover.algebraOfHom π (Wop φ I i₀)).algebraMap r * PsiFun φ π m s := by
  induction s using Quotient.inductionOn with
  | h x => exact PsiNum_smul_repr φ π m r x

include hi₀ in

def Psi : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I →ₗ[A] twistObj π φ m (interI φ I) where
  toFun s := twistObjOfFun φ π m (interI_le φ hi₀) (PsiFun φ π m s)
  map_add' s t := by rw [PsiFun_add, twistObjOfFun_add]
  map_smul' r s := by
    rw [PsiFun_smul, RingHom.id_apply, twistObj.algebraMap_smul, ← twistObjOfFun_smul]
    congr 1
    rw [restrictFun_algebraMap' π]

theorem Psi_val_self (s : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I) :
    (Psi φ π m hi₀ s).val i₀ = PsiFun φ π m s :=
  twistObjOfFun_val_self φ π m _ _

theorem Psi_mk_val_self (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    (Psi φ π m hi₀ (ProjSpaceCech.GradedModule.sec.mk _ I x)).val i₀ = PsiNum φ π m x :=
  twistObjOfFun_val_self φ π m _ _

end Psi

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem exists_pow_mul_eq_zero_of_restrict_basicOpen {V : X.Opens} (hV : IsAffineOpen V) (g s : Γ(X, V))
    (hs : restrictFun (X.basicOpen_le g) s = 0) : ∃ n : ℕ, g ^ n * s = 0 := by
  haveI := hV.isLocalization_basicOpen g
  have h0 : algebraMap Γ(X, V) Γ(X, X.basicOpen g) s = algebraMap Γ(X, V) Γ(X, X.basicOpen g) 0 := by
    rw [map_zero]; exact hs
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers g) h0
  exact ⟨n, by simpa using hc⟩

theorem exists_pow_mul_eq_zero_of_restrict {V O : X.Opens} (hV : IsAffineOpen V) (g s : Γ(X, V)) (hOV : O ≤ V)
    (hgO : X.basicOpen g ≤ O) (hs : restrictFun hOV s = 0) : ∃ n : ℕ, g ^ n * s = 0 := by
  refine exists_pow_mul_eq_zero_of_restrict_basicOpen hV g s ?_
  have := congrArg (restrictFun hgO) hs
  rwa [map_zero, restrictFun_restrictFun] at this

theorem isAffineOpen_top_inf_pullbackChart [IsAffineHom φ] (i : Fin (N + 1)) :
    IsAffineOpen ((⊤ : X.Opens) ⊓ pullbackChart φ i) := by
  rw [top_inf_eq]; exact isAffineOpen_pullbackChart φ i

section Inj

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem stepA (t : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i₀)) (ht : restrictFun (Wop_le_top φ (I := I)) t = 0) :
    ∃ n : ℕ, restrictFun inf_le_right (frameProd φ I i₀) ^ n * t = 0 := by
  refine exists_pow_mul_eq_zero_of_restrict (isAffineOpen_top_inf_pullbackChart φ i₀) _ t (Wop_le_top φ) ?_ ht

  rw [show restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)
      = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀)).op).hom
          (frameProd φ I i₀) from rfl, Scheme.basicOpen_res, ← interI_eq_basicOpen φ hi₀]
  exact le_inf inf_le_right (inf_le_left.trans inf_le_right)

omit hi₀ in

theorem stepB_restrict (e : ℕ) (g : ∀ i, Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)) (hg : TwistCompat φ e ⊤ g)
    (n : ℕ) (i : Fin (N + 1)) :
    restrictFun (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i)
        ((∏ j ∈ I, uTop φ i j ^ n) * g i)
      = restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i)
          (frameUnit φ i i₀) ^ (n * I.card + e)
        * restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀)
          (restrictFun inf_le_right (frameProd φ I i₀) ^ n * g i₀) := by
  have hc := hg i i₀
  rw [map_mul, hc, map_mul, map_pow, map_prod, restrictFun_restrictFun, frameProd, map_prod]

  have hcoc : ∀ j, restrictFun (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i)
        (uTop φ i j ^ n)
      = (restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i) (frameUnit φ i i₀)
          * restrictFun (inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameUnit φ i₀ j)) ^ n := by
    intro j
    rw [map_pow, uTop, restrictFun_restrictFun, frameUnit_cocycle_of_le φ i i₀ j]
  simp only [hcoc, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
  ring

theorem stepB (e : ℕ) (g : ∀ i, Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)) (hg : TwistCompat φ e ⊤ g) (n : ℕ)
    (hkill : restrictFun inf_le_right (frameProd φ I i₀) ^ n * g i₀ = 0) (i : Fin (N + 1)) :
    ∃ k : ℕ, uTop φ i i₀ ^ k * ((∏ j ∈ I, uTop φ i j ^ n) * g i) = 0 := by
  refine exists_pow_mul_eq_zero_of_restrict (isAffineOpen_top_inf_pullbackChart φ i) _ _
    (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i) ?_ ?_
  · rw [show uTop φ i i₀ = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i ≤ pullbackChart φ i)).op).hom
        (frameUnit φ i i₀) from rfl, Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  · rw [stepB_restrict φ e g hg n i, hkill, map_zero, mul_zero]

end Inj

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Inj2

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem stepC (a : Fin (N + 1) → ℕ) (f : ((twistGradedModule φ π).shift (m : ℤ)).M)
    (hf : f ∈ ((twistGradedModule φ π).shift (m : ℤ)).grade (∑ j, (a j : ℤ)))
    (hW : restrictFun (Wop_le_top φ (I := I)) (f ((∑ j, (a j : ℤ)) + m) i₀) = 0) :
    ∃ c : Fin (N + 1) → ℕ, (∀ j ∉ I, c j = 0) ∧
      ProjSpaceCech.GradedModule.monMul ((twistGradedModule φ π).shift (m : ℤ)) c f = 0 := by
  classical
  set e : ℤ := (∑ j, (a j : ℤ)) + m with he_def
  have he : 0 ≤ e := by positivity
  have hcompat : TwistCompat φ e.toNat ⊤ (f e) := hf.2.2 he
  obtain ⟨n, hn⟩ := stepA φ hi₀ (f e i₀) hW
  choose k hk using fun i => stepB φ hi₀ e.toNat (f e) hcompat n hn i
  set K : ℕ := Finset.univ.sup k with hK
  refine ⟨fun j => (if j ∈ I then n else 0) + (if j = i₀ then K else 0), fun j hj => by
    simp [hj, show j ≠ i₀ from fun h => hj (h ▸ hi₀)], ?_⟩
  funext d i
  rw [twistMonMul_shift_apply]
  show _ = (0 : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i))
  by_cases hd : d - ∑ j, (((if j ∈ I then n else 0) + (if j = i₀ then K else 0) : ℕ) : ℤ) = e
  · rw [hd]
    have hprod : (∏ j, uTop φ i j ^ ((if j ∈ I then n else 0) + (if j = i₀ then K else 0)))
        = uTop φ i i₀ ^ K * ∏ j ∈ I, uTop φ i j ^ n := by
      simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true,
        Finset.prod_ite_mem, Finset.univ_inter]
      ring
    rw [hprod]
    have hKi : k i ≤ K := Finset.le_sup (f := k) (Finset.mem_univ i)
    calc uTop φ i i₀ ^ K * (∏ j ∈ I, uTop φ i j ^ n) * f e i
        = uTop φ i i₀ ^ (K - k i) * (uTop φ i i₀ ^ k i * ((∏ j ∈ I, uTop φ i j ^ n) * f e i)) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hKi]
      _ = 0 := by rw [hk i, mul_zero]
  · rw [hf.1 _ hd]
    exact mul_zero _

theorem Psi_injective : Function.Injective (Psi φ π m hi₀ (I := I)) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  induction s using Quotient.inductionOn with
  | h x =>
    obtain ⟨a, ha, f, hf⟩ := x

    have h1 := congrArg (fun g : twistObj π φ m (interI φ I) => g.val i₀) hs
    rw [show (⟦(⟨a, ha, f, hf⟩ : ProjSpaceCech.GradedModule.Frac _ I)⟧ : ProjSpaceCech.GradedModule.sec _ I)
        = ProjSpaceCech.GradedModule.sec.mk _ I ⟨a, ha, f, hf⟩ from rfl, Psi_mk_val_self, twistObj.zero_val] at h1
    have hW : restrictFun (Wop_le_top φ (I := I)) (f ((∑ j, (a j : ℤ)) + m) i₀) = 0 := by
      have h2 := congrArg (fun t => t * dirProd φ I i₀ a) h1
      simp only [PsiNum, Pi.zero_apply, zero_mul, mul_assoc] at h2
      rwa [mul_comm (invProd φ I i₀ a), dirProd_mul_invProd, mul_one] at h2
    obtain ⟨c, hc, hmon⟩ := stepC φ π m hi₀ a f hf hW
    show ProjSpaceCech.GradedModule.sec.mk _ I ⟨a, ha, f, hf⟩
      = ProjSpaceCech.GradedModule.sec.mk _ I ⟨0, fun _ _ => rfl, 0, by simp⟩
    refine (ProjSpaceCech.GradedModule.sec_mk_eq _ I).mpr ⟨c, hc, ?_⟩
    show ProjSpaceCech.GradedModule.monMul _ (c + 0) f = ProjSpaceCech.GradedModule.monMul _ (c + a) 0
    rw [add_zero, map_zero, hmon]

end Inj2

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem exists_extend_of_affine {V O : X.Opens} (hV : IsAffineOpen V) (g : Γ(X, V)) (hOV : O ≤ V) (hgO : X.basicOpen g ≤ O)
    (s : Γ(X, O)) : ∃ (n : ℕ) (t : Γ(X, V)),
      restrictFun (X.basicOpen_le g) t = restrictFun (X.basicOpen_le g) g ^ n * restrictFun hgO s := by
  haveI := hV.isLocalization_basicOpen g
  obtain ⟨⟨t, ⟨_, n, rfl⟩⟩, ht⟩ := IsLocalization.surj (Submonoid.powers g) (restrictFun hgO s)
  refine ⟨n, t, ?_⟩

  have : restrictFun (X.basicOpen_le g) t = restrictFun hgO s * restrictFun (X.basicOpen_le g) (g ^ n) := ht.symm
  rw [this, map_pow, mul_comm]

theorem restrictFun_self {W : X.Opens} (h : W ≤ W) (x : Γ(X, W)) : restrictFun h x = x := restrictFun_refl x

section Surj

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem basicOpen_frameProd_le_Wop :
    X.basicOpen (restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)) ≤ Wop φ I i₀ := by
  rw [show restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)
      = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀)).op).hom
          (frameProd φ I i₀) from rfl, Scheme.basicOpen_res, ← interI_eq_basicOpen φ hi₀]
  exact le_inf inf_le_right (inf_le_left.trans inf_le_right)

theorem Wop_le_basicOpen_frameProd :
    Wop φ I i₀ ≤ X.basicOpen (restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)) := by
  rw [show restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)
      = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀)).op).hom
          (frameProd φ I i₀) from rfl, Scheme.basicOpen_res, ← interI_eq_basicOpen φ hi₀]
  exact le_inf (le_inf le_top inf_le_right) inf_le_left

theorem surj_step1 (h : Γ(X, Wop φ I i₀)) : ∃ (n : ℕ) (t : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i₀)),
    restrictFun (Wop_le_top φ) t = restrictFun (Wop_le_top φ) (restrictFun inf_le_right (frameProd φ I i₀)) ^ n * h := by
  obtain ⟨n, t, ht⟩ := exists_extend_of_affine (isAffineOpen_top_inf_pullbackChart φ i₀)
    (restrictFun inf_le_right (frameProd φ I i₀)) (Wop_le_top φ) (basicOpen_frameProd_le_Wop φ hi₀) h
  refine ⟨n, t, ?_⟩
  have key := congrArg (restrictFun (Wop_le_basicOpen_frameProd φ hi₀)) ht
  simp only [map_mul, map_pow, restrictFun_restrictFun, restrictFun_self] at key
  rw [restrictFun_restrictFun]
  exact key

omit hi₀ in

theorem surj_step2 (e₁ : ℕ) (t : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i₀)) (i : Fin (N + 1)) :
    ∃ (k : ℕ) (f : Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)),
      restrictFun (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i) f
        = restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i)
            (frameUnit φ i i₀) ^ (k + e₁)
          * restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀) t := by

  have hle : X.basicOpen (uTop φ i i₀) ≤ ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ := by
    rw [show uTop φ i i₀ = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i ≤ pullbackChart φ i)).op).hom
        (frameUnit φ i i₀) from rfl, Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  have hge : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ X.basicOpen (uTop φ i i₀) := by
    rw [show uTop φ i i₀ = (X.presheaf.map (homOfLE (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i ≤ pullbackChart φ i)).op).hom
        (frameUnit φ i i₀) from rfl, Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  set s : Γ(X, ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀) :=
    restrictFun (inf_le_left.trans inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i)
        (frameUnit φ i i₀) ^ e₁
      * restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i₀ ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i₀) t with hs
  obtain ⟨k, f, hf⟩ := exists_extend_of_affine (isAffineOpen_top_inf_pullbackChart φ i) (uTop φ i i₀) inf_le_left hle s
  refine ⟨k, f, ?_⟩
  have key := congrArg (restrictFun hge) hf
  simp only [map_mul, map_pow, restrictFun_restrictFun, restrictFun_self] at key
  rw [key, hs, pow_add]
  ring

end Surj

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

theorem isAffineOpen_topChart_inf [IsAffineHom φ] (i j : Fin (N + 1)) :
    IsAffineOpen (((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ j) := by
  rw [top_inf_eq, ← pullbackOverlap_eq_inf]; exact isAffineOpen_pullbackOverlap φ i j

section Surj3

variable {i₀ : Fin (N + 1)}

abbrev Vt (i : Fin (N + 1)) : X.Opens := (⊤ : X.Opens) ⊓ pullbackChart φ i
abbrev Ot (i i' : Fin (N + 1)) : X.Opens := ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i'

theorem Ot_le_Vt (i i' : Fin (N + 1)) : Ot φ i i' ≤ Vt φ i := inf_le_left
theorem Ot_le_chart_left (i i' : Fin (N + 1)) : Ot φ i i' ≤ pullbackChart φ i := inf_le_left.trans inf_le_right
theorem Ot_le_chart_right (i i' : Fin (N + 1)) : Ot φ i i' ≤ pullbackChart φ i' := inf_le_right
theorem Ot_le_Vt_right (i i' : Fin (N + 1)) : Ot φ i i' ≤ Vt φ i' := le_inf (inf_le_left.trans inf_le_left) inf_le_right

theorem surj_step3a [IsAffineHom φ] (E : ℕ) (t : Γ(X, Vt φ i₀)) (F : ∀ i, Γ(X, Vt φ i))
    (hF : ∀ i, restrictFun (Ot_le_Vt φ i i₀) (F i)
      = restrictFun (Ot_le_chart_left φ i i₀) (frameUnit φ i i₀) ^ E * restrictFun (Ot_le_Vt_right φ i i₀) t)
    (i j : Fin (N + 1)) :
    ∃ r : ℕ, restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀) ^ r
      * (restrictFun (Ot_le_Vt φ i j) (F i)
          - restrictFun (Ot_le_chart_left φ i j) (frameUnit φ i j) ^ E * restrictFun (Ot_le_Vt_right φ i j) (F j)) = 0 := by

  refine exists_pow_mul_eq_zero_of_restrict (isAffineOpen_topChart_inf φ i j) _ _
    (inf_le_left : Ot φ i j ⊓ pullbackChart φ i₀ ≤ Ot φ i j) ?_ ?_
  · rw [show restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀)
        = (X.presheaf.map (homOfLE (Ot_le_chart_left φ i j)).op).hom (frameUnit φ i i₀) from by
          simp only [uTop, restrictFun_restrictFun],
      Scheme.basicOpen_res, ← inf_pullbackChart_eq_basicOpen]
    exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
  ·
    have hi := congrArg (restrictFun (le_inf (inf_le_left.trans (Ot_le_Vt φ i j)) inf_le_right :
      Ot φ i j ⊓ pullbackChart φ i₀ ≤ Ot φ i i₀)) (hF i)
    have hj := congrArg (restrictFun (le_inf (inf_le_left.trans (Ot_le_Vt_right φ i j)) inf_le_right :
      Ot φ i j ⊓ pullbackChart φ i₀ ≤ Ot φ j i₀)) (hF j)
    simp only [map_mul, map_pow, restrictFun_restrictFun] at hi hj
    rw [map_sub, map_mul, map_pow, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun, hi, hj,
      ← mul_assoc, ← mul_pow,
      frameUnit_cocycle_of_le φ i j i₀ (inf_le_left.trans (Ot_le_chart_left φ i j)) (inf_le_left.trans (Ot_le_chart_right φ i j)),
      sub_self]

theorem surj_step3b [IsAffineHom φ] (E : ℕ) (t : Γ(X, Vt φ i₀)) (F : ∀ i, Γ(X, Vt φ i))
    (hF : ∀ i, restrictFun (Ot_le_Vt φ i i₀) (F i)
      = restrictFun (Ot_le_chart_left φ i i₀) (frameUnit φ i i₀) ^ E * restrictFun (Ot_le_Vt_right φ i i₀) t) :
    ∃ R : ℕ, TwistCompat φ (R + E) ⊤ (fun i => uTop φ i i₀ ^ R * F i) := by
  classical
  choose r hr using fun p : Fin (N + 1) × Fin (N + 1) => surj_step3a φ E t F hF p.1 p.2
  refine ⟨Finset.univ.sup r, fun i j => ?_⟩
  have hRij : r (i, j) ≤ Finset.univ.sup r := Finset.le_sup (f := r) (Finset.mem_univ (i, j))
  have key := hr (i, j)
  simp only at key

  have key' := congrArg (fun z => restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀) ^ (Finset.univ.sup r - r (i, j)) * z) key
  simp only [mul_zero, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hRij, mul_sub] at key'

  show restrictFun _ (uTop φ i i₀ ^ Finset.univ.sup r * F i)
    = restrictFun _ (frameUnit φ i j) ^ (Finset.univ.sup r + E) * restrictFun _ (uTop φ j i₀ ^ Finset.univ.sup r * F j)
  rw [map_mul, map_pow, map_mul, map_pow]
  rw [sub_eq_zero] at key'
  rw [key', pow_add]

  have hc := frameUnit_cocycle_of_le φ i j i₀ (Ot_le_chart_left φ i j) (Ot_le_chart_right φ i j)
  have hu : restrictFun (Ot_le_Vt_right φ i j) (uTop φ j i₀) = restrictFun (Ot_le_chart_right φ i j) (frameUnit φ j i₀) := by
    simp only [uTop, restrictFun_restrictFun]
  have hu' : restrictFun (Ot_le_Vt φ i j) (uTop φ i i₀) = restrictFun (Ot_le_chart_left φ i j) (frameUnit φ i i₀) := by
    simp only [uTop, restrictFun_restrictFun]
  rw [hu, hu', ← hc]
  ring

end Surj3

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Surj4

variable [IsAffineHom φ] {I : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I)
include hi₀

theorem invProd_single_self (M : ℕ) : invProd φ I i₀ (Pi.single i₀ M) = 1 := by
  unfold invProd
  refine Finset.prod_eq_one fun j _ => ?_
  by_cases hj : (j : Fin (N + 1)) = i₀
  · have : restrictFun (Wop_le_chart φ (i₀ := i₀) j.2) (frameUnit φ j i₀) = 1 := by
      have h1 : frameUnit φ (j : Fin (N + 1)) i₀ = 1 := by rw [hj, frameUnit_self]
      rw [h1, map_one]
    rw [this, one_pow]
  · rw [Pi.single_apply, if_neg hj, pow_zero]

theorem restrictFun_frameProd_pow (n : ℕ) :
    restrictFun (Wop_le_top φ) (restrictFun (inf_le_right : (⊤ : X.Opens) ⊓ pullbackChart φ i₀ ≤ pullbackChart φ i₀) (frameProd φ I i₀)) ^ n
      = dirProd φ I i₀ (fun j => if j ∈ I then n else 0) := by
  classical
  rw [restrictFun_restrictFun, frameProd, map_prod, ← Finset.prod_attach I, ← Finset.prod_pow, dirProd]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [if_pos j.2]

theorem PsiNum_surjective (h : Γ(X, Wop φ I i₀)) :
    ∃ x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I, PsiNum φ π m (i₀ := i₀) x = h := by
  classical
  obtain ⟨n, t, ht⟩ := surj_step1 φ hi₀ h
  set e₁ : ℕ := n * I.card + m with he₁
  choose k f hf using fun i => surj_step2 φ (i₀ := i₀) e₁ t i
  set K : ℕ := Finset.univ.sup k with hK

  set F : ∀ i, Γ(X, Vt φ i) := fun i => uTop φ i i₀ ^ (K - k i) * f i with hFdef
  have hF : ∀ i, restrictFun (Ot_le_Vt φ i i₀) (F i)
      = restrictFun (Ot_le_chart_left φ i i₀) (frameUnit φ i i₀) ^ (K + e₁) * restrictFun (Ot_le_Vt_right φ i i₀) t := by
    intro i
    have hKi : k i ≤ K := Finset.le_sup (f := k) (Finset.mem_univ i)
    simp only [hFdef, map_mul, map_pow, hf i, uTop, restrictFun_restrictFun]
    rw [← mul_assoc, ← pow_add, show K - k i + (k i + e₁) = K + e₁ by omega]
  obtain ⟨R, hG⟩ := surj_step3b φ (K + e₁) t F hF

  set c₁ : Fin (N + 1) → ℕ := fun j => if j ∈ I then n else 0 with hc₁
  set a : Fin (N + 1) → ℕ := c₁ + Pi.single i₀ (K + R) with ha_def
  have ha : ∀ j ∉ I, a j = 0 := fun j hj => by
    simp [ha_def, hc₁, hj, show j ≠ i₀ from fun h => hj (h ▸ hi₀)]
  have hdeg : (∑ j, (a j : ℤ)) + m = ((R + (K + e₁) : ℕ) : ℤ) := by
    have h1 : (∑ j, (c₁ j : ℤ)) = n * I.card := by
      simp only [hc₁, Nat.cast_ite, Nat.cast_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      ring
    have h2 : (∑ j, ((Pi.single i₀ (K + R) : Fin (N + 1) → ℕ) j : ℤ)) = K + R := by
      rw [Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_apply, hj]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    simp only [ha_def, Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib, h1, h2, he₁]
    push_cast; ring

  set num : ((twistGradedModule φ π).shift (m : ℤ)).M := fun d => if d = (∑ j, (a j : ℤ)) + m then (fun i => uTop φ i i₀ ^ R * F i) else 0
    with hnum_def
  have hnum : num ∈ ((twistGradedModule φ π).shift (m : ℤ)).grade (∑ j, (a j : ℤ)) := by
    refine ⟨fun d' hd' => ?_, fun hd => ?_, fun hd => ?_⟩
    · simp only [hnum_def, if_neg hd']
    · exfalso; rw [hdeg] at hd; omega
    · show TwistCompat φ _ ⊤ (num ((∑ j, (a j : ℤ)) + m))
      simp only [hnum_def, if_pos rfl, hdeg, Int.toNat_natCast]
      exact hG
  refine ⟨⟨a, ha, num, hnum⟩, ?_⟩

  have hnum_at : num ((∑ j, (a j : ℤ)) + m) = fun i => uTop φ i i₀ ^ R * F i := by simp only [hnum_def, if_pos rfl]
  have hfi₀ : restrictFun (Wop_le_top φ (I := I)) (f i₀) = restrictFun (Wop_le_top φ) t := by
    have := congrArg (restrictFun (le_inf (Wop_le_top φ (I := I)) inf_le_right : Wop φ I i₀ ≤ Ot φ i₀ i₀)) (hf i₀)
    simp only [map_mul, map_pow, restrictFun_restrictFun, frameUnit_self, map_one, one_pow, one_mul] at this
    exact this
  show restrictFun (Wop_le_top φ) (num ((∑ j, (a j : ℤ)) + m) i₀) * invProd φ I i₀ a = h
  rw [hnum_at]
  simp only [hFdef, map_mul, map_pow, uTop, frameUnit_self, map_one, one_pow, one_mul]
  rw [hfi₀, ht, ha_def, invProd_add, invProd_single_self φ hi₀, mul_one, restrictFun_frameProd_pow φ hi₀]
  calc dirProd φ I i₀ c₁ * h * invProd φ I i₀ c₁ = h * (dirProd φ I i₀ c₁ * invProd φ I i₀ c₁) := by ring
    _ = h := by rw [dirProd_mul_invProd, mul_one]

theorem Psi_surjective : Function.Surjective (Psi φ π m hi₀ (I := I)) := by
  intro g
  obtain ⟨x, hx⟩ := PsiNum_surjective φ π m hi₀ (g.val i₀)
  refine ⟨ProjSpaceCech.GradedModule.sec.mk _ I x, ?_⟩
  apply twistObj_eq_of_val_eq φ π m (interI_le φ hi₀)
  rw [Psi_mk_val_self, hx]

theorem Psi_bijective : Function.Bijective (Psi φ π m hi₀ (I := I)) :=
  ⟨Psi_injective φ π m hi₀, Psi_surjective φ π m hi₀⟩

end Surj4

end AlgebraicGeometry.ProjSpace.GMSec

end

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Nat

variable {I J : Finset (Fin (N + 1))} {i₀ : Fin (N + 1)}

theorem invProd_eq_prod_dite {K : Finset (Fin (N + 1))} (hIK : I ⊆ K) (a : Fin (N + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0) :
    invProd φ K i₀ a = ∏ j, (if hj : j ∈ I then restrictFun (Wop_le_chart φ (i₀ := i₀) (hIK hj)) (frameUnit φ j i₀) ^ a j else 1) := by
  classical
  unfold invProd

  have h1 : (∏ j ∈ K.attach, restrictFun (Wop_le_chart φ (i₀ := i₀) j.2) (frameUnit φ j i₀) ^ a j)
      = ∏ j ∈ K.attach, (fun j : Fin (N + 1) =>
          if hj : j ∈ K then restrictFun (Wop_le_chart φ (i₀ := i₀) hj) (frameUnit φ j i₀) ^ a j else 1) j := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [dif_pos j.2]
  rw [h1, Finset.prod_attach K (fun j : Fin (N + 1) =>
      if hj : j ∈ K then restrictFun (Wop_le_chart φ (i₀ := i₀) hj) (frameUnit φ j i₀) ^ a j else 1)]
  rw [Finset.prod_subset (Finset.subset_univ K)
    (f := fun j : Fin (N + 1) => if hj : j ∈ K then restrictFun (Wop_le_chart φ (i₀ := i₀) hj) (frameUnit φ j i₀) ^ a j else 1)
    (fun j _ hj => by simp only [dif_neg hj])]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hjI : j ∈ I
  · rw [dif_pos (hIK hjI), dif_pos hjI]
  · rw [dif_neg hjI]
    by_cases hjK : j ∈ K
    · rw [dif_pos hjK, ha j hjI, pow_zero]
    · rw [dif_neg hjK]

theorem restrictFun_invProd (hIJ : I ⊆ J) (a : Fin (N + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0) :
    restrictFun (inf_le_inf_right (pullbackChart φ i₀) (interI_anti φ hIJ) : Wop φ J i₀ ≤ Wop φ I i₀) (invProd φ I i₀ a)
      = invProd φ J i₀ a := by
  classical
  rw [invProd_eq_prod_dite φ (subset_refl I) a ha, invProd_eq_prod_dite φ hIJ a ha, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hjI : j ∈ I
  · rw [dif_pos hjI, dif_pos hjI, map_pow, restrictFun_restrictFun]
  · rw [dif_neg hjI, dif_neg hjI, map_one]

theorem secIncl_mk (hIJ : I ⊆ J) (x : ProjSpaceCech.GradedModule.Frac ((twistGradedModule φ π).shift (m : ℤ)) I) :
    ProjSpaceCech.GradedModule.secIncl ((twistGradedModule φ π).shift (m : ℤ)) hIJ (ProjSpaceCech.GradedModule.sec.mk _ I x)
      = ProjSpaceCech.GradedModule.sec.mk _ J ⟨x.denExp, fun j hj => x.hden j (fun h => hj (hIJ h)), x.num, x.hnum⟩ := rfl

theorem Psi_secIncl (hi₀ : i₀ ∈ I) (hIJ : I ⊆ J)
    (s : ProjSpaceCech.GradedModule.sec ((twistGradedModule φ π).shift (m : ℤ)) I) :
    Psi φ π m (hIJ hi₀) (ProjSpaceCech.GradedModule.secIncl _ hIJ s)
      = (twist π φ m).res (interI_anti φ hIJ) (Psi φ π m hi₀ s) := by
  induction s using Quotient.inductionOn with
  | h x =>
    apply twistObj_eq_of_val_eq φ π m (interI_le φ (hIJ hi₀))
    rw [show (⟦x⟧ : ProjSpaceCech.GradedModule.sec _ I) = ProjSpaceCech.GradedModule.sec.mk _ I x from rfl,
      secIncl_mk, Psi_mk_val_self, twist_res_val, Psi_mk_val_self]
    show restrictFun _ (x.num _ i₀) * invProd φ J i₀ x.denExp
      = restrictFun _ (restrictFun _ (x.num _ i₀) * invProd φ I i₀ x.denExp)
    rw [map_mul, restrictFun_restrictFun, restrictFun_invProd φ hIJ x.denExp x.hden]

end Nat

end AlgebraicGeometry.ProjSpace.GMSec

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
namespace GMSec
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A)) (m : ℕ)

section Indep

variable {I : Finset (Fin (N + 1))} {i₀ i₁ : Fin (N + 1)} (hi₀ : i₀ ∈ I) (hi₁ : i₁ ∈ I)
include hi₀ hi₁

theorem invProd_change (a : Fin (N + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0) :
    restrictFun (inf_le_left : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ Wop φ I i₀) (invProd φ I i₀ a)
      = restrictFun (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ Wop φ I i₁) (invProd φ I i₁ a)
        * restrictFun (inf_le_right : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ pullbackChart φ i₁)
            (frameUnit φ i₁ i₀) ^ (∑ j, a j) := by
  classical
  rw [invProd_eq_prod_dite φ (subset_refl I) a ha, invProd_eq_prod_dite φ (subset_refl I) a ha, map_prod, map_prod,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ I
  · rw [dif_pos hj, dif_pos hj, map_pow, map_pow, restrictFun_restrictFun, restrictFun_restrictFun, ← mul_pow,
      frameUnit_cocycle_of_le φ j i₁ i₀]
  · rw [dif_neg hj, dif_neg hj, map_one, map_one, ha j hj, pow_zero, mul_one]

theorem Psi_eq_of_mem : Psi φ π m hi₀ (I := I) = Psi φ π m hi₁ := by
  refine LinearMap.ext fun s => ?_
  induction s using Quotient.inductionOn with
  | h x =>

    apply twistObj_eq_of_val_eq φ π m (interI_le φ hi₀)
    rw [show (⟦x⟧ : ProjSpaceCech.GradedModule.sec _ I) = ProjSpaceCech.GradedModule.sec.mk _ I x from rfl, Psi_mk_val_self]

    rw [show Psi φ π m hi₁ (ProjSpaceCech.GradedModule.sec.mk _ I x) = twistObjOfFun φ π m (interI_le φ hi₁) (PsiNum φ π m x) from rfl,
      twistObjOfFun_val]

    have heq : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ = Wop φ I i₀ :=
      inf_eq_left.mpr (inf_le_left.trans (interI_le φ hi₁))
    apply restrictFun_injective_of_eq heq
    obtain ⟨a, ha, f, hf⟩ := x
    have hcompat : TwistCompat φ (((∑ j, (a j : ℤ)) + m).toNat) ⊤ (f ((∑ j, (a j : ℤ)) + m)) := hf.2.2 (by positivity)
    have hc := hcompat i₀ i₁

    simp only [PsiNum, map_mul, map_pow, restrictFun_restrictFun]
    rw [restrictFun_irrel (le_of_eq heq) inf_le_left]
    have hc' := congrArg (restrictFun (le_inf (le_inf (le_top) (inf_le_left.trans inf_le_right)) inf_le_right :
      interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ ((⊤ : X.Opens) ⊓ pullbackChart φ i₀) ⊓ pullbackChart φ i₁)) hc
    simp only [map_mul, map_pow, restrictFun_restrictFun] at hc'
    rw [hc', invProd_change φ hi₀ hi₁ a ha]

    have hto : (((∑ j, (a j : ℤ)) + m).toNat) = (∑ j, a j) + m := by
      have : ((∑ j, (a j : ℤ)) + m) = (((∑ j, a j) + m : ℕ) : ℤ) := by push_cast; rfl
      rw [this, Int.toNat_natCast]
    rw [hto, pow_add]

    have hsw := frameUnit_mul_swap_of_le φ i₀ i₁
      (inf_le_left.trans inf_le_right : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ pullbackChart φ i₀)
      (inf_le_right : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ pullbackChart φ i₁)

    calc _ = restrictFun (inf_le_left.trans inf_le_right : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ pullbackChart φ i₀)
              (frameUnit φ i₀ i₁) ^ m
            * (restrictFun _ (f ((∑ j, (a j : ℤ)) + m) i₁) * restrictFun _ (invProd φ I i₁ a))
            * (restrictFun (inf_le_left.trans inf_le_right : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ pullbackChart φ i₀)
                (frameUnit φ i₀ i₁)
              * restrictFun (inf_le_right : interI φ I ⊓ pullbackChart φ i₀ ⊓ pullbackChart φ i₁ ≤ pullbackChart φ i₁)
                (frameUnit φ i₁ i₀)) ^ (∑ j, a j) := by ring
      _ = _ := by rw [hsw, one_pow, mul_one]

end Indep

end AlgebraicGeometry.ProjSpace.GMSec

end

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.mem_basicOpen Scheme.basicOpen_res Surjective Scheme.preimage_basicOpen Spec Scheme Proj.mem_basicOpen Proj Proj.stalkIso' Proj.basicOpen Proj.basicOpen_mul Scheme.basicOpen_mul IsAffineOpen IsAffineHom Proj.awayToSection Scheme.basicOpen_le ProjectiveSpectrum.Proj.awayToSection_germ ProjSpace.X_mem_one Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom ProjSpace.pullbackChart ProjSpace.twistObj ProjSpace.twistRes ProjSpace.twistGradedModule"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "π X_mem_one ratio map pullbackChart frameUnit restrictFun TwistCompat restrictFun_restrictFun restrictFun_irrel restrictFun_refl restrictFun_algebraMap' twistObj twistObj.smul_val twistObj.algebraMap_smul twistRes twist pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle frameUnit_self twistObj.add_val twistObj.zero_val twist_res_val twistFam twistGradedModule isAffineOpen_pullbackChart isAffineOpen_pullbackOverlap twistObj.ext"
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_sec_shift_twistGradedModule_equiv'
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    (π : X ⟶ Spec (.of A)) (m : ℕ) :
    ∃ e : ∀ (I : Finset (Fin (N + 1))), I.Nonempty →
        (ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I
          ≃ₗ[A] ProjSpace.twistObj π φ m (⨅ i ∈ I, ProjSpace.pullbackChart φ i)),
      ∀ (I J : Finset (Fin (N + 1))) (hI : I.Nonempty) (hIJ : I ⊆ J)
        (x : ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I),
        e J (hI.mono hIJ) (ProjSpaceCech.GradedModule.secIncl _ hIJ x)
          = ProjSpace.twistRes π φ m
              (le_iInf fun i => le_iInf fun hi => (iInf_le _ i).trans (iInf_le _ (hIJ hi)) :
                (⨅ i ∈ J, ProjSpace.pullbackChart φ i) ≤ ⨅ i ∈ I, ProjSpace.pullbackChart φ i)
              (e I hI x) := by
  classical
  refine ⟨fun I hI => LinearEquiv.ofBijective (GMSec.Psi φ π m hI.choose_spec) (GMSec.Psi_bijective φ π m hI.choose_spec), ?_⟩
  intro I J hI hIJ x
  show GMSec.Psi φ π m (hI.mono hIJ).choose_spec (ProjSpaceCech.GradedModule.secIncl _ hIJ x)
    = ProjSpace.twistRes π φ m _ (GMSec.Psi φ π m hI.choose_spec x)
  rw [GMSec.Psi_eq_of_mem φ π m (hI.mono hIJ).choose_spec (hIJ hI.choose_spec), GMSec.Psi_secIncl]
  rfl

end AlgebraicGeometry.ProjSpace

theorem solution
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    (π : X ⟶ Spec (.of A)) (m : ℕ) :
    ∃ e : ∀ (I : Finset (Fin (N + 1))), I.Nonempty →
        (ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I
          ≃ₗ[A] ProjSpace.twistObj π φ m (⨅ i ∈ I, ProjSpace.pullbackChart φ i)),
      ∀ (I J : Finset (Fin (N + 1))) (hI : I.Nonempty) (hIJ : I ⊆ J)
        (x : ProjSpaceCech.GradedModule.sec ((ProjSpace.twistGradedModule φ π).shift (m : ℤ)) I),
        e J (hI.mono hIJ) (ProjSpaceCech.GradedModule.secIncl _ hIJ x)
          = ProjSpace.twistRes π φ m
              (le_iInf fun i => le_iInf fun hi => (iInf_le _ i).trans (iInf_le _ (hIJ hi)) :
                (⨅ i ∈ J, ProjSpace.pullbackChart φ i) ≤ ⨅ i ∈ I, ProjSpace.pullbackChart φ i)
              (e I hI x) :=
  AlgebraicGeometry.ProjSpace.exists_sec_shift_twistGradedModule_equiv' φ π m

end

end S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_sec_shift_twistGradedModule_equiv (solution)
