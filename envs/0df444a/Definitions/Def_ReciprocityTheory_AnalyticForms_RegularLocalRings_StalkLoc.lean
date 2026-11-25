-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:23.582823+00:00
-- url     : https://prove2.me/theorems/6e2acc8f-cf84-5ce7-a461-87c829c0281e
-- title:
--   Stalk Loc
-- statement:
--   Definitions and structural lemmas for Stalk Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_le_ptIdeal_iff__72a6f546eb9f
import Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_isUnit_germ_secH_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_secH_surjective
import Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_quot_mk
import Theorems.Thm_ReciprocityTheory_AnForm_R_isLocalization_locRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_mk_mem_ptQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
variable (s) in

structure AffPres where

  V : W.Opens

  n : ℕ

  K : Ideal (MvPolynomial (Fin n) ℂ)

  iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K))
  hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
    V.ι ≫ s
namespace AffPres
variable (P : AffPres s)
def secHom : MvPolynomial (Fin P.n) ℂ →+* Γ(W, P.V) :=
  P.V.topIso.hom.hom.comp (P.iso.hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv.hom.comp (Ideal.Quotient.mk P.K)))
def ptOf (x : W) (hx : x ∈ P.V) : Ideal (MvPolynomial (Fin P.n) ℂ) :=
  (P.iso.hom.base ⟨x, hx⟩).asIdeal.comap (Ideal.Quotient.mk P.K)
def coord (x : W) (hx : x ∈ P.V) : Fin P.n → ℂ :=
  fun j => Classical.epsilon fun c : ℂ => X j - C c ∈ P.ptOf x hx
theorem ptOf_eq_ptIdeal (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    P.ptOf x hx = ptIdeal (P.coord x hx) := by
  classical
  have hcV : IsClosed ({⟨x, hx⟩} : Set P.V) := by
    have h1 : ({⟨x, hx⟩} : Set P.V) = Subtype.val ⁻¹' {x} := by
      ext z
      constructor
      · intro h
        rw [Set.mem_singleton_iff.mp h]
        exact Set.mem_singleton x
      · intro h
        exact Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp (Set.mem_preimage.mp h)))
    rw [h1]
    exact hc.preimage continuous_subtype_val
  have hcy : IsClosed ({P.iso.hom.base ⟨x, hx⟩} :
      Set (Spec (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K)))) := by
    have h := (Scheme.homeoOfIso P.iso).isClosedMap _ hcV
    first
    | (convert h using 1; exact Set.image_singleton.symm)
    | (convert h using 1; ext z; simp)
    | (simp only [Set.image_singleton] at h; exact h)
  have hmax : (P.iso.hom.base ⟨x, hx⟩).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcy
  have hmax' : (P.ptOf x hx).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨q, hq⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hmax'
  have hq' : P.ptOf x hx = ptIdeal q := by
    rw [hq]
    ext h
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp only [ptIdeal, RingHom.mem_ker]
    first
    | rw [MvPolynomial.coe_aeval_eq_eval]
    | exact Iff.rfl
    | simp [MvPolynomial.aeval_eq_eval]
  have hcoord : P.coord x hx = q := by
    funext j
    have hex : ∃ c : ℂ, X j - C c ∈ P.ptOf x hx := by
      refine ⟨q j, ?_⟩
      rw [hq']
      simp [ptIdeal]
    have hspec := Classical.epsilon_spec hex
    have h2 : X j - C (P.coord x hx j) ∈ ptIdeal q := hq'.le hspec
    simp only [ptIdeal, RingHom.mem_ker] at h2
    simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] at h2
    exact (sub_eq_zero.mp h2).symm
  rw [hq', hcoord]
theorem eval_coord_eq_zero (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    ∀ h ∈ P.K, eval (P.coord x hx) h = 0 := by
  intro h hh
  have hmem : h ∈ P.ptOf x hx := by
    show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base ⟨x, hx⟩).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hh]
    exact Ideal.zero_mem _
  rw [P.ptOf_eq_ptIdeal x hx hc] at hmem
  simp only [ptIdeal, RingHom.mem_ker] at hmem
  exact hmem
theorem exists_stalkEquiv (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    ∃ ψ : W.presheaf.stalk x ≃+* locRing P.K (P.coord x hx), ∀ f : MvPolynomial (Fin P.n) ℂ,
      ψ (W.presheaf.germ P.V x hx (P.secHom f)) = algebraMap _ (locRing P.K (P.coord x hx)) f := by
  set p := P.coord x hx
  have hpt := P.ptOf_eq_ptIdeal x hx hc
  have hK : P.K ≤ ptIdeal p := (le_ptIdeal_iff' _ _).2 (P.eval_coord_eq_zero x hx hc)
  have hV : IsAffineOpen P.V := IsAffine.of_isIso P.iso.hom
  let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hx⟩ : P.V)
  have := hV.isLocalization_stalk ⟨x, hx⟩
  set Q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let _ := ptQ_isPrime hK
  have hloc : IsLocalization (ptQ P.K p).primeCompl (locRing P.K p) := isLocalization_locRing hK
  have hQ : ∀ f, P.secHom f ∈ Q ↔ f ∈ ptIdeal p := by
    intro f
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (W.presheaf.stalk x) Q]
    change W.presheaf.germ P.V x hx (P.secHom f) ∈ _ ↔ _
    have hu := StalkLocB.isUnit_germ_secH_iff P.V P.K P.iso ⟨x, hx⟩ f
    change IsUnit (W.presheaf.germ P.V x hx (P.secHom f)) ↔ _ at hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu, not_not, ← Ideal.mem_comap]
    change f ∈ P.ptOf x hx ↔ _
    rw [hpt]
  let e : Γ(W, P.V) ≃+* (MvPolynomial (Fin P.n) ℂ ⧸ P.K) := (StalkLocB.phiE P.V P.K P.iso).symm
  have he : ∀ f, e (P.secHom f) = Ideal.Quotient.mk P.K f := fun f =>
    (StalkLocB.phiE P.V P.K P.iso).symm_apply_apply (Ideal.Quotient.mk P.K f)
  have H : Q.primeCompl.map e.toMonoidHom = (ptQ P.K p).primeCompl := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨f, rfl⟩ := StalkLocB.secH_surjective P.V P.K P.iso a
      show e (P.secHom f) ∉ ptQ P.K p
      rw [he, mk_mem_ptQ hK, ← hQ]
      exact ha
    · intro hy
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨P.secHom f, ?_, he f⟩
      show P.secHom f ∉ Q
      rw [hQ, ← mk_mem_ptQ hK]
      exact hy
  refine ⟨IsLocalization.ringEquivOfRingEquiv (W.presheaf.stalk x) (locRing P.K p) e H, fun f => ?_⟩
  have h1 := IsLocalization.ringEquivOfRingEquiv_eq (S := W.presheaf.stalk x) (Q := locRing P.K p) H
    (P.secHom f)
  rw [he, algebraMap_quot_mk] at h1
  exact h1
def stalkEquiv (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    W.presheaf.stalk x ≃+* locRing P.K (P.coord x hx) :=
  Classical.choose (P.exists_stalkEquiv x hx hc)
end AffPres
end
end ReciprocityTheory.AnForm.R


