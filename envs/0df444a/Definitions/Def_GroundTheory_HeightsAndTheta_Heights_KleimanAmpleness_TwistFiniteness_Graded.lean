-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:08.282914+00:00
-- url     : https://prove2.me/theorems/76eac8df-7f12-4fba-bb12-d08bda22fe03
-- title:
--   Graded
-- statement:
--   Definitions and structural lemmas for Graded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/Graded.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mem_tgr_0b163f9c37ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_mem_tgr_ca561eb3db71
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844

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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
namespace TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
def projT (c : ℤ) : LA Ω →ₗ[Ω] LA Ω :=
  GradedAlgebra.proj (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) c
theorem projT_apply (c : ℤ) (a : LA Ω) :
    projT c a = (DirectSum.decompose (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) a c :
      LA Ω) :=
  GradedAlgebra.proj_apply _ _ _
theorem projT_mem (c : ℤ) (a : LA Ω) : projT c a ∈ tgr c := by
  rw [projT_apply]; exact Subtype.property _
theorem projT_of_mem {a : LA Ω} {d : ℤ} (ha : a ∈ tgr d) (c : ℤ) :
    projT c a = if d = c then a else 0 := by
  rw [projT_apply]
  split_ifs with h
  · subst h; exact DirectSum.decompose_of_mem_same _ ha
  · exact DirectSum.decompose_of_mem_ne _ ha h
theorem projT_mul_of_mem {a : LA Ω} {d : ℤ} (ha : a ∈ tgr d) (b : LA Ω) (c : ℤ) :
    projT c (a * b) = a * projT (c - d) b := by
  have := DirectSum.coe_decompose_mul_add_of_left_mem
    (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) (j := c - d) ha (b := b)
  rw [add_sub_cancel] at this
  rw [projT_apply, projT_apply]
  exact this
theorem exists_sum_projT (a : LA Ω) : ∃ F : Finset ℤ, ∑ c ∈ F, projT c a = a := by
  classical
  refine ⟨(DirectSum.decompose (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω)) a).support, ?_⟩
  simp only [projT_apply]
  exact DirectSum.sum_support_decompose _ a
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
def genT (j : Fin n0) : Amb x η := (toA x η).symm (single (d0 j, 0) (g0 j))
def TMod : Submodule (Poly (Sy S r) N) (Amb x η) := Submodule.span _ (Set.range (genT x η n0 d0 g0))
instance TMod.finite : Module.Finite (Poly (Sy S r) N) (TMod x η S n0 d0 g0) :=
  Module.Finite.span_of_finite _ (Set.finite_range _)
theorem projT_mem_TMod {m : Amb x η} (hm : m ∈ TMod x η S n0 d0 g0) (c : ℤ) :
    (toA x η).symm (projT c (toA x η m)) ∈ TMod x η S n0 d0 g0 := by
  induction hm using Submodule.span_induction generalizing c with
  | mem m hm =>
    obtain ⟨j, rfl⟩ := hm
    rw [genT, AddEquiv.apply_symm_apply, projT_of_mem (single_mem_tgr _ _ _)]
    split_ifs
    · exact Submodule.subset_span ⟨j, rfl⟩
    · rw [map_zero]; exact zero_mem _
  | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, map_add, map_add]; exact add_mem (ha c) (hb c)
  | smul p m _ hm =>
    have hsum : toA x η (p • m) = ∑ d ∈ Finset.range (p.totalDegree + 1),
        phi x η S (homogeneousComponent d p) * toA x η m := by
      rw [toA_smulP, ← Finset.sum_mul, ← map_sum, sum_homogeneousComponent]
    rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    rw [projT_mul_of_mem (phi_mem_tgr x η S (homogeneousComponent_isHomogeneous d p))]
    have h := Submodule.smul_mem _ (homogeneousComponent d p) (hm (c - d))
    convert h using 1
    apply (toA x η).injective
    rw [toA_smulP, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
def pieceM (c : ℤ) : Submodule (Sy S r) (TMod x η S n0 d0 g0) where
  carrier := {m | toA x η (m : Amb x η) ∈ tgr c}
  add_mem' {a b} ha hb := by
    change toA x η ((a : Amb x η) + b) ∈ tgr c
    rw [map_add]; exact add_mem ha hb
  zero_mem' := by
    change toA x η ((0 : TMod x η S n0 d0 g0) : Amb x η) ∈ tgr c
    rw [Submodule.coe_zero, map_zero]; exact zero_mem _
  smul_mem' s m hm := by
    change toA x η ((s • m : TMod x η S n0 d0 g0) : Amb x η) ∈ tgr c
    rw [Submodule.coe_smul_of_tower, toA_smulSy]
    simpa using SetLike.mul_mem_graded (psi_mem_tgr η S s) hm
theorem isInternal_pieceM : DirectSum.IsInternal (pieceM x η S n0 d0 g0) := by
  classical
  let 𝒜 := (gradeBy Ω (AddMonoidHom.fst ℤ ℤ) : ℤ → Submodule Ω (LA Ω))
  let pc : ∀ c, pieceM x η S n0 d0 g0 c →+ 𝒜 c := fun c =>
    { toFun := fun m => ⟨toA x η ((m : TMod x η S n0 d0 g0) : Amb x η), m.2⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let Φ : (DirectSum ℤ fun c => pieceM x η S n0 d0 g0 c) →+ DirectSum ℤ fun c => 𝒜 c :=
    DFinsupp.mapRange.addMonoidHom pc
  have hΦ : ∀ v, DirectSum.coeAddMonoidHom 𝒜 (Φ v) =
      toA x η ((DirectSum.coeAddMonoidHom (pieceM x η S n0 d0 g0) v : TMod x η S n0 d0 g0) : Amb x η) := by
    intro v
    induction v using DirectSum.induction_on with
    | zero => simp
    | of c m =>
      rw [DirectSum.coeAddMonoidHom_of]
      have : Φ (DirectSum.of (fun c => ↥(pieceM x η S n0 d0 g0 c)) c m) =
          DirectSum.of (fun c => ↥(𝒜 c)) c (pc c m) :=
        DFinsupp.mapRange_single (hf := fun c => map_zero (pc c))
      rw [this, DirectSum.coeAddMonoidHom_of]
      rfl
    | add a b ha hb => simp only [map_add, ha, hb, Submodule.coe_add]
  constructor
  · intro v w hvw
    have h1 : Φ v = Φ w := (gradeBy.isInternal (R := Ω) (AddMonoidHom.fst ℤ ℤ)).1 (by
      change DirectSum.coeAddMonoidHom 𝒜 (Φ v) = DirectSum.coeAddMonoidHom 𝒜 (Φ w)
      rw [hΦ, hΦ, hvw])
    refine DFinsupp.ext fun c => ?_
    have h2 := DFunLike.congr_fun h1 c
    have h3 : pc c (v c) = pc c (w c) := by
      rw [← DFinsupp.mapRange_apply (hf := fun c => map_zero (pc c)),
        ← DFinsupp.mapRange_apply (hf := fun c => map_zero (pc c))]
      exact h2
    have h4 : ((pc c (v c) : 𝒜 c) : LA Ω) = ((pc c (w c) : 𝒜 c) : LA Ω) := by rw [h3]
    exact Subtype.ext (Subtype.ext ((toA x η).injective h4))
  · intro m
    obtain ⟨F, hF⟩ := exists_sum_projT (toA x η (m : Amb x η))
    refine ⟨∑ c ∈ F, DirectSum.of (fun c => pieceM x η S n0 d0 g0 c) c
      ⟨⟨(toA x η).symm (projT c (toA x η (m : Amb x η))), projT_mem_TMod x η S n0 d0 g0 m.2 c⟩, by
        change toA x η ((toA x η).symm _) ∈ tgr c
        rw [AddEquiv.apply_symm_apply]; exact projT_mem c _⟩, ?_⟩
    apply Subtype.ext
    apply (toA x η).injective
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of, Submodule.coe_sum, map_sum, AddEquiv.apply_symm_apply]
    exact hF
def tgraded : GradedPMod (Sy S r) N (TMod x η S n0 d0 g0) where
  piece := pieceM x η S n0 d0 g0
  isInternal := isInternal_pieceM x η S n0 d0 g0
  smul_mem d c p m hp hm := by
    change toA x η ((p • m : TMod x η S n0 d0 g0) : Amb x η) ∈ tgr (c + d)
    rw [Submodule.coe_smul, toA_smulP, add_comm]
    exact SetLike.mul_mem_graded (phi_mem_tgr x η S hp) hm
end TwistFin
end
end GroundTheory.Heights₂.Heights.Kleiman


