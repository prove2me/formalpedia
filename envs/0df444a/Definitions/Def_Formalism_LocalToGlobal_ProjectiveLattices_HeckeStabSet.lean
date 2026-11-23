-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeStabSet
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_HeckeStabSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:23.969028+00:00
-- url     : https://prove2.me/theorems/778030f0-93cb-4aa1-bd2e-1f7c1ab85030
-- title:
--   Hecke Stab Set
-- statement:
--   Definitions and structural lemmas for Hecke Stab Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/HeckeStabSet.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
section Hecke
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable (hkIdx : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], pts Ω → Type)
variable (quotR : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), hkIdx Ω y → pts Ω → Prop)
def hkTerm (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y) : Ω :=
  open Classical in
  if h : ∃ z : pts Ω, quotR Ω y H z then evalAt pts mapR f h.choose else 0
def hkVal (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) : Ω :=
  ∑ᶠ H : hkIdx Ω y, hkTerm pts mapR hkIdx quotR f y H
def HkFin : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), Finite (hkIdx Ω y)
theorem hkTerm_add (f g : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω)
    (H : hkIdx Ω y) :
    hkTerm pts mapR hkIdx quotR (f + g) y H = hkTerm pts mapR hkIdx quotR f y H + hkTerm pts mapR hkIdx quotR g y H := by
  unfold hkTerm
  split_ifs with h
  · exact evalAt_add _ _ _ _ _
  · exact (add_zero 0).symm
theorem hkTerm_smul (c : K) (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω)
    (H : hkIdx Ω y) :
    hkTerm pts mapR hkIdx quotR (c • f) y H = algebraMap K Ω c * hkTerm pts mapR hkIdx quotR f y H := by
  unfold hkTerm
  split_ifs with h
  · exact evalAt_smul _ _ _ _ _
  · exact (mul_zero _).symm
theorem hkVal_add (hF : HkFin pts hkIdx) (f g : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (y : pts Ω) :
    hkVal pts mapR hkIdx quotR (f + g) y = hkVal pts mapR hkIdx quotR f y + hkVal pts mapR hkIdx quotR g y := by
  haveI := hF Ω y
  unfold hkVal
  simp_rw [hkTerm_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
theorem hkVal_smul (c : K) (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) :
    hkVal pts mapR hkIdx quotR (c • f) y = algebraMap K Ω c * hkVal pts mapR hkIdx quotR f y := by
  unfold hkVal
  simp_rw [hkTerm_smul]
  exact (mul_finsum (fun H => hkTerm pts mapR hkIdx quotR f y H) (algebraMap K Ω c)).symm
def HkRel (c : K) (f g : Rules pts) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω),
    evalAt pts mapR g y = algebraMap K Ω c * hkVal pts mapR hkIdx quotR f y
def HkTotal : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y), ∃ z, quotR Ω y H z
def HkFun : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y) (z z' : pts Ω),
    quotR Ω y H z → quotR Ω y H z' → mapR (AlgHom.id K Ω) z z'
def PtsDetect [Fintype ι] (e : ι → ℕ) : Prop :=
  ∀ g ∈ secW pts mapR borR e, (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω),
    evalAt pts mapR g y = 0) → g = 0
def HkEx [Fintype ι] (e : ι → ℕ) (c : K) : Prop :=
  ∀ f ∈ secW pts mapR borR e, ∃ g ∈ secW pts mapR borR e, HkRel pts mapR hkIdx quotR c f g
variable {pts mapR borR hkIdx quotR}
theorem hkRel_unique [Fintype ι] {e : ι → ℕ} (hD : PtsDetect pts mapR borR e) {c : K} {f g g' : Rules pts}
    (hg : g ∈ secW pts mapR borR e) (hg' : g' ∈ secW pts mapR borR e)
    (h : HkRel pts mapR hkIdx quotR c f g) (h' : HkRel pts mapR hkIdx quotR c f g') : g = g' := by
  have hz : g - g' = 0 := by
    refine hD _ (Submodule.sub_mem _ hg hg') ?_
    intro Ω _ _ _ y
    rw [sub_eq_add_neg, ← neg_one_smul K g', evalAt_add, evalAt_smul, h Ω y, h' Ω y]
    simp
  exact sub_eq_zero.1 hz
theorem hkRel_add (hF : HkFin pts hkIdx) {c : K} {f f' g g' : Rules pts} (h : HkRel pts mapR hkIdx quotR c f g)
    (h' : HkRel pts mapR hkIdx quotR c f' g') : HkRel pts mapR hkIdx quotR c (f + f') (g + g') := by
  intro Ω _ _ _ y
  rw [evalAt_add, h Ω y, h' Ω y, hkVal_add _ _ _ _ hF, mul_add]
theorem hkRel_smul {c : K} (a : K) {f g : Rules pts} (h : HkRel pts mapR hkIdx quotR c f g) :
    HkRel pts mapR hkIdx quotR c (a • f) (a • g) := by
  intro Ω _ _ _ y
  rw [evalAt_smul, h Ω y, hkVal_smul, mul_left_comm]
def hkOp [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) : secW pts mapR borR e →ₗ[K] secW pts mapR borR e where
  toFun f := ⟨(hE f.1 f.2).choose, (hE f.1 f.2).choose_spec.1⟩
  map_add' f f' := by
    apply Subtype.ext
    exact hkRel_unique hD (hE _ (f + f').2).choose_spec.1
      (Submodule.add_mem _ (hE f.1 f.2).choose_spec.1 (hE f'.1 f'.2).choose_spec.1)
      (hE _ (f + f').2).choose_spec.2 (hkRel_add hF (hE f.1 f.2).choose_spec.2 (hE f'.1 f'.2).choose_spec.2)
  map_smul' a f := by
    apply Subtype.ext
    exact hkRel_unique hD (hE _ (a • f).2).choose_spec.1
      (Submodule.smul_mem _ a (hE f.1 f.2).choose_spec.1)
      (hE _ (a • f).2).choose_spec.2 (hkRel_smul a (hE f.1 f.2).choose_spec.2)
def HeckeStabW [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (W : Submodule K (secW pts mapR borR e)) : Prop :=
  ∀ f ∈ W, hkOp hE hD hF f ∈ W
def HeckeStabSet [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (M : Set (secW pts mapR borR e)) : Prop :=
  ∀ f ∈ M, hkOp hE hD hF f ∈ M
end Hecke
end Formalism.L2.Pj


