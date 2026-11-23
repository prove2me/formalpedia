-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:55.019496+00:00
-- url     : https://prove2.me/theorems/e4986663-2189-4890-8072-4b0995e82ed1
-- title:
--   Corr ESymm Coe
-- statement:
--   Definitions and structural lemmas for Corr ESymm Coe, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CorrESymmCoe.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
def fixSp (K Q : Subgroup G) (π : Q →* G') (c₀ : G → ℂ) (ρ : K →* (W →L[ℂ] W)) : Submodule ℂ W where
  carrier := {w | ∀ r : K, ∀ hr : (r : G) ∈ Q, π ⟨r, hr⟩ = 1 → c₀ r • ρ r w = w}
  add_mem' := fun {a b} ha hb r hr h1 => by rw [map_add, smul_add, ha r hr h1, hb r hr h1]
  zero_mem' := fun r _ _ => by simp
  smul_mem' := fun a w hw r hr h1 => by rw [map_smul, smul_comm, hw r hr h1]
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
def kι (hL : IsLevi Γ K Q Γ' K' π ι c₀) : K' →* K :=
  (Q.subtype.comp (ι.comp K'.subtype)).codRestrict K (fun m => hL.ιK m m.2)
@[simp] theorem kι_coe (hL : IsLevi Γ K Q Γ' K' π ι c₀) (m : K') : ((kι hL m : K) : G) = ι m := rfl
theorem c₀_mul (hL : IsLevi Γ K Q Γ' K' π ι c₀) (a b : Q) :
    c₀ ((a * b : Q) : G) = c₀ a * c₀ b := hL.par.ch.mul a a.2 b b.2
theorem c₀_ι_left (hL : IsLevi Γ K Q Γ' K' π ι c₀) (m : G') (a : Q) :
    c₀ ((ι m * a : Q) : G) = c₀ a := by
  rw [c₀_mul hL, hL.triv, one_mul]
theorem c₀_ι_right (hL : IsLevi Γ K Q Γ' K' π ι c₀) (m : G') (a : Q) :
    c₀ ((a * ι m : Q) : G) = c₀ a := by
  rw [c₀_mul hL, hL.triv, mul_one]
theorem fix_stable (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (m : K') {w : W}
    (hw : w ∈ fixSp K Q π c₀ ρ) : ρ (kι hL m) w ∈ fixSp K Q π c₀ ρ := by
  intro r hr h1
  set u : K := kι hL m with hu
  have hconj : (((u⁻¹ * r * u : K)) : G) ∈ Q := by
    have : (((u⁻¹ * r * u : K)) : G) = (((ι (m : G'))⁻¹ * ⟨r, hr⟩ * ι (m : G') : Q) : G) := by
      simp [hu]
    rw [this]
    exact Subtype.property _
  have hval : (⟨((u⁻¹ * r * u : K) : G), hconj⟩ : Q) = (ι (m : G'))⁻¹ * ⟨r, hr⟩ * ι (m : G') := by
    apply Subtype.ext
    simp [hu]
  have hπ : π ⟨((u⁻¹ * r * u : K) : G), hconj⟩ = 1 := by
    rw [hval, map_mul, map_mul, h1, map_inv, hL.sect]
    simp
  have hc : c₀ ((u⁻¹ * r * u : K) : G) = c₀ r := by
    have : c₀ ((u⁻¹ * r * u : K) : G) = c₀ (((ι (m : G'))⁻¹ * ⟨r, hr⟩ * ι (m : G') : Q) : G) :=
      congrArg c₀ (congrArg Subtype.val hval)
    rw [this, c₀_ι_right hL, ← map_inv, c₀_ι_left hL]
  have h2 := hw (u⁻¹ * r * u) hconj hπ
  rw [hc] at h2
  have h3 : ρ r (ρ u w) = ρ u (ρ (u⁻¹ * r * u) w) := by
    have : r * u = u * (u⁻¹ * r * u) := by group
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul, this]
  rw [h3, ← map_smul, h2]
def resRep (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) :
    K' →* (fixSp K Q π c₀ ρ →L[ℂ] fixSp K Q π c₀ ρ) where
  toFun m := ((ρ (kι hL m)).comp (fixSp K Q π c₀ ρ).subtypeL).codRestrict _
    (fun v => fix_stable hL ρ m v.2)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp
    rfl
def am (ρ : K →* (W →L[ℂ] W)) (c₀ : G → ℂ) (π : Q →* G') (q : Q) (k : K) :
    fixSp K Q π c₀ ρ →L[ℂ] W := c₀ q • (ρ k⁻¹).comp (fixSp K Q π c₀ ρ).subtypeL
theorem exists_qk (hL : IsLevi Γ K Q Γ' K' π ι c₀) (g : G) : ∃ (q : Q) (k : K), g = q * k := by
  obtain ⟨p, hp, k, hk, h⟩ := hL.par.iwa g
  exact ⟨⟨p, hp⟩, ⟨k, hk⟩, h⟩
def qOf (hL : IsLevi Γ K Q Γ' K' π ι c₀) (g : G) : Q := (exists_qk hL g).choose
def kOf (hL : IsLevi Γ K Q Γ' K' π ι c₀) (g : G) : K := (exists_qk hL g).choose_spec.choose
section Ext
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def ext (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) (F : G' → E →L[ℂ] fixSp K Q π c₀ ρ)
    (g : G) : E →L[ℂ] W :=
  (am ρ c₀ π (qOf hL g) (kOf hL g)).comp (F (π (qOf hL g)))
def Equi (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W))
    (F : G' → E →L[ℂ] fixSp K Q π c₀ ρ) : Prop :=
  ∀ (g : G') (k : K') (x : E), F (g * k) x = resRep hL ρ k⁻¹ (F g x)
variable [IsTopologicalGroup G]
end Ext
section Pull
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
def Law (K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) : Prop :=
  ∀ w ∈ secSp K P c ρ, ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w
end Pull
section Main
def Corr (ρ : K →* (W →L[ℂ] W)) (L : Submodule ℂ W) (L' : Submodule ℂ (fixSp K Q π c₀ ρ)) : Prop :=
  ∀ w, w ∈ L ↔ ∃ hw : w ∈ fixSp K Q π c₀ ρ, (⟨w, hw⟩ : fixSp K Q π c₀ ρ) ∈ L'
def corrE [FiniteDimensional ℂ W] {ρ : K →* (W →L[ℂ] W)} {L : Submodule ℂ W}
    {L' : Submodule ℂ (fixSp K Q π c₀ ρ)} (h : Corr ρ L L') : L ≃L[ℂ] L' :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun w => ⟨⟨w, ((h w).1 w.2).choose⟩, ((h w).1 w.2).choose_spec⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => ⟨v.1.1, (h _).2 ⟨v.1.2, v.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
variable {A A' B B' : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup A']
  [NormedSpace ℂ A'] [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup B']
  [NormedSpace ℂ B']
def cj (e : A ≃L[ℂ] A') (f : B ≃L[ℂ] B') : (A' →L[ℂ] B') →L[ℂ] (A →L[ℂ] B) :=
  (ContinuousLinearMap.compL ℂ A B' B (f.symm : B' →L[ℂ] B)).comp
    ((ContinuousLinearMap.compL ℂ A A' B').flip (e : A →L[ℂ] A'))
def hOf (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) {L' : Type}
    [NormedAddCommGroup L'] [NormedSpace ℂ L'] (e : A ≃L[ℂ] L')
    (H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)) (z : ℂ) (g : G) : A →L[ℂ] W :=
  ext hL ρ (fun g' => (H' z g').comp (e : A →L[ℂ] L')) g
variable {P₁ P₂ : Subgroup G} {P₁' P₂' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
  {η₁ η₂ β : G → ℝ} {η₁' η₂' β' : G' → ℝ}
end Main
end GlobalTheory.CompanionTheory.RgTransfer


