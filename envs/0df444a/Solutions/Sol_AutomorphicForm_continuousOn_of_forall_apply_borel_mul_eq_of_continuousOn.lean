-- Prove2me | solution 1 for AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b6e114de-5ff1-5282-bbe1-008e2a78c810

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel Topology Filter

noncomputable section

namespace ICGProof

variable (F : Type) [Field F] [NumberField F]

private theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) := by
  have : (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F))
      = (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) ⁻¹' {0} := by
    ext g; rfl
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val).matrix_elem 1 0)

private theorem main
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (f : X → AdelicGL2 (𝓞 F) F → ℂ) (Φ : X → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => Φ p.1 p.2.1 p.2.2)
      (U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ
        {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})))
    (hf : ∀ x ∈ U, ∀ b ∈ adelicBorel (𝓞 F) F, ∀ k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      f x (b * k) = Φ x b k) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) := by
  classical

  choose bI kI hbI hkI1 hkI2 hdecI using fun g : AdelicGL2 (𝓞 F) F => AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  set Kc : Set (AdelicGL2 (𝓞 F) F) := {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} with hKc
  have hKc_cpt : IsCompact Kc := isCompact_adelicMaximalCompact F
  have hkI_mem : ∀ g, kI g ∈ Kc := fun g => ⟨hkI1 g, hkI2 g⟩
  have hbI_eq : ∀ g, bI g = g * (kI g)⁻¹ := fun g => by
    rw [eq_mul_inv_iff_mul_eq]; exact (hdecI g).symm
  rw [(hU.prod isOpen_univ).continuousOn_iff]
  rintro ⟨x₀, g₀⟩ ⟨hx₀, -⟩
  rw [continuousAt_iff_ultrafilter]
  intro 𝒰 h𝒰

  obtain ⟨k₁, hk₁, hk𝒰⟩ : ∃ k₁ ∈ Kc, (↑(𝒰.map (fun p : X × AdelicGL2 (𝓞 F) F => kI p.2)) : Filter _) ≤ 𝓝 k₁ := by
    apply hKc_cpt.ultrafilter_le_nhds
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    exact Filter.univ_mem' (fun p => hkI_mem p.2)
  have hk : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => kI p.2) 𝒰 (𝓝 k₁) := by
    rw [Tendsto, ← Ultrafilter.coe_map]; exact hk𝒰
  have hx : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => p.1) 𝒰 (𝓝 x₀) :=
    (continuous_fst.tendsto (x₀, g₀)).mono_left h𝒰
  have hg : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => p.2) 𝒰 (𝓝 g₀) :=
    (continuous_snd.tendsto (x₀, g₀)).mono_left h𝒰

  set b₁ : AdelicGL2 (𝓞 F) F := g₀ * k₁⁻¹ with hb₁def
  have hb : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => bI p.2) 𝒰 (𝓝 b₁) := by
    have : (fun p : X × AdelicGL2 (𝓞 F) F => bI p.2) = fun p => p.2 * (kI p.2)⁻¹ := by
      funext p; exact hbI_eq p.2
    rw [this]
    exact hg.mul hk.inv
  have hb₁ : b₁ ∈ adelicBorel (𝓞 F) F :=
    (isClosed_adelicBorel F).mem_of_tendsto hb (Filter.Eventually.of_forall (fun p => hbI p.2))

  have hxU : ∀ᶠ p in (𝒰 : Filter (X × AdelicGL2 (𝓞 F) F)), p.1 ∈ U := hx (hU.mem_nhds hx₀)

  have hΦt : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => Φ p.1 (bI p.2) (kI p.2)) 𝒰 (𝓝 (Φ x₀ b₁ k₁)) := by
    have hq : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => (p.1, bI p.2, kI p.2)) 𝒰
        (𝓝[U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ Kc)] (x₀, b₁, k₁)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hx.prodMk_nhds (hb.prodMk_nhds hk), ?_⟩
      filter_upwards [hxU] with p hp
      exact ⟨hp, hbI p.2, hkI_mem p.2⟩
    exact (hΦ (x₀, b₁, k₁) ⟨hx₀, hb₁, hk₁⟩).tendsto.comp hq

  have heq : (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) =ᶠ[(𝒰 : Filter _)]
      fun p => Φ p.1 (bI p.2) (kI p.2) := by
    filter_upwards [hxU] with p hp
    show f p.1 p.2 = _
    conv_lhs => rw [hdecI p.2]
    exact hf p.1 hp (bI p.2) (hbI p.2) (kI p.2) (hkI1 p.2) (hkI2 p.2)
  have hlim : f x₀ g₀ = Φ x₀ b₁ k₁ := by
    have hg₀ : g₀ = b₁ * k₁ := by rw [hb₁def, inv_mul_cancel_right]
    conv_lhs => rw [hg₀]
    exact hf x₀ hx₀ b₁ hb₁ k₁ hk₁.1 hk₁.2
  show Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) 𝒰 (𝓝 (f x₀ g₀))
  rw [hlim]
  exact hΦt.congr' heq.symm

end ICGProof

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    {X : Type*} [TopologicalSpace X] (U : Set X) (_hU : IsOpen U)
    (f : X → AdelicGL2 (𝓞 F) F → ℂ) (Φ : X → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℂ)
    (_hΦ : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => Φ p.1 p.2.1 p.2.2)
      (U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ
        {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})))
    (_hf : ∀ x ∈ U, ∀ b ∈ adelicBorel (𝓞 F) F, ∀ k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      f x (b * k) = Φ x b k) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) :=
  ICGProof.main F U _hU f Φ _hΦ _hf

end S_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn
end P2MW
export P2MW.S_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn (solution)
