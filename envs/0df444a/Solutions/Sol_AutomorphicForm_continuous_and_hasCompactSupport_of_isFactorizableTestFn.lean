-- Prove2me | solution 1 for AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/cc264dd5-a1dd-51c8-8476-593f339d56a2

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
p2m_open "NumberField.InfiniteAdeleRing AutomorphicForm Topology"
open scoped Classical

noncomputable section

namespace M4aP3B
namespace Rows
namespace TestFnTop

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField F] in
theorem continuous_archEntries : Continuous (archEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

theorem continuous_of_isArchTestFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (h : IsArchTestFactor F fa) : Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  rw [show fa = Φ ∘ archEntries F from funext hfa]
  exact hΦ.continuous.comp (continuous_archEntries F)

theorem continuous_of_isFactorizableTestFn {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    (hf : IsFactorizableTestFn F f) : Continuous f := by
  obtain ⟨fa, ff, hfa, hff, hfg⟩ := hf
  rw [show f = fun g => fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g)
    from funext hfg]
  exact ((continuous_of_isArchTestFactor F hfa).comp (AdelicLevel.continuous_glArch (𝓞 F) F)).mul
    (hff.1.continuous.comp (AdelicLevel.continuous_glFin (𝓞 F) F))

def zip (p : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => (p.1 i j, p.2 i j)

theorem continuous_zip : Continuous (zip F) :=
  continuous_matrix fun i j => (continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j)

theorem zip_glArch_glFin (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    zip F ((AdelicLevel.glArch (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)),
      (AdelicLevel.glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
      = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
  Matrix.ext fun _ _ => rfl

theorem isCompact_preimage_glArch_inter_preimage_glFin
    {Ka : Set (GL (Fin 2) (InfiniteAdeleRing F))} {Kf : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))}
    (hKa : IsCompact Ka) (hKa' : IsClosed Ka) (hKf : IsCompact Kf) (hKf' : IsClosed Kf) :
    IsCompact (AdelicLevel.glArch (𝓞 F) F ⁻¹' Ka ∩ AdelicLevel.glFin (𝓞 F) F ⁻¹' Kf) := by
  set K := AdelicLevel.glArch (𝓞 F) F ⁻¹' Ka ∩ AdelicLevel.glFin (𝓞 F) F ⁻¹' Kf with hK
  have he : IsClosedEmbedding (Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) :=
    Units.isClosedEmbedding_embedProduct
  have hKclosed : IsClosed K :=
    (hKa'.preimage (AdelicLevel.continuous_glArch (𝓞 F) F)).inter
      (hKf'.preimage (AdelicLevel.continuous_glFin (𝓞 F) F))

  let Ψ : (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ×
      (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) →
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) × (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ :=
    fun q => (zip F q.1, MulOpposite.op (zip F q.2))
  have hΨ : Continuous Ψ :=
    ((continuous_zip F).comp continuous_fst).prodMk
      (MulOpposite.continuous_op.comp ((continuous_zip F).comp continuous_snd))
  have hC : IsCompact (Ψ '' (((Units.val '' Ka) ×ˢ (Units.val '' Kf)) ×ˢ
      (((fun u => ((u⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) '' Ka) ×ˢ
       ((fun u => ((u⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))) '' Kf)))) :=
    (((hKa.image Units.continuous_val).prod (hKf.image Units.continuous_val)).prod
      ((hKa.image Units.continuous_coe_inv).prod (hKf.image Units.continuous_coe_inv))).image hΨ
  have hsub : Units.embedProduct _ '' K ⊆ Ψ '' (((Units.val '' Ka) ×ˢ (Units.val '' Kf)) ×ˢ
      (((fun u => ((u⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) '' Ka) ×ˢ
       ((fun u => ((u⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))) '' Kf))) := by
    rintro _ ⟨g, ⟨hga, hgf⟩, rfl⟩
    refine ⟨(((AdelicLevel.glArch (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)),
        (AdelicLevel.glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))),
        (((AdelicLevel.glArch (𝓞 F) F g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)),
         (((AdelicLevel.glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)))),
      ⟨⟨⟨_, hga, rfl⟩, ⟨_, hgf, rfl⟩⟩, ⟨⟨_, hga, rfl⟩, ⟨_, hgf, rfl⟩⟩⟩, ?_⟩
    show (zip F _, MulOpposite.op (zip F _)) = _
    rw [Units.embedProduct_apply, zip_glArch_glFin, ← map_inv, ← map_inv, zip_glArch_glFin]
  exact he.isInducing.isCompact_iff.mpr (hC.of_isClosed_subset (he.isClosedMap K hKclosed) hsub)

theorem hasCompactSupport_of_isFactorizableTestFn {f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}
    (hf : IsFactorizableTestFn F f) : HasCompactSupport f := by
  obtain ⟨fa, ff, hfa, hff, hfg⟩ := hf
  refine HasCompactSupport.intro'
    (isCompact_preimage_glArch_inter_preimage_glFin F hfa.2.isCompact (isClosed_tsupport fa)
      hff.2.isCompact (isClosed_tsupport ff))
    (((isClosed_tsupport fa).preimage (AdelicLevel.continuous_glArch (𝓞 F) F)).inter
      ((isClosed_tsupport ff).preimage (AdelicLevel.continuous_glFin (𝓞 F) F))) fun g hg => ?_
  rw [hfg]
  rcases not_and_or.mp hg with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem continuous_and_hasCompactSupport_of_isFactorizableTestFn_impl (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f :=
  ⟨continuous_of_isFactorizableTestFn F hf, hasCompactSupport_of_isFactorizableTestFn F hf⟩

theorem gate_zero : Continuous (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) ∧
    HasCompactSupport (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) :=
  continuous_and_hasCompactSupport_of_isFactorizableTestFn_impl F _ (isFactorizableTestFn_zero F)

end M4aP3B.Rows.TestFnTop

end

p2m_open "NumberField NumberField.InfinitePlace.NumberField IsDedekindDomain"

theorem solution (F : Type) [Field F] [NumberField F]
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : AutomorphicForm.IsFactorizableTestFn F f) :
    Continuous f ∧ HasCompactSupport f := by
  exact M4aP3B.Rows.TestFnTop.continuous_and_hasCompactSupport_of_isFactorizableTestFn_impl F f hf

end S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn (solution)
