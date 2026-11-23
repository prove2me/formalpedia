-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_ProGTransfer
-- name    : Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_ProGTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:55.346805+00:00
-- url     : https://prove2.me/theorems/10e44482-1e93-4d03-ab3c-ce0258b8e536
-- title:
--   Pro GTransfer
-- statement:
--   Definitions and structural lemmas for Pro GTransfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/ProGTransfer.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct
namespace Formalism.L2.G.Triv
def IwProG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    IsProGrp g (iwU F k v)
def ProGTransfer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (σ : E →ₐ[F] E)
    (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsUnit J.det →
  ∀ (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x)) →
    (∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)) →
  ∀ (h : GL (Fin k) (v.adicCompletion F)) (P : Subgroup (GL (Fin k) (v.adicCompletion F)))
    (Uw : Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F))), Uw ≤ UPts σ J (v.adicCompletion F) →
    (∀ x ∈ UPts σ J (v.adicCompletion F), x ∈ Uw ↔ h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) x * h ∈ P) →
  ∀ g : ℕ, IsProGrp g P →
    letI := tensTopL (F := F) (E := E) (v.adicCompletion F)
    IsProGrp g Uw
section Level
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
end Level
end Formalism.L2.G.Triv
end


