-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicBoxLatticeCountRatio
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicBoxLatticeCountRatio
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:53.711407+00:00
-- url     : https://prove2.me/theorems/4c842ec8-d58e-49e6-bc7c-3eafd6641f26
-- title:
--   Adelic Box Lattice Count Ratio
-- statement:
--   Definitions and structural lemmas for Adelic Box Lattice Count Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicBoxLatticeCountRatio.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Pack
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def intSub {d M : ℕ} (b : Module.Basis (Fin d) F E) {Λ : Type} [AddCommGroup Λ]
    (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) : AddSubgroup Λ where
  carrier := {l | ∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin (e l)) a i) ∈ latV b v}
  zero_mem' := by
    intro v a i k
    simp [projV, projFin]
  add_mem' := by
    intro x y hx hy v a i k
    have h := add_mem (hx v a i k) (hy v a i k)
    simpa [projV, projFin, mul_add, map_add] using h
  neg_mem' := by
    intro x hx v a i k
    have h := neg_mem (hx v a i k)
    simpa [projV, projFin, mul_neg, map_neg] using h
def coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin 1 → Fin M → AF F ⊗[F] E) →+ PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ) :=
  AddMonoidHom.mk' (fun X => WithLp.toLp 1 fun p =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2.2.2)
      ((Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X p.1 p.2.1) p.2.2.1 p.2.2.2)) (by
    intro X Y
    ext p
    simp only [projInf, map_add, Pi.add_apply, Finsupp.coe_add, PiLp.add_apply]
    exact map_add _ _ _)
end GlobalTheory.CompanionTheory.SW.Pack


