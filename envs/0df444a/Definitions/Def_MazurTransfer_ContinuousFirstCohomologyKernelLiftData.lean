-- Prove2me | Definitions.Def_MazurTransfer_ContinuousFirstCohomologyKernelLiftData
-- name    : MazurTransfer_ContinuousFirstCohomologyKernelLiftData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T02:06:12.393407+00:00
-- url     : https://prove2.me/theorems/3923b64b-6819-4b4b-953d-e01da4102e6f
-- title:
--   Original continuous kernel-valued cocycle lift data and H1 compatibility
-- statement:
--   Retain the original image-valued continuous cocycle lift data, its continuous cocycle constructor and the coefficient-map and H1 class identities. The full original group, topology and action contexts are preserved. All four original types and both nonproof constructor values are compared. The lift uses the existing publicly proved continuous equivariant cocycle-lifting theorem. Named downstream consumer: exactness at the middle continuous H1 of the ordered actual norm-character sequence.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologyKernelLift, Apache-2.0. All original declaration bodies are retained; only imports are replaced by checked public dependencies.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: lift a continuous cocycle valued pointwise in the kernel
of a discrete coefficient quotient through its injective kernel map.
Named downstream consumer: continuous H1 exactness for the actual ordered
arithmetic norm-character sequences.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoefficientMapData
import Theorems.Thm_MazurTransfer_continuous_equivariant_cocycle_lift

noncomputable section
namespace MazurTransfer.ContinuousFirstCohomologyKernelLift
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologyCoefficientMap
variable (G M N P : Type) [Group G] [CommGroup M] [CommGroup N] [CommGroup P]
  [MulDistribMulAction G M] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [IsTopologicalGroup M] [IsTopologicalGroup N]
  [DiscreteTopology M] [DiscreteTopology N]
variable (i : M →* N) (hi : Function.Injective i)
  (he : ∀ (g : G) (m : M), i (g • m) = g • i m)
  (p : N →* P) (hk : ∀ n : N, p n = 1 → ∃ m : M, i m = n)
variable (z : continuousCocycles G N) (hz : ∀ g : G, p (Additive.toMul (z.val g) : N) = 1)

def liftData : {w : G → M // Continuous w ∧ groupCohomology.IsMulCocycle₁ w ∧
    ∀ g : G, i (w g) = (Additive.toMul (z.val g) : N)} := by
  have h := MazurTransfer.continuous_equivariant_cocycle_lift G M N i hi he
    (fun g : G => (Additive.toMul (z.val g) : N))
    (groupCohomology.isMulCocycle₁_of_mem_cocycles₁
      (fun g : G => (Additive.toMul (z.val g) : N)) z.val.property)
    z.property (fun g => hk _ (hz g))
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

def liftCocycle : continuousCocycles G M :=
  ⟨groupCohomology.cocyclesOfIsMulCocycle₁ (liftData G M N P i hi he p hk z hz).property.2.1,
    (liftData G M N P i hi he p hk z hz).property.1⟩

theorem map_liftCocycle :
    mapContinuousCocycles G M N i he continuous_of_discreteTopology
      (liftCocycle G M N P i hi he p hk z hz) = z := by
  apply Subtype.ext
  apply groupCohomology.cocycles₁_ext
  intro g
  apply Additive.toMul.injective
  exact (liftData G M N P i hi he p hk z hz).property.2.2 g

theorem class_liftCocycle :
    coefficientMap G M N i he continuous_of_discreteTopology
      (classMap G M (liftCocycle G M N P i hi he p hk z hz)) = classMap G N z := by
  rw [coefficientMap_classMap, map_liftCocycle]

end MazurTransfer.ContinuousFirstCohomologyKernelLift
#print axioms MazurTransfer.ContinuousFirstCohomologyKernelLift.class_liftCocycle


