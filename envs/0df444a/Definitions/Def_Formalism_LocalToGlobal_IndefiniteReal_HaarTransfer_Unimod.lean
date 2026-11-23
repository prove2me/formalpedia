-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_Unimod
-- name    : Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_Unimod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:45.235144+00:00
-- url     : https://prove2.me/theorems/38dc9795-2d17-4e4a-bffc-9a8f97e2b20f
-- title:
--   Unimod
-- statement:
--   Definitions and structural lemmas for Unimod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HaarTransfer/Unimod.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.Leaf
open MeasureTheory
def HaarRightInvProd : Prop :=
  ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [T2Space G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [T2Space G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂],
    (∀ μ : Measure G₁, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    (∀ μ : Measure G₂, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → μ.IsMulRightInvariant
def HaarRightInvPi : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)]
    [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)],
    (∀ i, ∀ μ : Measure (G i), μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ μ : Measure (∀ i, G i), μ.IsHaarMeasure → μ.IsMulRightInvariant
def HaarRightInvTransfer : Prop :=
  ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (_e : G ≃ₜ* H),
    (∀ μ : Measure G, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
      ∀ ν : Measure H, ν.IsHaarMeasure → ν.IsMulRightInvariant
end Formalism.IndefR.Leaf


