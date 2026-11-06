-- Prove2me | Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
-- name    : QEC_Locality_ConnectivityTradeoff_MaxFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:50:53.228335+00:00
-- url     : https://prove2.me/theorems/e0ae8696-2a6a-4b9a-82ce-2ad9a98e85da
-- title:
--   Max Family
-- statement:
--   Definitions and structural lemmas for Max Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
universe u v
def ConnectivityGraph.HasEdge {ι : Type u} [Fintype ι]
    (G : ConnectivityGraph ι) : Prop :=
  ∃ p q : ι, G.adjacent p q
structure BKQLDPCFamily
    (ι : Nat → Type u) (κ : Nat → Type v)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)] where
  validIndex : Nat → Prop
  parameterData : ∀ n, Coding.StabilizerCode.StabilizerParameterData
    (ι := ι n) (κ := κ n)
  blockLength_eq_index : ∀ n, validIndex n → (parameterData n).blockLength = n
  distance_two_le : ∀ n, validIndex n → 2 ≤ (parameterData n).distance
  distance_le_index : ∀ n, validIndex n → (parameterData n).distance ≤ n
  fixedGeneratorGraph_hasEdge : ∀ n, validIndex n →
    (parameterData n).presentation.fixedGeneratorInteractionGraph.HasEdge
  isQLDPC : QLDPC.IsLDPCStabilizerFamily
    (fun i : {n : Nat // validIndex n} => (parameterData i.1).presentation.code)
namespace BKQLDPCFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
abbrev Index (family : BKQLDPCFamily ι κ) := {n : Nat // family.validIndex n}
abbrev presentation (family : BKQLDPCFamily ι κ) (n : Nat) :=
  (family.parameterData n).presentation
abbrev blockLength (family : BKQLDPCFamily ι κ) (n : Nat) : Nat :=
  (family.parameterData n).blockLength
abbrev encodedQubits (family : BKQLDPCFamily ι κ) (n : Nat) : Nat :=
  (family.parameterData n).encodedQubits
abbrev distance (family : BKQLDPCFamily ι κ) (n : Nat) : Nat :=
  (family.parameterData n).distance
abbrev fixedGeneratorGraph (family : BKQLDPCFamily ι κ) (i : family.Index) :
    ConnectivityGraph (ι i.1) :=
  (family.parameterData i.1).presentation.fixedGeneratorInteractionGraph
noncomputable def measuredSeparationProfile
    (family : BKQLDPCFamily ι κ) (i : family.Index) (r : Nat) : Nat :=
  twoThirdsSeparationProfile (family.fixedGeneratorGraph i) r
def validScales (family : BKQLDPCFamily ι κ) (i : family.Index) : Finset Nat :=
  Finset.Icc (family.distance i.1) i.1
theorem validScales_nonempty (family : BKQLDPCFamily ι κ) (i : family.Index) :
    (family.validScales i).Nonempty := by
  exact ⟨family.distance i.1,
    Finset.mem_Icc.mpr ⟨le_rfl, family.distance_le_index i.1 i.2⟩⟩
noncomputable def cN (family : BKQLDPCFamily ι κ)
    (i : family.Index) (r : Nat) : ℝ :=
  Real.logb (r : ℝ) (family.measuredSeparationProfile i r : ℝ)
noncomputable def observedExponents
    (family : BKQLDPCFamily ι κ) (i : family.Index) : Finset ℝ :=
  (family.validScales i).image (family.cN i)
theorem observedExponents_nonempty (family : BKQLDPCFamily ι κ) (i : family.Index) :
    (family.observedExponents i).Nonempty := by
  rcases family.validScales_nonempty i with ⟨r, hr⟩
  exact ⟨family.cN i r, Finset.mem_image.mpr ⟨r, hr, rfl⟩⟩
noncomputable def cMax (family : BKQLDPCFamily ι κ) (i : family.Index) : ℝ :=
  (family.observedExponents i).max' (family.observedExponents_nonempty i)
def EventuallyOnValidIndices
    (family : BKQLDPCFamily ι κ) (predicate : family.Index → Prop) : Prop :=
  ∃ start : Nat, ∀ (n : Nat), start ≤ n →
    ∀ hvalid : family.validIndex n, predicate ⟨n, hvalid⟩
def HasCofinalValidIndices (family : BKQLDPCFamily ι κ) : Prop :=
  ∀ start : Nat, ∃ n : Nat, start ≤ n ∧ family.validIndex n
def UniformCMaxBelowOne (family : BKQLDPCFamily ι κ) : Prop :=
  ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
    family.EventuallyOnValidIndices (fun i => family.cMax i ≤ ceiling)
end BKQLDPCFamily
end QEC.Locality


