-- Prove2me | Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
-- name    : QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:50:57.266288+00:00
-- url     : https://prove2.me/theorems/6dab6d27-1514-4487-a352-732e64517b21
-- title:
--   RXCoarse Graining
-- statement:
--   Definitions and structural lemmas for RXCoarse Graining, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXCoarseGraining.lean

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC
namespace Coding
namespace MultiscaleDecoder
namespace RXCoarseGraining
open scoped BigOperators
universe u v
abbrev Field := BDL26Field
abbrev RXVertex (X Q Z : Type v) := X ⊕ (Q ⊕ Z)
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
noncomputable def diagonalMap
    {Z : Type v} [Fintype Z] :
    Word Field Z →ₗ[Field] Word Field (Z × Fin 2) where
  toFun signal := fun p => signal p.1
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl
structure RXInducedMaps
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {X Q : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] where
  adjacencyMap : Word Field X →ₗ[Field] Word Field Q
  gXQ0 : Word Field X →ₗ[Field] Word Field Q
  gXQ0_eq_adjacency : gXQ0 = adjacencyMap
  qzAdjacency : Word Field Q →ₗ[Field] Word Field (C2 i.castSucc)
  gQZ1 : Word Field Q →ₗ[Field]
    Word Field (C2 i.castSucc × Fin 2)
  gQZ1_eq_diagonal_comp :
    gQZ1 = (diagonalMap (Z := C2 i.castSucc)).comp qzAdjacency
  /-- The subset of upper syndrome coordinates belonging to the doubled Z sector. -/
  zSector : Finset (C2 i.succ)
  zPairEquiv : (C2 i.castSucc × Fin 2) ≃
    LocalRegionIndex zSector
  map2_diagonal : ∀ (s : D.family.Cochain2 i.castSucc)
    (z : C2 i.castSucc) (b : Fin 2),
    (D.rxMap i).map2 s (zPairEquiv (z, b)).1 = s z
  map2_auxiliary_zero : ∀ (s : D.family.Cochain2 i.castSucc)
    (p : C2 i.succ), p ∉ zSector → (D.rxMap i).map2 s p = 0
noncomputable def correctionRegionUnion
    {V : Type v} {S C : Type u} [Fintype V] [DecidableEq V]
    [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (L : LocalComplexData V S C) : Finset C :=
  Finset.biUnion Finset.univ (fun v => L.correctionRegion v)
def SupportedOn
    {α : Type u} [Fintype α] [DecidableEq α]
    (Y : Finset α) (f : Word Field α) : Prop :=
  ∀ a, a ∉ Y → f a = 0
structure RXCoarseGrainingData
    (D : BDL26DecoderData depth C0 C1 C2) (i : StepIndex depth)
    {X Q : Type v} [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q]
    (Lx : LocalComplexData X (C2 i.succ) (C1 i.succ))
    (Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ))
    {Z : Type v} [Fintype Z] [DecidableEq Z]
    (Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ))
    {X0 : X → Type u} {Q0 : Q → Type u}
    {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
    [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
    [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)] where
  induced : RXInducedMaps (X := X) (Q := Q) D i
  contract : RXConstructionContractSlice (X0 := X0) (Q0 := Q0)
      (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz
  xSector : Finset (C2 i.succ)
  qSector : Finset (C2 i.succ)
  zSector : Finset (C2 i.succ)
  zSector_eq_induced : zSector = induced.zSector
  xSector_eq_regions : xSector = rxRegionUnion Lx
  qSector_eq_regions : qSector = rxRegionUnion Lq
  sectors_pairwise_disjoint :
    Disjoint xSector qSector ∧ Disjoint xSector zSector ∧ Disjoint qSector zSector
  sectors_cover : xSector ∪ qSector ∪ zSector = Finset.univ
  /-- The full Q correction coordinates, i.e. the union of the Q local fibres. -/
  qCorrectionSector : Finset (C1 i.succ)
  qCorrectionSector_eq_regions : qCorrectionSector = correctionRegionUnion Lq
  correction_sectors_cover :
    correctionRegionUnion Lx ∪ qCorrectionSector = Finset.univ
  correction_sectors_disjoint :
    Disjoint (correctionRegionUnion Lx) qCorrectionSector
  /-- The support sector reserved for the chosen local cohomology section. -/
  qRepresentativeSector : Finset (C1 i.succ)
  qRepresentativeSector_subset_qCorrectionSector :
    qRepresentativeSector ⊆ qCorrectionSector
  /-- A selected cocycle representative for every local cohomology class. -/
  cqRepresentative : ∀ q,
    (contract.rx_local_complexes.cq q).middleCohomology →ₗ[Field]
      (contract.rx_local_complexes.cq q).middleCocycleCode.carrier
  /-- The selected representative projects back to its quotient class. -/
  cqRepresentative_mkQ : ∀ q h,
    (contract.rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
        (cqRepresentative q h) = h
  /-- Only the selected section output, not arbitrary cocycles, is supported
      on the representative sector. -/
  cqRepresentative_supported : ∀ q h p,
    p.1 ∉ qRepresentativeSector → (cqRepresentative q h).1 p = 0
  /-- The local cohomology classes identify with the lower one-cochain space. -/
  qCohomologyEquiv :
    (∀ q, (contract.rx_local_complexes.cq q).middleCohomology) ≃ₗ[Field]
      D.family.Cochain1 i.castSucc
  /-- Structural formula for the induced `map1`: it extends the selected
      local quotient representatives and sums them. -/
  rxMap1_eq_cqRepresentative : ∀ lower,
    (D.rxMap i).map1 lower =
      ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        ((cqRepresentative q ((qCohomologyEquiv.symm lower) q)).1)
  /--
  Global bookkeeping for the local `δ⁰` stabilizer adjustment.  This is a
  structural decomposition of the lifted local coboundaries, not a decoder
  conclusion.
  -/
  cqDelta0_sum_decomposition : ∀ (s : ∀ q, Word Field (Q0 q)),
    D.family.coboundary0 i.succ
        (∑ q : Q, contract.support_decomposition.cqLift0 q (s q)) =
      ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
        (contract.rx_local_complexes.cqDelta0 q (s q))
  /-- F11 cross-sector non-interference of the Q-to-Z connecting boundary. -/
  cqFlow_outside_xSector : ∀ q f p, p ∈ xSector →
    contract.support_decomposition.cqFlow q f p = 0
  /-- The source decoding graph, with its canonical `X → Q → Z` labels. -/
  levelGraph : LevelGraph (RXVertex X Q Z)
  levelGraph_kind_x : ∀ x, levelGraph.kind (Sum.inl x) = .x
  levelGraph_kind_q : ∀ q, levelGraph.kind (Sum.inr (Sum.inl q)) = .q
  levelGraph_kind_z : ∀ z, levelGraph.kind (Sum.inr (Sum.inr z)) = .z
  /-- The top coordinate owner used by the source-local restrictions. -/
  topCenter : C2 i.succ → RXVertex X Q Z
  /-- Coarse coordinates are given their own `Z`-side graph centre. -/
  coarseCenter : C2 i.castSucc → RXVertex X Q Z
  coarseCenter_is_z : ∀ z, ∃ z0 : Z,
    coarseCenter z = Sum.inr (Sum.inr z0)
  topCenter_coarse_pair : ∀ z (b : Fin 2),
    topCenter (induced.zPairEquiv (z, b)).1 = coarseCenter z
  topCenter_x_iff : ∀ x p,
    p ∈ Lx.syndromeRegion x ↔ topCenter p = Sum.inl x
  topCenter_q_iff : ∀ q p,
    p ∈ Lq.syndromeRegion q ↔ topCenter p = Sum.inr (Sum.inl q)
  topCenter_z_iff : ∀ z p,
    p ∈ Lz.syndromeRegion z ↔ topCenter p = Sum.inr (Sum.inr z)
  zSector_eq_regions : zSector = rxRegionUnion Lz
  lz_regions_pairwise_disjoint :
    ∀ z z', z ≠ z' → Disjoint (Lz.syndromeRegion z) (Lz.syndromeRegion z')
  cx_correction_regions_pairwise_disjoint :
    ∀ x x', x ≠ x' →
      Disjoint (Lx.correctionRegion x) (Lx.correctionRegion x')
  cq_correction_regions_pairwise_disjoint :
    ∀ q q', q ≠ q' →
      Disjoint (Lq.correctionRegion q) (Lq.correctionRegion q')
  /-- F11 flow support is confined to the directed source radius one. -/
  cxFlow_radius_one : ∀ x f p,
    contract.support_decomposition.cxFlow x f p ≠ 0 →
      DirectedGraph.distance levelGraph.graph (Sum.inl x) (topCenter p) ≤ 1
  cqFlow_radius_one : ∀ q f p,
    contract.support_decomposition.cqFlow q f p ≠ 0 →
      DirectedGraph.distance levelGraph.graph (Sum.inr (Sum.inl q)) (topCenter p) ≤ 1
  /-- The two-step source path law used when an X flow feeds a Q flow. -/
  distance_one_comp : ∀ u v w : RXVertex X Q Z,
    DirectedGraph.distance levelGraph.graph u v ≤ 1 →
      DirectedGraph.distance levelGraph.graph v w ≤ 1 →
        DirectedGraph.distance levelGraph.graph u w ≤ 2
namespace RXCoarseGrainingData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
  (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)
noncomputable def qCohomologyClass
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (error : D.family.Cochain1 i.succ)
    (hCocycle : ∀ q,
      A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0) :
    (∀ q, (A.contract.rx_local_complexes.cq q).middleCohomology) :=
  fun q => (A.contract.rx_local_complexes.cq q).middleCoboundaryInCocycles.mkQ
    ⟨restrictWordLinear (Lq.correctionRegion q) error, by
      change A.contract.rx_local_complexes.cqDelta1 q
        (restrictWordLinear (Lq.correctionRegion q) error) = 0
      exact hCocycle q⟩
noncomputable def zPairImage
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (z : C2 i.castSucc) : Finset (C2 i.succ) :=
  (Finset.univ : Finset (Fin 2)).image
    (fun b => (A.induced.zPairEquiv (z, b)).1)
noncomputable def cxWitnessRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)) :
    ∀ x, Word Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  fun x => Classical.choose (A.contract.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) (hlocal x))
noncomputable def cqWitnessRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)) :
    ∀ q, Word Field (LocalRegionIndex (Lq.correctionRegion q)) :=
  fun q => Classical.choose (A.contract.local_boundary_weight_budgets.cq q
    (restrictWordLinear (Lq.syndromeRegion q) sigma) (hlocal q))
noncomputable def cxCorrectionRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)) :
    D.family.Correction i.succ :=
  ∑ x : X, extendWordLinear (Lx.correctionRegion x)
    (cxWitnessRG A sigma hlocal x)
noncomputable def cqCorrectionRG
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (hlocal : ∀ q, restrictWordLinear (Lq.syndromeRegion q) sigma ∈
      LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)) :
    D.family.Correction i.succ :=
  ∑ q : Q, extendWordLinear (Lq.correctionRegion q)
    (cqWitnessRG A sigma hlocal q)
noncomputable def rxXiLocalComplex
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalComplexData (RXVertex X Q Z) (C2 i.succ) (C1 i.succ) where
  syndromeRegion := fun v =>
    match v with
    | Sum.inl x => Lx.syndromeRegion x
    | Sum.inr (Sum.inl q) => Lq.syndromeRegion q
    | Sum.inr (Sum.inr z) => Lz.syndromeRegion z
  correctionRegion := fun v =>
    match v with
    | Sum.inl x => Lx.correctionRegion x
    | Sum.inr (Sum.inl q) => Lq.correctionRegion q
    | Sum.inr (Sum.inr _z) => ∅
noncomputable def rxXiSignal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ)
    (center : RXVertex X Q Z) (radius : Nat) :
    D.family.Cochain2 i.succ :=
  xiAggregate A.levelGraph.graph (rxXiLocalComplex A) sigma center radius
def rxSignalAgreementWithin
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (center : RXVertex X Q Z) (radius : Nat)
    (sigma tau : D.family.Cochain2 i.succ) : Prop :=
  ∀ p, DirectedGraph.distance A.levelGraph.graph (A.topCenter p) center ≤ radius →
    sigma p = tau p
noncomputable def coarseProjection
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.castSucc :=
  fun z => sigma (A.induced.zPairEquiv (z, 0)).1
def CxLocalRange
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : Prop :=
  ∀ x, restrictWordLinear (Lx.syndromeRegion x) sigma ∈
    LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)
def CxLocalRangeAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) : Prop :=
  restrictWordLinear (Lx.syndromeRegion x) sigma ∈
  LinearMap.range (A.contract.rx_local_complexes.cxDelta1 x)
noncomputable def cxWitnessAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X)
    (h : CxLocalRangeAt A sigma x) :
    Word Field (LocalRegionIndex (Lx.correctionRegion x)) :=
  Classical.choose (A.contract.local_boundary_weight_budgets.cx x
    (restrictWordLinear (Lx.syndromeRegion x) sigma) h)
noncomputable def cxCorrectionTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Correction i.succ := by
  classical
  exact ∑ x : X, if h : CxLocalRangeAt A sigma x then
    extendWordLinear (Lx.correctionRegion x) (cxWitnessAt A sigma x h)
  else 0
noncomputable def cxComponentTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (x : X) : D.family.Correction i.succ := by
  classical
  exact if h : CxLocalRangeAt A sigma x then
    extendWordLinear (Lx.correctionRegion x) (cxWitnessAt A sigma x h)
  else 0
def CqLocalRange
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : Prop :=
  ∀ q, restrictWordLinear (Lq.syndromeRegion q)
      (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)) ∈
    LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)
def CqLocalRangeAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) : Prop :=
  restrictWordLinear (Lq.syndromeRegion q)
      (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)) ∈
    LinearMap.range (A.contract.rx_local_complexes.cqDelta1 q)
noncomputable def cqWitnessAt
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q)
    (h : CqLocalRangeAt A sigma q) :
    Word Field (LocalRegionIndex (Lq.correctionRegion q)) :=
  Classical.choose (A.contract.local_boundary_weight_budgets.cq q
    (restrictWordLinear (Lq.syndromeRegion q)
      (sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma))) h)
noncomputable def cqCorrectionTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Correction i.succ := by
  classical
  exact ∑ q : Q, if h : CqLocalRangeAt A sigma q then
    extendWordLinear (Lq.correctionRegion q)
      (cqWitnessAt A sigma q h)
  else 0
noncomputable def cqComponentTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
    D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) (q : Q) : D.family.Correction i.succ := by
  classical
  exact if h : CqLocalRangeAt A sigma q then
    extendWordLinear (Lq.correctionRegion q)
      (cqWitnessAt A sigma q h)
  else 0
noncomputable def rxCorrectionTotal
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Correction i.succ :=
  cxCorrectionTotal A sigma + cqCorrectionTotal A sigma
noncomputable def rxSigmaAfterCx
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.succ :=
  sigma + D.family.coboundary1 i.succ (cxCorrectionTotal A sigma)
noncomputable def rxSigmaAfterCq
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.succ :=
  rxSigmaAfterCx A sigma + D.family.coboundary1 i.succ (cqCorrectionTotal A sigma)
noncomputable def rxCoarseWord
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma : D.family.Cochain2 i.succ) : D.family.Cochain2 i.castSucc :=
  coarseProjection A (rxSigmaAfterCq A sigma)
noncomputable def rxLocalComponents
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalCorrectionComponents (RXVertex X Q Z) (C2 i.succ) (C1 i.succ)
      Field Field (rxXiLocalComplex A) where
  component := fun v sigma =>
    match v with
    | Sum.inl x => cxComponentTotal A sigma x
    | Sum.inr (Sum.inl q) => cqComponentTotal A sigma q
    | Sum.inr (Sum.inr _z) => 0
noncomputable def rxLocalInterface
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) :
    LocalComputabilityInterface (RXVertex X Q Z) (C2 i.succ) (C1 i.succ)
      (C2 i.castSucc) Field Field (rxXiLocalComplex A) A.levelGraph.graph where
  correction := rxCorrectionTotal A
  components := rxLocalComponents A
  coarseSyndrome := rxCoarseWord A
  coarseCenter := A.coarseCenter
structure RXLocalComputabilityCertificate
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz) where
  totalCorrectionDecomposition :
    LocalComputabilityInterface.totalCorrectionDecomposition
      (rxLocalInterface A)
  componentSupported :
    LocalComputabilityInterface.componentSupported
      (rxLocalInterface A)
  maskedTotalCorrectionEqComponent :
    LocalComputabilityInterface.maskedTotalCorrectionEqComponent
      (rxLocalInterface A)
  componentInvariantAtXiOne :
    LocalComputabilityInterface.componentInvariantAtXiOne
      (rxLocalInterface A)
  coarseCoordinateInvariantAtXiTwo :
    LocalComputabilityInterface.coarseCoordinateInvariantAtXiTwo
      (rxLocalInterface A)
end RXCoarseGrainingData
end RXCoarseGraining
end MultiscaleDecoder
end Coding
end QEC
namespace QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
namespace RXCoarseGrainingData
end RXCoarseGrainingData
end QEC.Coding.MultiscaleDecoder.RXCoarseGraining


