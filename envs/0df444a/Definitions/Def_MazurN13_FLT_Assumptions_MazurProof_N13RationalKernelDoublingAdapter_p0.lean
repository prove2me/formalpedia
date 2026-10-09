-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13RationalKernelDoublingAdapter_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13RationalKernelDoublingAdapter_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T19:53:06.426311+00:00
-- url     : https://prove2.me/theorems/cd25ec35-7fcd-40d1-b1ac-8d7cfb175591
-- title:
--   FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFormalTransitionJet_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13ConcreteGraphRecovery_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpreadRationalPointReduction_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartSection_p0

set_option autoImplicit false




/-!
# N13 rational-kernel unary doubling adapter

The two-adic transition calculation already controls the tensor square of
one near-base line bundle to first order.  To turn that calculation into
separatedness for the actual rational reduction kernel, two geometric
producers remain:

* a centered near-base integral Mumford graph for every kernel class; and
* comparison, modulo the square of the moving coordinate ideal, between
  the chosen graph for `2 • z` and the square of the graph for `z`.

This file packages those producers and derives the exact
`RationalKernelDoublingData` consumed by the N13 endgame.  It introduces no
new assumption and keeps the remaining first-jet theorem explicit.
-/

namespace MazurProof.N13RationalKernelDoublingAdapter

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

universe u

/-- The rational oriented Picard group of the N13 curve. -/
abbrev RationalPic : Type :=
  N13TwoAdicAbelChartSection.RationalPic

/-- Ordered pairs in the two distinguished two-adic residue disks. -/
abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair

/-- Smooth integral Mumford graphs reducing to the fixed base graph. -/
abbrev NearBaseMumford : Type :=
  N13TwoAdicAbelChartRecover.NearBaseMumford

/-- The two-adic integer coefficient ring of the Abel chart. -/
abbrev R₂ : Type :=
  ℤ_[2]

/-- The oriented Picard group of the N13 curve over the two-adic field. -/
abbrev Pic₂ : Type :=
  N13TwoAdicAbelChartPic.Pic

/-- The balanced N13 Mumford model over the two-adic field. -/
abbrev Model₂ : SexticMumford.Model ℚ_[2] :=
  N13ConcreteGraphRecovery.Model

/-- The Picard class of the distinguished nonspecial base disk pair. -/
def basePic : Pic₂ :=
  N13TwoAdicAbelChartPic.DiskPair.pic
    N13TwoAdicAbelChartData.basePair

/-! ## Recovering canonical disk pairs from kernel representatives -/

/-- A kernel-indexed family of smooth integral graphs reducing to the
selected nonspecial quadratic graph.

The stored equality is centered at the distinguished base divisor, exactly
as required by the Abel chart.  Hensel recovery will turn each graph into a
unique ordered disk pair without any additional choice compatibility. -/
structure NearBaseFamily
    (H : AddSubgroup RationalPic) where
  graph : H → NearBaseMumford
  realize_graph :
    ∀ z,
      (graph z).centeredPic =
        N13TwoAdicAbelChartSection.subgroupToPic H z

namespace NearBaseFamily

variable {H : AddSubgroup RationalPic}

/-- Pointwise existence is sufficient to package a representative family.
Injectivity of the centered disk-pair Picard map later removes dependence
on these choices at the geometric-coordinate level. -/
def ofExists
    (h :
      ∀ z : H, ∃ E : NearBaseMumford,
        E.centeredPic =
          N13TwoAdicAbelChartSection.subgroupToPic H z) :
    NearBaseFamily H where
  graph z := Classical.choose (h z)
  realize_graph z := Classical.choose_spec (h z)

/-- Recover the unique ordered pair of Hensel roots from each near-base
integral graph. -/
def pair
    (F : NearBaseFamily H) :
    H → DiskPair :=
  fun z => (F.graph z).diskPair

/-- Near-base graph recovery supplies the exact centered Picard realization
required by `RationalKernelDoublingData`. -/
theorem realize
    (F : NearBaseFamily H) (z : H) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (F.pair z) =
      N13TwoAdicAbelChartSection.subgroupToPic H z := by
  calc
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
          (F.pair z) =
        (F.graph z).centeredPic := by
      simpa [pair] using
        ((F.graph z).centeredPic_eq_diskPair_centeredPic).symm
    _ = N13TwoAdicAbelChartSection.subgroupToPic H z :=
      F.realize_graph z

end NearBaseFamily

/-- A balanced quadratic representative of a centered two-adic Picard
class whose canonical contraction has the literal selected special graph.

The represented uncentered class is translated by `basePic`.  This
translation is forced because disk-pair coordinates are centered at the
distinguished base divisor. -/
structure MappedSpecialRepresentative
    (c : Pic₂) where
  mumford : SexticMumford.Mumford Model₂
  class_eq :
    SexticMumford.classOf
        Model₂ (N13Infinity.positiveInfinityOrder ℚ_[2])
        mumford =
      c + basePic
  map_contract_eq_special :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal
            mumford.toSemi)) =
      N13SpecialQuotientBasis.specialIdeal

namespace MappedSpecialRepresentative

variable {c : Pic₂}

/-- Literal special-ideal reduction recovers a disk pair whose centered
Picard class is the prescribed class `c`.  All normalization and Hensel
lifting are supplied by the existing concrete graph-recovery theorem. -/
theorem exists_nearBase
    (R : MappedSpecialRepresentative c) :
    ∃ E : NearBaseMumford, E.centeredPic = c := by
  obtain ⟨P, hP⟩ :=
    N13ConcreteGraphRecovery.exists_diskPair_class_eq
      R.mumford R.map_contract_eq_special
  refine
    ⟨N13TwoAdicAbelChartRecover.NearBaseMumford.ofDiskPair P, ?_⟩
  rw [
    N13TwoAdicAbelChartRecover.NearBaseMumford.centeredPic_ofDiskPair,
    N13TwoAdicAbelChartPic.DiskPair.centeredPic]
  have hPic :
      N13TwoAdicAbelChartPic.DiskPair.pic P =
        c + basePic :=
    hP.symm.trans R.class_eq
  rw [hPic, basePic]
  abel

end MappedSpecialRepresentative

/-- A literal mapped-special representative for every class in a rational
kernel.  This is the concrete representative producer from which the
abstract near-base family can now be derived. -/
structure MappedSpecialFamily
    (H : AddSubgroup RationalPic) where
  representative :
    ∀ z : H,
      MappedSpecialRepresentative
        (N13TwoAdicAbelChartSection.subgroupToPic H z)

namespace MappedSpecialFamily

variable {H : AddSubgroup RationalPic}

/-- Concrete graph recovery discharges the entire pointwise near-base
realization field from literal mapped-special representatives. -/
def toNearBaseFamily
    (R : MappedSpecialFamily H) :
    NearBaseFamily H :=
  NearBaseFamily.ofExists
    (fun z => (R.representative z).exists_nearBase)

end MappedSpecialFamily

/-! ## Canonical mapped-special representatives -/

/-- The canonical balanced Mumford representative of the translated
two-adic class `c + basePic`.  Fixing this normal form removes both the
pointwise representative choice and the separate proof of its Picard
class from the remaining kernel-recovery input. -/
def canonicalMappedSpecialMumford
    (c : Pic₂) :
    SexticMumford.Mumford Model₂ :=
  SexticMumford.normalize
    Model₂
    (N13Infinity.positiveInfinityOrder ℚ_[2])
    (c + basePic)

/-- Normal-form theory identifies the canonical representative with the
translated Picard class used by centered disk coordinates. -/
@[simp] theorem classOf_canonicalMappedSpecialMumford
    (c : Pic₂) :
    SexticMumford.classOf
        Model₂
        (N13Infinity.positiveInfinityOrder ℚ_[2])
        (canonicalMappedSpecialMumford c) =
      c + basePic := by
  simpa only [canonicalMappedSpecialMumford] using
    (SexticMumford.classOf_normalize
      Model₂
      (N13Infinity.positiveInfinityOrder ℚ_[2])
      (c + basePic))

/-- Minimal literal special-fibre input for a rational subgroup.

For each subgroup element, the only stored fact is that the canonical
balanced representative of its translated two-adic class has canonical
contraction equal to the fixed special graph after reduction. -/
structure CanonicalMappedSpecialFamily
    (H : AddSubgroup RationalPic) where
  map_contract_eq_special :
    ∀ z : H,
      Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal
              (canonicalMappedSpecialMumford
                (N13TwoAdicAbelChartSection.subgroupToPic H z)).toSemi)) =
        N13SpecialQuotientBasis.specialIdeal

namespace CanonicalMappedSpecialFamily

variable {H : AddSubgroup RationalPic}

/-- Package the canonical normal form into the arbitrary representative
interface.  Its translated class equality is supplied by normalization. -/
def toMappedSpecialFamily
    (R : CanonicalMappedSpecialFamily H) :
    MappedSpecialFamily H where
  representative z :=
    { mumford :=
        canonicalMappedSpecialMumford
          (N13TwoAdicAbelChartSection.subgroupToPic H z)
      class_eq :=
        classOf_canonicalMappedSpecialMumford
          (N13TwoAdicAbelChartSection.subgroupToPic H z)
      map_contract_eq_special :=
        R.map_contract_eq_special z }

/-- Literal special-ideal equality for the canonical normal forms recovers
a centered near-base Mumford graph for every subgroup element. -/
def toNearBaseFamily
    (R : CanonicalMappedSpecialFamily H) :
    NearBaseFamily H :=
  R.toMappedSpecialFamily.toNearBaseFamily

/-- The ordered Hensel pair recovered from each canonical representative. -/
def recoveredPair
    (R : CanonicalMappedSpecialFamily H) :
    H → DiskPair :=
  R.toNearBaseFamily.pair

/-- Each recovered Hensel pair realizes the original rational subgroup
element after base change to the two-adic Picard group. -/
theorem realize_recoveredPair
    (R : CanonicalMappedSpecialFamily H)
    (z : H) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (R.recoveredPair z) =
      N13TwoAdicAbelChartSection.subgroupToPic H z := by
  simpa only [recoveredPair] using
    NearBaseFamily.realize R.toNearBaseFamily z

end CanonicalMappedSpecialFamily

namespace NearBaseFamily

variable {H : AddSubgroup RationalPic}

/-- The two integral Abel-chart coordinates of the recovered disk pair. -/
def coord
    (F : NearBaseFamily H) :
    H → Fin 2 → R₂ :=
  fun z =>
    N13TwoAdicAbelChartData.DiskPair.coord (F.pair z)

/-! ## Comparing a selected double with the squared transition -/

/-- The weighted first jet of the tensor square of the actual formal
transition attached to the selected disk representative of `z`. -/
def squareJet
    (F : NearBaseFamily H) (z : H) :
    Fin 2 → R₂ :=
  N13MumfordFormalTransitionJet.firstJet
    (N13MumfordFormalTransitionJet.weightedDeviationOfTransition
      (N13MumfordFormalTransitionJet.diskTransition
        (F.pair z)).square)

/-- Existing transition algebra proves that the square jet is twice the
original disk coordinate modulo the square of its coordinate ideal. -/
theorem squareJet_sub_double_coord_mem_sq
    (F : NearBaseFamily H) (z : H) (i : Fin 2) :
    F.squareJet z i -
        (F.coord z i + F.coord z i) ∈
      N13TwoAdicKernelChart.coordIdeal F.coord z *
        N13TwoAdicKernelChart.coordIdeal F.coord z := by
  simpa [squareJet, coord,
    N13TwoAdicKernelChart.coordIdeal] using
    N13MumfordFormalTransitionJet.firstJet_square_sub_double_coord_mem_sq
      (F.pair z) i

/-- Once the unary law is known, the representative family fills the exact
rational-kernel structure used by separatedness. -/
def ofDoublingLaw
    (F : NearBaseFamily H)
    (L : N13TwoAdicAbelChartLaw.DoublingLaw F.coord) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData H where
  pair := F.pair
  realize := F.realize
  law := by
    change N13TwoAdicAbelChartLaw.DoublingLaw F.coord
    exact L

end NearBaseFamily

/-! ## The exact remaining unary compatibility -/

/-- Comparison between the canonical representative chosen for `2 • z`
and the tensor square of the representative chosen for `z`.

Exact equality of transitions is unnecessary.  Agreement of their first
jets modulo the square of the moving coordinate ideal is precisely the
congruence consumed by the formal-kernel argument. -/
structure FirstJetDoublingCompatibility
    {H : AddSubgroup RationalPic}
    (F : NearBaseFamily H) : Prop where
  compare :
    ∀ z i,
      F.coord (2 • z) i - F.squareJet z i ∈
        N13TwoAdicKernelChart.coordIdeal F.coord z *
          N13TwoAdicKernelChart.coordIdeal F.coord z

namespace FirstJetDoublingCompatibility

variable {H : AddSubgroup RationalPic}
variable {F : NearBaseFamily H}

/-- The representative-comparison congruence and the existing
transition-square congruence add to the required unary doubling law. -/
def toDoublingLaw
    (C : FirstJetDoublingCompatibility F) :
    N13TwoAdicAbelChartLaw.DoublingLaw F.coord where
  double_error_mem z i := by
    let I :=
      N13TwoAdicKernelChart.coordIdeal F.coord z
    change
      F.coord (2 • z) i -
          (F.coord z i + F.coord z i) ∈
        I * I
    have hcompare :
        F.coord (2 • z) i - F.squareJet z i ∈ I * I := by
      simpa [I] using C.compare z i
    have hsquare :
        F.squareJet z i -
            (F.coord z i + F.coord z i) ∈ I * I := by
      simpa [I] using
        NearBaseFamily.squareJet_sub_double_coord_mem_sq
          F z i
    have heq :
        (F.coord (2 • z) i - F.squareJet z i) +
            (F.squareJet z i -
              (F.coord z i + F.coord z i)) =
          F.coord (2 • z) i -
            (F.coord z i + F.coord z i) := by
      ring
    rw [← heq]
    exact (I * I).add_mem hcompare hsquare

/-- The two geometric producers assemble directly into the exact structure
consumed by the rational-point reduction endpoint. -/
def toRationalKernelDoublingData
    (C : FirstJetDoublingCompatibility F) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData H :=
  NearBaseFamily.ofDoublingLaw F C.toDoublingLaw

end FirstJetDoublingCompatibility

/-! ## One-call assembly from mapped-special representatives -/

namespace MappedSpecialFamily

variable {H : AddSubgroup RationalPic}

/-- A mapped-special representative family reaches the rational-kernel
doubling structure once the selected doubles agree with transition squares
to first order. -/
def toRationalKernelDoublingData
    (R : MappedSpecialFamily H)
    (C :
      FirstJetDoublingCompatibility R.toNearBaseFamily) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData H :=
  C.toRationalKernelDoublingData

/-- The recovered representatives and their first-jet doubling comparison
imply two-adic separatedness of the rational subgroup. -/
theorem separated
    (R : MappedSpecialFamily H)
    (C :
      FirstJetDoublingCompatibility R.toNearBaseFamily) :
    N18RouteC.Separated.NSeparated H 2 :=
  N13TwoAdicAbelChartSection.RationalKernelDoublingData.separated
    (R.toRationalKernelDoublingData C)

end MappedSpecialFamily

namespace CanonicalMappedSpecialFamily

variable {H : AddSubgroup RationalPic}

/-- For canonical normal forms, literal mapped-special equality and the
single first-jet comparison are the complete inputs to the rational-kernel
doubling structure. -/
def toRationalKernelDoublingData
    (R : CanonicalMappedSpecialFamily H)
    (C :
      FirstJetDoublingCompatibility R.toNearBaseFamily) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData H :=
  C.toRationalKernelDoublingData

/-- Canonical mapped-special representatives reduce separatedness to the
one remaining first-jet compatibility theorem. -/
theorem separated
    (R : CanonicalMappedSpecialFamily H)
    (C :
      FirstJetDoublingCompatibility R.toNearBaseFamily) :
    N18RouteC.Separated.NSeparated H 2 :=
  N13TwoAdicAbelChartSection.RationalKernelDoublingData.separated
    (R.toRationalKernelDoublingData C)

end CanonicalMappedSpecialFamily

/-! ## Specialization to the eventual spread classifier -/

namespace Concrete

variable {Line : Type u}

/-- The literal subgroup occurring in the spread-classifier endpoint. -/
abbrev Kernel
    (D : N13SpreadRationalPointReduction.Data Line) :
    AddSubgroup RationalPic :=
  D.compatibleReduction.classifier.red.ker

/-- The quotient-map kernel is definitionally the kernel stored by the
concrete spread classifier. -/
theorem kernel_eq_spreadKernel
    (D : N13SpreadRationalPointReduction.Data Line) :
    Kernel D = D.spread.kernel := by
  calc
    Kernel D =
        D.compatibleReduction.classifier.kernel :=
      N13ReductionClassifier.Data.red_ker
        D.compatibleReduction.classifier
    _ = D.spread.kernel := rfl

/-- A kernel element has the same chosen special classifier value as zero.
This is the abstract input to, but not a substitute for, the concrete
near-base graph extraction theorem. -/
theorem classify_eq_zero
    (D : N13SpreadRationalPointReduction.Data Line)
    (z : Kernel D) :
    D.compatibleReduction.classifier.classify
        (z : RationalPic) =
      D.compatibleReduction.classifier.classify 0 := by
  have hz :
      (z : RationalPic) ∈
        D.compatibleReduction.classifier.kernel := by
    simpa only [Kernel,
      N13ReductionClassifier.Data.red_ker] using z.property
  exact
    (N13ReductionClassifier.Data.classify_eq_zero_iff
      D.compatibleReduction.classifier
      (z : RationalPic)).2 hz

/-- Assemble the formal-kernel package from the representative family and
its first-jet compatibility. -/
def build
    (D : N13SpreadRationalPointReduction.Data Line)
    (F : NearBaseFamily (Kernel D))
    (C : FirstJetDoublingCompatibility F) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData
      (Kernel D) :=
  C.toRationalKernelDoublingData

/-- Pointwise centered near-base existence and the first-jet comparison
are the only remaining mathematical arguments at this adapter boundary. -/
def buildFromPointwiseExistence
    (D : N13SpreadRationalPointReduction.Data Line)
    (hrep :
      ∀ z : Kernel D, ∃ E : NearBaseMumford,
        E.centeredPic =
          N13TwoAdicAbelChartSection.subgroupToPic
            (Kernel D) z)
    (hjet :
      FirstJetDoublingCompatibility
        (NearBaseFamily.ofExists hrep)) :
    N13TwoAdicAbelChartSection.RationalKernelDoublingData
      (Kernel D) :=
  build D (NearBaseFamily.ofExists hrep) hjet

/-- After the two producers, separatedness is a formal consequence of the
existing two-adic Abel-chart theory. -/
theorem separated
    (D : N13SpreadRationalPointReduction.Data Line)
    (F : NearBaseFamily (Kernel D))
    (C : FirstJetDoublingCompatibility F) :
    N18RouteC.Separated.NSeparated (Kernel D) 2 :=
  N13TwoAdicAbelChartSection.RationalKernelDoublingData.separated
    (build D F C)

end Concrete

end

end MazurProof.N13RationalKernelDoublingAdapter


