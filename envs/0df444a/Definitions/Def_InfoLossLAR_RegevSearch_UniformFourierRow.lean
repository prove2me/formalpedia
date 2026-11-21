-- Prove2me | Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
-- name    : InfoLossLAR_RegevSearch_UniformFourierRow
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:27:09.306477+00:00
-- url     : https://prove2.me/theorems/08b933ca-6b63-41bd-b5b0-120dd75b8fc4
-- title:
--   Uniform Fourier sampling from a shared pool
-- statement:
--   This interface specifies a single coherent Fourier readout from a shared pool of integer coefficient vectors. It fixes the finite query amplitudes before the old pool is supplied, records the canonical signed-vector prefix in the output, and bounds the discrepancy on finite events using the preparation error, the decoder failure on the old pool, and the Fourier-grid error. It also specifies how a uniform parser and a polynomial-time table of independent query lengths describe the circuit family.
-- source:
--   InfoLossLAR formalization of the single-coefficient Gaussian reduction, coherent shared-pool Fourier sampling, https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_LARLLL_CurrentData
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ShorAlgorithms_QFT_Circuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

section

open scoped BigOperators Classical ENNReal

open Filter

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

noncomputable section

variable {X Y : Type*}

def finiteMass (p : PMF X) (T : Finset X) := ∑ x ∈ T, (p x).toReal

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end

section

open scoped BigOperators Classical ENNReal

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open QAlgorithms.Complexity

noncomputable section

def measuredBits (F : MFamily) (w : Str) : PMF (Bits (w.length+(F.anc w.length+1))) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (Complex.normSq (runLayered (F.circ w.length) (basisInput (toBits w)) x)))
    (by rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => Complex.normSq_nonneg _),runLayered_mass,basisInput_mass];simp)

def measuredWord (F : MFamily) (w : Str) : PMF Str :=
  (measuredBits F w).map (fun x => List.ofFn (fun j => x (F.outW w.length j)))

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end

section

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

noncomputable section

def dualHeight (n H : ℕ) : ℕ := 2*((n+H)*n)

end

end InfoLossLAR.WorstCase.RationalInverse

end

section

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- Unary size reflection materializes the exact actual binary encoding
length; it never enumerates a Gaussian window or a numerical magnitude. -/
def rationalTicks (value : ℚ) : List Unit :=
  List.replicate 7 ()++(value.num.natAbs.bits.flatMap (fun _ => [(),()]))++
    value.den.bits.map (fun _ => ())

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end

section

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase GaussianPoissonSeries IntegerBasis RegevLWE.GaussConv

open CoherentDecoder FiniteLatticeFourier

noncomputable section

variable {n M : ℕ} [NeZero M]

def gridError (n : ℕ) : ℝ := 4*Real.sqrt (2*(1/2:ℝ)^n)+(1/4:ℝ)^n

end

end GridReadout

end

section

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open InfoLossLAR.WorstCase.RegevSearch RegevLWE.GaussConv

open scoped BigOperators Classical

namespace SharedPoolCoherence

noncomputable section

variable {n : ℕ}

def failureMass {m : ℕ} {I : Type} [Fintype I] (C : MFamily) {B : Matrix (Fin n) (Fin n) ℤ} {R : ℚ}
    (precision : ℕ) (pool : Fin m → Fin n → ℤ) (q : I → Query B R) (a : I → ℂ) : ℝ :=
  ∑ i, ‖a i‖^2 * outputProb C (word precision pool (q i)) (fun out => ¬ encVec encI (q i).answer <+: out)

end

end SharedPoolCoherence

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries

open GaussianProjection.CosetGeometry

open GaussianProjection GaussianLatticeTransport

noncomputable section

variable {n M : ℕ} [NeZero M]

abbrev PointSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev Separated (L : Submodule ℤ (PointSpace n)) (R : ℝ) := ∀ x : L, x ≠ 0 → 2*R ≤ ‖(x : PointSpace n)‖

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

namespace InfoLossLAR.WorstCase.RegevSearch.OracleTable

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2PlatformSerialization Integration9_9.TM2StockLists QMCNumericRuntime

open Integration9_9.LARPlatformEncoding (readS readBinaryList)

noncomputable section

def unpack (w : Str) := readBinaryList readS w

def lookup (u : Str×ℕ) : Str := (unpack u.1).2[u.2]?.getD []

end

end InfoLossLAR.WorstCase.RegevSearch.OracleTable

end

section

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 QMCNumericRuntime

noncomputable section

def powTwo (s : Str) : ℕ := bitValue (s.map (fun _ => false) ++ [true])

@[fun_prop] theorem powTwo_poly : Poly powTwo := by unfold powTwo; fun_prop

def signedRow (s : Str) : ℤ :=
  let v := bitValue s.reverse
  if 2*v < powTwo s then -(v:ℤ) else (powTwo s:ℤ)-(v:ℤ)

@[fun_prop] theorem signedRow_poly : Poly signedRow := by
  unfold signedRow
  fun_prop

def rowSlices (x : List Unit × (List Unit × Str)) : List Str :=
  (List.range x.1.length).map (fun i => (x.2.2.drop (i*x.2.1.length)).take x.2.1.length)

@[fun_prop] theorem rowSlices_poly : Poly rowSlices := by
  unfold rowSlices
  apply Poly.list_map
  · change Poly (fun t : (List Unit × (List Unit × Str)) × ℕ => (t.1.2.2.drop (t.2*t.1.2.1.length)).take t.1.2.1.length)
    have hd : Poly (fun t : (List Unit × (List Unit × Str)) × ℕ => t.1.2.2.drop (t.2*t.1.2.1.length)) :=
      Poly.comp (f:=fun s : Str × ℕ => s.1.drop s.2) (g:=fun t : (List Unit × (List Unit × Str)) × ℕ => (t.1.2.2,t.2*t.1.2.1.length)) parser_drop_poly (by fun_prop)
    exact Poly.comp (f:=fun s : Str × ℕ => s.1.take s.2) (g:=fun t : (List Unit × (List Unit × Str)) × ℕ => (t.1.2.2.drop (t.2*t.1.2.1.length),t.1.2.1.length)) parser_take_poly (Poly.pair hd (by fun_prop))
  · exact Poly.comp (f:=fun t : List Unit => List.range t.length) (g:=Prod.fst) Poly.list_indices Poly.fst

def encodeSlices (x : List Unit × (List Unit × Str)) : Str :=
  TM2NativeAffineEmitter.serializeVector ((rowSlices x).map signedRow)

@[fun_prop] theorem encodeSlices_poly : Poly encodeSlices := by unfold encodeSlices; fun_prop

end

end GridReadout.Axis

end

section

open scoped BigOperators Classical

namespace GridReadout

open InfoLossLAR.WorstCase RegevSearch

variable {n : ℕ}

def gridBits (n H K : ℕ) : ℕ := 2 + (2*n + (n+H)*n + 1) + n + (K+1)

end GridReadout

end

section

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization GridReadout.Axis PhysicalFourier

open TM2Boolean TM2Boolean.PolyProgramCircuit

open scoped Classical BigOperators

noncomputable section

def read (ws : Str) : Str := let r := (readUnary ws).2; encodeSlices (unarySlots ws,unarySlots r,(readUnary r).2)

@[fun_prop] theorem read_poly : Poly read := by
  have hr : Poly (fun ws : Str => (readUnary ws).2) := Poly.comp Poly.snd readUnary_poly
  exact Poly.comp (f:=encodeSlices) (g:=fun ws : Str => (unarySlots ws,unarySlots (readUnary ws).2,(readUnary (readUnary ws).2).2)) encodeSlices_poly (Poly.pair unarySlots_poly (Poly.pair (Poly.comp (f:=unarySlots) (g:=fun ws : Str => (readUnary ws).2) unarySlots_poly hr) (Poly.comp (f:=fun ws : Str => (readUnary ws).2) (g:=fun ws : Str => (readUnary ws).2) hr hr)))

def prefixWord (nt bt : List Unit) := lengthToken nt ++ lengthToken bt

def program := Integration9_9.LARCoinLayout.rawPolyProgram read_poly

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end

section

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open QAlgorithms QAlgorithms.Complexity

open FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit TM2Boolean.CodeGenerator

open Integration9_9.TM2PlatformSerialization

open scoped Classical BigOperators

noncomputable section

abbrev Sizes := List Unit×List Unit

def digits (s : Sizes) := s.1.flatMap (fun _ => s.2)

def inputTape (s : Sizes) := (prefixWord s.1 s.2).map (fun _ => ())++digits s

def clock (s : Sizes) := (inputTape s).map (fun _ => true)

def slot (s : Sizes) := (request program (clock s)).2.1

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RationalInverse

open scoped BigOperators

noncomputable section

/-- This exponent depends only polynomially on the original basis height. -/
def dualColumnBudgetBits (dimension bits : ℕ) : ℕ := dualHeight dimension bits+2*dimension+2

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open GaussianPoissonSeries RationalInverse GridReadout

noncomputable section

def bits (n H K d : ℕ) :=
  max (gridBits n H K) (dualColumnBudgetBits n H + (K+1) + (n+2*d+8) + (d+2))

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic AFT.RationalNumerics

open GaussianPoissonSeries RationalInverse RationalGramSchmidt.Native GridReadout

abbrev Setup := List (List ℤ) × (ℚ × List Unit)

def gridCount (s : Setup) : ℕ :=
  bits s.1.length (integerMatrixTicks s.1).length (rationalTicks s.2.1).length s.2.2.length

def slots (s : Setup) : List Unit :=
  s.1.map (fun _ => ()) ++ integerMatrixTicks s.1 ++ rationalTicks s.2.1 ++ s.2.2 ++ [()]

def capacity (s : Setup) : List Unit :=
  (slots s).flatMap (fun _ => (slots s).flatMap (fun _ => List.replicate 64 ()))

def gridTape (s : Setup) : List Unit := (capacity s).take (gridCount s)

noncomputable def setup {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (d : ℕ) : Setup :=
  (Native.inputRows B,r,List.replicate d ())

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

open QAlgorithms.Complexity SharedPoolCoherence CoherentDecoder RegevSketch

noncomputable section

abbrev Vec (n : ℕ) := Fin n→ℤ

abbrev Rows (n m : ℕ) := Fin m→Vec n

end

end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

end

section

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open RegevLWE.GaussConv GaussianPoissonSeries GaussianProjection

open FiniteGateTransport RegevSearch.PhysicalFourier

open RegevSearch.PhysicalGrid

noncomputable section

def physics (r : ℚ) : ℝ :=1/(Real.sqrt 2*(r:ℝ))

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open TM2Boolean.PolyProgramCircuit SharedPoolCoherence GridReadout.Axis

open IntegerBasis RegevLWE.GaussConv GaussianPoissonSeries CoherentDecoder

noncomputable section

abbrev StageL {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) := dual (inputLattice B hB)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch

open Public

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2PlatformSerialization

noncomputable section

abbrev Stage := List (List ℤ) × (ℚ × ℚ) × List Unit × List Unit × List Unit

abbrev Input := (Stage × (List Unit×List Unit)) × (Str×Str)

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

open QAlgorithms QAlgorithms.Complexity

open FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean GaussianIteration

noncomputable section

def decodeWord (n : ℕ) (w : Str) : Vec n := fun i => (Integration9_9.TM2NativeAffineEncoding.readVector w).2[i.val]?.getD 0

def canon (n S : ℕ) (w : Str) := ∃ z : Vec n,encVec encI z <+: w.take S

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.SignedSlot

end

section

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch

open IntegerBasis

open RectangularSource.Public

noncomputable section

def receipt (P : List (List ℤ)) (R r : ℚ) (copies acc oracle count width : List Unit) (tape advice : Str) : Input :=
  (((P,(R,r),copies,acc,oracle),(count,width)),tape,advice)

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end

section

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity GaussianIteration RegevSketch SharedPoolCoherence

noncomputable section

variable {n : ℕ} {C : MFamily} {P : Polynomial ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {R t : ℚ} {k m : ℕ}

structure AnalysisData (C : MFamily) (P : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ) where
  grid : ℕ
  covers : gridAdequate B R (2^grid)
  I : Type
  inst : Fintype I
  inhabited : Nonempty I
  query : I→Query B R
  amp : I→ℂ
  norm : letI := inst;∑ i, ‖amp i‖^2=1
  prep : ℝ
  prep_nonneg : 0≤prep
  L : ℕ
  length_ge : k+1≤L
  source : prep≤2/(L:ℝ)+1/(2:ℝ)^n+2*Real.sqrt ((1/4:ℝ)^n)

def AnalysisData.cost (v : AnalysisData C P B R k) (z : Rows n (P.eval n)) :=
  letI := v.inst
  2*v.prep+4*Real.sqrt (failureMass C (poolBDDPrecision (((P+1)+(P+1)).eval n) k) z v.query v.amp)+
    4*Real.sqrt (2*(1/2:ℝ)^n)+1/(4*((k:ℝ)+1))+GridReadout.gridError n

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end

section

namespace InfoLossLAR.WorstCase.RegevSearch

open QAlgorithms QAlgorithms.Complexity GaussianIteration RegevSketch AdaptiveStages RectangularSource

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open PhysicalFourier CoherentDecoder RectangularSource.Public

open scoped Classical BigOperators

noncomputable section

/-- The call length can be determined before generating the table of oracle descriptions. -/
def TableIndependent (request : Cell.Input→List Unit) := ∀ (h : Cell.Stage) (slots : List Unit×List Unit) (raw tbl : Str),
  request ((h,slots),raw,tbl)=request ((h,slots),raw,[])

/-- One uniform circuit family, run on a word parsed into a lattice, the parameters of a width
transition, a shared old pool and oracle descriptions. All justified presentations of the
same old row tuple satisfy the same finite-event bound. -/
def FourierRowGuarantee (P : Polynomial ℕ) (C F G : MFamily) (query : Cell.Input→List Unit)
    (parse : Str→Cell.Input) : Prop :=
  ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0), 0<n → ∀ (R t : ℚ), 0<R → 0<t →
  ∀ c : ℝ, 0<c → (n:ℝ)*(physics t)^2 ≤ c^2 → c ≤ (n+1:ℕ)*(t.den+1:ℕ) →
  c ≤ (famσ n:ℝ)/(2*(R:ℝ)) → Separated (StageL B hB) c →
  ∀ (nt count acc oracle width : List Unit), nt.length=n → count.length=P.eval n →
     oracle.length=poolBDDPrecision (((P+1)+(P+1)).eval n) acc.length →
     (SignedSlot.slot (nt,PhysicalGrid.gridTape (PhysicalGrid.setup B t n))).length ≤ width.length →
  ∃ a : Outer.AnalysisData C P B R acc.length,
    ∀ (raw tbl w : Str) (z : Rows n (P.eval n)),
    let info := Cell.receipt (RationalInverse.Native.inputRows B) R t count acc oracle count width raw tbl
    parse w=info → OracleTable.lookup (tbl,(query info).length)=F.encAt (query info).length →
    (∀ u,encVec encI (z u) <+: (raw.drop (u.val*width.length)).take width.length) →
    outputProb G w (SignedSlot.canon n width.length)=1 ∧
      ∀ T : Finset (Vec n), |finiteMass ((measuredWord G w).map (SignedSlot.decodeWord n)) T-
        ∑ v∈T,coefficientMass B t v| ≤ a.cost z

def UniformFourierRow (C : MFamily) (P : Polynomial ℕ) : Prop :=
  ∃ F : MFamily, IsMQPT F ∧ ∃ query : Cell.Input→List Unit, Poly query ∧ TableIndependent query ∧
  ∀ parse : Str→Cell.Input, Poly parse → ∃ (G : MFamily) (desc : Str→Str), Poly desc ∧
    (∀ j,desc (unary j)=G.encAt j) ∧ FourierRowGuarantee P C F G query parse

end

end InfoLossLAR.WorstCase.RegevSearch

end


