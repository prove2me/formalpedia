-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P47
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:09:17.141009+00:00
-- url     : https://prove2.me/theorems/46ba526c-1987-4af5-9da2-f8503827897d
-- title:
--   Definitions for On the quantum, classical and total amount of correlations in a quantum state
-- statement:
--   The objects the formalized statements of *On the quantum, classical and total amount of correlations in a quantum state* (arXiv:quant-ph/0410091) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sourcePower`: PDF p.2: rho tensor n in party order A^n:B^n.
--   - `LocalNoise`: PDF p.2: a finite probability ensemble; zero-weight entries are permitted.
--   - `COLUR`: PDF p.2, (2): one shared random index, with actual product unitaries.
--   - `COLUR.operation`: PDF p.2, (2): the channel implemented by the chosen ensemble.
--   - `NoiseClass`: PDF p.2: the four noise restrictions distinguished by the source.
--   - `COLUR.allowed`: PDF p.2: LUR independence is imposed on the implementing ensemble, not just its channel.
--   - `NoiseCost`: PDF pp.2--3, (4): the three ensemble noise costs.
--   - `COLUR.cost`: PDF pp.2--3: size and Shannon cost belong to an ensemble; exchange belongs to its channel.
--   - `Decorrelates`: PDF p.2, (3): approximation by a normalized product, full trace norm.
--   - `Disentangles`: PDF p.6, (14): closeness to an actual normalized separable state.
--   - `erasureEta`: PDF p.3, (5): the capped entropy correction, including the continuous value at zero.
--   - `logDimension`: PDF pp.3,6: fixed one-copy dimension d=d_A*d_B, independent of blocklength.
--   - `totalCosts`: PDF p.4: feasible noise costs at a finite block.
--   - `totalBlockRate`: PDF p.4: optimal finite noise per copy; n=k+1 excludes division by zero.
--   - `rateLimit`: PDF pp.4,7: choose liminf (optimistic) or limsup (pessimistic), before vanishing error.
--   - `totalErasure`: PDF p.4, Theorem II.3: operational erasure rate, independently computed from ensembles.
--   - `disentanglingSizes`: PDF p.7: admissible finite ensemble sizes for entanglement erasure.
--   - `minimumDisentanglingSize`: PDF p.7: N(n,eps), the smallest size, defined by the actual feasible channels.
--   - `entanglementBlockRate`: PDF p.7: normalized finite-block cost; only positive lengths enter the limit.
--   - `entanglementErasure`: PDF pp.7--8: optimistic/pessimistic erasure, without assuming the conjectured entropy formula.
--   - `separableEntropyCosts`: PDF p.6, Proposition III.1: all COLUR maps and nearby separable targets are optimized.
--   - `withAncilla`: PDF p.5: combine rho and an arbitrary ancillary bipartite state in party order.
--   - `discountedCosts`: PDF p.5: finite ancillary dimensions are varied explicitly, with their cost discounted.
--   - `blockIndex`: PDF pp.6--7: concatenate n successive k-copy blocks, retaining the party order.
--   - `regroupedChannelPower`: PDF p.7: transport the accepted tensor-power channel from copy order (AB)^n into party order A^n:B^n, on every matrix coefficient including reference blocks.
--   - `schmidtKet`: PDF p.8: normalized Schmidt ket in arbitrary orthonormal local frames.
--   - `schmidtDiagonal`: PDF p.8: the dephased Schmidt state; the output is constructed, not assumed.
--   - `schmidtPhase`: PDF p.8: positive phase exp(2*pi*i*k*j/D), identity on the unused orthogonal complement.
--   - `PublicProtocol`: PDF pp.5--6, Remark II.6: a finite adaptive public-instrument tree. Every outcome is public; subsequent local instruments may depend on the full transcript. All finite local dimensions, outcomes, Kraus counts, and finite numbers of rounds occur.
--   - `PublicProtocol.average`: PDF pp.5--6, (12)--(13): actual expected final mutual information conditional on all public messages. Zero-probability branches contribute zero, without normalization.
--   - `MultiCopies`: PDF p.10: party i's n-copy register.
--   - `multiSourcePower`: PDF p.10: independent copies of the multipartite source, regrouped by party.
--   - `MultiNoise`: PDF p.10: multipartite COLUR, with actual product unitaries and one shared index.
--   - `MultiNoise.productUnitary`: PDF p.10: the tensor-product unitary for one ensemble member.
--   - `MultiNoise.operation`: PDF p.10: the actual randomizing operation on every joint operator.
--   - `MultiNoise.independent`: PDF p.10: independent LUR choices imposed on the ensemble itself.
--   - `MultiNoise.cost`: PDF p.10: the same three costs, counted on a multipartite ensemble.
--   - `MultiDecorrelates`: PDF p.10: a fully product target, normalized at every party.
--   - `reducedOn`: PDF p.10: an actual partial trace onto a specified set of parties.
--   - `multiInformation`: PDF p.10, (16): the entropy expression, distinct from the operational erasure rate.
--   - `tailInformation`: PDF p.10: I(A_j : A_{j+1}...A_p), on the original tail marginal.
--   - `multiCosts`: PDF p.10: finite-block multipartite feasible costs.
--   - `multiBlockRate`: PDF p.10: normalized finite cost, with strictly positive copy count.
--   - `multiErasure`: PDF p.10: operational multipartite total erasure, without an entropy definition.
--   - `successiveBlockOutput`: PDF p.10: the same execution at arbitrary positive blocklength.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, https://arxiv.org/abs/quant-ph/0410091v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05

/-!
Groisman--Popescu--Winter, arXiv:quant-ph/0410091v2.
All entropies are in bits; traceNorm is the full Schatten 1-norm.
Accepted frozen interfaces are imported; new operational definitions are confined to
this paper. The operational costs below contain no mutual-information formula. Finite nonzero local spaces may have unequal dimensions.
The source's conjectures, erroneous formulas, and cited background are inventoried
in HARD.md. Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)
open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)
open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)
open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: rho tensor n in party order A^n:B^n. -/
def sourcePower {A B : Type} (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix (Copies A n × Copies B n) (Copies A n × Copies B n) ℂ :=
  fun x y => ∏ t, rho (x.1 t, x.2 t) (y.1 t, y.2 t)

/-- PDF p.2: a finite probability ensemble; zero-weight entries are permitted. -/
structure LocalNoise (A : Type) [Fintype A] where
  count : ℕ
  count_pos : 0 < count
  weight : Fin count → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  unitary : Fin count → Matrix.unitaryGroup A ℂ

/-- PDF p.2, (2): one shared random index, with actual product unitaries. -/
structure COLUR (A B : Type) [Fintype A] [Fintype B] where
  count : ℕ
  count_pos : 0 < count
  weight : Fin count → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  alice : Fin count → Matrix.unitaryGroup A ℂ
  bob : Fin count → Matrix.unitaryGroup B ℂ

/-- PDF p.2, (2): the channel implemented by the chosen ensemble. -/
def COLUR.operation {A B : Type} [Fintype A] [Fintype B] (R : COLUR A B) :
    Superop (A × B) (A × B) :=
  fun rho => ∑ i, (R.weight i : ℂ) •
    (Matrix.kronecker (R.alice i : Matrix A A ℂ) (R.bob i : Matrix B B ℂ) * rho *
      (Matrix.kronecker (R.alice i : Matrix A A ℂ) (R.bob i : Matrix B B ℂ))ᴴ)

/-- PDF p.2: the four noise restrictions distinguished by the source. -/
inductive NoiseClass where
  | coordinated | alice | bob | independent
  deriving DecidableEq

/-- PDF p.2: LUR independence is imposed on the implementing ensemble, not just its channel. -/
def COLUR.allowed {A B : Type} [Fintype A] [Fintype B]
    (R : COLUR A B) : NoiseClass → Prop
  | .coordinated => True
  | .alice => ∀ i, R.bob i = 1
  | .bob => ∀ i, R.alice i = 1
  | .independent => ∃ L : LocalNoise A, ∃ M : LocalNoise B,
      ∃ e : Fin R.count ≃ (Fin L.count × Fin M.count),
        (∀ i, R.weight i = L.weight (e i).1 * M.weight (e i).2) ∧
        (∀ i, R.alice i = L.unitary (e i).1) ∧
        (∀ i, R.bob i = M.unitary (e i).2)

/-- PDF pp.2--3, (4): the three ensemble noise costs. -/
inductive NoiseCost where
  | size | entropy | exchange
  deriving DecidableEq

/-- PDF pp.2--3: size and Shannon cost belong to an ensemble; exchange belongs to its channel. -/
def COLUR.cost {A B : Type} [Fintype A] [Fintype B] (R : COLUR A B)
    (rho : Matrix (A × B) (A × B) ℂ) : NoiseCost → ℝ
  | .size => Real.logb 2 R.count
  | .entropy => shannon R.weight
  | .exchange => entropyExchange R.operation rho

/-- PDF p.2, (3): approximation by a normalized product, full trace norm. -/
def Decorrelates {A B : Type} [Fintype A] [Fintype B]
    (out : Matrix (A × B) (A × B) ℂ) (eps : ℝ) : Prop :=
  ∃ a : Matrix A A ℂ, ∃ b : Matrix B B ℂ,
    IsDensityMatrix a ∧ IsDensityMatrix b ∧ traceNorm (out - Matrix.kronecker a b) ≤ eps

/-- PDF p.6, (14): closeness to an actual normalized separable state. -/
def Disentangles {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (out : Matrix (A × B) (A × B) ℂ) (eps : ℝ) : Prop :=
  ∃ sigma : Matrix (A × B) (A × B) ℂ,
    Entanglement.IsSeparableDensity sigma ∧ traceNorm (out - sigma) ≤ eps

/-- PDF p.3, (5): the capped entropy correction, including the continuous value at zero. -/
def erasureEta (x : ℝ) : ℝ :=
  if x ≤ (Real.exp 1)⁻¹ then -x * Real.logb 2 x
  else (Real.exp 1)⁻¹ * Real.logb 2 (Real.exp 1)

/-- PDF pp.3,6: fixed one-copy dimension d=d_A*d_B, independent of blocklength. -/
def logDimension (A B : Type) [Fintype A] [Fintype B] : ℝ :=
  Real.logb 2 (Fintype.card A * Fintype.card B : ℕ)

/-- PDF p.4: feasible noise costs at a finite block. -/
def totalCosts {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) (eps : ℝ)
    (mode : NoiseClass) (cost : NoiseCost) : Set ℝ :=
  {v | ∃ R : COLUR (Copies A n) (Copies B n), R.allowed mode ∧
    Decorrelates (R.operation (sourcePower rho n)) eps ∧
    v = R.cost (sourcePower rho n) cost}

/-- PDF p.4: optimal finite noise per copy; n=k+1 excludes division by zero. -/
def totalBlockRate {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (eps : ℝ) (mode : NoiseClass)
    (cost : NoiseCost) (k : ℕ) : ℝ :=
  sInf (totalCosts rho (k+1) eps mode cost) / (k+1 : ℕ)

/-- PDF pp.4,7: choose liminf (optimistic) or limsup (pessimistic), before vanishing error. -/
def rateLimit (pessimistic : Bool) (f : ℕ → ℝ) : ℝ :=
  if pessimistic then limsup f atTop else liminf f atTop

/-- PDF p.4, Theorem II.3: operational erasure rate, independently computed from ensembles. -/
def totalErasure {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (mode : NoiseClass)
    (cost : NoiseCost) (pessimistic : Bool) : ℝ :=
  sSup {v | ∃ eps > (0 : ℝ), v = rateLimit pessimistic (totalBlockRate rho eps mode cost)}

/-- PDF p.7: admissible finite ensemble sizes for entanglement erasure. -/
def disentanglingSizes {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) (eps : ℝ) : Set ℕ :=
  {N | ∃ R : COLUR (Copies A n) (Copies B n), R.count = N ∧
    Disentangles (R.operation (sourcePower rho n)) eps}

/-- PDF p.7: N(n,eps), the smallest size, defined by the actual feasible channels. -/
def minimumDisentanglingSize {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) (eps : ℝ) : ℕ :=
  sInf (disentanglingSizes rho n eps)

/-- PDF p.7: normalized finite-block cost; only positive lengths enter the limit. -/
def entanglementBlockRate {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ) (eps : ℝ) (k : ℕ) : ℝ :=
  Real.logb 2 (minimumDisentanglingSize rho (k+1) eps) / (k+1 : ℕ)

/-- PDF pp.7--8: optimistic/pessimistic erasure, without assuming the conjectured entropy formula. -/
def entanglementErasure {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (pessimistic : Bool) : ℝ :=
  sSup {v | ∃ eps > (0 : ℝ), v = rateLimit pessimistic (entanglementBlockRate rho eps)}

/-- PDF p.6, Proposition III.1: all COLUR maps and nearby separable targets are optimized. -/
def separableEntropyCosts {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (n : ℕ) (eps : ℝ) : Set ℝ :=
  {v | ∃ R : COLUR (Copies A n) (Copies B n),
    ∃ sigma : Matrix (Copies A n × Copies B n) (Copies A n × Copies B n) ℂ,
      Entanglement.IsSeparableDensity sigma ∧
      traceNorm (sigma - R.operation (sourcePower rho n)) ≤ eps ∧
      v = vnEntropy sigma - n * vnEntropy rho - n * eps * logDimension A B - erasureEta eps}

/-- Sanity: no-copy tensors are the scalar unit, not the zero state. -/
example {A B : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (x y : Copies A 0 × Copies B 0) : sourcePower rho 0 x y = 1 := by
  simp [sourcePower]

/-- Sanity: the one-copy matrix preserves every entry and its party order. -/
example {A B : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (x y : Copies A 1 × Copies B 1) :
    sourcePower rho 1 x y = rho (x.1 0, x.2 0) (y.1 0, y.2 0) := by
  simp [sourcePower]

/-- Sanity: the zero probability and erasureEta boundary are continuous entropy contributions. -/
example : shannon (fun _ : Fin 1 => (1 : ℝ)) = 0 ∧ erasureEta 0 = 0 := by
  simp [shannon, erasureEta, le_of_lt (inv_pos.mpr (Real.exp_pos 1))]

/-- Sanity: every chosen randomizing ensemble sends the zero operator to zero. -/
example {A B : Type} [Fintype A] [Fintype B] (R : COLUR A B) :
    R.operation 0 = 0 := by
  simp [COLUR.operation]

/-- Sanity: the one-copy zero source retains zero. -/
example {A B : Type}
    (x y : Copies A 1 × Copies B 1) :
    sourcePower (0 : Matrix (A × B) (A × B) ℂ) 1 x y = 0 := by
  simp [sourcePower]

/-- PDF p.5: combine rho and an arbitrary ancillary bipartite state in party order. -/
def withAncilla {A B C D : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (gamma : Matrix (C × D) (C × D) ℂ) :
    Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ :=
  fun x y => rho (x.1.1,x.2.1) (y.1.1,y.2.1) * gamma (x.1.2,x.2.2) (y.1.2,y.2.2)

/-- PDF p.5: finite ancillary dimensions are varied explicitly, with their cost discounted. -/
def discountedCosts {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {v | ∃ c d : ℕ, ∃ hc : 0 < c, ∃ hd : 0 < d,
    ∃ gamma : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ, IsDensityMatrix gamma ∧
      v = totalErasure (withAncilla rho gamma) .coordinated .size true -
        totalErasure gamma .coordinated .size true}

/-- PDF pp.6--7: concatenate n successive k-copy blocks, retaining the party order. -/
def blockIndex {k n : ℕ} (t : Fin n) (s : Fin k) : Fin (k*n) :=
  Fin.cast (Nat.mul_comm n k) (finProdFinEquiv (t,s))

/-- PDF p.7: transport the accepted tensor-power channel from copy order (AB)^n
into party order A^n:B^n, on every matrix coefficient including reference blocks. -/
def regroupedChannelPower {A B : Type} [Fintype A] [Fintype B]
    (T : Superop (A × B) (A × B)) (n : ℕ) :
    Superop (Copies A n × Copies B n) (Copies A n × Copies B n) :=
  fun rho x y => channelPower T n
    (fun u v => rho ((fun t => (u t).1), (fun t => (u t).2))
      ((fun t => (v t).1), (fun t => (v t).2)))
    (fun t => (x.1 t, x.2 t)) (fun t => (y.1 t, y.2 t))

/-- PDF p.8: normalized Schmidt ket in arbitrary orthonormal local frames. -/
def schmidtKet {A B : Type} {D : ℕ} (f : Fin D → ℝ)
    (a : Matrix A (Fin D) ℂ) (b : Matrix B (Fin D) ℂ) : EuclideanSpace ℂ (A × B) :=
  WithLp.toLp 2 fun x => ∑ j, (Real.sqrt (f j) : ℂ) * a x.1 j * b x.2 j

/-- PDF p.8: the dephased Schmidt state; the output is constructed, not assumed. -/
def schmidtDiagonal {A B : Type} {D : ℕ} (f : Fin D → ℝ)
    (a : Matrix A (Fin D) ℂ) (b : Matrix B (Fin D) ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun x y => ∑ j, (f j : ℂ) * a x.1 j * b x.2 j * conj (a y.1 j * b y.2 j)

/-- PDF p.8: positive phase exp(2*pi*i*k*j/D), identity on the unused orthogonal complement. -/
def schmidtPhase {A : Type} [Fintype A] {D : ℕ}
    (a : Matrix A (Fin D) ℂ) (k : Fin D) : Matrix A A ℂ :=
  (1 : Matrix A A ℂ) + (Matrix.of fun (x y : A) => ∑ j,
    (Complex.exp (2 * Real.pi * Complex.I *
      (k.val : ℂ) * (j.val : ℂ) / (D : ℂ)) - 1) * a x j * conj (a y j))

/-- PDF pp.5--6, Remark II.6: a finite adaptive public-instrument tree.
Every outcome is public; subsequent local instruments may depend on the full transcript.
All finite local dimensions, outcomes, Kraus counts, and finite numbers of rounds occur. -/
inductive PublicProtocol : ℕ → ℕ → Type
  | stop {a b : ℕ} : PublicProtocol a b
  | alice {a b c : ℕ} (hc : 0 < c) (outcomeCount : ℕ)
      (I : RectangularInstrument (Fin a) (Fin c) (Fin (outcomeCount+1)))
      (next : Fin (outcomeCount+1) → PublicProtocol c b) : PublicProtocol a b
  | bob {a b d : ℕ} (hd : 0 < d) (outcomeCount : ℕ)
      (I : RectangularInstrument (Fin b) (Fin d) (Fin (outcomeCount+1)))
      (next : Fin (outcomeCount+1) → PublicProtocol a d) : PublicProtocol a b

/-- PDF pp.5--6, (12)--(13): actual expected final mutual information conditional on
all public messages. Zero-probability branches contribute zero, without normalization. -/
def PublicProtocol.average : {a b : ℕ} → PublicProtocol a b →
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ → ℝ
  | _, _, .stop, rho => mutualInformation rho
  | _, _, .alice _ _ I next, rho => ∑ x,
      let omega := first (I.branch x) rho
      let p := omega.trace.re
      if 0 < p then p * (next x).average ((p : ℂ)⁻¹ • omega) else 0
  | _, _, .bob _ _ I next, rho => ∑ x,
      let omega := idTensorSuperop (I.branch x) rho
      let p := omega.trace.re
      if 0 < p then p * (next x).average ((p : ℂ)⁻¹ • omega) else 0

/-- Sanity: no instrument leaves the original total correlation. -/
example {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    PublicProtocol.average .stop rho = mutualInformation rho := rfl

/-- PDF p.10: party i's n-copy register. -/
abbrev MultiCopies {p : ℕ} (d : Fin p → ℕ) (n : ℕ) (i : Fin p) := Copies (Fin (d i)) n

/-- PDF p.10: independent copies of the multipartite source, regrouped by party. -/
def multiSourcePower {p : ℕ} {d : Fin p → ℕ}
    (rho : Matrix (Config d) (Config d) ℂ) (n : ℕ) :
    Matrix ((i : Fin p) → MultiCopies d n i) ((i : Fin p) → MultiCopies d n i) ℂ :=
  fun x y => ∏ t, rho (fun i => x i t) (fun i => y i t)

/-- PDF p.10: multipartite COLUR, with actual product unitaries and one shared index. -/
structure MultiNoise {p : ℕ} (D : Fin p → Type) [∀ i, Fintype (D i)] where
  count : ℕ
  count_pos : 0 < count
  weight : Fin count → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  weight_sum : ∑ j, weight j = 1
  unitary : Fin count → (i : Fin p) → Matrix.unitaryGroup (D i) ℂ

/-- PDF p.10: the tensor-product unitary for one ensemble member. -/
def MultiNoise.productUnitary {p : ℕ} {D : Fin p → Type} [∀ i, Fintype (D i)]
    (R : MultiNoise D) (j : Fin R.count) : Matrix ((i : Fin p) → D i) ((i : Fin p) → D i) ℂ :=
  fun x y => ∏ i, (R.unitary j i : Matrix (D i) (D i) ℂ) (x i) (y i)

/-- PDF p.10: the actual randomizing operation on every joint operator. -/
def MultiNoise.operation {p : ℕ} {D : Fin p → Type} [∀ i, Fintype (D i)]
    (R : MultiNoise D) : Superop ((i : Fin p) → D i) ((i : Fin p) → D i) :=
  fun rho => ∑ j, (R.weight j : ℂ) •
    (R.productUnitary j * rho * (R.productUnitary j)ᴴ)

/-- PDF p.10: independent LUR choices imposed on the ensemble itself. -/
def MultiNoise.independent {p : ℕ} {D : Fin p → Type} [∀ i, Fintype (D i)]
    (R : MultiNoise D) : Prop :=
  ∃ L : (i : Fin p) → LocalNoise (D i),
    ∃ e : Fin R.count ≃ ((i : Fin p) → Fin (L i).count),
      (∀ j, R.weight j = ∏ i, (L i).weight (e j i)) ∧
      (∀ j i, R.unitary j i = (L i).unitary (e j i))

/-- PDF p.10: the same three costs, counted on a multipartite ensemble. -/
def MultiNoise.cost {p : ℕ} {D : Fin p → Type} [∀ i, Fintype (D i)]
    (R : MultiNoise D) (rho : Matrix ((i : Fin p) → D i) ((i : Fin p) → D i) ℂ) : NoiseCost → ℝ
  | .size => Real.logb 2 R.count
  | .entropy => shannon R.weight
  | .exchange => entropyExchange R.operation rho

/-- PDF p.10: a fully product target, normalized at every party. -/
def MultiDecorrelates {p : ℕ} {D : Fin p → Type} [∀ i, Fintype (D i)]
    (out : Matrix ((i : Fin p) → D i) ((i : Fin p) → D i) ℂ) (eps : ℝ) : Prop :=
  ∃ sigma : (i : Fin p) → Matrix (D i) (D i) ℂ,
    (∀ i, IsDensityMatrix (sigma i)) ∧
    traceNorm (out - (Matrix.of fun (x y : (i : Fin p) → D i) =>
      ∏ i, sigma i (x i) (y i))) ≤ eps

/-- PDF p.10: an actual partial trace onto a specified set of parties. -/
def reducedOn {p : ℕ} {d : Fin p → ℕ}
    (rho : Matrix (Config d) (Config d) ℂ)
    (S : Finset (Fin p)) :
    Matrix ((i : {i // i ∈ S}) → Fin (d i.val))
      ((i : {i // i ∈ S}) → Fin (d i.val)) ℂ :=
  fun u v => ∑ x, ∑ y,
    if (∀ i : {i // i ∈ S}, x i.val = u i) ∧
       (∀ i : {i // i ∈ S}, y i.val = v i) ∧
       (∀ i, i ∉ S → x i = y i) then rho x y else 0

/-- PDF p.10, (16): the entropy expression, distinct from the operational erasure rate. -/
def multiInformation {p : ℕ} {d : Fin p → ℕ}
    (rho : Matrix (Config d) (Config d) ℂ) : ℝ :=
  (∑ i, vnEntropy (reducedOn rho {i})) - vnEntropy rho

/-- PDF p.10: I(A_j : A_{j+1}...A_p), on the original tail marginal. -/
def tailInformation {p : ℕ} {d : Fin p → ℕ}
    (rho : Matrix (Config d) (Config d) ℂ)
    (j : Fin (p-1)) : ℝ :=
  vnEntropy (reducedOn rho (Finset.univ.filter fun i => i.val = j.val)) +
    vnEntropy (reducedOn rho (Finset.univ.filter fun i => j.val < i.val)) -
    vnEntropy (reducedOn rho (Finset.univ.filter fun i => j.val ≤ i.val))

/-- PDF p.10: finite-block multipartite feasible costs. -/
def multiCosts {p : ℕ} {d : Fin p → ℕ}
    (rho : Matrix (Config d) (Config d) ℂ)
    (n : ℕ) (eps : ℝ) (independent : Bool) (cost : NoiseCost) : Set ℝ :=
  {v | ∃ R : MultiNoise (MultiCopies d n),
    (independent = true → R.independent) ∧
    MultiDecorrelates (R.operation (multiSourcePower rho n)) eps ∧
    v = R.cost (multiSourcePower rho n) cost}

/-- PDF p.10: normalized finite cost, with strictly positive copy count. -/
def multiBlockRate {p : ℕ} {d : Fin p → ℕ}
    (rho : Matrix (Config d) (Config d) ℂ)
    (eps : ℝ) (independent : Bool) (cost : NoiseCost) (k : ℕ) : ℝ :=
  sInf (multiCosts rho (k+1) eps independent cost) / (k+1 : ℕ)

/-- PDF p.10: operational multipartite total erasure, without an entropy definition. -/
def multiErasure {p : ℕ} {d : Fin p → ℕ}
    (rho : Matrix (Config d) (Config d) ℂ)
    (independent : Bool) (cost : NoiseCost) (pessimistic : Bool) : ℝ :=
  sSup {v | ∃ eps > (0 : ℝ), v = rateLimit pessimistic (multiBlockRate rho eps independent cost)}

/-- PDF p.10: the same execution at arbitrary positive blocklength. -/
def successiveBlockOutput {p : ℕ} {d : Fin p → ℕ} {n : ℕ}
    (R : Fin (p-1) → MultiNoise (MultiCopies d n))
    (rho : Matrix ((i : Fin p) → MultiCopies d n i) ((i : Fin p) → MultiCopies d n i) ℂ) :=
  (List.finRange (p-1)).foldl (fun state j => (R j).operation state) rho

/-- Sanity: a single party requires no successive stage. -/
example {d : Fin 1 → ℕ} {n : ℕ}
    (R : Fin (1-1) → MultiNoise (MultiCopies d n))
    (rho : Matrix ((i : Fin 1) → MultiCopies d n i) ((i : Fin 1) → MultiCopies d n i) ℂ) :
    successiveBlockOutput R rho = rho := by
  simp [successiveBlockOutput]

end QAlgorithms.Papers.Independent.Intakenext100.P47


