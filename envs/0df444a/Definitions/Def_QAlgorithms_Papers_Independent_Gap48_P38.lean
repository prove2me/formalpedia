-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38
-- name    : QAlgorithms_Papers_Independent_Gap48_P38
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:04:09.561976+00:00
-- url     : https://prove2.me/theorems/7ffbe44d-9d54-405b-a8ca-fa064fcdfbc4
-- title:
--   Definitions for Optimal quantum source coding with quantum information at the encoder and decoder
-- statement:
--   The objects the formalized statements of *Optimal quantum source coding with quantum information at the encoder and decoder* (arXiv:0706.2907) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Restricted`: Configurations of exactly the named subsystem, including the empty tensor product (p.2).
--   - `subsystemIndex`: Assemble retained and traced-out computational indices; no coordinate is discarded twice (p.2).
--   - `subsystemReduction`: Actual partial trace of the full operator over the complement of s (PDF p.2). The accepted traceRight is applied after regrouping retained/complementary indices; off-diagonal retained entries are preserved.
--   - `registerEntropy`: Entropy in bits of an actual reduced operator, not independent entropy data (PDF p.2).
--   - `registerMutualInfo`: I(S;T)=H(S)+H(T)-H(ST); the statements use disjoint subsystems (PDF p.2).
--   - `registerCMI`: I(S;T|V)=H(SV)+H(TV)-H(V)-H(STV), in bits (PDF p.2).
--   - `cornerQ`: The numerical corner qubit cost from (2), with A,B,C,D numbered 0,1,2,3 (PDF p.2). This definition is the entropy expression, not a definition of operational achievability.
--   - `cornerE`: The signed numerical corner ebit cost from (2), consumption positive (PDF p.2).
--   - `iidGrouped`: IID copies regrouped by subsystem, with exactly the original amplitudes (PDF pp.4--5).
--   - `productProjection`: Product of the local projections, in the same regrouped tensor convention (PDF p.5).
--   - `TypicalBounds`: All clauses of Theorem 5, including its continuation on PDF p.5. Ranks are Schatten zero quantities; frobNorm squared is the squared Schatten two norm; specNorm is the Schatten infinity norm. The six subsystems exclude ABC.
--   - `decouplingMarginal`: The actual Bhat,E marginal of (WU tensor I_E)rho(WU tensor I_E)^dagger, tracing S only, with S,Bhat,E order fixed explicitly (PDF pp.6,11).
--   - `localAct`: Apply an X operator, leaving the reference Y untouched (PDF p.7).
--   - `coherentDecoder`: The explicitly constructed coherent decoder, with output X,K order (PDF p.7). The square root on Lambda is essential.
--   - `decoderOverlap`: The overlap <j|<psi|(L tensor I_Y)|phi>, including both references (PDF p.7).
--   - `coherentMeasurementError`: P in Lemma 5 is the average measurement error on U_j psi (PDF p.7).
--   - `decodingFidelity`: F in Lemma 5 is the average SQUARED pure-state fidelity (PDF p.7).
--   - `assistedChannel`: The actual channel D composed with (E tensor identity) on rho tensor tau. E acts on X,L; D acts on Y,Lprime; the untouched Lprime off-diagonal blocks are retained. No extra communication or classical message is available (PDF p.9).
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, https://arxiv.org/abs/0706.2907v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_LinearSystems
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

/-!
Statements from Yard--Devetak, arXiv:0706.2907v2. PDF pages are used throughout.
All registers are finite complex registers with fixed bases; nonempty register
instances permit dimension one. Entropies are in bits, distances are FULL trace
norms, and pure-state fidelities are squared overlaps. Operational resource
inequalities without an audited simulation interface are explicitly deferred
in the unit's HARD.md rather than replaced by entropy inequalities.
-/

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Configurations of exactly the named subsystem, including the empty tensor product (p.2). -/
abbrev Restricted {m : ℕ} (I : Fin m → Type) (s : Finset (Fin m)) :=
  (i : {j : Fin m // j ∈ s}) → I i.val

/-- Assemble retained and traced-out computational indices; no coordinate is discarded twice (p.2). -/
def subsystemIndex {m : ℕ} (I : Fin m → Type) (s : Finset (Fin m))
    (x : Restricted I s) (z : Restricted I (Finset.univ \ s)) : (∀ i, I i) :=
  fun i => if h : i ∈ s then x ⟨i, h⟩
    else z ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩⟩

/-- Actual partial trace of the full operator over the complement of s (PDF p.2).
The accepted traceRight is applied after regrouping retained/complementary
indices; off-diagonal retained entries are preserved. -/
def subsystemReduction {m : ℕ} (I : Fin m → Type) [∀ i, Fintype (I i)]
    (rho : Matrix (∀ i, I i) (∀ i, I i) ℂ) (s : Finset (Fin m)) :
    Matrix (Restricted I s) (Restricted I s) ℂ :=
  traceRight (fun x y : Restricted I s × Restricted I (Finset.univ \ s) =>
    rho (subsystemIndex I s x.1 x.2) (subsystemIndex I s y.1 y.2))

/-- Entropy in bits of an actual reduced operator, not independent entropy data (PDF p.2). -/
def registerEntropy {m : ℕ} (I : Fin m → Type) [∀ i, Fintype (I i)]
    (rho : Matrix (∀ i, I i) (∀ i, I i) ℂ) (s : Finset (Fin m)) : ℝ :=
  vnEntropy (subsystemReduction I rho s)

/-- I(S;T)=H(S)+H(T)-H(ST); the statements use disjoint subsystems (PDF p.2). -/
def registerMutualInfo {m : ℕ} (I : Fin m → Type) [∀ i, Fintype (I i)]
    (rho : Matrix (∀ i, I i) (∀ i, I i) ℂ) (s t : Finset (Fin m)) : ℝ :=
  registerEntropy I rho s + registerEntropy I rho t - registerEntropy I rho (s ∪ t)

/-- I(S;T|V)=H(SV)+H(TV)-H(V)-H(STV), in bits (PDF p.2). -/
def registerCMI {m : ℕ} (I : Fin m → Type) [∀ i, Fintype (I i)]
    (rho : Matrix (∀ i, I i) (∀ i, I i) ℂ) (s t v : Finset (Fin m)) : ℝ :=
  registerEntropy I rho (s ∪ v) + registerEntropy I rho (t ∪ v) -
    registerEntropy I rho v - registerEntropy I rho (s ∪ t ∪ v)

/-- The numerical corner qubit cost from (2), with A,B,C,D numbered 0,1,2,3 (PDF p.2).
This definition is the entropy expression, not a definition of operational achievability. -/
def cornerQ (I : Fin 4 → Type) [∀ i, Fintype (I i)]
    (rho : Matrix (∀ i, I i) (∀ i, I i) ℂ) : ℝ := registerCMI I rho {2} {3} {1} / 2

/-- The signed numerical corner ebit cost from (2), consumption positive (PDF p.2). -/
def cornerE (I : Fin 4 → Type) [∀ i, Fintype (I i)]
    (rho : Matrix (∀ i, I i) (∀ i, I i) ℂ) : ℝ :=
  registerMutualInfo I rho {0} {2} / 2 - registerMutualInfo I rho {1} {2} / 2

example {m : ℕ} (I : Fin m → Type) (s : Finset (Fin m))
    (x : Restricted I s) (z : Restricted I (Finset.univ \ s))
    (i : Fin m) (hi : i ∈ s) : subsystemIndex I s x z i = x ⟨i, hi⟩ := by
  simp [subsystemIndex, hi]

example {m : ℕ} (I : Fin m → Type) [∀ i, Fintype (I i)] (s : Finset (Fin m)) :
    subsystemReduction I (0 : Matrix (∀ i, I i) (∀ i, I i) ℂ) s = 0 := by
  ext x y
  simp [subsystemReduction, traceRight]

example {m : ℕ} (I : Fin m → Type) [∀ i, Fintype (I i)] (s : Finset (Fin m)) :
    registerEntropy I (0 : Matrix (∀ i, I i) (∀ i, I i) ℂ) s = 0 := by
  have hz : subsystemReduction I (0 : Matrix (∀ i, I i) (∀ i, I i) ℂ) s = 0 := by
    ext x y
    simp [subsystemReduction, traceRight]
  rw [registerEntropy, hz]
  simp [vnEntropy]

/-- IID copies regrouped by subsystem, with exactly the original amplitudes (PDF pp.4--5). -/
def iidGrouped {m : ℕ} (I : Fin m → Type) (n : ℕ)
    (psi : EuclideanSpace ℂ (∀ i, I i)) : EuclideanSpace ℂ (∀ i, Fin n → I i) :=
  WithLp.toLp 2 fun x => ∏ t : Fin n, psi (fun i => x i t)

/-- Product of the local projections, in the same regrouped tensor convention (PDF p.5). -/
def productProjection (I : Fin 3 → Type) [∀ i, Fintype (I i)] (n : ℕ)
    (P : (i : Fin 3) → Matrix (Restricted (fun j => Fin n → I j) {i})
      (Restricted (fun j => Fin n → I j) {i}) ℂ) :
    Matrix (∀ i, Fin n → I i) (∀ i, Fin n → I i) ℂ :=
  fun x y => ∏ i : Fin 3, P i (fun j => x j.val) (fun j => y j.val)

/-- All clauses of Theorem 5, including its continuation on PDF p.5.
Ranks are Schatten zero quantities; frobNorm squared is the squared Schatten two norm;
specNorm is the Schatten infinity norm. The six subsystems exclude ABC. -/
def TypicalBounds (I : Fin 3 → Type) [∀ i, Fintype (I i)]
    (psi : EuclideanSpace ℂ (∀ i, I i)) (n : ℕ) (delta epsilon : ℝ)
    (P : (i : Fin 3) → Matrix (Restricted (fun j => Fin n → I j) {i})
      (Restricted (fun j => Fin n → I j) {i}) ℂ) : Prop :=
  let J := fun i => Fin n → I i
  let rho := pureDensity psi
  let source := iidGrouped I n psi
  let v := act (productProjection I n P) source
  let vC := act (productProjection I n (fun i => if i = 2 then P i else 1)) source
  let phi := pureDensity (normalizedVec v)
  (∀ i : Fin 3, (P i).IsHermitian ∧ P i * P i = P i ∧
    effectProb (P i) (subsystemReduction J (pureDensity source) {i}) ≥ 1 - epsilon ∧
    Real.rpow 2 ((n : ℝ) * registerEntropy I rho {i} - n * delta) ≤ (P i).trace.re ∧
    (P i).trace.re ≤ Real.rpow 2 ((n : ℝ) * registerEntropy I rho {i} + n * delta)) ∧
  0 < ‖v‖ ∧ traceNorm (phi - pureDensity source) ≤ epsilon ∧
  (∀ s : Finset (Fin 3), s ∈ ({ {0}, {1}, {2}, {0,1}, {1,2}, {0,2} } :
      Finset (Finset (Fin 3))) →
    let h := registerEntropy I rho s
    let tau := subsystemReduction J phi s
    Real.rpow 2 ((n : ℝ) * h - n * delta) ≤ (Matrix.rank tau : ℝ) ∧
    (Matrix.rank tau : ℝ) ≤ Real.rpow 2 ((n : ℝ) * h + n * delta) ∧
    Real.rpow 2 (-(n : ℝ) * h - n * delta) ≤ frobNorm tau ^ 2 ∧
    frobNorm tau ^ 2 ≤ Real.rpow 2 (-(n : ℝ) * h + n * delta) ∧
    Real.rpow 2 (-(n : ℝ) * h - n * delta) ≤ specNorm tau ∧
    specNorm tau ≤ Real.rpow 2 (-(n : ℝ) * h + n * delta)) ∧
  0 < ‖vC‖ ∧ traceNorm (pureDensity (normalizedVec vC) - pureDensity source) ≤ epsilon

example {m : ℕ} (I : Fin m → Type) (psi : EuclideanSpace ℂ (∀ i, I i))
    (x : (∀ i, Fin 0 → I i)) : iidGrouped I 0 psi x = 1 := by
  simp [iidGrouped]

example {J : Type} [Fintype J] : normalizedVec (0 : EuclideanSpace ℂ J) = 0 := by
  simp [normalizedVec]

example (I : Fin 3 → Type) [∀ i, Fintype (I i)] (n : ℕ) :
    productProjection I n (fun _ => 0) = 0 := by
  ext x y
  simp [productProjection]

/-- The actual Bhat,E marginal of (WU tensor I_E)rho(WU tensor I_E)^dagger,
tracing S only, with S,Bhat,E order fixed explicitly (PDF pp.6,11). -/
def decouplingMarginal {c s b e : ℕ}
    (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (rho : Matrix (Fin c × Fin e) (Fin c × Fin e) ℂ)
    (U : Matrix.unitaryGroup (Fin c) ℂ) :
    Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ :=
  let V := Matrix.kronecker (W * (U : Matrix (Fin c) (Fin c) ℂ))
    (1 : Matrix (Fin e) (Fin e) ℂ)
  let tau := V * rho * Vᴴ
  fun x y => ∑ a : Fin s, tau ((a, x.1), x.2) ((a, y.1), y.2)

example : QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [QAlgorithms.Papers.Independent.Information100.P08.maximallyMixed]

example {c s b e : ℕ} (W : Matrix (Fin s × Fin b) (Fin c) ℂ)
    (U : Matrix.unitaryGroup (Fin c) ℂ) :
    decouplingMarginal (e := e) W 0 U = 0 := by
  ext x y
  simp [decouplingMarginal]

example {J : Type} [Fintype J] [DecidableEq J] [Nonempty J] :
    QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt (0 : Matrix J J ℂ) = 0 := by
  simp [QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt, cfc_zero]

/-- Apply an X operator, leaving the reference Y untouched (PDF p.7). -/
def localAct {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X X ℂ) (psi : EuclideanSpace ℂ (X × Y)) :
    EuclideanSpace ℂ (X × Y) := act (Matrix.kronecker M (1 : Matrix Y Y ℂ)) psi

/-- The explicitly constructed coherent decoder, with output X,K order (PDF p.7).
The square root on Lambda is essential. -/
def coherentDecoder {X : Type} [Fintype X] [DecidableEq X] {k : ℕ}
    (alpha : Fin k → ℂ) (U : Fin k → Matrix.unitaryGroup X ℂ)
    (Lambda : Fin k → Matrix X X ℂ) : Matrix (X × Fin k) X ℂ :=
  fun x y => alpha x.2 * (((U x.2 : Matrix X X ℂ)ᴴ * cfc Real.sqrt (Lambda x.2)) x.1 y)

/-- The overlap <j|<psi|(L tensor I_Y)|phi>, including both references (PDF p.7). -/
def decoderOverlap {X Y : Type} [Fintype X] [Fintype Y] {k : ℕ}
    (psi : EuclideanSpace ℂ (X × Y)) (L : Matrix (X × Fin k) X ℂ)
    (phi : EuclideanSpace ℂ (X × Y)) (j : Fin k) : ℂ :=
  ∑ x : X, ∑ y : Y, conj (psi (x,y)) * ∑ z : X, L (x,j) z * phi (z,y)

/-- P in Lemma 5 is the average measurement error on U_j psi (PDF p.7). -/
def coherentMeasurementError {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] {k : ℕ}
    (psi : EuclideanSpace ℂ (X × Y)) (U : Fin k → Matrix.unitaryGroup X ℂ)
    (Lambda : Fin k → Matrix X X ℂ) : ℝ :=
  1 - (k : ℝ)⁻¹ * ∑ j, effectProb (Lambda j)
    (traceRight (pureDensity (localAct (U j : Matrix X X ℂ) psi)))

/-- F in Lemma 5 is the average SQUARED pure-state fidelity (PDF p.7). -/
def decodingFidelity {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] {k : ℕ}
    (psi : EuclideanSpace ℂ (X × Y)) (U : Fin k → Matrix.unitaryGroup X ℂ)
    (psiPrime : Fin k → EuclideanSpace ℂ (X × Y)) : ℝ :=
  (k : ℝ)⁻¹ * ∑ j, Complex.normSq (inner ℂ (localAct (U j : Matrix X X ℂ) psi) (psiPrime j))

example {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    (psi : EuclideanSpace ℂ (X × Y)) : localAct (0 : Matrix X X ℂ) psi = 0 := by
  simp [localAct, act, Matrix.mulVec]

example {X : Type} [Fintype X] [DecidableEq X] {k : ℕ}
    (U : Fin k → Matrix.unitaryGroup X ℂ) (Lambda : Fin k → Matrix X X ℂ) :
    coherentDecoder (fun _ => 0) U Lambda = 0 := by
  ext x y
  simp [coherentDecoder]

example {X Y : Type} [Fintype X] [Fintype Y] {k : ℕ}
    (psi phi : EuclideanSpace ℂ (X × Y)) (j : Fin k) :
    decoderOverlap psi (0 : Matrix (X × Fin k) X ℂ) phi j = 0 := by
  simp [decoderOverlap]

/-- The actual channel D composed with (E tensor identity) on rho tensor tau.
E acts on X,L; D acts on Y,Lprime; the untouched Lprime off-diagonal blocks
are retained. No extra communication or classical message is available (PDF p.9). -/
def assistedChannel {X Y L Lprime : Type} [Fintype X] [Fintype Y] [Fintype L]
    (E : Superop (X × L) Y) (D : Superop (Y × Lprime) X)
    (tau : Matrix (L × Lprime) (L × Lprime) ℂ) : Superop X X :=
  fun rho => D (fun a b => E
    (fun x y => rho x.1 y.1 * tau (x.2,a.2) (y.2,b.2)) a.1 b.1)

example : assistedChannel
    (fun M : Matrix (Unit × Unit) (Unit × Unit) ℂ =>
      (fun _ _ : Unit => M ((),()) ((),())))
    (fun M : Matrix (Unit × Unit) (Unit × Unit) ℂ =>
      (fun _ _ : Unit => M ((),()) ((),())))
    (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ)
    (1 : Matrix Unit Unit ℂ) () () = 1 := by
  simp [assistedChannel]

end QAlgorithms.Papers.Independent.Gap48.P38


