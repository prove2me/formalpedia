-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
-- name    : QAlgorithms_Papers_Independent_Dependency50_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:08:43.050449+00:00
-- url     : https://prove2.me/theorems/0f55ff53-23eb-4c40-b012-09306a7cc967
-- title:
--   Definitions for The mother of all protocols: Restructuring quantum information's family tree
-- statement:
--   The objects the formalized statements of *The mother of all protocols: Restructuring quantum information's family tree* (arXiv:quant-ph/0606225) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `flip`: Swap register order, without changing ownership or discarding a subsystem (p.2).
--   - `first`: A local superoperator on the first tensor factor, including off-diagonal blocks (p.14).
--   - `both`: Two independent local maps; no communication or assistance (p.14).
--   - `associate`: Reassociate the three indicated registers (p.2).
--   - `epr`: The normalized maximally entangled density matrix of local dimension d (pp.3,6). Theorems require d>0. At d=0 this total formula is zero on the empty space.
--   - `IsIso`: An isometry has orthonormal columns; rectangular codomains are permitted (p.6).
--   - `marginalRA`: R,A marginal of a density matrix ordered R,(A,B) (p.6).
--   - `marginalRB`: B,R marginal, with R first (p.15).
--   - `mutualInformation`: Quantum mutual information in bits (p.2).
--   - `quasiMutual`: J(A;B)=H(A)+H(B)+H(AB), with the source's plus sign (p.14, Eq.(37)).
--   - `sourceCopies`: The n-copy source with copies regrouped into R^n,(A^n,B^n) (pp.12,14). At n=0 every entry is 1 on a singleton space.
--   - `bipartiteBlock`: Tensor power of a bipartite density matrix, grouped by party (p.18).
--   - `motherTarget`: FQSW target: the complete transferred RAB source jointly product with one EPR state; Bob holds both the copied AB register and the second EPR half (pp.3,6).
--   - `motherOutput`: Actual forward-only FQSW evolution: encode, send Q, decode Q with Bob's B; L remains at Alice and R is never acted upon (pp.5–6).
--   - `sigma`: The post-unitary R,A2 state after discarding A1 (p.6). A is Fin(a1*a2), and finProdFinEquiv fixes the factor identification.
--   - `decouplingDifference`: Decoupling difference, with the reference first rather than last (p.6, Eq.(5)).
--   - `motherIsometry`: The complete one-shot mother isometry; A2 is retained, A1 goes to Bob (p.6).
--   - `oneShotTarget`: One-shot target in the output order R,A2,(ABcopy,Btilde) (p.6). The full AB copy makes the source-identifying W the identity and permits padding.
--   - `swap`: Swap of two complete identical registers (p.2).
--   - `swapSecond`: Swap A2 only between two copies of A=A1*A2 (p.7).
--   - `MotherCode`: One block FQSW code with physical local maps, a joint target and dimension costs (pp.3,12–13). L is distilled, Q alone is communicated.
--   - `fatherSource`: The source constructed in Eq.(31) from an actual Stinespring isometry and W1; reference (A0,B3), channel output (B,E), all EPR factors normalized (p.10).
--   - `fatherResidual`: Full purifying register H=(A0,B3,B), ordered E,H (p.10). It is a copy of the original purifier, avoiding an undersized decoding codomain.
--   - `fatherOneShotOutput`: One-shot father state after encoding, the channel and Bob's decoder, with the reference and environment retained (p.10, Eq.(32)).
--   - `fatherOneShotTarget`: The joint product target for Eq.(32), including the residual environment (p.10).
--   - `assistedInput`: Append preshared EPR assistance to the sender's input, keeping Bob's half separate. R is first; Alice then holds (X,A3) and Bob B3 (pp.9–10).
--   - `assistedOutput`: Entanglement-assisted output with a physically untouched reference (pp.9–10).
--   - `FatherCode`: Father entanglement-transmission code with source-dependent rate and unlimited local CPTP maps, no backward communication (pp.13–14).
--   - `channelSource`: Channel action on the chosen pure input, retaining feedback E (pp.4,13).
--   - `reverseOutput`: Actual feedback reverse-Shannon evolution: Alice encodes her source and EPR half into E and Q, sends Q, and Bob decodes Q with his EPR half (pp.11–12,14).
--   - `ReverseCode`: A source-relative feedback-channel simulation code; E stays at Alice and B is delivered to Bob, with complete RBE correlation tested (pp.11–12,14).
--   - `CompressionCode`: A fully quantum distributed-compression block code: independent CPTP encoders, then Charlie's CPTP decoder, tested by pure-state overlap (p.14, Eq.(36)).
--   - `compressionAchievable`: Achievable nonnegative rates, with all sufficiently large integer blocks (p.14). No slack is built into this set; SW is its Euclidean closure, as printed.
--   - `compressionRegion`: SW(phi), the closure of achievable nonnegative distributed rates (p.14).
--   - `rateRegion`: Entropic half-space region; the subtraction appears once in the sum bound (pp.15,18, Eqs.(38),(51),(52)).
--   - `conditionalMutual`: Conditional mutualInformation information I(A;B|E), state ordered (A,B),E (p.18).
--   - `squashed`: Squashed entanglement: infimum of half the conditional mutualInformation information across every finite nonempty extension dimension, without a cap (p.18). For density inputs the set is nonempty (trivial extension) and bounded below by 0. For invalid inputs this total definition may return 0; no theorem uses such inputs.
--   - `LocallyDistillable`: No-communication local distillation at rate D, using actual local channels and normalized EPR output, with no side messages or assistance (p.18).
--   - `localDistillable`: D0 is the supremum of operational local-only rates, not LOCC distillable entanglement (p.18). For density inputs the set contains 0 and is bounded above by the smaller marginal entropy. No theorem uses the junk value on invalid inputs.
--   - `cliffordOnFactors`: A projective Clifford representative in the specified two qubit factors; scalar phases do not affect the output density matrices (p.19).
--   - `twoCopy`: Two-copy conjugation; scalar phases cancel exactly (p.19, Eq.(53)).
--   - `pairedSource`: The two equal pure pairs of Section XII, with Alice's registers kept in fixed left/right order. If reverse=true, Bob and Rebecca exchange roles (pp.20–21).
--   - `RecipientGood`: One fixed sender encoder works for a specified recipient if a local decoder can recover the joint FQSW product target (pp.20–21).
--   - `randomizedEncoder`: Haar randomization after a fixed local compression, with retained L and sent Q identified in that order (pp.5,20–21).
--   - `Spectrum`: A spectral decomposition of a density matrix: normalized nonnegative eigenvalues and an orthonormal eigenbasis (Appendix A, p.22). Zero weights are permitted.
--   - `Spectrum.density`: Density matrix determined by its spectral data, not an unrelated state (p.22).
--   - `count`: Empirical count in a realized sequence, including length zero (p.21).
--   - `Typical`: Frequency typicality on positive spectral support (pp.21–22). The support clause excludes the kernel, whose original product probability is zero.
--   - `typicalProjector`: Spectral typical projector, zero on the kernel and re-embedded in the full n-copy ambient register (p.22, following Eq.(A5)).
--   - `spectralTypeProjector`: Projector for the actual type of a realized sequence, never an unrealizable real probability vector (pp.21–22).
--   - `blockVector`: Copies regrouped as R^n,(A^n,B^n) at vector level (pp.12,23).
--   - `normalizeProjection`: Normalized projected vector (p.23). At zero success the total value is zero; all uses below explicitly assert positive success before its norm/overlap bounds.
--   - `onAlice`: Extend Alice's projector by identity on R and B (pp.12,23).
--   - `schumacher`: Schumacher project-and-replace channel re-embedded into the original space; the fallback vector lies in the compressed subspace (p.23).
--   - `RankWindow`: Rank window with entropy slack in bits (p.12, property iii).
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, https://arxiv.org/abs/quant-ph/0606225v1

import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

/-! Statements from Abeyesinghe–Devetak–Hayden–Winter, quant-ph/0606225v1.
Registers are finite basis types; the first factor is the first named register.
All distances below are the full Schatten 1-norm, with maximum state distance 2.
The code predicates have explicit CPTP local maps and leave the reference untouched.
Compilation is pending the separately authorized batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P32 (purity)
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Swap register order, without changing ownership or discarding a subsystem (p.2). -/
def flip {X Y : Type*} (M : Matrix (X × Y) (X × Y) ℂ) :
    Matrix (Y × X) (Y × X) ℂ := fun i j => M (i.2,i.1) (j.2,j.1)

/-- A local superoperator on the first tensor factor, including off-diagonal blocks (p.14). -/
def first {X Y Z : Type*} (F : Superop X Y) : Superop (X × Z) (Y × Z) :=
  fun M i j => F (fun a b => M (a,i.2) (b,j.2)) i.1 j.1

/-- Two independent local maps; no communication or assistance (p.14). -/
def both {X Y Z T : Type*} (F : Superop X Y) (G : Superop Z T) :
    Superop (X × Z) (Y × T) := idTensorSuperop G ∘ first F

/-- Reassociate the three indicated registers (p.2). -/
def associate {X Y Z : Type*} (M : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ) :
    Matrix (X × (Y × Z)) (X × (Y × Z)) ℂ :=
  fun i j => M ((i.1,i.2.1),i.2.2) ((j.1,j.2.1),j.2.2)

/-- The normalized maximally entangled density matrix of local dimension d (pp.3,6).
Theorems require d>0. At d=0 this total formula is zero on the empty space. -/
def epr (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun i j => if i.1 = i.2 ∧ j.1 = j.2 then ((d : ℂ)⁻¹) else 0

/-- An isometry has orthonormal columns; rectangular codomains are permitted (p.6). -/
def IsIso {X Y : Type*} [Fintype Y] [DecidableEq X] (V : Matrix Y X ℂ) : Prop :=
  Vᴴ * V = 1

/-- R,A marginal of a density matrix ordered R,(A,B) (p.6). -/
def marginalRA {R A B : Type*} [Fintype B]
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) : Matrix (R × A) (R × A) ℂ :=
  idTensorSuperop traceRight M

/-- B,R marginal, with R first (p.15). -/
def marginalRB {R A B : Type*} [Fintype A]
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) : Matrix (R × B) (R × B) ℂ :=
  idTensorSuperop traceLeft M

/-- Quantum mutual information in bits (p.2). -/
def mutualInformation {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (M : Matrix (X × Y) (X × Y) ℂ) : ℝ :=
  vnEntropy (traceRight M) + vnEntropy (traceLeft M) - vnEntropy M

/-- J(A;B)=H(A)+H(B)+H(AB), with the source's plus sign (p.14, Eq.(37)). -/
def quasiMutual {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (traceRight M) + vnEntropy (traceLeft M) + vnEntropy M

/-- The n-copy source with copies regrouped into R^n,(A^n,B^n) (pp.12,14).
At n=0 every entry is 1 on a singleton space. -/
def sourceCopies {R A B : Type*} (n : ℕ)
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) :
    Matrix ((Fin n → R) × ((Fin n → A) × (Fin n → B)))
      ((Fin n → R) × ((Fin n → A) × (Fin n → B))) ℂ :=
  fun i j => ∏ t, M (i.1 t,(i.2.1 t,i.2.2 t)) (j.1 t,(j.2.1 t,j.2.2 t))

/-- Tensor power of a bipartite density matrix, grouped by party (p.18). -/
def bipartiteBlock {A B : Type*} (n : ℕ) (M : Matrix (A × B) (A × B) ℂ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun i j => ∏ t, M (i.1 t,i.2 t) (j.1 t,j.2 t)

/-- FQSW target: the complete transferred RAB source jointly product with one EPR state;
Bob holds both the copied AB register and the second EPR half (pp.3,6). -/
def motherTarget {R A B : Type*} (l : ℕ)
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) :
    Matrix (R × (Fin l × (Fin l × (A × B))))
      (R × (Fin l × (Fin l × (A × B)))) ℂ :=
  fun i j => M (i.1,i.2.2.2) (j.1,j.2.2.2) * epr l (i.2.1,i.2.2.1) (j.2.1,j.2.2.1)

/-- Actual forward-only FQSW evolution: encode, send Q, decode Q with Bob's B;
L remains at Alice and R is never acted upon (pp.5–6). -/
def motherOutput {R A B : Type*} {l q : ℕ}
    (Enc : Superop A (Fin l × Fin q))
    (Dec : Superop (Fin q × B) (Fin l × (A × B)))
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) :=
  idTensorSuperop (fun X => idTensorSuperop Dec (associate (first Enc X))) M

/-- The post-unitary R,A2 state after discarding A1 (p.6).
A is Fin(a1*a2), and finProdFinEquiv fixes the factor identification. -/
def sigma {R : Type*} [Fintype R] (a1 a2 : ℕ)
    (M : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) :
    Matrix (R × Fin a2) (R × Fin a2) ℂ :=
  fun i j => ∑ k : Fin a1, ∑ a, ∑ b,
    U (finProdFinEquiv (k,i.2)) a * M (i.1,a) (j.1,b) *
      conj (U (finProdFinEquiv (k,j.2)) b)

/-- Decoupling difference, with the reference first rather than last (p.6, Eq.(5)). -/
def decouplingDifference {R : Type*} [Fintype R] (a1 a2 : ℕ)
    (M : Matrix (R × Fin (a1*a2)) (R × Fin (a1*a2)) ℂ)
    (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ) :=
  let S := sigma a1 a2 M U
  S - Matrix.kronecker (traceRight S) (traceLeft S)

/-- The complete one-shot mother isometry; A2 is retained, A1 goes to Bob (p.6). -/
def motherIsometry {B : Type*} [Fintype B] {a1 a2 : ℕ}
    (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ)
    (V : Matrix ((Fin (a1*a2) × B) × Fin a2) (Fin a1 × B) ℂ) :
    Matrix (Fin a2 × ((Fin (a1*a2) × B) × Fin a2)) (Fin (a1*a2) × B) ℂ :=
  fun i j => ∑ k : Fin a1, V i.2 (k,j.2) * U (finProdFinEquiv (k,i.1)) j.1

/-- One-shot target in the output order R,A2,(ABcopy,Btilde) (p.6).
The full AB copy makes the source-identifying W the identity and permits padding. -/
def oneShotTarget {R B : Type*} (a1 a2 : ℕ)
    (M : Matrix (R × (Fin (a1*a2) × B)) (R × (Fin (a1*a2) × B)) ℂ) :
    Matrix (R × (Fin a2 × ((Fin (a1*a2) × B) × Fin a2)))
      (R × (Fin a2 × ((Fin (a1*a2) × B) × Fin a2))) ℂ :=
  fun i j => M (i.1,i.2.2.1) (j.1,j.2.2.1) *
    epr a2 (i.2.1,i.2.2.2) (j.2.1,j.2.2.2)

/-- Swap of two complete identical registers (p.2). -/
def swap (X : Type*) [DecidableEq X] : Matrix (X × X) (X × X) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

/-- Swap A2 only between two copies of A=A1*A2 (p.7). -/
def swapSecond (a1 a2 : ℕ) :
    Matrix (Fin (a1*a2) × Fin (a1*a2)) (Fin (a1*a2) × Fin (a1*a2)) ℂ :=
  fun i j =>
    let s : Fin (a1*a2) → Fin a1 × Fin a2 := finProdFinEquiv.symm
    if (s i.1).1 = (s j.1).1 ∧ (s i.2).1 = (s j.2).1 ∧
      (s i.1).2 = (s j.2).2 ∧ (s i.2).2 = (s j.1).2 then 1 else 0

/-- Identity on a register is an isometry, including dimension one (p.6). -/
example {X : Type*} [Fintype X] [DecidableEq X] : IsIso (1 : Matrix X X ℂ) := by
  simp [IsIso]

/-- Zero copies are a singleton unit source (pp.12,14). -/
example {R A B : Type*} (M : Matrix (R × (A × B)) (R × (A × B)) ℂ)
    (i j : (Fin 0 → R) × ((Fin 0 → A) × (Fin 0 → B))) : sourceCopies 0 M i j = 1 := by
  simp [sourceCopies]

/-- One-dimensional EPR normalization (p.6). -/
example : epr 1 (0,0) (0,0) = 1 := by simp [epr]

/-- One block FQSW code with physical local maps, a joint target and dimension costs
(pp.3,12–13). L is distilled, Q alone is communicated. -/
def MotherCode {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) (n : ℕ)
    (qrate erate eps delta : ℝ) : Prop :=
  ∃ l q : ℕ, 0 < l ∧ 0 < q ∧
    Real.logb 2 q ≤ n * (qrate + delta) ∧ n * (erate-delta) ≤ Real.logb 2 l ∧
    ∃ Enc : Superop (Fin n → A) (Fin l × Fin q), IsChannel Enc ∧
    ∃ Dec : Superop (Fin q × (Fin n → B))
        (Fin l × ((Fin n → A) × (Fin n → B))), IsChannel Dec ∧
      traceNorm (motherOutput Enc Dec (sourceCopies n M) - motherTarget l (sourceCopies n M)) ≤ eps

/-- The source constructed in Eq.(31) from an actual Stinespring isometry and W1;
reference (A0,B3), channel output (B,E), all EPR factors normalized (p.10). -/
def fatherSource {A B E : Type*} [Fintype A] (k m : ℕ)
    (N : Matrix (B × E) A ℂ) (W : Matrix A (Fin k × Fin m) ℂ) :
    Matrix ((Fin k × Fin m) × (B × E)) ((Fin k × Fin m) × (B × E)) ℂ :=
  fun i j => (N * W) i.2 i.1 * conj ((N * W) j.2 j.1) /
    ((k : ℂ)*(m : ℂ))

/-- Full purifying register H=(A0,B3,B), ordered E,H (p.10).
It is a copy of the original purifier, avoiding an undersized decoding codomain. -/
def fatherResidual {B E : Type*} (k m : ℕ)
    (S : Matrix ((Fin k × Fin m) × (B × E)) ((Fin k × Fin m) × (B × E)) ℂ) :
    Matrix (E × ((Fin k × Fin m) × B)) (E × ((Fin k × Fin m) × B)) ℂ :=
  fun i j => S (i.2.1,(i.2.2,i.1)) (j.2.1,(j.2.2,j.1))

/-- One-shot father state after encoding, the channel and Bob's decoder, with the
reference and environment retained (p.10, Eq.(32)). -/
def fatherOneShotOutput {A B E H : Type*} [Fintype A] [Fintype B]
    {k m : ℕ} (N : Matrix (B × E) A ℂ) (W : Matrix A (Fin k × Fin m) ℂ)
    (V : Matrix (H × Fin k) (Fin m × B) ℂ) :
    Matrix (Fin k × (E × (H × Fin k))) (Fin k × (E × (H × Fin k))) ℂ :=
  let v : EuclideanSpace ℂ (Fin k × (E × (H × Fin k))) :=
    WithLp.toLp 2 fun i =>
      (∑ t : Fin m, ∑ b : B, V i.2.2 (t,b) * (N*W) (b,i.2.1) (i.1,t)) /
        (Real.sqrt ((k : ℝ)*(m : ℝ)) : ℂ)
  pureDensity v

/-- The joint product target for Eq.(32), including the residual environment (p.10). -/
def fatherOneShotTarget {E H : Type*} (k : ℕ) (S : Matrix (E × H) (E × H) ℂ) :
    Matrix (Fin k × (E × (H × Fin k))) (Fin k × (E × (H × Fin k))) ℂ :=
  fun i j => S (i.2.1,i.2.2.1) (j.2.1,j.2.2.1) * epr k (i.1,i.2.2.2) (j.1,j.2.2.2)

/-- Append preshared EPR assistance to the sender's input, keeping Bob's half
separate. R is first; Alice then holds (X,A3) and Bob B3 (pp.9–10). -/
def assistedInput {R X : Type*} (m : ℕ) (M : Matrix (R × X) (R × X) ℂ) :
    Matrix (R × ((X × Fin m) × Fin m)) (R × ((X × Fin m) × Fin m)) ℂ :=
  fun i j => M (i.1,i.2.1.1) (j.1,j.2.1.1) *
    epr m (i.2.1.2,i.2.2) (j.2.1.2,j.2.2)

/-- Entanglement-assisted output with a physically untouched reference (pp.9–10). -/
def assistedOutput {R X A B Y : Type*} {m : ℕ}
    (Enc : Superop (X × Fin m) A) (N : Superop A B)
    (Dec : Superop (Fin m × B) Y) (M : Matrix (R × X) (R × X) ℂ) :=
  idTensorSuperop (fun Z => Dec (flip (first N (first Enc Z)))) (assistedInput m M)

/-- Father entanglement-transmission code with source-dependent rate and
unlimited local CPTP maps, no backward communication (pp.13–14). -/
def FatherCode {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (Nch : Superop A B) (n : ℕ) (qrate erate eps delta : ℝ) : Prop :=
  ∃ k m : ℕ, 0 < k ∧ 0 < m ∧
    n*(qrate-delta) ≤ Real.logb 2 k ∧ Real.logb 2 m ≤ n*(erate+delta) ∧
    ∃ Enc : Superop (Fin k × Fin m) (Fin n → A), IsChannel Enc ∧
    ∃ Dec : Superop (Fin m × (Fin n → B)) (Fin k), IsChannel Dec ∧
      traceNorm (assistedOutput Enc (piSuperop (fun _ : Fin n => Nch)) Dec (epr k) - epr k) ≤ eps

/-- Channel action on the chosen pure input, retaining feedback E (pp.4,13). -/
def channelSource {R A B E : Type*} [Fintype A]
    (N : Matrix (B × E) A ℂ) (psi : EuclideanSpace ℂ (R × A)) :
    EuclideanSpace ℂ (R × (B × E)) :=
  WithLp.toLp 2 fun i => ∑ a, N i.2 a * psi (i.1,a)

/-- Actual feedback reverse-Shannon evolution: Alice encodes her source and EPR
half into E and Q, sends Q, and Bob decodes Q with his EPR half (pp.11–12,14). -/
def reverseOutput {R A B E : Type*} {m q : ℕ}
    (Enc : Superop (A × Fin m) (E × Fin q))
    (Dec : Superop (Fin q × Fin m) B) (M : Matrix (R × A) (R × A) ℂ) :=
  idTensorSuperop (fun Z => idTensorSuperop Dec (associate (first Enc Z))) (assistedInput m M)

/-- A source-relative feedback-channel simulation code; E stays at Alice and B
is delivered to Bob, with complete RBE correlation tested (pp.11–12,14). -/
def ReverseCode {R A B E : Type*} [Fintype R] [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq R] [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (N : Matrix (B × E) A ℂ) (psi : EuclideanSpace ℂ (R × A))
    (n : ℕ) (qrate erate eps delta : ℝ) : Prop :=
  let input : Matrix ((Fin n → R) × (Fin n → A)) ((Fin n → R) × (Fin n → A)) ℂ :=
    fun i j => ∏ t, pureDensity psi (i.1 t,i.2 t) (j.1 t,j.2 t)
  let target := idTensorSuperop flip (sourceCopies n (pureDensity (channelSource N psi)))
  ∃ q m : ℕ, 0 < q ∧ 0 < m ∧
    Real.logb 2 q ≤ n*(qrate+delta) ∧ Real.logb 2 m ≤ n*(erate+delta) ∧
    ∃ Enc : Superop ((Fin n → A) × Fin m) ((Fin n → E) × Fin q), IsChannel Enc ∧
    ∃ Dec : Superop (Fin q × Fin m) (Fin n → B), IsChannel Dec ∧
      traceNorm (reverseOutput Enc Dec input - target) ≤ eps

/-- A fully quantum distributed-compression block code: independent CPTP encoders,
then Charlie's CPTP decoder, tested by pure-state overlap (p.14, Eq.(36)). -/
def CompressionCode {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) (n : ℕ)
    (qa qb eps : ℝ) : Prop :=
  ∃ ca cb : ℕ, 0 < ca ∧ 0 < cb ∧
    Real.logb 2 ca ≤ n*qa ∧ Real.logb 2 cb ≤ n*qb ∧
    ∃ EA : Superop (Fin n → A) (Fin ca), IsChannel EA ∧
    ∃ EB : Superop (Fin n → B) (Fin cb), IsChannel EB ∧
    ∃ D : Superop (Fin ca × Fin cb) ((Fin n → A) × (Fin n → B)), IsChannel D ∧
      1-eps ≤ ((sourceCopies n M) * idTensorSuperop (D ∘ both EA EB) (sourceCopies n M)).trace.re

/-- Achievable nonnegative rates, with all sufficiently large integer blocks (p.14).
No slack is built into this set; SW is its Euclidean closure, as printed. -/
def compressionAchievable {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ ∀ eps > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
    CompressionCode M n q.1 q.2 eps}

/-- SW(phi), the closure of achievable nonnegative distributed rates (p.14). -/
def compressionRegion {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) : Set (ℝ × ℝ) :=
  closure (compressionAchievable M)

/-- Entropic half-space region; the subtraction appears once in the sum bound
(pp.15,18, Eqs.(38),(51),(52)). -/
def rateRegion {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    (M : Matrix (R × (A × B)) (R × (A × B)) ℂ) (saving : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ mutualInformation (marginalRA M)/2 ≤ q.1 ∧
    mutualInformation (marginalRB M)/2 ≤ q.2 ∧ quasiMutual (traceLeft M)/2-saving ≤ q.1+q.2}

/-- Conditional mutualInformation information I(A;B|E), state ordered (A,B),E (p.18). -/
def conditionalMutual {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (M : Matrix ((A × B) × E) ((A × B) × E) ℂ) : ℝ :=
  let AE : Matrix (A × E) (A × E) ℂ :=
    fun i j => ∑ b, M ((i.1,b),i.2) ((j.1,b),j.2)
  let BE : Matrix (B × E) (B × E) ℂ :=
    fun i j => ∑ a, M ((a,i.1),i.2) ((a,j.1),j.2)
  vnEntropy AE + vnEntropy BE - vnEntropy (traceLeft M) - vnEntropy M

/-- Squashed entanglement: infimum of half the conditional mutualInformation information
across every finite nonempty extension dimension, without a cap (p.18).
For density inputs the set is nonempty (trivial extension) and bounded below by 0.
For invalid inputs this total definition may return 0; no theorem uses such inputs. -/
def squashed {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {x : ℝ | ∃ e : ℕ, 0 < e ∧
    ∃ S : Matrix ((A × B) × Fin e) ((A × B) × Fin e) ℂ,
      IsDensityMatrix S ∧ traceRight S = M ∧ x = conditionalMutual S / 2}

/-- No-communication local distillation at rate D, using actual local channels and
normalized EPR output, with no side messages or assistance (p.18). -/
def LocallyDistillable {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (M : Matrix (A × B) (A × B) ℂ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
    ∃ l : ℕ, 0 < l ∧ n*(D-delta) ≤ Real.logb 2 l ∧
    ∃ EA : Superop (Fin n → A) (Fin l), IsChannel EA ∧
    ∃ EB : Superop (Fin n → B) (Fin l), IsChannel EB ∧
      traceNorm (both EA EB (bipartiteBlock n M) - epr l) ≤ eps

/-- D0 is the supremum of operational local-only rates, not LOCC distillable
entanglement (p.18). For density inputs the set contains 0 and is bounded above
by the smaller marginal entropy. No theorem uses the junk value on invalid inputs. -/
def localDistillable {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (M : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {D : ℝ | LocallyDistillable M D}

/-- A projective Clifford representative in the specified two qubit factors;
scalar phases do not affect the output density matrices (p.19). -/
def cliffordOnFactors (m1 m2 : ℕ) (g : Clifford.ProjectiveGroup (m1+m2)) :
    Matrix (Fin (2^m1*2^m2)) (Fin (2^m1*2^m2)) ℂ :=
  let e : Fin (2^m1*2^m2) ≃ Qubits (m1+m2) :=
    finProdFinEquiv.symm.trans
      (((bitsEquivFin m1).symm.prodCongr (bitsEquivFin m2).symm).trans
        (qubitsAppendEquiv m1 m2).symm)
  fun i j => (Clifford.representative g).val.val (e i) (e j)

/-- Two-copy conjugation; scalar phases cancel exactly (p.19, Eq.(53)). -/
def twoCopy {X : Type*} [Fintype X] (U : Matrix X X ℂ)
    (M : Matrix (X × X) (X × X) ℂ) : Matrix (X × X) (X × X) ℂ :=
  let T := Matrix.kronecker U U
  T * M * Tᴴ

/-- The two equal pure pairs of Section XII, with Alice's registers kept in fixed
left/right order. If reverse=true, Bob and Rebecca exchange roles (pp.20–21). -/
def pairedSource {X Y : Type*} (psi : EuclideanSpace ℂ (X × Y)) (reverse : Bool) :
    EuclideanSpace ℂ (Y × ((X × X) × Y)) :=
  WithLp.toLp 2 fun i => if reverse then psi (i.2.1.1,i.2.2) * psi (i.2.1.2,i.1)
    else psi (i.2.1.1,i.1) * psi (i.2.1.2,i.2.2)

/-- One fixed sender encoder works for a specified recipient if a local decoder
can recover the joint FQSW product target (pp.20–21). -/
def RecipientGood {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (psi : EuclideanSpace ℂ (X × Y))
    (n l q : ℕ) (Enc : Superop (Fin n → X × X) (Fin l × Fin q)) (eps : ℝ) : Prop :=
  ∀ reverse : Bool, ∃ Dec : Superop (Fin q × (Fin n → Y))
      (Fin l × ((Fin n → X × X) × (Fin n → Y))), IsChannel Dec ∧
    traceNorm (motherOutput Enc Dec (sourceCopies n (pureDensity (pairedSource psi reverse))) -
      motherTarget l (sourceCopies n (pureDensity (pairedSource psi reverse)))) ≤ eps

/-- Haar randomization after a fixed local compression, with retained L and sent Q
identified in that order (pp.5,20–21). -/
def randomizedEncoder {A : Type*} [Fintype A] (l q : ℕ)
    (S : Superop A (Fin (l*q))) (U : Matrix.unitaryGroup (Fin (l*q)) ℂ) :
    Superop A (Fin l × Fin q) :=
  fun M i j => conjSuperop (U : Matrix _ _ ℂ) (S M)
    (finProdFinEquiv i) (finProdFinEquiv j)

/-- Tensoring identities on off-diagonal reference blocks really preserves them (p.2). -/
example {R X : Type*} (M : Matrix (R × X) (R × X) ℂ) :
    idTensorSuperop (fun Z : Matrix X X ℂ => Z) M = M := rfl

/-- A separable product's marginal convention is pinned by the literal sourceCopies formula (p.14). -/
example {A B : Type*} (M : Matrix (A × B) (A × B) ℂ) (i j : (Fin 1 → A) × (Fin 1 → B)) :
    bipartiteBlock 1 M i j = M (i.1 0,i.2 0) (j.1 0,j.2 0) := by
  simp [bipartiteBlock]

/-- A spectral decomposition of a density matrix: normalized nonnegative eigenvalues
and an orthonormal eigenbasis (Appendix A, p.22). Zero weights are permitted. -/
structure Spectrum (X : Type*) [Fintype X] [DecidableEq X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1
  basis : Matrix.unitaryGroup X ℂ

/-- Density matrix determined by its spectral data, not an unrelated state (p.22). -/
def Spectrum.density {X : Type*} [Fintype X] [DecidableEq X] (D : Spectrum X) : Matrix X X ℂ :=
  conjSuperop (D.basis : Matrix X X ℂ) (Matrix.diagonal fun x => (D.weight x : ℂ))

/-- Empirical count in a realized sequence, including length zero (p.21). -/
def count {X : Type*} [DecidableEq X] {n : ℕ} (z : Fin n → X) (x : X) : ℕ :=
  (Finset.univ.filter fun t => z t = x).card

/-- Frequency typicality on positive spectral support (pp.21–22).
The support clause excludes the kernel, whose original product probability is zero. -/
def Typical {X : Type*} [Fintype X] [DecidableEq X] (D : Spectrum X)
    (n : ℕ) (tau : ℝ) (z : Fin n → X) : Prop :=
  (∀ t, 0 < D.weight (z t)) ∧ ∀ x, |(count z x : ℝ)/(n : ℝ)-D.weight x| ≤ tau

/-- Spectral typical projector, zero on the kernel and re-embedded in the full
n-copy ambient register (p.22, following Eq.(A5)). -/
def typicalProjector {X : Type*} [Fintype X] [DecidableEq X] (D : Spectrum X)
    (n : ℕ) (tau : ℝ) : Matrix (Fin n → X) (Fin n → X) ℂ :=
  fun i j => ∑ z ∈ Finset.univ.filter (Typical D n tau),
    (∏ t, (D.basis : Matrix X X ℂ) (i t) (z t)) *
      conj (∏ t, (D.basis : Matrix X X ℂ) (j t) (z t))

/-- Projector for the actual type of a realized sequence, never an unrealizable
real probability vector (pp.21–22). -/
def spectralTypeProjector {X : Type*} [Fintype X] [DecidableEq X] (D : Spectrum X)
    {n : ℕ} (z : Fin n → X) : Matrix (Fin n → X) (Fin n → X) ℂ :=
  fun i j => ∑ w ∈ Finset.univ.filter (fun w : Fin n → X => ∀ x, count w x = count z x),
    (∏ t, (D.basis : Matrix X X ℂ) (i t) (w t)) *
      conj (∏ t, (D.basis : Matrix X X ℂ) (j t) (w t))

/-- Copies regrouped as R^n,(A^n,B^n) at vector level (pp.12,23). -/
def blockVector {R A B : Type*} (n : ℕ) (phi : EuclideanSpace ℂ (R × (A × B))) :
    EuclideanSpace ℂ ((Fin n → R) × ((Fin n → A) × (Fin n → B))) :=
  WithLp.toLp 2 fun i => ∏ t, phi (i.1 t,(i.2.1 t,i.2.2 t))

/-- Normalized projected vector (p.23). At zero success the total value is zero;
all uses below explicitly assert positive success before its norm/overlap bounds. -/
def normalizeProjection {X : Type*} [Fintype X]
    (P : Matrix X X ℂ) (v : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  ((‖act P v‖)⁻¹ : ℂ) • act P v

/-- Extend Alice's projector by identity on R and B (pp.12,23). -/
def onAlice {R A B : Type*} [DecidableEq R] [DecidableEq B]
    (PA : Matrix A A ℂ) : Matrix (R × (A × B)) (R × (A × B)) ℂ :=
  Matrix.kronecker 1 (Matrix.kronecker PA 1)

/-- Schumacher project-and-replace channel re-embedded into the original space;
the fallback vector lies in the compressed subspace (p.23). -/
def schumacher {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℂ) (fallback : EuclideanSpace ℂ X) : Superop X X :=
  fun M => P*M*Pᴴ + ((1-P)*M).trace • pureDensity fallback

/-- Rank window with entropy slack in bits (p.12, property iii). -/
def RankWindow {X : Type*} [Fintype X] [DecidableEq X] (n : ℕ) (h delta : ℝ)
    (P : Matrix X X ℂ) : Prop :=
  Real.rpow 2 (n*(h-delta)) ≤ (P.rank : ℝ) ∧
    (P.rank : ℝ) ≤ Real.rpow 2 (n*(h+delta))

/-- Type counts at length zero are all zero, so no natural subtraction is hidden (p.21). -/
example {X : Type*} [DecidableEq X] (z : Fin 0 → X) (x : X) : count z x = 0 := by
  simp [count]

/-- Normalizing an impossible projected branch gives zero; success guards exclude
this branch from the appendix statements (p.23). -/
example {X : Type*} [Fintype X] (v : EuclideanSpace ℂ X) :
    normalizeProjection (0 : Matrix X X ℂ) v = 0 := by
  simp [normalizeProjection, act]

end QAlgorithms.Papers.Independent.Dependency50.P19


