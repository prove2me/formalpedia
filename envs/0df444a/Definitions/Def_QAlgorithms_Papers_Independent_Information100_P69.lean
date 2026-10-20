-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
-- name    : QAlgorithms_Papers_Independent_Information100_P69
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:52:12.165569+00:00
-- url     : https://prove2.me/theorems/64d8cf50-a41e-4dfe-9a39-6dcd0762bc95
-- title:
--   Definitions for A Generalized Stein Lemma for Quantum Channels
-- statement:
--   The objects the formalized statements of *A Generalized Stein Lemma for Quantum Channels* (arXiv:2609.30762) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Sites`: Product basis for n sites; arXiv:2609.30762v1, PDF pp.4–5.
--   - `CP`: CP maps, without trace normalization, via finite Kraus families; PDF pp.4–5.
--   - `CPLe`: Complete-positive order, with the smaller map first; PDF p.4.
--   - `diamond`: Rectangular full diamond norm on complex-linear maps (and differences of CP maps), stabilized by the input dimension; PDF pp.4–5.
--   - `Faithful`: A faithful density matrix, PDF p.4.
--   - `capacity`: Faithful-replacer dimension constant; PDF p.7. Only used with Faithful omega.
--   - `replacer`: Preparation/replacer channel; PDF p.5.
--   - `matrixPower`: n-fold matrix tensor power in the fixed product basis; PDF p.5.
--   - `power`: n-fold channel tensor power, including entangled inputs; PDF pp.5–6.
--   - `BlockFamily`: Block channel alternatives; only positive blocklengths are constrained; PDF p.5. Distinct from the accepted Complexity.Family, which describes circuit families.
--   - `concatenate`: Tensor concatenation in labeled-site order, PDF p.5, F2.
--   - `permute`: Simultaneous relabeling of tensor sites, PDF p.19, F4.
--   - `permuteChannel`: Conjugation of a channel by the same site permutation on input/output, PDF p.19.
--   - `marginal`: Insert the fixed tau in the last input, discard its output, retain site order; PDF p.19.
--   - `CompactConvexChannels`: F1 alone, or its blockwise local version; PDF p.5 and Lemma 5, p.9.
--   - `ConvexBlocks`: Convex CPTP block sets, without compactness or nonemptiness; PDF p.12.
--   - `TensorClosed`: F2 tensor closure for positive blocks; PDF p.5.
--   - `ReplacerWitness`: F3, with the witnessing faithful state explicit; PDF p.5.
--   - `Admissible`: Exactly F1–F3; no symmetry or processing closure; PDF p.5.
--   - `PermutationClosed`: F4 alone; PDF p.19.
--   - `Additional`: F4 and F5, witnessed by one fixed faithful input state; PDF p.19. The last-site formulation is the printed F5; F4 supplies every discarded subset.
--   - `Tester`: A pure, reference-assisted parallel tester. Reference comes first; PDF pp.6–7.
--   - `acceptance`: Target/alternative acceptance of the same tester; PDF p.6.
--   - `worst`: Worst alternative acceptance, optimized after the tester is fixed; PDF p.6.
--   - `beta`: Composite testing optimum, compressed reference isomorphic to the input; PDF pp.6–7. For nonempty CPTP alternatives and 0<eps<1 the feasible set is nonempty, bounded in [0,1].
--   - `simpleBeta`: Single-alternative coefficient, PDF p.7.
--   - `entropy`: Umegaki relative entropy in bits, preserving +infinity on support mismatch; PDF p.4. Uses the accepted extended entropy in nats and converts its units, without toReal.
--   - `channelEntropy`: Stabilized Umegaki channel relative entropy, PDF p.6.
--   - `resourceEntropy`: E_n is computed by minimizing over the specified alternatives; PDF p.6.
--   - `exponent`: Finite-block testing exponent, PDF p.7.
--   - `rate`: Common rate computed as the liminf at tolerance 1/2; PDF pp.12,16. The main theorem proves ordinary convergence, nonnegativity, and the upper bound.
--   - `ExponentialApproximation`: Exponential approximation at all sufficiently large positive lengths, PDF p.7, (5).
--   - `smoothCost`: Optimized CPTP smoothing, jointly over the approximation and free dominator; PDF p.17. Extended infimum of log2 lambda, lambda>=1; never an empty-set real infimum.
--   - `testingTail`: The testing tail h_t from the common tester acceptance pair; PDF p.10.
--   - `dilationMap`: Stinespring channel induced by a prescribed dilation, PDF p.10.
--   - `adjointIdentity`: Hilbert–Schmidt adjoint evaluated on the identity, PDF p.11.
--   - `defect`: Trace defect computed from Q; PDF p.11.
--   - `complete`: Explicit completion, PDF p.11.
--   - `hermitianPart`: Real Hermitian part; PDF p.25.
--   - `choi`: Choi matrix, unnormalized and reference first, PDF p.5, (3).
--   - `ebFamily`: Full rectangular EB family via its separable-positive Choi cone; PDF p.23.
--   - `pptFamily`: Full PPT family, with transposition on the entire output; PDF p.23.
--   - `preservingFamily`: State-preserving family, PDF p.21, (23).
--   - `stateBeta`: State testing coefficient, PDF p.21, (24).
--   - `mioFamily`: Full block MIO family; PDF p.22.
--   - `dioFamily`: Full block DIO family; PDF p.22.
--   - `mixed`: Maximally mixed local state, PDF p.22.
--   - `covariantFamily`: Collective covariance family, PDF p.22.
--   - `canonical`: Canonical purification of the physical input marginal rho; reference marginal rho^T; PDF pp.38–39.
--   - `entropyFunction`: Entropy as a function of the physical marginal and alternative, PDF p.38.
--   - `overhead`: Quantitative overhead; logarithm is base 2, exponent is the real number 2/3; PDF p.19.
--   - `Supported`: A chosen site support, distinct from operator range support, PDF p.29.
--   - `LocalExpansion`: Finite local-support contraction expansion, PDF p.29.
--   - `LocalExpansion.operator`: Operator represented by the finite expansion, PDF p.29.
--   - `LocalExpansion.cost`: Absolute coefficient cost, allowing arbitrary complex coefficients, PDF p.29.
--   - `join`: Ordered concatenation of configurations, PDF pp.29–30.
--   - `weightedDiscard`: Weighted partial trace, using cyclicity on the discarded sites to write the sandwich formula entrywise; PDF p.30, (32). k+m=n retains the surviving site order.
--   - `multiplierCost`: Cost for one supported multiplier, PDF p.32, (36).
--   - `weightedCost`: Total weighted cost, PDF p.32, (36).
--   - `imageProjector`: Product-image projector, sites paired as A tensor C0; PDF p.33.
--   - `correlatedGenerator`: A partition of the labeled sites is represented by fibers of label. Each nonempty fiber independently receives zeta or the faithful product state; empty fibers contribute 1. This generates exactly all states in Example 24 before taking the convex hull; PDF p.24.
--   - `correlatedFamily`: The specified correlated-state free family, lifted to preparation channels with one-dimensional input; PDF p.24.
--   - `zeta`: The state zeta_n in Example 24, PDF p.24.
--   - `SteinConclusion`: The full conclusion of Theorem 2, used by the application in Proposition 20.
--   - `OperationalConclusion`: Full operational conclusion of Theorem 12, including achievability; PDF p.18.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, https://arxiv.org/abs/2609.30762v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Measurement

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Product basis for n sites; arXiv:2609.30762v1, PDF pp.4–5. -/
abbrev Sites (A : Type*) (n : ℕ) := Fin n → A

/-- CP maps, without trace normalization, via finite Kraus families; PDF pp.4–5. -/
def CP {A B : Type*} [Fintype A] [Fintype B] (T : Superop A B) : Prop :=
  ∃ m : ℕ, ∃ K : Fin m → Matrix B A ℂ, ∀ X, T X = krausApply K X

/-- Complete-positive order, with the smaller map first; PDF p.4. -/
def CPLe {A B : Type*} [Fintype A] [Fintype B] (T M : Superop A B) : Prop := CP (M - T)

/-- Rectangular full diamond norm on complex-linear maps (and differences of CP maps),
stabilized by the input dimension; PDF pp.4–5. -/
def diamond {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T : Superop A B) : ℝ :=
  sSup {v | ∃ X : Matrix (A × A) (A × A) ℂ, traceNorm X ≤ 1 ∧
    v = traceNorm (idTensorSuperop (R := A) T X)}

/-- A faithful density matrix, PDF p.4. -/
def Faithful {A : Type*} [Fintype A] (rho : Matrix A A ℂ) : Prop :=
  IsDensityMatrix rho ∧ rho.PosDef

/-- Faithful-replacer dimension constant; PDF p.7. Only used with Faithful omega. -/
def capacity {B : Type*} [Fintype B] [DecidableEq B] (omega : Matrix B B ℂ) : ℝ :=
  Real.logb 2 (Fintype.card B) - Real.logb 2 (minPositiveEigenvalue omega)

/-- Preparation/replacer channel; PDF p.5. -/
def replacer {A B : Type*} [Fintype A] (rho : Matrix B B ℂ) : Superop A B :=
  fun X => X.trace • rho

/-- n-fold matrix tensor power in the fixed product basis; PDF p.5. -/
def matrixPower {A B : Type*} (K : Matrix B A ℂ) (n : ℕ) :
    Matrix (Sites B n) (Sites A n) ℂ := fun x y => ∏ i, K (x i) (y i)

/-- n-fold channel tensor power, including entangled inputs; PDF pp.5–6. -/
def power {A B : Type*} [Fintype A] [DecidableEq A] (N : Superop A B) (n : ℕ) :
    Superop (Sites A n) (Sites B n) := piSuperop (fun _ => N)

/-- Block channel alternatives; only positive blocklengths are constrained; PDF p.5.
Distinct from the accepted Complexity.Family, which describes circuit families. -/
abbrev BlockFamily (A B : Type*) := (n : ℕ) → Set (Superop (Sites A n) (Sites B n))

/-- Tensor concatenation in labeled-site order, PDF p.5, F2. -/
def concatenate {A B : Type*} [Fintype A] [DecidableEq A] {n m : ℕ}
    (T : Superop (Sites A n) (Sites B n)) (M : Superop (Sites A m) (Sites B m)) :
    Superop (Sites A (n+m)) (Sites B (n+m)) :=
  fun X y z => ∑ x, ∑ x', X x x' *
    T (Matrix.single (x ∘ Fin.castAdd m) (x' ∘ Fin.castAdd m) 1)
      (y ∘ Fin.castAdd m) (z ∘ Fin.castAdd m) *
    M (Matrix.single (x ∘ Fin.natAdd n) (x' ∘ Fin.natAdd n) 1)
      (y ∘ Fin.natAdd n) (z ∘ Fin.natAdd n)

/-- Simultaneous relabeling of tensor sites, PDF p.19, F4. -/
def permute {A : Type*} {n : ℕ} (pi : Equiv.Perm (Fin n))
    (X : Matrix (Sites A n) (Sites A n) ℂ) : Matrix (Sites A n) (Sites A n) ℂ :=
  fun x y => X (x ∘ pi) (y ∘ pi)

/-- Conjugation of a channel by the same site permutation on input/output, PDF p.19. -/
def permuteChannel {A B : Type*} {n : ℕ} (pi : Equiv.Perm (Fin n))
    (M : Superop (Sites A n) (Sites B n)) : Superop (Sites A n) (Sites B n) :=
  fun X => permute pi (M (permute pi.symm X))

/-- Insert the fixed tau in the last input, discard its output, retain site order; PDF p.19. -/
def marginal {A B : Type*} [Fintype B] {n : ℕ} (tau : Matrix A A ℂ)
    (M : Superop (Sites A (n+1)) (Sites B (n+1))) : Superop (Sites A n) (Sites B n) :=
  fun X y z => ∑ b : B, M
    (fun u v => X (u ∘ Fin.castSucc) (v ∘ Fin.castSucc) * tau (u (Fin.last n)) (v (Fin.last n)))
    (Fin.snoc y b) (Fin.snoc z b)

/-- F1 alone, or its blockwise local version; PDF p.5 and Lemma 5, p.9. -/
def CompactConvexChannels {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (F : Set (Superop A B)) : Prop :=
  F.Nonempty ∧ IsCompact F ∧ Convex ℝ F ∧ ∀ M ∈ F, IsChannel M

/-- Convex CPTP block sets, without compactness or nonemptiness; PDF p.12. -/
def ConvexBlocks {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] (F : BlockFamily A B) : Prop :=
  ∀ n, 1 ≤ n → Convex ℝ (F n) ∧ ∀ M ∈ F n, IsChannel M

/-- F2 tensor closure for positive blocks; PDF p.5. -/
def TensorClosed {A B : Type*} [Fintype A] [DecidableEq A] (F : BlockFamily A B) : Prop :=
  ∀ n m, 1 ≤ n → 1 ≤ m → ∀ T ∈ F n, ∀ M ∈ F m, concatenate T M ∈ F (n+m)

/-- F3, with the witnessing faithful state explicit; PDF p.5. -/
def ReplacerWitness {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (F : BlockFamily A B) (omega : Matrix B B ℂ) : Prop :=
  Faithful omega ∧ power (replacer (A := A) omega) 1 ∈ F 1

/-- Exactly F1–F3; no symmetry or processing closure; PDF p.5. -/
def Admissible {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (F : BlockFamily A B) (omega : Matrix B B ℂ) : Prop :=
  (∀ n, 1 ≤ n → CompactConvexChannels (F n)) ∧ TensorClosed F ∧ ReplacerWitness F omega

/-- F4 alone; PDF p.19. -/
def PermutationClosed {A B : Type*} (F : BlockFamily A B) : Prop :=
  ∀ n, 1 ≤ n → ∀ pi, ∀ M ∈ F n, permuteChannel pi M ∈ F n

/-- F4 and F5, witnessed by one fixed faithful input state; PDF p.19.
The last-site formulation is the printed F5; F4 supplies every discarded subset. -/
def Additional {A B : Type*} [Fintype A] [Fintype B]
    (F : BlockFamily A B) (tau : Matrix A A ℂ) : Prop :=
  Faithful tau ∧ PermutationClosed F ∧
    ∀ n, 1 ≤ n → ∀ M ∈ F (n+1), marginal tau M ∈ F n

/-- A pure, reference-assisted parallel tester. Reference comes first; PDF pp.6–7. -/
structure Tester (R A B : Type*) [Fintype R] [Fintype A] [Fintype B] [DecidableEq B]
    [DecidableEq R] where
  input : EuclideanSpace ℂ (R × A)
  unit : ‖input‖ = 1
  effect : Matrix (R × B) (R × B) ℂ
  validEffect : IsEffect effect

/-- Target/alternative acceptance of the same tester; PDF p.6. -/
def acceptance {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq B] [DecidableEq R] (t : Tester R A B) (M : Superop A B) : ℝ :=
  effectProb t.effect (idTensorSuperop M (pureDensity t.input))

/-- Worst alternative acceptance, optimized after the tester is fixed; PDF p.6. -/
def worst {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq B] [DecidableEq R] (t : Tester R A B) (F : Set (Superop A B)) : ℝ :=
  sSup {q | ∃ M ∈ F, q = acceptance t M}

/-- Composite testing optimum, compressed reference isomorphic to the input; PDF pp.6–7.
For nonempty CPTP alternatives and 0<eps<1 the feasible set is nonempty, bounded in [0,1]. -/
def beta {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T : Superop A B) (F : Set (Superop A B)) (eps : ℝ) : ℝ :=
  sInf {q | ∃ t : Tester A A B, 1-eps ≤ acceptance t T ∧ q = worst t F}

/-- Single-alternative coefficient, PDF p.7. -/
def simpleBeta {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T M : Superop A B) (eps : ℝ) : ℝ := beta T {M} eps

/-- Umegaki relative entropy in bits, preserving +infinity on support mismatch; PDF p.4.
Uses the accepted extended entropy in nats and converts its units, without toReal. -/
def entropy {I : Type*} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) : ℝ≥0∞ :=
  if hr : IsDensityMatrix rho then
    if hs : IsDensityMatrix sigma then
      QuantumLoss.umegakiEntropy rho sigma hr hs / ENNReal.ofReal (Real.log 2)
    else ⊤
  else ⊤

/-- Stabilized Umegaki channel relative entropy, PDF p.6. -/
def channelEntropy {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T M : Superop A B) : ℝ≥0∞ :=
  ⨆ psi : {v : EuclideanSpace ℂ (A × A) // ‖v‖ = 1},
    entropy (idTensorSuperop T (pureDensity psi.val)) (idTensorSuperop M (pureDensity psi.val))

/-- E_n is computed by minimizing over the specified alternatives; PDF p.6. -/
def resourceEntropy {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T : Superop A B) (F : Set (Superop A B)) : ℝ≥0∞ := ⨅ M : F, channelEntropy T M.val

/-- Finite-block testing exponent, PDF p.7. -/
def exponent {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T : Superop A B) (F : Set (Superop A B)) (eps : ℝ) : ℝ := -Real.logb 2 (beta T F eps)

/-- Common rate computed as the liminf at tolerance 1/2; PDF pp.12,16.
The main theorem proves ordinary convergence, nonnegativity, and the upper bound. -/
def rate {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (F : BlockFamily A B) : ℝ :=
  liminf (fun j : ℕ => exponent (power N (j+1)) (F (j+1)) (1/2) / (j+1)) atTop

/-- Exponential approximation at all sufficiently large positive lengths, PDF p.7, (5). -/
def ExponentialApproximation {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (F : BlockFamily A B) (S : ℝ) : Prop :=
  ∃ K gamma : ℝ, 0 < K ∧ 0 < gamma ∧ ∃ n0 : ℕ, ∀ n, 1 ≤ n → n0 ≤ n →
    ∃ T ∈ F n, ∃ L : Superop (Sites A n) (Sites B n), IsChannel L ∧
      CPLe L ((Real.rpow 2 ((n:ℝ)*S) : ℂ) • T) ∧
      diamond (L - power N n) ≤ K * Real.exp (-gamma*n)

/-- Optimized CPTP smoothing, jointly over the approximation and free dominator; PDF p.17.
Extended infimum of log2 lambda, lambda>=1; never an empty-set real infimum. -/
def smoothCost {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T : Superop A B) (F : Set (Superop A B)) (delta : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ L : Superop A B, IsChannel L ∧ diamond (L-T) ≤ delta ∧
    ∃ M ∈ F, ∃ lam : ℝ, 1 ≤ lam ∧ CPLe L ((lam:ℂ) • M) ∧ v = ENNReal.ofReal (Real.logb 2 lam)}

/-- The testing tail h_t from the common tester acceptance pair; PDF p.10. -/
def testingTail {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T M : Superop A B) (t : ℝ) : ℝ :=
  sSup {x | ∃ tester : Tester A A B, x = acceptance tester T - t * acceptance tester M}

/-- Stinespring channel induced by a prescribed dilation, PDF p.10. -/
def dilationMap {H K E : Type*} [Fintype H] [Fintype E] (V : Matrix (K × E) H ℂ) : Superop H K :=
  fun X => QAlgorithms.traceRight (conjSuperop V X)

/-- Hilbert–Schmidt adjoint evaluated on the identity, PDF p.11. -/
def adjointIdentity {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (Q : Superop A B) : Matrix A A ℂ := fun i j => (Q (Matrix.single j i 1)).trace

/-- Trace defect computed from Q; PDF p.11. -/
def defect {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] (Q : Superop A B) : Matrix A A ℂ :=
  1 - adjointIdentity Q

/-- Explicit completion, PDF p.11. -/
def complete {A B : Type*} [Fintype A] (Q : Superop A B) (D : Matrix A A ℂ)
    (omega : Matrix B B ℂ) : Superop A B := fun X => Q X + (D*X).trace • omega

/-- Real Hermitian part; PDF p.25. -/
def hermitianPart {A : Type*} (X : Matrix A A ℂ) : Matrix A A ℂ := (1/2:ℂ) • (X+X.conjTranspose)

/-- Choi matrix, unnormalized and reference first, PDF p.5, (3). -/
def choi {A B : Type*} [DecidableEq A] (M : Superop A B) : Matrix (A × B) (A × B) ℂ :=
  fun x y => M (Matrix.single x.1 y.1 1) x.2 y.2

/-- Full rectangular EB family via its separable-positive Choi cone; PDF p.23. -/
def ebFamily {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] : BlockFamily A B :=
  fun n => {M | IsChannel M ∧ Entanglement.IsSeparablePositive (choi M)}

/-- Full PPT family, with transposition on the entire output; PDF p.23. -/
def pptFamily {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] : BlockFamily A B :=
  fun n => {M | IsChannel M ∧ Matrix.PosSemidef (fun (x y : Sites A n × Sites B n) => choi M (x.1,y.2) (y.1,x.2))}

/-- State-preserving family, PDF p.21, (23). -/
def preservingFamily {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (tau : Matrix A A ℂ) (omega : Matrix B B ℂ) : BlockFamily A B :=
  fun n => {M | IsChannel M ∧ M (matrixPower tau n) = matrixPower omega n}

/-- State testing coefficient, PDF p.21, (24). -/
def stateBeta {B : Type*} [Fintype B] [DecidableEq B] (rho sigma : Matrix B B ℂ) (eps : ℝ) : ℝ :=
  sInf {x | ∃ Q : Matrix B B ℂ, IsEffect Q ∧ 1-eps ≤ effectProb Q rho ∧ x = effectProb Q sigma}

/-- Full block MIO family; PDF p.22. -/
def mioFamily {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] : BlockFamily A B :=
  fun n => {M | IsChannel M ∧ ∀ X, Matrix.diagonal (Matrix.diag (M (Matrix.diagonal (Matrix.diag X)))) =
    M (Matrix.diagonal (Matrix.diag X))}

/-- Full block DIO family; PDF p.22. -/
def dioFamily {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] : BlockFamily A B :=
  fun n => {M | IsChannel M ∧ ∀ X, Matrix.diagonal (Matrix.diag (M X)) = M (Matrix.diagonal (Matrix.diag X))}

/-- Maximally mixed local state, PDF p.22. -/
def mixed {A : Type*} [Fintype A] [DecidableEq A] : Matrix A A ℂ := ((Fintype.card A:ℂ)⁻¹) • 1

/-- Collective covariance family, PDF p.22. -/
def covariantFamily {G A B : Type*} [Group G] [Fintype A] [Fintype B] [DecidableEq A]
    (UA : G → Matrix A A ℂ) (UB : G → Matrix B B ℂ) : BlockFamily A B :=
  fun n => {M | IsChannel M ∧ ∀ g X,
    M (conjSuperop (matrixPower (UA g) n) X) = conjSuperop (matrixPower (UB g) n) (M X)}

/-- Canonical purification of the physical input marginal rho; reference marginal rho^T;
PDF pp.38–39. -/
def canonical {A : Type*} [Fintype A] [DecidableEq A] (rho : Matrix A A ℂ) : EuclideanSpace ℂ (A × A) :=
  WithLp.toLp 2 (fun x => cfc Real.sqrt rho x.2 x.1)

/-- Entropy as a function of the physical marginal and alternative, PDF p.38. -/
def entropyFunction {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (T M : Superop A B) (rho : Matrix A A ℂ) : ℝ≥0∞ :=
  entropy (idTensorSuperop T (pureDensity (canonical rho)))
    (idTensorSuperop M (pureDensity (canonical rho)))

/-- Quantitative overhead; logarithm is base 2, exponent is the real number 2/3; PDF p.19. -/
def overhead (K : ℝ) (n : ℕ) (delta : ℝ) : ℝ :=
  K * (n:ℝ) ^ (2/3:ℝ) * Real.logb 2 (((n:ℝ)+1)/delta)

/-- Sanity: the empty tensor power is the scalar identity, PDF p.4 convention. -/
example {A B : Type*} (K : Matrix B A ℂ) (x : Sites B 0) (y : Sites A 0) :
    matrixPower K 0 x y = 1 := by simp [matrixPower]

/-- Sanity: channel preparation acts by trace, PDF p.5. -/
example {A B : Type*} [Fintype A] (rho : Matrix B B ℂ) (X : Matrix A A ℂ) :
    replacer rho X = X.trace • rho := rfl

/-- Sanity: zero operator trace defect really is identity, PDF p.11. -/
example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] :
    defect (0 : Superop A B) = 1 := by
  have hz : adjointIdentity (0 : Superop A B) = 0 := by
    ext i j
    simp [adjointIdentity, Matrix.trace]
  rw [defect, hz, sub_zero]

/-- Sanity: canonical purification of identity has the expected reference-first entries. -/
example {A : Type*} [Fintype A] [DecidableEq A] (i j : A) :
    canonical (1 : Matrix A A ℂ) (i,j) = (1 : Matrix A A ℂ) j i := by
  simp [canonical, cfc_one]

/-- A chosen site support, distinct from operator range support, PDF p.29. -/
def Supported {D : Type*} [DecidableEq D] {n : ℕ}
    (S : Finset (Fin n)) (F : Matrix (Sites D n) (Sites D n) ℂ) : Prop :=
  ∃ G : Matrix (S → D) (S → D) ℂ, ∀ x y,
    F x y = G (fun i => x i.val) (fun i => y i.val) *
      ∏ i ∈ Finset.univ \ S, if x i=y i then (1:ℂ) else 0

/-- Finite local-support contraction expansion, PDF p.29. -/
structure LocalExpansion (D : Type*) [Fintype D] [DecidableEq D] (n : ℕ) where
  count : ℕ
  coefficient : Fin count → ℂ
  term : Fin count → Matrix (Sites D n) (Sites D n) ℂ
  support : Fin count → Finset (Fin n)
  supported : ∀ i, Supported (support i) (term i)
  contraction : ∀ i, specNorm (term i) ≤ 1

/-- Operator represented by the finite expansion, PDF p.29. -/
def LocalExpansion.operator {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}
    (P : LocalExpansion D n) : Matrix (Sites D n) (Sites D n) ℂ :=
  ∑ i, P.coefficient i • P.term i

/-- Absolute coefficient cost, allowing arbitrary complex coefficients, PDF p.29. -/
def LocalExpansion.cost {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}
    (P : LocalExpansion D n) : ℝ := ∑ i, ‖P.coefficient i‖

/-- Ordered concatenation of configurations, PDF pp.29–30. -/
def join {D : Type*} {k m : ℕ} (x : Sites D k) (u : Sites D m) : Sites D (k+m) :=
  Fin.addCases x u

/-- Weighted partial trace, using cyclicity on the discarded sites to write the
sandwich formula entrywise; PDF p.30, (32). k+m=n retains the surviving site order. -/
def weightedDiscard {D : Type*} [Fintype D] {n k m : ℕ} (h : k+m=n)
    (tau : Matrix D D ℂ) (W : Matrix (Sites D n) (Sites D n) ℂ) : Matrix (Sites D k) (Sites D k) ℂ :=
  fun x y => ∑ u : Sites D m, ∑ v : Sites D m,
    W ((join x u) ∘ Fin.cast h.symm) ((join y v) ∘ Fin.cast h.symm) * matrixPower tau m v u

/-- Cost for one supported multiplier, PDF p.32, (36). -/
def multiplierCost (a d : ℕ) (t w : ℝ) (r : ℕ) : ℝ :=
  ((a:ℝ)*d)^r * (((a:ℝ)*t)*((d:ℝ)*w))^(-(r:ℝ)/2)

/-- Total weighted cost, PDF p.32, (36). -/
def weightedCost {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}
    (a : ℕ) (t w : ℝ) (P : LocalExpansion D n) : ℝ :=
  ∑ i, ‖P.coefficient i‖*multiplierCost a (Fintype.card D) t w (P.support i).card

/-- Product-image projector, sites paired as A tensor C0; PDF p.33. -/
def imageProjector {A C : Type*} [DecidableEq A] (zero : EuclideanSpace ℂ C) (k : ℕ) :
    Matrix (Sites (A × C) k) (Sites (A × C) k) ℂ :=
  matrixPower (Matrix.kronecker (1 : Matrix A A ℂ) (pureDensity zero)) k

/-- A partition of the labeled sites is represented by fibers of label. Each nonempty
fiber independently receives zeta or the faithful product state; empty fibers contribute 1.
This generates exactly all states in Example 24 before taking the convex hull; PDF p.24. -/
def correlatedGenerator {D : Type*} (rho omega : Matrix D D ℂ) (c : ℝ) (n : ℕ)
    (label : Fin n → Fin n) (useZeta : Fin n → Bool) : Matrix (Sites D n) (Sites D n) ℂ :=
  fun x y => ∏ l : Fin n,
    let block := Finset.univ.filter (fun i => label i=l)
    if block.Nonempty ∧ useZeta l = true then
      (c:ℂ)*(∏ i ∈ block, rho (x i) (y i))+(1-c:ℂ)*(∏ i ∈ block, omega (x i) (y i))
    else ∏ i ∈ block, omega (x i) (y i)

/-- The specified correlated-state free family, lifted to preparation channels with
one-dimensional input; PDF p.24. -/
def correlatedFamily {D : Type*} (rho omega : Matrix D D ℂ) (c : ℝ) : BlockFamily (Fin 1) D :=
  fun n => convexHull ℝ {M | ∃ label : Fin n → Fin n, ∃ zeta : Fin n → Bool,
    M = replacer (correlatedGenerator rho omega c n label zeta)}

/-- The state zeta_n in Example 24, PDF p.24. -/
def zeta {D : Type*} (rho omega : Matrix D D ℂ) (c : ℝ) (n : ℕ) :
    Matrix (Sites D n) (Sites D n) ℂ :=
  (c:ℂ) • matrixPower rho n+(1-c:ℂ) • matrixPower omega n

/-- Sanity: an uncorrelated fiber choice gives exactly the product state for one site. -/
example {D : Type*} (rho omega : Matrix D D ℂ) (c : ℝ) (x y : Sites D 1) :
    correlatedGenerator rho omega c 1 (fun i => i) (fun _ => false) x y = omega (x 0) (y 0) := by
  simp [correlatedGenerator, Finset.filter_singleton]

/-- Sanity: the zero-length product image projector is scalar identity. -/
example {A C : Type*} [DecidableEq A] (zero : EuclideanSpace ℂ C)
    (x y : Sites (A × C) 0) : imageProjector (A := A) zero 0 x y = 1 := by
  simp [imageProjector, matrixPower]

/-- The full conclusion of Theorem 2, used by the application in Proposition 20. -/
def SteinConclusion {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (F : BlockFamily A B) (omega : Matrix B B ℂ) : Prop :=
  0 ≤ rate N F ∧ rate N F ≤ capacity omega ∧
    Tendsto (fun j : ℕ => resourceEntropy (power N (j+1)) (F (j+1))/(j+1))
      atTop (nhds (ENNReal.ofReal (rate N F))) ∧
    ∀ eps : ℝ, 0 < eps → eps < 1 → Tendsto
      (fun j : ℕ => exponent (power N (j+1)) (F (j+1)) eps/(j+1)) atTop (nhds (rate N F))

/-- Full operational conclusion of Theorem 12, including achievability; PDF p.18. -/
def OperationalConclusion {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (F : BlockFamily A B) : Prop :=
  (∃ t : (n : ℕ) → Tester (Sites A n) (Sites A n) (Sites B n),
      (∀ n, 1 ≤ n → 0 < worst (t n) (F n)) ∧
      Tendsto (fun j : ℕ => acceptance (t (j+1)) (power N (j+1))) atTop (nhds 1) ∧
      Tendsto (fun j : ℕ => -Real.logb 2 (worst (t (j+1)) (F (j+1)))/(j+1)) atTop (nhds (rate N F))) ∧
    (∀ r : ℝ, rate N F < r → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ n, 1 ≤ n → ∀ d : ℕ, ∀ t : Tester (Fin d) (Sites A n) (Sites B n),
        worst t (F n) ≤ Real.rpow 2 (-(n:ℝ)*r) →
          acceptance t (power N n) ≤ K*Real.rpow 2 (-c*n))

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

end Statements

end QAlgorithms.Papers.Independent.Information100.P69


