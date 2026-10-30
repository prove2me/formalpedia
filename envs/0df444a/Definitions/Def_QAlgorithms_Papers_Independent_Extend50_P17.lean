-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17
-- name    : QAlgorithms_Papers_Independent_Extend50_P17
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:49:41.962259+00:00
-- url     : https://prove2.me/theorems/4d06d6db-d6ac-4181-ae84-deb7b2d3e0af
-- title:
--   Definitions for Multiport based teleportation -- transmission of a large amount of quantum information
-- statement:
--   The objects the formalized statements of *Multiport based teleportation -- transmission of a large amount of quantum information* (arXiv:2008.00856) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MPBTRegister`: PDF pp.2–3: the product computational basis of n d-level particles.
--   - `MPBTPortSelection`: PDF pp.2–3: distinct ordered ports, with reversed input order as in Eq.(27).
--   - `AliceBasis`: PDF p.3: Alice's ports together with the k input/reference systems.
--   - `AliceOp`: PDF p.3: matrices on the actual Alice/input space.
--   - `outcomeCount`: PDF p.2: the number of ordered outcomes; equals k! choose(N,k) when k≤N.
--   - `pairingWord`: PDF pp.8–10, Eq.(27): the product of disjoint swaps, rightmost acting first.
--   - `mpbtWordOperator`: PDF pp.8–10: unnormalized partially transposed permutation word W(a). The crossed second coordinates implement transpose on precisely the last k factors.
--   - `mpbtSignal`: PDF pp.2–3, Eq.(2), and p.8, Eq.(25): normalized signals, of trace one.
--   - `signalSum`: PDF p.4, Eq.(6): sum of normalized signals; not Definition 4's unscaled sum.
--   - `unscaledSum`: PDF p.8, Definition 4: unscaled sum of words R=d^N rho.
--   - `normalizedSum`: PDF p.4, Lemma 1: normalize by the actual trace, without assuming invertibility.
--   - `supportInverseSqrt`: PDF p.4, Eq.(6): spectral inverse square root, zero on the kernel.
--   - `rawSRM`: PDF p.4, Eq.(6): SRM on the support of the signal sum.
--   - `completedSRM`: PDF p.4, support convention: uniformly distribute the kernel projector among outcomes.
--   - `discrimination`: PDF p.4, Eq.(5): discrimination success with equal prior over normalized signals.
--   - `mpbtFidelity`: PDF p.3, Eq.(3): entanglement fidelity for the fixed EPR resource and completed SRM. This is the overlap with k reference EPR pairs, not root or average-state mpbtFidelity.
--   - `binomialBound`: PDF p.4, Eq.(9): the stronger binomial-ratio lower bound.
--   - `powerBound`: PDF p.4, Eq.(9): the weaker power lower bound. Subtractions are in the reals.
--   - `packagedLower`: PDF pp.4–5, Eq.(12): the displayed packaged lower estimate, not its actual fidelity.
--   - `packagedFidelity`: PDF pp.4–5, Eq.(11): actual fixed-resource SRM packaged fidelity.
--   - `packagedOptimalFidelity`: PDF pp.4–5, Eq.(13): exact optimal packaged qubit fidelity, with equal packages.
--   - `accumulated`: PDF p.9, Notation 5: accumulate L_s ... L_1 on port indices. At step s the swap is (a_s, accumulated(b_s)); equal endpoints give identity.
--   - `collisionCount`: PDF p.10, Eq.(38): sum of the Kronecker deltas in the contraction factor.
--   - `portAction`: PDF pp.8–10: untransposed port permutation, with the last k factors fixed.
--   - `eprResource`: PDF pp.2–3: the N shared normalized EPR pairs, in Alice/Bob product coordinates.
--   - `mpbtSelectedPorts`: PDF pp.2–3: ordered output selection matching the reversed list in Eq.(27).
--   - `mpbtBranchChannel`: PDF pp.2–3, Eq.(1): a branch of the physical teleportation channel. Alice is traced out; Bob traces unselected ports and only reorders mpbtSelectedPorts ports. The bilinear coordinate contraction uses the effect E, so it agrees with the sqrt(E) instrument after Alice's register is discarded.
--   - `Conclusive`: PDF p.3, Eq.(4): physical conclusive schemes. The failure effect is I-sum(E_i). Every mpbtBranchChannel is p_i times the identity channel on ALL matrix units, hence also on arbitrary reference-entangled inputs. The explicit probability interval is redundant physically and keeps every optimization set bounded on bad parameters.
--   - `mpbtSuccessProbability`: PDF p.3: optimal conclusive success for the fixed maximally entangled resource. Zero mpbtSuccessProbability is included explicitly; every other feasible value lies in [0,1]. This is an operational optimization, not the scalar formula to be proved.
--   - `optimizedSuccess`: PDF p.6, Eq.(17) context: optimize BOTH shared density matrix and conclusive effects. Mixed resources are allowed; linearity makes this equivalent to optimizing pure resources.
--   - `packagedSuccess`: PDF p.6, Table 3: all independent fixed-resource single-qubit packages must succeed.
--   - `packagedOptimalSuccess`: PDF p.6, Table 3: all independent resource-optimized packages must succeed.
--   - `integerChoose`: PDF p.14, Eq.(67): binomial coefficient zero outside its integer range.
--   - `branchingExpression`: PDF p.14, Eq.(67): binomial-difference expression, with s=m/2-r, j=(m+k)/2-t. The difference is in R; negative integer arguments are NOT truncated to zero indices.
--   - `lowerAdded`: PDF pp.13–14: count lower-row additions among the first q boxes of a path word.
--   - `branchingPaths`: PDF pp.13–14: count ACTUAL box-addition paths between two-row shapes. True adds to the lower row, false to the upper; every intermediate shape is valid.
--   - `qubitFidelityExpression`: PDF p.14, Eq.(68): the canonical qubit fidelity expression, indexed by lower-row lengths. The outer r is a shape of N-k and inner t a shape of N, so both spin parities are fixed.
--   - `qubitSuccessExpression`: PDF p.6, Eq.(14), and p.14, Eq.(71): correct weighted qubit success formula.
--   - `gaussianLimit`: PDF pp.6,16, Eqs.(15),(76),(77): the Gaussian limiting function, with x squared.
--   - `elementary`: PDF p.12: corrected ELEMENTARY symmetric polynomial in x_0,...,x_(k-1). The printed weak inequality in Eq.(55) would instead include squares and is incompatible with (56).
--   - `boundVariables`: PDF p.12, Eqs.(56)–(57): x_s=1/(d²+N-s-1), zero-based consistently.
--   - `symmetricBound`: PDF p.12, Eq.(56): the elementary-symmetric expansion of the lower bound.
--   - `PackageSchedule`: PDF pp.5–6: physical integer schedules for equal packages, N→∞.
--   - `Scales`: PDF pp.5–6: integer interpretation of k~a N^alpha.
--   - `RegimeLimit`: PDF pp.5–6: the three regimes of a packaged protocol's critical exponent.
--   - `examplePortA`: PDF p.12, Example 14, Eqs.(58)–(59): a=(3,4), b=(4,3) in one-based notation.
--   - `examplePortB`: PDF p.12, Example 14: reversed lists have the same selected port set.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, https://arxiv.org/abs/2008.00856v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Defs_Information

/-!
Statements from arXiv:2008.00856v3. Paper-local definitions have complete bodies.
Coordinates use Alice's N ports followed by k input/reference factors. Source
lists a_1,...,a_k are zero-based embeddings; a_1 is paired with the last factor.
The two inconsistent finite-size Gaussian sandwiches are deferred in HARD.md.
Compilation is pending the authorized mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory
open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF pp.2–3: the product computational basis of n d-level particles. -/
abbrev MPBTRegister (d n : ℕ) := Fin n → Fin d

/-- PDF pp.2–3: distinct ordered ports, with reversed input order as in Eq.(27). -/
abbrev MPBTPortSelection (N k : ℕ) := Fin k ↪ Fin N

/-- PDF p.3: Alice's ports together with the k input/reference systems. -/
abbrev AliceBasis (d N k : ℕ) := MPBTRegister d N × MPBTRegister d k

/-- PDF p.3: matrices on the actual Alice/input space. -/
abbrev AliceOp (d N k : ℕ) := Matrix (AliceBasis d N k) (AliceBasis d N k) ℂ

/-- PDF p.2: the number of ordered outcomes; equals k! choose(N,k) when k≤N. -/
def outcomeCount (N k : ℕ) : ℕ := Fintype.card (MPBTPortSelection N k)

/-- PDF pp.8–10, Eq.(27): the product of disjoint swaps, rightmost acting first. -/
def pairingWord {N k : ℕ} (a : MPBTPortSelection N k) : Equiv.Perm (Fin (N + k)) :=
  (List.ofFn fun i : Fin k =>
    Equiv.swap (Fin.castAdd k (a i)) (Fin.natAdd N (Fin.rev i))).prod

/-- PDF pp.8–10: unnormalized partially transposed permutation word W(a).
The crossed second coordinates implement transpose on precisely the last k factors. -/
def mpbtWordOperator (d N k : ℕ) (a : MPBTPortSelection N k) : AliceOp d N k :=
  fun x y => QAlgorithms.Schur.tensorPermutation d (N + k) (pairingWord a)
    (Fin.append x.1 y.2) (Fin.append y.1 x.2)

/-- PDF pp.2–3, Eq.(2), and p.8, Eq.(25): normalized signals, of trace one. -/
def mpbtSignal (d N k : ℕ) (a : MPBTPortSelection N k) : AliceOp d N k :=
  ((d : ℂ) ^ N)⁻¹ • mpbtWordOperator d N k a

/-- PDF p.4, Eq.(6): sum of normalized signals; not Definition 4's unscaled sum. -/
def signalSum (d N k : ℕ) : AliceOp d N k := ∑ a, mpbtSignal d N k a

/-- PDF p.8, Definition 4: unscaled sum of words R=d^N rho. -/
def unscaledSum (d N k : ℕ) : AliceOp d N k := ∑ a, mpbtWordOperator d N k a

/-- PDF p.4, Lemma 1: normalize by the actual trace, without assuming invertibility. -/
def normalizedSum (d N k : ℕ) : AliceOp d N k :=
  (signalSum d N k).trace⁻¹ • signalSum d N k

/-- PDF p.4, Eq.(6): spectral inverse square root, zero on the kernel. -/
def supportInverseSqrt (d N k : ℕ) : AliceOp d N k :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (signalSum d N k)

/-- PDF p.4, Eq.(6): SRM on the support of the signal sum. -/
def rawSRM (d N k : ℕ) (a : MPBTPortSelection N k) : AliceOp d N k :=
  supportInverseSqrt d N k * mpbtSignal d N k a * supportInverseSqrt d N k

/-- PDF p.4, support convention: uniformly distribute the kernel projector among outcomes. -/
def completedSRM (d N k : ℕ) (a : MPBTPortSelection N k) : AliceOp d N k :=
  rawSRM d N k a + ((outcomeCount N k : ℂ)⁻¹) • (1 - ∑ b, rawSRM d N k b)

/-- PDF p.4, Eq.(5): discrimination success with equal prior over normalized signals. -/
def discrimination (d N k : ℕ) : ℝ :=
  (outcomeCount N k : ℝ)⁻¹ *
    ∑ a, (completedSRM d N k a * mpbtSignal d N k a).trace.re

/-- PDF p.3, Eq.(3): entanglement fidelity for the fixed EPR resource and completed SRM.
This is the overlap with k reference EPR pairs, not root or average-state mpbtFidelity. -/
def mpbtFidelity (d N k : ℕ) : ℝ :=
  ((d : ℝ) ^ (2 * k))⁻¹ *
    ∑ a, (completedSRM d N k a * mpbtSignal d N k a).trace.re

/-- PDF p.4, Eq.(9): the stronger binomial-ratio lower bound. -/
def binomialBound (d N k : ℕ) : ℝ :=
  (N.choose k : ℝ) / ((d ^ 2 + N - 1).choose k : ℝ)

/-- PDF p.4, Eq.(9): the weaker power lower bound. Subtractions are in the reals. -/
def powerBound (d N k : ℕ) : ℝ :=
  (1 - ((d : ℝ)^2 - 1) / ((d : ℝ)^2 + N - k)) ^ k

/-- PDF pp.4–5, Eq.(12): the displayed packaged lower estimate, not its actual fidelity. -/
def packagedLower (N k : ℕ) : ℝ := (1 - 3 * (k : ℝ) / (4 * N)) ^ k

/-- PDF pp.4–5, Eq.(11): actual fixed-resource SRM packaged fidelity. -/
def packagedFidelity (N k : ℕ) : ℝ := mpbtFidelity 2 (N / k) 1 ^ k

/-- PDF pp.4–5, Eq.(13): exact optimal packaged qubit fidelity, with equal packages. -/
def packagedOptimalFidelity (N k : ℕ) : ℝ :=
  Real.cos (Real.pi / ((N / k : ℕ) + 2 : ℝ)) ^ (2 * k)

/-- PDF p.9, Notation 5: accumulate L_s ... L_1 on port indices.
At step s the swap is (a_s, accumulated(b_s)); equal endpoints give identity. -/
def accumulated {N k : ℕ} (a b : MPBTPortSelection N k) (s : ℕ) : Equiv.Perm (Fin N) :=
  ((List.ofFn fun i : Fin k => (a i, b i)).take s).foldl
    (fun p ab => Equiv.swap ab.1 (p ab.2) * p) 1

/-- PDF p.10, Eq.(38): sum of the Kronecker deltas in the contraction factor. -/
def collisionCount {N k : ℕ} (a b : MPBTPortSelection N k) : ℕ :=
  ∑ i : Fin k, if a i = accumulated a b i.val (b i) then 1 else 0

/-- PDF pp.8–10: untransposed port permutation, with the last k factors fixed. -/
def portAction (d N k : ℕ) (p : Equiv.Perm (Fin N)) : AliceOp d N k :=
  fun y x => if y.1 = x.1 ∘ p.symm ∧ y.2 = x.2 then 1 else 0

/-- PDF pp.2–3: the N shared normalized EPR pairs, in Alice/Bob product coordinates. -/
def eprResource (d N : ℕ) :
    Matrix (MPBTRegister d N × MPBTRegister d N) (MPBTRegister d N × MPBTRegister d N) ℂ :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then ((d : ℂ)^N)⁻¹ else 0

/-- PDF pp.2–3: ordered output selection matching the reversed list in Eq.(27). -/
def mpbtSelectedPorts {d N k : ℕ} (a : MPBTPortSelection N k) (b : MPBTRegister d N) : MPBTRegister d k :=
  fun i => b (a (Fin.rev i))

/-- PDF pp.2–3, Eq.(1): a branch of the physical teleportation channel.
Alice is traced out; Bob traces unselected ports and only reorders mpbtSelectedPorts ports.
The bilinear coordinate contraction uses the effect E, so it agrees with the
sqrt(E) instrument after Alice's register is discarded. -/
def mpbtBranchChannel {d N k : ℕ}
    (omega : Matrix (MPBTRegister d N × MPBTRegister d N) (MPBTRegister d N × MPBTRegister d N) ℂ)
    (a : MPBTPortSelection N k) (E : AliceOp d N k)
    (X : Matrix (MPBTRegister d k) (MPBTRegister d k) ℂ) :
    Matrix (MPBTRegister d k) (MPBTRegister d k) ℂ :=
  fun u v => ∑ b : MPBTRegister d N, ∑ bp : MPBTRegister d N,
    if mpbtSelectedPorts a b = u ∧ mpbtSelectedPorts a bp = v ∧
      (∀ j : Fin N, j ∉ Set.range a → b j = bp j) then
      ∑ x : MPBTRegister d N, ∑ xp : MPBTRegister d N,
        ∑ c : MPBTRegister d k, ∑ cp : MPBTRegister d k,
          E (xp, cp) (x, c) * omega (x, b) (xp, bp) * X c cp
    else 0

/-- PDF p.3, Eq.(4): physical conclusive schemes. The failure effect is I-sum(E_i).
Every mpbtBranchChannel is p_i times the identity channel on ALL matrix units, hence also
on arbitrary reference-entangled inputs. The explicit probability interval is
redundant physically and keeps every optimization set bounded on bad parameters. -/
def Conclusive {d N k : ℕ}
    (omega : Matrix (MPBTRegister d N × MPBTRegister d N) (MPBTRegister d N × MPBTRegister d N) ℂ)
    (E : MPBTPortSelection N k → AliceOp d N k) (p : MPBTPortSelection N k → ℝ) : Prop :=
  (∀ a, (E a).PosSemidef) ∧ (1 - ∑ a, E a).PosSemidef ∧
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a) ≤ 1 ∧
  ∀ a X, mpbtBranchChannel omega a (E a) X = (p a : ℂ) • X

/-- PDF p.3: optimal conclusive success for the fixed maximally entangled resource.
Zero mpbtSuccessProbability is included explicitly; every other feasible value lies in [0,1].
This is an operational optimization, not the scalar formula to be proved. -/
def mpbtSuccessProbability (d N k : ℕ) : ℝ :=
  sSup (insert 0 {q : ℝ | ∃ (E : MPBTPortSelection N k → AliceOp d N k)
    (p : MPBTPortSelection N k → ℝ), Conclusive (eprResource d N) E p ∧ q = ∑ a, p a})

/-- PDF p.6, Eq.(17) context: optimize BOTH shared density matrix and conclusive effects.
Mixed resources are allowed; linearity makes this equivalent to optimizing pure resources. -/
def optimizedSuccess (d N k : ℕ) : ℝ :=
  sSup (insert 0 {q : ℝ | ∃
    (omega : Matrix (MPBTRegister d N × MPBTRegister d N) (MPBTRegister d N × MPBTRegister d N) ℂ)
    (E : MPBTPortSelection N k → AliceOp d N k) (p : MPBTPortSelection N k → ℝ),
    QAlgorithms.IsDensityMatrix omega ∧ Conclusive omega E p ∧ q = ∑ a, p a})

/-- PDF p.6, Table 3: all independent fixed-resource single-qubit packages must succeed. -/
def packagedSuccess (N k : ℕ) : ℝ := mpbtSuccessProbability 2 (N / k) 1 ^ k

/-- PDF p.6, Table 3: all independent resource-optimized packages must succeed. -/
def packagedOptimalSuccess (N k : ℕ) : ℝ := optimizedSuccess 2 (N / k) 1 ^ k

/-- PDF p.14, Eq.(67): binomial coefficient zero outside its integer range. -/
def integerChoose (k : ℕ) (z : ℤ) : ℝ :=
  if 0 ≤ z then (k.choose z.toNat : ℝ) else 0

/-- PDF p.14, Eq.(67): binomial-difference expression, with s=m/2-r, j=(m+k)/2-t.
The difference is in R; negative integer arguments are NOT truncated to zero indices. -/
def branchingExpression (m k r t : ℕ) : ℝ :=
  integerChoose k ((t : ℤ) - r) - integerChoose k ((m : ℤ) + k - r - t + 1)

/-- PDF pp.13–14: count lower-row additions among the first q boxes of a path word. -/
def lowerAdded {k : ℕ} (w : Fin k → Bool) (q : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin k => i.val < q ∧ w i = true).card

/-- PDF pp.13–14: count ACTUAL box-addition paths between two-row shapes.
True adds to the lower row, false to the upper; every intermediate shape is valid. -/
def branchingPaths (m k r t : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin k → Bool =>
    r + lowerAdded w k = t ∧
    ∀ q ∈ Finset.range (k + 1), 2 * (r + lowerAdded w q) ≤ m + q).card

/-- PDF p.14, Eq.(68): the canonical qubit fidelity expression, indexed by lower-row lengths.
The outer r is a shape of N-k and inner t a shape of N, so both spin parities are fixed. -/
def qubitFidelityExpression (N k : ℕ) : ℝ :=
  ((2 : ℝ) ^ (N + 2 * k))⁻¹ *
    ∑ r ∈ Finset.range ((N - k) / 2 + 1),
      (∑ t ∈ (Finset.range (N / 2 + 1)).filter
          (fun t => r ≤ t ∧ t ≤ r + k ∧ r + t ≤ N),
        branchingExpression (N - k) k r t *
          Real.sqrt (((N - 2 * t + 1 : ℕ) : ℝ)^2 * (N.factorial : ℝ) /
            ((t.factorial : ℝ) * ((N - t + 1).factorial : ℝ)))) ^ 2

/-- PDF p.6, Eq.(14), and p.14, Eq.(71): correct weighted qubit success formula. -/
def qubitSuccessExpression (N k : ℕ) : ℝ :=
  ((2 : ℝ)^N * (N + 1))⁻¹ *
    ∑ r ∈ Finset.range ((N - k) / 2 + 1),
      ((N - k - 2 * r + 1 : ℕ) : ℝ)^2 * ((N + 1).choose r : ℝ)

/-- PDF pp.6,16, Eqs.(15),(76),(77): the Gaussian limiting function, with x squared. -/
def gaussianLimit (a : ℝ) : ℝ :=
  2 * ∫ x in Set.Ioi (0 : ℝ), x^2 / Real.sqrt (2 * Real.pi) *
    Real.exp (-((x + a)^2) / 2)

/-- PDF p.12: corrected ELEMENTARY symmetric polynomial in x_0,...,x_(k-1).
The printed weak inequality in Eq.(55) would instead include squares and is incompatible with (56). -/
def elementary {k : ℕ} (x : Fin k → ℝ) (l : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin k)).powersetCard l, ∏ i ∈ S, x i

/-- PDF p.12, Eqs.(56)–(57): x_s=1/(d²+N-s-1), zero-based consistently. -/
def boundVariables (d N k : ℕ) (s : Fin k) : ℝ :=
  ((d : ℝ)^2 + N - s.val - 1)⁻¹

/-- PDF p.12, Eq.(56): the elementary-symmetric expansion of the lower bound. -/
def symmetricBound (d N k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1), (-1 : ℝ)^l * ((d : ℝ)^2 - 1)^l *
    elementary (boundVariables d N k) l

/-- PDF pp.5–6: physical integer schedules for equal packages, N→∞. -/
def PackageSchedule (N k : ℕ → ℕ) : Prop :=
  Tendsto N atTop atTop ∧ ∀ᶠ t in atTop, 1 ≤ k t ∧ k t ≤ N t ∧ k t ∣ N t

/-- PDF pp.5–6: integer interpretation of k~a N^alpha. -/
def Scales (N k : ℕ → ℕ) (a alpha : ℝ) : Prop :=
  Tendsto (fun t => (k t : ℝ) / (N t : ℝ)^alpha) atTop (nhds a)

/-- PDF pp.5–6: the three regimes of a packaged protocol's critical exponent. -/
def RegimeLimit (N k : ℕ → ℕ) (value : ℕ → ℕ → ℝ)
    (alpha criticalValue boundary : ℝ) : Prop :=
  (alpha < criticalValue → Tendsto (fun t => value (N t) (k t)) atTop (nhds 1)) ∧
  (alpha = criticalValue → Tendsto (fun t => value (N t) (k t)) atTop (nhds boundary)) ∧
  (criticalValue < alpha → Tendsto (fun t => value (N t) (k t)) atTop (nhds 0))

example : integerChoose 3 (-1) = 0 := by norm_num [integerChoose]

example {N k : ℕ} (a b : MPBTPortSelection N k) : accumulated a b 0 = 1 := by
  simp [accumulated]

example : branchingPaths 0 0 0 0 = 1 := by
  simp [branchingPaths, lowerAdded]

example (d : ℕ) : binomialBound d 2 0 = 1 := by
  simp [binomialBound]

example {d N k : ℕ}
    (omega : Matrix (MPBTRegister d N × MPBTRegister d N) (MPBTRegister d N × MPBTRegister d N) ℂ)
    (a : MPBTPortSelection N k) (E : AliceOp d N k) : mpbtBranchChannel omega a E 0 = 0 := by
  ext u v
  simp [mpbtBranchChannel]

example : branchingExpression 1 1 0 0 = 1 := by
  have hzero : Nat.choose 1 (Int.toNat 3) = 0 :=
    Nat.choose_eq_zero_of_lt (by decide)
  norm_num [branchingExpression, integerChoose, hzero]

example : branchingExpression 1 1 0 1 = 1 := by
  have hzero : Nat.choose 1 (Int.toNat 2) = 0 :=
    Nat.choose_eq_zero_of_lt (by decide)
  norm_num [branchingExpression, integerChoose, hzero]

/-- PDF p.12, Example 14, Eqs.(58)–(59): a=(3,4), b=(4,3) in one-based notation. -/
def examplePortA : MPBTPortSelection 4 2 := ⟨![2, 3], by decide⟩

/-- PDF p.12, Example 14: reversed lists have the same selected port set. -/
def examplePortB : MPBTPortSelection 4 2 := ⟨![3, 2], by decide⟩

end QAlgorithms.Papers.Independent.Extend50.P17


