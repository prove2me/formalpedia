-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20
-- name    : QAlgorithms_Papers_Independent_Extend50_P20
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:04:39.1552+00:00
-- url     : https://prove2.me/theorems/69912eb9-a77c-47d7-b6e7-86cb40861d96
-- title:
--   Definitions for Optimal Multi-port-based Teleportation Schemes
-- statement:
--   The objects the formalized statements of *Optimal Multi-port-based Teleportation Schemes* (arXiv:2011.09256) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MpbtWord`: Computational words for r qudits; PDF pp.3-6, Eqs.(1),(13).
--   - `PortOutcome`: Ordered, pairwise distinct port outcomes, PDF p.3, Eq.(2).
--   - `UnselectedPorts`: The unselected port positions for one outcome, PDF pp.7,15.
--   - `JointWord`: All Alice ports followed by the k input/reference positions, PDF pp.4-7. The product coordinate type is the computational basis of N+k factors.
--   - `JointOp`: Matrices on the N+k factors, PDF pp.4-7.
--   - `ThetaFamily`: A conclusive auxiliary operator on precisely the unselected ports, Eq.(49).
--   - `liftPorts`: A matrix tensored with the identity on all k remaining factors, Eq.(18).
--   - `bellInsertion`: Insert k normalized Bell vectors at the selected ordered ports, leaving all unselected positions untouched; PDF pp.4,15, Eqs.(5),(49). Pair j is (i(j),j), so Bob's output is in the indicated order.
--   - `successEffect`: The rotated conclusive effect P_i^+ tensor Theta_i, PDF p.15, Eq.(49). This factorization expresses exact transmission also for entangled inputs.
--   - `mpbtSignal`: Normalized signal state, PDF p.4, Eq.(4); its trace is one for d>0. Printed Eqs.(9)-(10), p.5, use inconsistent n-exponents; Eq.(4) and Appendix B p.18 instead give sigma_i=V_i^(k)/d^N. We use the latter, which also follows directly by tracing normalized Bell pairs.
--   - `traceOutputs`: Trace out all k final factors, not just one; PDF pp.7-8, Eqs.(20),(23).
--   - `IsResource`: The normalized pure-resource Gram operator, PDF p.3, Eq.(1).
--   - `ProbFeasible`: Full probabilistic primal domain, PDF p.7, Eqs.(17)-(18), p.15, Eq.(49). No symmetry ansatz is imposed. The slack is the rotated failure effect.
--   - `probScore`: Average exact success, PDF pp.5,7, Eqs.(7),(17); Bell factors have trace one.
--   - `probValues`: Attainable objective set of the unrestricted probabilistic primal SDP, PDF p.7, Eqs.(17)-(18); both resource and effects vary.
--   - `optimalMpbtSuccess`: Optimal exact success, PDF pp.7,10. The valid-domain theorem below states an attained greatest value, so the real supremum is not used as a default.
--   - `RealizesMpbtEffects`: Physical POVM realization of rotated conclusive effects, PDF pp.3-5. Failure is an actual PSD effect and the unrotated effects sum to identity.
--   - `DetFeasible`: Unrestricted deterministic primal domain, PDF p.8, Eqs.(21)-(22). Its PSD slack can complete the physical POVM; it is not discarded by assuming that rotated effects themselves form a normalized POVM.
--   - `detScore`: Entanglement fidelity against the normalized k-qudit maximally entangled state, PDF p.5, Eq.(6), p.8, Eq.(21).
--   - `detValues`: Attainable deterministic primal objectives, PDF p.8, Eqs.(21)-(22).
--   - `ProbDualFeasible`: Probabilistic dual domain, PDF p.7, Eqs.(19)-(20). Omega acts on N+k factors. E_i^* Omega E_i is the partial Bell trace in (20)(b), an operator on the unselected N-k factors.
--   - `probDualValues`: Attainable probabilistic dual objectives d^N b, PDF p.7, Eq.(19).
--   - `DetDualFeasible`: Deterministic dual in the epigraph form of the positive partial-trace operator norm, PDF p.8, Eqs.(23)-(24). On the valid domain Omega dominates a PSD signal, so its partial trace is PSD and bI >= Tr_out Omega is exactly the upper-eigenvalue epigraph of the source infinity norm.
--   - `detDualValues`: Attainable deterministic dual epigraph objectives, PDF p.8, Eq.(23). The real ratio d^N/d^(2k) avoids truncated natural subtraction in the exponent.
--   - `mpbtSchurMultiplicity`: Actual swap-representation multiplicity: dimension of the constructed Schur GL_d module, PDF p.14, Eqs.(42)-(45).
--   - `spechtDimension`: Actual Specht dimension, distinguished from local dimension d, PDF pp.8-9,14.
--   - `multiplicitySquares`: Sum of squared physical multiplicities, PDF pp.14,22, Eqs.(46),(105).
--   - `complementNumbering`: A fixed complement numbering, PDF p.15, Eq.(50). The Young projector is central, so choosing another numbering leaves the physical operator unchanged.
--   - `unselectedYoungProjector`: Full physical Young projector on the unselected positions, not one Young-symmetrizer copy; PDF p.15, Eq.(50).
--   - `optimalProbTheta`: The conclusive Theta_i prescribed by Theorem 5: S_N is in the denominator, PDF p.11, Eq.(36), and p.16, Eq.(52).
--   - `optimalProbOperation`: The resource operation of Theorem 5, including S_N under the square root, PDF p.11, Eq.(36), p.16, Eq.(53), p.18, Eq.(69).
--   - `factorialRatio`: Closed factorial expression, PDF p.10, Eq.(33). All division is real; usage theorems require positive d and 1 <= k <= N.
--   - `BoundedShape`: All shapes up to a fixed degree, used only as a finite ambient path type, PDF pp.8-9.
--   - `IsYoungPath`: A chain adding exactly one box at each step, including valid intermediate Young diagrams, PDF pp.8-9, Definition 6 pp.11-12. Endpoints are underlying diagrams so no dependent casts identify different partitions.
--   - `pathCount`: Number of all legal k-box paths, zero if endpoints are incompatible, PDF pp.8-9,12. These are counted paths, not free multiplicity parameters.
--   - `teleportationMatrix`: Generalized teleportation matrix, the Gram form of Eqs.(37)-(38),(83)-(85), PDF pp.11-12,19-20. The printed S(N-1) for alpha in Definition 6 is corrected to S(N-k), as required by its k-box definition and the proof.
--   - `largestTeleportationEigenvalue`: Largest eigenvalue in its Rayleigh-variational characterization, PDF p.20, Eq.(85), on the actual constructed finite symmetric matrix. The valid-domain shape set is nonempty and the unit sphere is compact.
--   - `cycleCount`: Count every permutation cycle, including fixed points; Mathlib cycleType alone omits the latter. PDF pp.22-23, Eqs.(105),(109).
--   - `fixLast`: Embed S(r) in S(r+1) by fixing the new final point, PDF p.23, Lemma 12.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, https://arxiv.org/abs/2011.09256v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition

noncomputable section

open scoped BigOperators Matrix ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Computational words for r qudits; PDF pp.3-6, Eqs.(1),(13). -/
abbrev MpbtWord (d r : ℕ) := Fin r → Fin d

/-- Ordered, pairwise distinct port outcomes, PDF p.3, Eq.(2). -/
abbrev PortOutcome (N k : ℕ) := Fin k ↪ Fin N

/-- The unselected port positions for one outcome, PDF pp.7,15. -/
abbrev UnselectedPorts {N k : ℕ} (i : PortOutcome N k) :=
  {a : Fin N // a ∉ Set.range i}

/-- All Alice ports followed by the k input/reference positions, PDF pp.4-7.
The product coordinate type is the computational basis of N+k factors. -/
abbrev JointWord (d N k : ℕ) := MpbtWord d N × MpbtWord d k

/-- Matrices on the N+k factors, PDF pp.4-7. -/
abbrev JointOp (d N k : ℕ) := Matrix (JointWord d N k) (JointWord d N k) ℂ

/-- A conclusive auxiliary operator on precisely the unselected ports, Eq.(49). -/
abbrev ThetaFamily (d N k : ℕ) :=
  (i : PortOutcome N k) → Matrix (UnselectedPorts i → Fin d) (UnselectedPorts i → Fin d) ℂ

/-- A matrix tensored with the identity on all k remaining factors, Eq.(18). -/
def liftPorts {d N k : ℕ} (X : Matrix (MpbtWord d N) (MpbtWord d N) ℂ) : JointOp d N k :=
  Matrix.of fun x y => X x.1 y.1 * if x.2 = y.2 then 1 else 0

/-- Insert k normalized Bell vectors at the selected ordered ports, leaving
all unselected positions untouched; PDF pp.4,15, Eqs.(5),(49).
Pair j is (i(j),j), so Bob's output is in the indicated order. -/
def bellInsertion {d N k : ℕ} (i : PortOutcome N k) :
    Matrix (JointWord d N k) (UnselectedPorts i → Fin d) ℂ :=
  Matrix.of fun x w =>
    if (∀ j, x.1 (i j) = x.2 j) ∧ (∀ a : UnselectedPorts i, x.1 a.val = w a)
    then (((Real.sqrt ((d : ℝ)^k))⁻¹ : ℝ) : ℂ) else 0

/-- The rotated conclusive effect P_i^+ tensor Theta_i, PDF p.15, Eq.(49).
This factorization expresses exact transmission also for entangled inputs. -/
def successEffect {d N k : ℕ} (i : PortOutcome N k)
    (T : Matrix (UnselectedPorts i → Fin d) (UnselectedPorts i → Fin d) ℂ) : JointOp d N k :=
  bellInsertion (d := d) i * T * Matrix.conjTranspose (bellInsertion (d := d) i)

/-- Normalized signal state, PDF p.4, Eq.(4); its trace is one for d>0.
Printed Eqs.(9)-(10), p.5, use inconsistent n-exponents; Eq.(4) and
Appendix B p.18 instead give sigma_i=V_i^(k)/d^N. We use the latter,
which also follows directly by tracing normalized Bell pairs. -/
def mpbtSignal {d N k : ℕ} (i : PortOutcome N k) : JointOp d N k :=
  ((1 : ℂ) / (d : ℂ)^(N-k)) • successEffect i 1

/-- Trace out all k final factors, not just one; PDF pp.7-8, Eqs.(20),(23). -/
def traceOutputs {d N k : ℕ} (Z : JointOp d N k) :
    Matrix (MpbtWord d N) (MpbtWord d N) ℂ :=
  Matrix.of fun a b => ∑ w : MpbtWord d k, Z (a,w) (b,w)

/-- The normalized pure-resource Gram operator, PDF p.3, Eq.(1). -/
def IsResource {d N : ℕ} (X : Matrix (MpbtWord d N) (MpbtWord d N) ℂ) : Prop :=
  X.PosSemidef ∧ X.trace = (d : ℂ)^N

/-- Full probabilistic primal domain, PDF p.7, Eqs.(17)-(18), p.15, Eq.(49).
No symmetry ansatz is imposed. The slack is the rotated failure effect. -/
def ProbFeasible {d N k : ℕ} (X : Matrix (MpbtWord d N) (MpbtWord d N) ℂ)
    (T : ThetaFamily d N k) : Prop :=
  IsResource X ∧ (∀ i, (T i).PosSemidef) ∧
    (liftPorts X - ∑ i : PortOutcome N k, successEffect i (T i)).PosSemidef

/-- Average exact success, PDF pp.5,7, Eqs.(7),(17); Bell factors have trace one. -/
def probScore {d N k : ℕ} (T : ThetaFamily d N k) : ℝ :=
  (∑ i : PortOutcome N k, (T i).trace.re) / (d : ℝ)^(N+k)

/-- Attainable objective set of the unrestricted probabilistic primal SDP,
PDF p.7, Eqs.(17)-(18); both resource and effects vary. -/
def probValues (d N k : ℕ) : Set ℝ :=
  {p | ∃ X : Matrix (MpbtWord d N) (MpbtWord d N) ℂ, ∃ T : ThetaFamily d N k,
    ProbFeasible X T ∧ p = probScore T}

/-- Optimal exact success, PDF pp.7,10. The valid-domain theorem below states
an attained greatest value, so the real supremum is not used as a default. -/
def optimalMpbtSuccess (d N k : ℕ) : ℝ := sSup (probValues d N k)

/-- Physical POVM realization of rotated conclusive effects, PDF pp.3-5.
Failure is an actual PSD effect and the unrotated effects sum to identity. -/
def RealizesMpbtEffects {d N k : ℕ} (O : Matrix (MpbtWord d N) (MpbtWord d N) ℂ)
    (P : PortOutcome N k → JointOp d N k) : Prop :=
  (Matrix.conjTranspose O * O).trace = (d : ℂ)^N ∧
    ∃ M : PortOutcome N k → JointOp d N k, ∃ failure : JointOp d N k,
      (∀ i, (M i).PosSemidef) ∧ failure.PosSemidef ∧
      (∑ i : PortOutcome N k, M i) + failure = 1 ∧
      ∀ i, Matrix.conjTranspose (liftPorts O) * M i * liftPorts O = P i

/-- Unrestricted deterministic primal domain, PDF p.8, Eqs.(21)-(22).
Its PSD slack can complete the physical POVM; it is not discarded by
assuming that rotated effects themselves form a normalized POVM. -/
def DetFeasible {d N k : ℕ} (X : Matrix (MpbtWord d N) (MpbtWord d N) ℂ)
    (P : PortOutcome N k → JointOp d N k) : Prop :=
  IsResource X ∧ (∀ i, (P i).PosSemidef) ∧
    (liftPorts X - ∑ i : PortOutcome N k, P i).PosSemidef

/-- Entanglement fidelity against the normalized k-qudit maximally entangled
state, PDF p.5, Eq.(6), p.8, Eq.(21). -/
def detScore {d N k : ℕ} (P : PortOutcome N k → JointOp d N k) : ℝ :=
  (∑ i : PortOutcome N k, ((P i) * mpbtSignal i).trace.re) / (d : ℝ)^(2*k)

/-- Attainable deterministic primal objectives, PDF p.8, Eqs.(21)-(22). -/
def detValues (d N k : ℕ) : Set ℝ :=
  {f | ∃ X : Matrix (MpbtWord d N) (MpbtWord d N) ℂ,
    ∃ P : PortOutcome N k → JointOp d N k, DetFeasible X P ∧ f = detScore P}

/-- Probabilistic dual domain, PDF p.7, Eqs.(19)-(20).
Omega acts on N+k factors. E_i^* Omega E_i is the partial Bell trace in
(20)(b), an operator on the unselected N-k factors. -/
def ProbDualFeasible {d N k : ℕ} (Z : JointOp d N k) (b : ℝ) : Prop :=
  Z.PosSemidef ∧ 0 ≤ b ∧
    (∀ i : PortOutcome N k,
      (Matrix.conjTranspose (bellInsertion (d := d) i) * Z *
        bellInsertion (d := d) i - 1).PosSemidef) ∧
    (((b : ℂ) • (1 : Matrix (MpbtWord d N) (MpbtWord d N) ℂ)) -
      ((1 : ℂ)/(d : ℂ)^(N+k)) • traceOutputs Z).PosSemidef

/-- Attainable probabilistic dual objectives d^N b, PDF p.7, Eq.(19). -/
def probDualValues (d N k : ℕ) : Set ℝ :=
  {p | ∃ Z : JointOp d N k, ∃ b : ℝ,
    ProbDualFeasible Z b ∧ p = (d : ℝ)^N * b}

/-- Deterministic dual in the epigraph form of the positive partial-trace
operator norm, PDF p.8, Eqs.(23)-(24). On the valid domain Omega dominates
a PSD signal, so its partial trace is PSD and bI >= Tr_out Omega is exactly
the upper-eigenvalue epigraph of the source infinity norm. -/
def DetDualFeasible {d N k : ℕ} (Z : JointOp d N k) (b : ℝ) : Prop :=
  (∀ i : PortOutcome N k, (Z - mpbtSignal i).PosSemidef) ∧
    (((b : ℂ) • (1 : Matrix (MpbtWord d N) (MpbtWord d N) ℂ)) - traceOutputs Z).PosSemidef

/-- Attainable deterministic dual epigraph objectives, PDF p.8, Eq.(23).
The real ratio d^N/d^(2k) avoids truncated natural subtraction in the exponent. -/
def detDualValues (d N k : ℕ) : Set ℝ :=
  {f | ∃ Z : JointOp d N k, ∃ b : ℝ, DetDualFeasible Z b ∧
    f = ((d : ℝ)^N / (d : ℝ)^(2*k)) * b}

/-- Actual swap-representation multiplicity: dimension of the constructed
Schur GL_d module, PDF p.14, Eqs.(42)-(45). -/
def mpbtSchurMultiplicity {d r : ℕ} (lambda : QAlgorithms.Schur.Partition d r) : ℕ :=
  Module.finrank ℂ (QAlgorithms.Schur.schurModule lambda)

/-- Actual Specht dimension, distinguished from local dimension d,
PDF pp.8-9,14. -/
def spechtDimension {d r : ℕ} (lambda : QAlgorithms.Schur.Partition d r) : ℕ :=
  Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)

/-- Sum of squared physical multiplicities, PDF pp.14,22, Eqs.(46),(105). -/
def multiplicitySquares (d r : ℕ) : ℝ :=
  ∑ lambda : QAlgorithms.Schur.Partition d r, (mpbtSchurMultiplicity lambda : ℝ)^2

/-- A fixed complement numbering, PDF p.15, Eq.(50). The Young projector is
central, so choosing another numbering leaves the physical operator unchanged. -/
def complementNumbering {N k : ℕ} (i : PortOutcome N k) : UnselectedPorts i ≃ Fin (N-k) :=
  Fintype.equivFinOfCardEq (by
    change Fintype.card ((Set.range i)ᶜ : Set (Fin N)) = N-k
    rw [Fintype.card_compl_set, Fintype.card_range i]
    simp)

/-- Full physical Young projector on the unselected positions, not one
Young-symmetrizer copy; PDF p.15, Eq.(50). -/
def unselectedYoungProjector {d N k : ℕ} (i : PortOutcome N k)
    (alpha : QAlgorithms.Schur.Partition d (N-k)) :
    Matrix (UnselectedPorts i → Fin d) (UnselectedPorts i → Fin d) ℂ :=
  Matrix.of fun x y => QAlgorithms.Schur.isotypicProjector alpha
    (fun a => x ((complementNumbering i).symm a))
    (fun a => y ((complementNumbering i).symm a))

/-- The conclusive Theta_i prescribed by Theorem 5: S_N is in the denominator,
PDF p.11, Eq.(36), and p.16, Eq.(52). -/
def optimalProbTheta (d N k : ℕ) : ThetaFamily d N k :=
  fun i => ∑ alpha : QAlgorithms.Schur.Partition d (N-k),
    ((((d : ℝ)^(N+k) * (mpbtSchurMultiplicity alpha : ℝ)) /
      (((k.factorial * N.choose k : ℕ) : ℝ) * (spechtDimension alpha : ℝ) *
        multiplicitySquares d N) : ℝ) : ℂ) • unselectedYoungProjector i alpha

/-- The resource operation of Theorem 5, including S_N under the square root,
PDF p.11, Eq.(36), p.16, Eq.(53), p.18, Eq.(69). -/
def optimalProbOperation (d N : ℕ) : Matrix (MpbtWord d N) (MpbtWord d N) ℂ :=
  ∑ mu : QAlgorithms.Schur.Partition d N,
    (((Real.sqrt ((d : ℝ)^N) * Real.sqrt ((mpbtSchurMultiplicity mu : ℝ) /
      ((spechtDimension mu : ℝ) * multiplicitySquares d N))) : ℝ) : ℂ) •
        QAlgorithms.Schur.isotypicProjector mu

/-- Closed factorial expression, PDF p.10, Eq.(33). All division is real;
usage theorems require positive d and 1 <= k <= N. -/
def factorialRatio (d N k : ℕ) : ℝ :=
  ((N.factorial : ℝ) * ((d^2+N-k-1).factorial : ℝ)) /
    (((N-k).factorial : ℝ) * ((d^2+N-1).factorial : ℝ))

/-- All shapes up to a fixed degree, used only as a finite ambient path type,
PDF pp.8-9. -/
abbrev BoundedShape (d R : ℕ) := (r : Fin (R+1)) × QAlgorithms.Schur.Partition d r.val

/-- A chain adding exactly one box at each step, including valid intermediate
Young diagrams, PDF pp.8-9, Definition 6 pp.11-12. Endpoints are underlying
diagrams so no dependent casts identify different partitions. -/
def IsYoungPath {d a b : ℕ} (alpha : QAlgorithms.Schur.Partition d a)
    (mu : QAlgorithms.Schur.Partition d b) (k : ℕ)
    (p : Fin (k+1) → BoundedShape d (a+k)) : Prop :=
  (p 0).2.val = alpha.val ∧ (p (Fin.last k)).2.val = mu.val ∧
    (∀ j, (p j).1.val = a+j.val) ∧
    ∀ j : Fin k, (p j.castSucc).2.val ≤ (p j.succ).2.val

/-- Number of all legal k-box paths, zero if endpoints are incompatible,
PDF pp.8-9,12. These are counted paths, not free multiplicity parameters. -/
def pathCount {d a b : ℕ} (alpha : QAlgorithms.Schur.Partition d a)
    (mu : QAlgorithms.Schur.Partition d b) (k : ℕ) : ℕ :=
  (Finset.univ.filter (IsYoungPath alpha mu k)).card

/-- Generalized teleportation matrix, the Gram form of Eqs.(37)-(38),(83)-(85),
PDF pp.11-12,19-20. The printed S(N-1) for alpha in Definition 6 is corrected
to S(N-k), as required by its k-box definition and the proof. -/
def teleportationMatrix (d N k : ℕ) :
    Matrix (QAlgorithms.Schur.Partition d N) (QAlgorithms.Schur.Partition d N) ℝ :=
  Matrix.of fun mu nu => ∑ alpha : QAlgorithms.Schur.Partition d (N-k),
    (pathCount alpha mu k : ℝ) * (pathCount alpha nu k : ℝ)

/-- Largest eigenvalue in its Rayleigh-variational characterization, PDF p.20,
Eq.(85), on the actual constructed finite symmetric matrix. The valid-domain
shape set is nonempty and the unit sphere is compact. -/
def largestTeleportationEigenvalue (d N k : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ v : QAlgorithms.Schur.Partition d N → ℝ,
    (∑ mu, v mu ^ 2) = 1 ∧
    r = ∑ mu, ∑ nu, v mu * teleportationMatrix d N k mu nu * v nu}

/-- Count every permutation cycle, including fixed points; Mathlib cycleType
alone omits the latter. PDF pp.22-23, Eqs.(105),(109). -/
def cycleCount {r : ℕ} (pi : Equiv.Perm (Fin r)) : ℕ :=
  pi.cycleType.card + (Finset.univ.filter fun a => pi a = a).card

/-- Embed S(r) in S(r+1) by fixing the new final point, PDF p.23, Lemma 12. -/
def fixLast {r : ℕ} (pi : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) :=
  Equiv.permCongr (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1))
    (Equiv.sumCongr pi (Equiv.refl (Fin 1)))

/-- Sanity: the lift preserves a zero operator, independently of input dimension. -/
example (d N k : ℕ) : liftPorts (k := k) (0 : Matrix (MpbtWord d N) (MpbtWord d N) ℂ) = 0 := by
  ext x y
  simp [liftPorts]

/-- Sanity: one port and one qubit have success 1/4, Eq.(34). -/
example : factorialRatio 2 1 1 = 1/4 := by norm_num [factorialRatio]

/-- Sanity: in dimension one even the full one-port endpoint succeeds surely. -/
example : factorialRatio 1 1 1 = 1 := by norm_num [factorialRatio]

/-- Sanity: the empty permutation has zero cycles, including fixed points. -/
example : cycleCount (1 : Equiv.Perm (Fin 0)) = 0 := by simp [cycleCount]

/-- Sanity: identity on r points has r cycles; fixed points cannot be dropped. -/
example (r : ℕ) : cycleCount (1 : Equiv.Perm (Fin r)) = r := by simp [cycleCount]

/-- Sanity: a zero-step path keeps its diagram and has no edge conditions. -/
example {d a : ℕ} (alpha : QAlgorithms.Schur.Partition d a) :
    IsYoungPath alpha alpha 0 (fun _ => ⟨⟨a, by omega⟩, alpha⟩) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro j
    have hj : j.val = 0 := by omega
    simp [hj]
  · intro j
    exact Fin.elim0 j

end QAlgorithms.Papers.Independent.Extend50.P20


