-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
-- name    : QAlgorithms_Papers_Independent_Information100_P34
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T10:24:47.610692+00:00
-- url     : https://prove2.me/theorems/b781ed0a-224e-4031-8abb-a97a1add61fa
-- title:
--   Definitions for The Structure of Higher-Order Quantum Resources with an Application to Coherence
-- statement:
--   The objects the formalized statements of *The Structure of Higher-Order Quantum Resources with an Application to Coherence* (arXiv:2609.40186) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `dephasing`: Complete dephasing in the specified finite computational basis (PDF pp.9,34). The accepted qubit-only dephasing does not cover arbitrary finite dimensions.
--   - `dephaseInput`: Dephase only the first wire of an input-first bipartite operator (PDF p.55).
--   - `dephaseOutput`: Dephase only the second wire (PDF p.55).
--   - `choi`: Unnormalized, input-first Choi matrix, Eq.(1), PDF p.2.
--   - `Theory`: The three channel coherence theories, Definition 9 (PDF pp.9-10).
--   - `Free`: Free-channel condition on every operator, Definition 9 (PDF pp.9-10). CPTP membership is included, rather than inferred from the dephasing equation.
--   - `supportProjector`: Orthogonal support projector: project onto the range in the Euclidean inner product, not an arbitrary algebraic projection (Lemma 19, PDF p.30).
--   - `permutationMatrix`: Permutation matrix with column k equal to the basis vector pi(k) (Lemma 20, PDF p.34).
--   - `TraceAnnihilator`: Trace annihilator in the real vector space of Hermitian operators, Eq.(B6b) (PDF p.20); star does not mean positive dual or adjoint.
--   - `maxRobustness`: Generalized multiplicative robustness in the equivalent Choi domination form (C125), PDF p.39, of Eq.(27), PDF p.7. Extended infimum: empty means infinity.
--   - `isometricAffineMinRobustness`: Affine min robustness for an ISOMETRIC channel, using Eq.(B4b), PDF p.20. The reference is input-sized and the input vector has norm one. The inverse of an empty extended infimum is zero, as required by Eq.(31), PDF p.8. This formula is used only for Fourier (hence isometric) channels.
--   - `fourierChannel`: Positive-exponent d-dimensional Fourier channel, not restricted to powers of two (PDF p.10; accepted Fourier matrix convention).
--   - `diamondDistance`: Half the diamond norm distance of CHANNELS, Eq.(9), PDF p.4. Input-sized reference; normalized density matrices include all entangled inputs. For channels the optimized set is nonempty and bounded in [0,1].
--   - `smallestEntrySq`: Smallest squared modulus of a unitary entry, Eq.(C133), PDF p.40. Used only for positive D, so the finite minimum is over a nonempty set.
--   - `cyclicPhase`: Positive Fourier phase of a cyclic residue (PDF p.35). All arithmetic inside the argument is in ZMod d, including subtraction.
--   - `cyclicFourier`: The accepted positive-exponent Fourier matrix reindexed by cyclic residues.
--   - `weyl`: Shift and clock product S^n Omega^m, Eqs.(C87-C88), PDF p.35.
--   - `weylPair`: Eq.(C89), PDF p.35. The star on W in the paper is entrywise conjugation.
--   - `fourierKet`: Normalized Fourier basis vector, PDF p.35.
--   - `jointKet`: Normalized joint eigenvector with coefficient 1/d, Eq.(C91a), PDF p.35.
--   - `jointProjector`: The rank-one projector Pi_(k,l), Eq.(C91a), PDF p.35.
--   - `leftProjector`: Projectors P_l, Eq.(C91b), PDF p.35.
--   - `rightProjector`: Projectors Q_k, Eq.(C91c), PDF p.35.
--   - `CompleteOrthogonal`: Completeness, self-adjoint idempotence and pairwise orthogonality of a finite projector family; no sum-to-identity clause is omitted (PDF pp.35-36).
--   - `liftOuter`: Lift an operator on wires 0,3 by identities on 1,2, with wire order ((0,1),(2,3)) throughout (PDF pp.37-38).
--   - `twirlOuter`: The actual average of Weyl conjugations on outer wires, Eq.(C90), PDF p.35. It is not defined by its claimed invariant-block characterization.
--   - `CombOne`: Fixed four-wire deterministic comb normalizations (6), PDF p.3. Both levels of the recursive normalization are part of the predicate.
--   - `blockOuter`: Reindex Y^(12) tensor Pi^(03) into fixed wire order ((0,1),(2,3)).
--   - `fromChoi`: Matrix of a channel reconstructed from its input-first Choi operator, Eq.(2), PDF p.2; its action is explicitly computed on all operators.
--   - `FreeChoi`: A specified matrix is exactly the Choi matrix of the computed free channel.
--   - `dyad`: Dyad |v><w| in the specified computational basis.
--   - `testerPsi`: The two normalized vectors of Eq.(C1), PDF p.25. The remaining B wires are grouped as R and may be trivial. Control basis entries 0 and 1 are distinct.
--   - `testerD`: D of Eq.(C2) in order ((1,2),B), PDF p.25.
--   - `testerQ`: Q of Eq.(C3), PDF p.25. Q acts on (1,B) first and is then tensored with I_2/d_2, permuted into ((1,2),B) order.
--   - `testerTerm`: The common non-background terms of (C4-C7), PDF p.25. Both antisymmetric factors are retained in the second variant.
--   - `testerAsCreation`: Reinterpret ((1,2),B) as input 1 and output (2,B), with no transpose.
--   - `testerAsDetection`: Reinterpret ((1,2),B) as input (1,B) and output 2, with no transpose.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, https://arxiv.org/abs/2609.40186v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
Statements from Ahnefeld, Theurer and Plenio, arXiv:2609.40186v1.
All new objects are local to this paper. Wire order is specified in each definition.
General compatible-family results are deferred in the unit's HARD.md.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Complete dephasing in the specified finite computational basis (PDF pp.9,34).
The accepted qubit-only dephasing does not cover arbitrary finite dimensions. -/
def dephasing {I : Type*} [DecidableEq I] (X : Matrix I I ℂ) : Matrix I I ℂ :=
  Matrix.diagonal fun i => X i i

/-- Dephase only the first wire of an input-first bipartite operator (PDF p.55). -/
def dephaseInput {A B : Type*} [DecidableEq A]
    (X : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => if p.1 = q.1 then X p q else 0

/-- Dephase only the second wire (PDF p.55). -/
def dephaseOutput {A B : Type*} [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ) : Matrix (A × B) (A × B) ℂ :=
  fun p q => if p.2 = q.2 then X p q else 0

/-- Unnormalized, input-first Choi matrix, Eq.(1), PDF p.2. -/
def choi {A B : Type*} [DecidableEq A] (E : Superop A B) :
    Matrix (A × B) (A × B) ℂ :=
  fun p q => E (Matrix.single p.1 q.1 1) p.2 q.2

/-- The three channel coherence theories, Definition 9 (PDF pp.9-10). -/
inductive Theory where
  | mio
  | di
  | dio
  deriving DecidableEq

/-- Free-channel condition on every operator, Definition 9 (PDF pp.9-10).
CPTP membership is included, rather than inferred from the dephasing equation. -/
def Free {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (O : Theory) (E : Superop A B) : Prop :=
  IsChannel E ∧ match O with
    | .mio => ∀ X, E (dephasing X) = dephasing (E (dephasing X))
    | .di => ∀ X, dephasing (E X) = dephasing (E (dephasing X))
    | .dio => ∀ X, dephasing (E X) = E (dephasing X)

/-- Orthogonal support projector: project onto the range in the Euclidean inner
product, not an arbitrary algebraic projection (Lemma 19, PDF p.30). -/
def supportProjector {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : Matrix I I ℂ :=
  Matrix.toEuclideanLin.symm
    ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection.toLinearMap)

/-- Permutation matrix with column k equal to the basis vector pi(k)
(Lemma 20, PDF p.34). -/
def permutationMatrix {I : Type*} [DecidableEq I] (pi : Equiv.Perm I) : Matrix I I ℂ :=
  fun i j => if i = pi j then 1 else 0

/-- Trace annihilator in the real vector space of Hermitian operators, Eq.(B6b)
(PDF p.20); star does not mean positive dual or adjoint. -/
def TraceAnnihilator {a b : ℕ} (O : Theory)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Prop :=
  X.IsHermitian ∧ ∀ E : Superop (Fin a) (Fin b), Free O E → (X * choi E).trace = 0

/-- Generalized multiplicative robustness in the equivalent Choi domination form
(C125), PDF p.39, of Eq.(27), PDF p.7. Extended infimum: empty means infinity. -/
def maxRobustness {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (O : Theory) (E : Superop A B) : ℝ≥0∞ :=
  sInf {s | ∃ t : ℝ, 1 ≤ t ∧ s = ENNReal.ofReal t ∧
    ∃ M : Superop A B, Free O M ∧ ((t : ℂ) • choi M - choi E).PosSemidef}

/-- Affine min robustness for an ISOMETRIC channel, using Eq.(B4b), PDF p.20.
The reference is input-sized and the input vector has norm one. The inverse of
an empty extended infimum is zero, as required by Eq.(31), PDF p.8.
This formula is used only for Fourier (hence isometric) channels. -/
def isometricAffineMinRobustness {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (O : Theory) (E : Superop A B) : ℝ≥0∞ :=
  (sInf {s | ∃ t : ℝ, 0 ≤ t ∧ s = ENNReal.ofReal t ∧
    ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧
      ∀ M : Superop A B, Free O M →
        ((idTensorSuperop (R := A) E (pureDensity psi)) *
          (idTensorSuperop (R := A) M (pureDensity psi))).trace.re = t})⁻¹

/-- Positive-exponent d-dimensional Fourier channel, not restricted to powers
of two (PDF p.10; accepted Fourier matrix convention). -/
def fourierChannel (d : ℕ) : Superop (Fin d) (Fin d) := conjSuperop (qftMatrix d)

/-- Half the diamond norm distance of CHANNELS, Eq.(9), PDF p.4.
Input-sized reference; normalized density matrices include all entangled inputs.
For channels the optimized set is nonempty and bounded in [0,1]. -/
def diamondDistance {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (E N : Superop A B) : ℝ :=
  sSup {v | ∃ rho : Matrix (A × A) (A × A) ℂ, IsDensityMatrix rho ∧
    v = traceNorm (idTensorSuperop (R := A) E rho -
      idTensorSuperop (R := A) N rho) / 2}

/-- Smallest squared modulus of a unitary entry, Eq.(C133), PDF p.40.
Used only for positive D, so the finite minimum is over a nonempty set. -/
def smallestEntrySq {D : ℕ} (hD : 0 < D) (U : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Finset.univ : Finset (Fin D × Fin D)).inf'
    ⟨(⟨0, hD⟩, ⟨0, hD⟩), Finset.mem_univ _⟩
    (fun ij => Complex.normSq (U ij.1 ij.2))

/-- Dephasing keeps diagonal entries and removes every off-diagonal entry. -/
example {I : Type*} [DecidableEq I] (X : Matrix I I ℂ) (i : I) :
    dephasing X i i = X i i := by simp [dephasing]

example {A B : Type*} [DecidableEq A] (E : Superop A B) (a a' : A) (b b' : B) :
    choi E (a,b) (a',b') = E (Matrix.single a a' 1) b b' := rfl

example {A B : Type*} [DecidableEq A] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ) (p q : A × B) (h : p.1 ≠ q.1) :
    dephaseInput X p q = 0 := by simp [dephaseInput,h]

/-- The paper's affine empty-feasible-set convention has the intended value. -/
example : (sInf (∅ : Set ℝ≥0∞))⁻¹ = 0 := by simp

/-- In a one-dimensional basis dephasing is the identity. -/
example (X : Matrix (Fin 1) (Fin 1) ℂ) : dephasing X = X := by
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp [dephasing]

/-- The identity permutation has the expected column orientation. -/
example {I : Type*} [DecidableEq I] :
    permutationMatrix (Equiv.refl I) = (1 : Matrix I I ℂ) := by
  ext i j
  simp [permutationMatrix, Matrix.one_apply] <;> rfl

/-- Positive Fourier phase of a cyclic residue (PDF p.35). All arithmetic
inside the argument is in ZMod d, including subtraction. -/
def cyclicPhase (d : ℕ) (x : ZMod d) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / (d : ℂ))

/-- The accepted positive-exponent Fourier matrix reindexed by cyclic residues. -/
def cyclicFourier (d : ℕ) [NeZero d] : Matrix (ZMod d) (ZMod d) ℂ :=
  (qftMatrix d).submatrix (ZMod.finEquiv d).symm (ZMod.finEquiv d).symm

/-- Shift and clock product S^n Omega^m, Eqs.(C87-C88), PDF p.35. -/
def weyl {d : ℕ} [NeZero d] (n m : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  let shift : Matrix (ZMod d) (ZMod d) ℂ := Matrix.of fun a b => if a = b + 1 then 1 else 0
  let clock : Matrix (ZMod d) (ZMod d) ℂ := Matrix.diagonal (cyclicPhase d)
  shift ^ n.val * clock ^ m.val

/-- Eq.(C89), PDF p.35. The star on W in the paper is entrywise conjugation. -/
def weylPair {d : ℕ} [NeZero d] (n m : ZMod d) :
    Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
  Matrix.kronecker (weyl n m)
    (cyclicFourier d *
      ((weyl n m).map conj) *
      (cyclicFourier d)ᴴ)

/-- Normalized Fourier basis vector, PDF p.35. -/
def fourierKet {d : ℕ} [NeZero d] (k : ZMod d) : EuclideanSpace ℂ (ZMod d) :=
  WithLp.toLp 2 fun b => cyclicPhase d (b*k) / (Real.sqrt d : ℂ)

/-- Normalized joint eigenvector with coefficient 1/d, Eq.(C91a), PDF p.35. -/
def jointKet {d : ℕ} [NeZero d] (k l : ZMod d) :
    EuclideanSpace ℂ (ZMod d × ZMod d) :=
  WithLp.toLp 2 fun ab => cyclicPhase d (ab.1 * (ab.2-k) - l*ab.2) / (d : ℂ)

/-- The rank-one projector Pi_(k,l), Eq.(C91a), PDF p.35. -/
def jointProjector {d : ℕ} [NeZero d] (k l : ZMod d) := pureDensity (jointKet k l)

/-- Projectors P_l, Eq.(C91b), PDF p.35. -/
def leftProjector {d : ℕ} [NeZero d] (l : ZMod d) :
    Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
  ∑ a, Matrix.kronecker (Matrix.single a a 1) (pureDensity (fourierKet (a-l)))

/-- Projectors Q_k, Eq.(C91c), PDF p.35. -/
def rightProjector {d : ℕ} [NeZero d] (k : ZMod d) :
    Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
  ∑ b, Matrix.kronecker (pureDensity (fourierKet (b-k))) (Matrix.single b b 1)

/-- Completeness, self-adjoint idempotence and pairwise orthogonality of a
finite projector family; no sum-to-identity clause is omitted (PDF pp.35-36). -/
def CompleteOrthogonal {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    (P : K → Matrix I I ℂ) : Prop :=
  (∀ k, (P k).IsHermitian ∧ P k * P k = P k) ∧
  (∀ k l, k ≠ l → P k * P l = 0) ∧ ∑ k, P k = 1

/-- Lift an operator on wires 0,3 by identities on 1,2, with wire order
((0,1),(2,3)) throughout (PDF pp.37-38). -/
def liftOuter {d a b : ℕ} [NeZero d]
    (U : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
    Matrix ((ZMod d × Fin a) × (Fin b × ZMod d))
      ((ZMod d × Fin a) × (Fin b × ZMod d)) ℂ :=
  fun p q => if p.1.2 = q.1.2 ∧ p.2.1 = q.2.1 then U (p.1.1,p.2.2) (q.1.1,q.2.2) else 0

/-- The actual average of Weyl conjugations on outer wires, Eq.(C90),
PDF p.35. It is not defined by its claimed invariant-block characterization. -/
def twirlOuter {d a b : ℕ} [NeZero d]
    (J : Matrix ((ZMod d × Fin a) × (Fin b × ZMod d))
      ((ZMod d × Fin a) × (Fin b × ZMod d)) ℂ) :=
  (1 / ((d : ℂ)^2)) • ∑ n : ZMod d, ∑ m : ZMod d,
    conjSuperop (liftOuter (a := a) (b := b) (weylPair n m)) J

/-- Fixed four-wire deterministic comb normalizations (6), PDF p.3.
Both levels of the recursive normalization are part of the predicate. -/
def CombOne {d a b : ℕ} [NeZero d]
    (J : Matrix ((ZMod d × Fin a) × (Fin b × ZMod d))
      ((ZMod d × Fin a) × (Fin b × ZMod d)) ℂ) : Prop :=
  J.PosSemidef ∧ ∃ L : Matrix (ZMod d × Fin a) (ZMod d × Fin a) ℂ,
    L.PosSemidef ∧
    (∀ i j : ZMod d, ∀ u v : Fin a, ∀ x y : Fin b,
      (∑ z : ZMod d, J ((i,u),(x,z)) ((j,v),(y,z))) =
        L (i,u) (j,v) * (if x=y then 1 else 0)) ∧
    (∀ i j : ZMod d, (∑ u : Fin a, L (i,u) (j,u)) = if i=j then 1 else 0)

/-- Reindex Y^(12) tensor Pi^(03) into fixed wire order ((0,1),(2,3)). -/
def blockOuter {d a b : ℕ} [NeZero d]
    (Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (P : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
    Matrix ((ZMod d × Fin a) × (Fin b × ZMod d))
      ((ZMod d × Fin a) × (Fin b × ZMod d)) ℂ :=
  fun p q => Y (p.1.2,p.2.1) (q.1.2,q.2.1) * P (p.1.1,p.2.2) (q.1.1,q.2.2)

/-- Matrix of a channel reconstructed from its input-first Choi operator,
Eq.(2), PDF p.2; its action is explicitly computed on all operators. -/
def fromChoi {A B : Type*} [Fintype A]
    (J : Matrix (A × B) (A × B) ℂ) : Superop A B :=
  fun X b b' => ∑ a, ∑ a', X a a' * J (a,b) (a',b')

/-- A specified matrix is exactly the Choi matrix of the computed free channel. -/
def FreeChoi {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (O : Theory)
    (J : Matrix (A × B) (A × B) ℂ) : Prop :=
  Free O (fromChoi J) ∧ choi (fromChoi J) = J

/-- Dyad |v><w| in the specified computational basis. -/
def dyad {I : Type*} (v w : EuclideanSpace ℂ I) : Matrix I I ℂ :=
  fun p q => v p * conj (w q)

/-- The two normalized vectors of Eq.(C1), PDF p.25. The remaining B wires
are grouped as R and may be trivial. Control basis entries 0 and 1 are distinct. -/
def testerPsi {c : ℕ} {R : Type*} [DecidableEq R]
    (hc : 2 ≤ c) (k l : R) (minus : Bool) : EuclideanSpace ℂ (Fin c × R) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (ket (⟨0, by omega⟩,k) + (if minus then (-1 : ℂ) else 1) • ket (⟨1, by omega⟩,l))

/-- D of Eq.(C2) in order ((1,2),B), PDF p.25. -/
def testerD {a b : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (k l : Fin a) : Matrix ((Fin a × Fin b) × B) ((Fin a × Fin b) × B) ℂ :=
  Matrix.kronecker
    (Matrix.kronecker ((1 : Matrix (Fin a) (Fin a) ℂ) - Matrix.single k k 1 - Matrix.single l l 1)
      (((b : ℂ)⁻¹) • (1 : Matrix (Fin b) (Fin b) ℂ)))
    (((Fintype.card B : ℂ)⁻¹) • (1 : Matrix B B ℂ))

/-- Q of Eq.(C3), PDF p.25. Q acts on (1,B) first and is then tensored
with I_2/d_2, permuted into ((1,2),B) order. -/
def testerQ {a b : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (k l : Fin a) (plus minus : EuclideanSpace ℂ B) :
    Matrix ((Fin a × Fin b) × B) ((Fin a × Fin b) × B) ℂ :=
  let Q : Matrix (Fin a × B) (Fin a × B) ℂ :=
    1 - (1/2 : ℂ) • Matrix.kronecker (Matrix.single k k 1 + Matrix.single l l 1)
      (pureDensity plus + pureDensity minus)
  fun p q => Q (p.1.1,p.2) (q.1.1,q.2) *
    (((b : ℂ)⁻¹) • (1 : Matrix (Fin b) (Fin b) ℂ)) p.1.2 q.1.2

/-- The common non-background terms of (C4-C7), PDF p.25. Both
antisymmetric factors are retained in the second variant. -/
def testerTerm {a b : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (k l : Fin a) (n m : Fin b) (plus minus : EuclideanSpace ℂ B)
    (antisymmetric : Bool) :
    Matrix ((Fin a × Fin b) × B) ((Fin a × Fin b) × B) ℂ :=
  let diag : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
    Matrix.single (k,n) (k,n) 1 + Matrix.single (l,m) (l,m) 1
  let fwd : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ := Matrix.single (k,n) (l,m) 1
  let rev : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ := Matrix.single (l,m) (k,n) 1
  (1/2 : ℂ) • Matrix.kronecker diag (pureDensity plus + pureDensity minus) +
    (1/2 : ℂ) • (if antisymmetric then
      Matrix.kronecker (fwd-rev) (dyad plus minus - dyad minus plus)
    else Matrix.kronecker (fwd+rev) (pureDensity plus - pureDensity minus))

/-- Reinterpret ((1,2),B) as input 1 and output (2,B), with no transpose. -/
def testerAsCreation {a b : ℕ} {B : Type*}
    (J : Matrix ((Fin a × Fin b) × B) ((Fin a × Fin b) × B) ℂ) :
    Matrix (Fin a × (Fin b × B)) (Fin a × (Fin b × B)) ℂ :=
  J.submatrix (fun p => ((p.1,p.2.1),p.2.2)) (fun p => ((p.1,p.2.1),p.2.2))

/-- Reinterpret ((1,2),B) as input (1,B) and output 2, with no transpose. -/
def testerAsDetection {a b : ℕ} {B : Type*}
    (J : Matrix ((Fin a × Fin b) × B) ((Fin a × Fin b) × B) ℂ) :
    Matrix ((Fin a × B) × Fin b) ((Fin a × B) × Fin b) ℂ :=
  J.submatrix (fun p => ((p.1.1,p.2),p.1.2)) (fun p => ((p.1.1,p.2),p.1.2))

/-- Cyclic subtraction wraps around, rather than truncating. -/
example : (0 - 1 : ZMod 3) = 2 := by decide

/-- The normalization of every dyad specializes to the accepted pure density. -/
example {I : Type*} (v : EuclideanSpace ℂ I) : dyad v v = pureDensity v := rfl

/-- Reindexing for K,L really puts wire B on the input side. -/
example {a b : ℕ} {B : Type*}
    (J : Matrix ((Fin a × Fin b) × B) ((Fin a × Fin b) × B) ℂ)
    (i j : Fin a) (n m : Fin b) (x y : B) :
    testerAsDetection J ((i,x),n) ((j,y),m) = J ((i,n),x) ((j,m),y) := rfl

/-- Zero powers of shift and clock give identity, including d=1. -/
example {d : ℕ} [NeZero d] : weyl (0 : ZMod d) 0 = 1 := by
  simp only [weyl, ZMod.val_zero, pow_zero, one_mul]

/-- The two antisymmetric dyads have a zero diagonal when their labels differ. -/
example {I : Type*} [DecidableEq I] (i j : I) (h : i ≠ j) :
    dyad (ket i) (ket j) i i = 0 := by simp [dyad, ket, h, Ne.symm h]

end QAlgorithms.Papers.Independent.Information100.P34


