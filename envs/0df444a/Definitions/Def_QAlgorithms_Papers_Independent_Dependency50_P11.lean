-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11
-- name    : QAlgorithms_Papers_Independent_Dependency50_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:32:51.278972+00:00
-- url     : https://prove2.me/theorems/d3624676-914c-40cd-816c-ab79297b34ab
-- title:
--   Definitions for Repeatable quantum memory channels
-- statement:
--   The objects the formalized statements of *Repeatable quantum memory channels* (arXiv:0808.3851) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `vonNeumannEntropy`: PDF pp.1,4: the accepted von Neumann entropy, in nats, including singular states.
--   - `MemoryDevice`: PDF pp.2–3, (2.1)–(2.3): one fixed unitary and one actual normalized initializer. No reset map, fresh bath, input-dependent unitary, or horizon-dependent field occurs.
--   - `jointStep`: PDF p.2, (2.1)–(2.2): joint state after a single collision, memory first.
--   - `memoryState`: PDF p.2, (2.3): memory after n collisions. Its fresh inputs are product inputs; old outputs may be correlated with it. Lean index zero is the paper's xi_1.
--   - `outputState`: PDF pp.2–3: the marginal output of use j+1, after the actual preceding history.
--   - `RepeatableFor`: PDF pp.3–4: the first n output marginals implement E for every product history. An infinite input sequence is only a convenient extension of each finite history; output j depends exclusively on inputs 0 through j. At n=0 the condition is empty.
--   - `Repeatable`: PDF p.3: a single device works at all horizons.
--   - `HasFiniteRepeatableImplementation`: PDF pp.3–4: existence of one finite memory, fixed before every horizon/input.
--   - `IsRandomUnitary`: PDF p.3, Theorem 1: a finite random-unitary decomposition on all operators.
--   - `IsUnital`: PDF pp.4–5: unital means the literal operator identity E(I)=I.
--   - `totalMixture`: PDF p.4: normalized total mixture; used only for d>0. At d=0 this is the zero operator, not a state. All uses below have a nonzero dimension guard.
--   - `entropyDecrease`: PDF p.4, (3.7): signed entropy decrease; it can be negative.
--   - `maxEntropyDecrease`: PDF p.4: Delta_max, not separately defined in print, is the maximum of the preceding Delta over density inputs. For CPTP E and d>0, the domain is nonempty compact and this continuous function is bounded and attains its supremum. Outside that regime sSup has Lean's default behavior; no result uses it there.
--   - `firstBlockMean`: PDF p.3: the mean of a first block of N equal probe inputs. N>0 is a theorem guard.
--   - `secondCollision`: PDF p.5: the same second collision, lifted past the retained first output. Its Kronecker delta keeps all off-diagonal blocks of that first output.
--   - `twoOutputState`: PDF p.5: two-output joint state from the actual unitary experiment with initializer xi and independent rho, sigma, retaining their possible correlations.
--   - `controlledFamily`: PDF p.3, controlled-unitary construction: diagonal memory controls the family.
--   - `qubitZ`: PDF pp.3,5: coordinate adapter for the accepted Pauli Z on the Fin 2 register.
--   - `sharedControlledZ`: PDF pp.3,5: the shared-bit controlled I/Z interaction used for the correlation witness.
--   - `dephasingChannel`: PDF pp.3,5: the channel of a fair shared I/Z control bit, extended to all operators.
--   - `signDensity`: PDF p.5: density matrices of the plus/minus qubit states, without square-root conventions.
--   - `correlatedSigns`: PDF p.5: the correlated fair mixture of two pluses or two minuses.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, https://arxiv.org/abs/0808.3851v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

/-!
Rybar and Ziman, Repeatable quantum memory channels, arXiv:0808.3851v1.
Finite, nonzero registers; memory is always the first tensor factor.
Repeatability concerns individual marginals on arbitrary product-input histories,
without resetting or inserting extra environments. Entropies use natural logs.
The accepted P23 operator alias and P39 entropy definition are reused directly.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- PDF pp.1,4: the accepted von Neumann entropy, in nats, including singular states. -/
abbrev vonNeumannEntropy {A : Type*} [Fintype A] [DecidableEq A]
    (rho : Matrix A A ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P39.quantumEntropy 1 rho

/-- PDF pp.2–3, (2.1)–(2.3): one fixed unitary and one actual normalized initializer.
No reset map, fresh bath, input-dependent unitary, or horizon-dependent field occurs. -/
structure MemoryDevice (d m : ℕ) where
  memory_pos : 0 < m
  unitary : Matrix.unitaryGroup (Fin m × Fin d) ℂ
  initial : Operator m
  initial_density : IsDensityMatrix initial

/-- PDF p.2, (2.1)–(2.2): joint state after a single collision, memory first. -/
def jointStep {d m : ℕ} (D : MemoryDevice d m) (xi : Operator m) (rho : Operator d) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ :=
  (D.unitary : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) *
    Matrix.kronecker xi rho *
      (D.unitary : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)ᴴ

/-- PDF p.2, (2.3): memory after n collisions. Its fresh inputs are product inputs;
old outputs may be correlated with it. Lean index zero is the paper's xi_1. -/
def memoryState {d m : ℕ} (D : MemoryDevice d m) (input : ℕ → Operator d) :
    ℕ → Operator m
  | 0 => D.initial
  | n + 1 => traceRight (jointStep D (memoryState D input n) (input n))

/-- PDF pp.2–3: the marginal output of use j+1, after the actual preceding history. -/
def outputState {d m : ℕ} (D : MemoryDevice d m) (input : ℕ → Operator d) (j : ℕ) :
    Operator d :=
  traceLeft (jointStep D (memoryState D input j) (input j))

/-- PDF pp.3–4: the first n output marginals implement E for every product history.
An infinite input sequence is only a convenient extension of each finite history;
output j depends exclusively on inputs 0 through j. At n=0 the condition is empty. -/
def RepeatableFor {d m : ℕ} (D : MemoryDevice d m)
    (E : Superop (Fin d) (Fin d)) (n : ℕ) : Prop :=
  ∀ input : ℕ → Operator d, (∀ j, IsDensityMatrix (input j)) →
    ∀ j : ℕ, j < n → outputState D input j = E (input j)

/-- PDF p.3: a single device works at all horizons. -/
def Repeatable {d m : ℕ} (D : MemoryDevice d m)
    (E : Superop (Fin d) (Fin d)) : Prop :=
  ∀ n : ℕ, RepeatableFor D E n

/-- PDF pp.3–4: existence of one finite memory, fixed before every horizon/input. -/
def HasFiniteRepeatableImplementation {d : ℕ}
    (E : Superop (Fin d) (Fin d)) : Prop :=
  ∃ m : ℕ, ∃ D : MemoryDevice d m, Repeatable D E

/-- PDF p.3, Theorem 1: a finite random-unitary decomposition on all operators. -/
def IsRandomUnitary {d : ℕ} (E : Superop (Fin d) (Fin d)) : Prop :=
  ∃ k : ℕ, ∃ p : Fin k → ℝ,
    ∃ V : Fin k → Matrix.unitaryGroup (Fin d) ℂ,
      (∀ j, 0 ≤ p j ∧ p j ≤ 1) ∧ (∑ j, p j) = 1 ∧
        ∀ X : Operator d, E X = ∑ j, (p j : ℂ) •
          ((V j : Operator d) * X * (V j : Operator d)ᴴ)

/-- PDF pp.4–5: unital means the literal operator identity E(I)=I. -/
def IsUnital {d : ℕ} (E : Superop (Fin d) (Fin d)) : Prop := E 1 = 1

/-- PDF p.4: normalized total mixture; used only for d>0. At d=0 this is the zero
operator, not a state. All uses below have a nonzero dimension guard. -/
def totalMixture (d : ℕ) : Operator d := ((d : ℂ)⁻¹) • 1

/-- PDF p.4, (3.7): signed entropy decrease; it can be negative. -/
def entropyDecrease {d : ℕ} (E : Superop (Fin d) (Fin d)) (rho : Operator d) : ℝ :=
  vonNeumannEntropy rho - vonNeumannEntropy (E rho)

/-- PDF p.4: Delta_max, not separately defined in print, is the maximum of the
preceding Delta over density inputs. For CPTP E and d>0, the domain is nonempty
compact and this continuous function is bounded and attains its supremum.
Outside that regime sSup has Lean's default behavior; no result uses it there. -/
def maxEntropyDecrease {d : ℕ} (E : Superop (Fin d) (Fin d)) : ℝ :=
  sSup {t : ℝ | ∃ rho : Operator d, IsDensityMatrix rho ∧ t = entropyDecrease E rho}

/-- PDF p.3: the mean of a first block of N equal probe inputs. N>0 is a theorem guard. -/
def firstBlockMean {d m : ℕ} (D : MemoryDevice d m) (rho : Operator d) (N : ℕ) :
    Operator d :=
  ((N : ℂ)⁻¹) • ∑ j ∈ Finset.range N, outputState D (fun _ => rho) j

/-- PDF p.5: the same second collision, lifted past the retained first output.
Its Kronecker delta keeps all off-diagonal blocks of that first output. -/
def secondCollision {d m : ℕ} (D : MemoryDevice d m) :
    Matrix (Fin m × (Fin d × Fin d)) (Fin m × (Fin d × Fin d)) ℂ :=
  Matrix.of fun p q => if p.2.1 = q.2.1 then
    (D.unitary : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
      (p.1, p.2.2) (q.1, q.2.2) else 0

/-- PDF p.5: two-output joint state from the actual unitary experiment with
initializer xi and independent rho, sigma, retaining their possible correlations. -/
def twoOutputState {d m : ℕ} (D : MemoryDevice d m) (rho sigma : Operator d) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  let X : Matrix (Fin m × (Fin d × Fin d)) (Fin m × (Fin d × Fin d)) ℂ :=
    Matrix.of fun p q =>
      Matrix.kronecker (jointStep D D.initial rho) sigma
        ((p.1, p.2.1), p.2.2) ((q.1, q.2.1), q.2.2)
  traceLeft (secondCollision D * X * (secondCollision D)ᴴ)

/-- PDF p.3, controlled-unitary construction: diagonal memory controls the family. -/
def controlledFamily {d k : ℕ} (V : Fin k → Operator d) :
    Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.1 p.2 q.2 else 0

/-- PDF pp.3,5: coordinate adapter for the accepted Pauli Z on the Fin 2 register. -/
def qubitZ : Operator 2 :=
  Matrix.of fun i j => pauliZ (decide (i = 1)) (decide (j = 1))

/-- PDF pp.3,5: the shared-bit controlled I/Z interaction used for the correlation witness. -/
def sharedControlledZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  controlledFamily (fun j : Fin 2 => if j = 0 then (1 : Operator 2) else qubitZ)

/-- PDF pp.3,5: the channel of a fair shared I/Z control bit, extended to all operators. -/
def dephasingChannel : Superop (Fin 2) (Fin 2) :=
  fun X => (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • (qubitZ * X * qubitZᴴ)

/-- PDF p.5: density matrices of the plus/minus qubit states, without square-root conventions. -/
def signDensity (minus : Bool) : Operator 2 :=
  Matrix.of fun i j => if i = j then 1 / 2 else if minus then -(1 / 2) else 1 / 2

/-- PDF p.5: the correlated fair mixture of two pluses or two minuses. -/
def correlatedSigns : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • Matrix.kronecker (signDensity false) (signDensity false) +
    (1 / 2 : ℂ) • Matrix.kronecker (signDensity true) (signDensity true)

/-! Sanity instances for the paper-local semantics (no theorem proofs). -/

example : Nonempty (MemoryDevice 1 1) := by
  refine ⟨{ memory_pos := by norm_num
            unitary := 1
            initial := 1
            initial_density := ⟨Matrix.PosSemidef.one, ?_⟩ }⟩
  simp [Matrix.trace]

example {d m : ℕ} (D : MemoryDevice d m) (xi : Operator m) (rho : Operator d)
    (hU : (D.unitary : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) = 1) :
    jointStep D xi rho = Matrix.kronecker xi rho := by
  simp [jointStep, hU]

example {d m : ℕ} (D : MemoryDevice d m) (input : ℕ → Operator d) :
    memoryState D input 0 = D.initial := by rfl

example {d m : ℕ} (D : MemoryDevice d m) (input : ℕ → Operator d) (n : ℕ) :
    memoryState D input (n + 1) =
      traceRight (jointStep D (memoryState D input n) (input n)) := by rfl

example {d m : ℕ} (D : MemoryDevice d m) (E : Superop (Fin d) (Fin d)) :
    RepeatableFor D E 0 := by
  intro input hinput j hj
  exact False.elim (Nat.not_lt_zero j hj)

example {d : ℕ} (rho : Operator d) : entropyDecrease (fun X => X) rho = 0 := by
  simp [entropyDecrease]

example : totalMixture 1 = (1 : Operator 1) := by simp [totalMixture]

example {d m : ℕ} (D : MemoryDevice d m) (rho : Operator d) :
    firstBlockMean D rho 1 = outputState D (fun _ => rho) 0 := by
  simp [firstBlockMean]

example {d m : ℕ} (D : MemoryDevice d m)
    (p q : Fin m × (Fin d × Fin d)) (h : p.2.1 ≠ q.2.1) :
    secondCollision D p q = 0 := by simp [secondCollision, h]

example : qubitZ 0 0 = 1 ∧ qubitZ 1 1 = -1 := by
  norm_num [qubitZ, pauliZ, Matrix.diagonal]

example : sharedControlledZ (1, 1) (1, 1) = -1 := by
  norm_num [sharedControlledZ, controlledFamily, qubitZ, pauliZ, Matrix.diagonal]

example : signDensity false 0 1 = (1 / 2 : ℂ) ∧
    signDensity true 0 1 = -(1 / 2 : ℂ) := by
  norm_num [signDensity]

end QAlgorithms.Papers.Independent.Dependency50.P11


