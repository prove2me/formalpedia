-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_Supplement_BitImplementation
-- name    : UniformPrecSched_Makespan_Supplement_BitImplementation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:23:13.724002+00:00
-- url     : https://prove2.me/theorems/0dd00359-19f9-4623-aff3-1cc1ca48164e
-- title:
--   Binary implementation and the polynomial-time approximation property
-- statement:
--   Rational data are interpreted in the existing real scheduling model and encoded by binary numerators, positive denominators, dimensions and the full precedence matrix. Each integer uses a unary bit-length prefix followed by its binary digits, so encoded magnitude is logarithmic in value. Outputs encode one original machine index and one rational start per job.
--
--   A finite Post–Turing machine uses Mathlib's ordinary move/write tape transitions with a fixed finite state set and a separate blank symbol. A polynomial implementation must halt on every valid input of bit length $B$ in
--
--   $$t\le a(B+1)^d$$
--
--   tape steps and leave an output satisfying the actual interval-LP pipeline relation. The fixed machine and fixed natural constants $a,d$ precede all inputs. LP solving, sorting, arithmetic and list scheduling are all charged tape computations, with no optimizer primitive.
--
--   The approximation property additionally requires an output on every real instance, feasibility and release-date compliance of every pipeline output, and weighted cost at most $16\rho_c(I)$ times that of every feasible original-instance comparator. Here $\rho_c$ is the minimum ratio defined in the weighted layer. This performance property is asserted in the theorem's conclusion; it is never assumed by a run. Standard finite bit complexity is asserted for rational encodings while correctness of the same mathematical operations covers all real data.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 1 (PDF 1), definition of approximation algorithm; pp. 12–14 (PDF 12–14), algorithm; p. 14 (PDF 14), Theorem 4.1

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Supplement_HalfInterval

namespace UniformPrecSched.Makespan.Supplement

/-- Binary finite-input view of the same scheduling data. This is an encoding layer,
not a second scheduling model. Real correctness remains unrestricted. -/
structure RationalInput where
  n : ℕ
  m : ℕ
  p : Fin n → ℚ
  s : Fin m → ℚ
  before : Fin n → Fin n → Bool
  r : Fin n → ℚ
  w : Fin n → ℚ
  m_pos : 0 < m
  p_pos : ∀ j, 0 < p j
  s_pos : ∀ i, 0 < s i
  irrefl : ∀ j, before j j = false
  trans : ∀ i j k, before i j = true → before j k = true → before i k = true
  r_nonneg : ∀ j, 0 ≤ r j
  w_nonneg : ∀ j, 0 ≤ w j

/-- Interpret rationally encoded jobs in the immutable published real model. -/
def RationalInput.instance (P : RationalInput) : Instance P.n P.m where
  p := fun j => P.p j
  s := fun i => P.s i
  prec := fun i j => P.before i j = true
  m_pos := P.m_pos
  p_pos := by intro j; exact_mod_cast P.p_pos j
  s_pos := by intro i; exact_mod_cast P.s_pos i
  prec_irrefl := by intro j; simp [P.irrefl j]
  prec_trans := P.trans

def RationalInput.releases (P : RationalInput) : ReleaseWeights P.n where
  r := fun j => P.r j
  w := fun j => P.w j
  r_nonneg := by intro j; exact_mod_cast P.r_nonneg j
  w_nonneg := by intro j; exact_mod_cast P.w_nonneg j

/-- Self-delimited binary natural numbers: unary bit length then a separator and
little-endian binary digits. The code length is O(log(v+1)), not O(v). -/
def encodeNat (v : ℕ) : List Bool :=
  List.replicate (Nat.bits v).length true ++ [false] ++ Nat.bits v

/-- Reduced rational: sign, absolute numerator and positive denominator, in binary. -/
def encodeRat (v : ℚ) : List Bool :=
  [decide (v.num < 0)] ++ encodeNat v.num.natAbs ++ encodeNat v.den

/-- n,m, processing requirements, machine speeds, the full precedence matrix,
release dates and weights. Every numeric magnitude contributes its binary length. -/
def encodeInput (P : RationalInput) : List Bool :=
  encodeNat P.n ++ encodeNat P.m ++
  (List.ofFn P.p).flatMap encodeRat ++ (List.ofFn P.s).flatMap encodeRat ++
  (List.ofFn fun i => List.ofFn (P.before i)).flatten ++
  (List.ofFn P.r).flatMap encodeRat ++ (List.ofFn P.w).flatMap encodeRat

/-- Output has one original-machine index and rational start time per job. -/
def encodeSchedule {n m : ℕ} (μ : Fin n → Fin m) (S : Fin n → ℚ) : List Bool :=
  (List.ofFn fun j => encodeNat (μ j).val ++ encodeRat (S j)).flatten

/-- A finite Post-Turing transition table from Mathlib, with binary symbols and
a distinct blank. No LP, arithmetic, or scheduling operation is a unit-cost instruction. -/
abbrev SchedulingMachine (q : ℕ) := Turing.TM0.Machine (Option Bool) (Fin (q + 1))

/-- Exactly t ordinary tape steps from the encoded input; halting is not padded
with free transitions. -/
def machineAfter {q : ℕ} (A : SchedulingMachine q) (input : List Bool) :
    ℕ → Option (Turing.TM0.Cfg (Option Bool) (Fin (q + 1)))
  | 0 => some (Turing.TM0.init (input.map some))
  | t + 1 => (machineAfter A input t).bind (Turing.TM0.step A)

/-- Operational polynomial time in the standard bit encoding. One fixed finite
transition table and one fixed polynomial work on all valid rational inputs. The
halted output must satisfy the actual LP/filter/fragment/concatenation specification.
Approximation and running-time guarantees are not assumptions of that specification.
This statement charges LP solving and every other internal computation as tape steps. -/
def ImplementsPipelineInPolyTime {q : ℕ} (A : SchedulingMachine q) (a d : ℕ) : Prop :=
  ∀ P : RationalInput, ∃ (t : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q + 1)))
      (μ : Fin P.n → Fin P.m) (S : Fin P.n → ℚ),
    t ≤ a * ((encodeInput P).length + 1) ^ d ∧
    machineAfter A (encodeInput P) t = some cfg ∧
    Turing.TM0.step A cfg = none ∧
    cfg.Tape.right₀ = Turing.ListBlank.mk ((encodeSchedule μ S).map some) ∧
    IsPipelineOutput P.instance P.releases μ (fun j => (S j : ℝ))

/-- A polynomial-time approximation algorithm in the sense of §1, p. 1, PDF 1,
with the specific ratio of Theorem 4.1, p. 14, PDF 14. This is the property asserted
in the conclusion, never a hypothesis on a pipeline run. All real data have outputs;
every admissible output is feasible and meets the guarantee, while the one finite
machine implements the same pipeline on the standard rational bit encoding. -/
def IsApproximationAlgorithm {q : ℕ} (c : ℝ) (A : SchedulingMachine q) (a d : ℕ) : Prop :=
  ImplementsPipelineInPolyTime A a d ∧
  ∀ (n m : ℕ) (I : Instance n m) (R : ReleaseWeights n),
    (∃ σ : Schedule I, IsPipelineOutput I R σ.μ σ.S) ∧
    (∀ (μ : Fin n → Fin m) (S : Fin n → ℝ), IsPipelineOutput I R μ S →
      ∃ σ : Schedule I, σ.μ = μ ∧ σ.S = S ∧ RespectsRelease R σ ∧
        ∀ σ' : Schedule I, RespectsRelease R σ' →
          weightedCost R σ ≤ 16 * approximationRatio c I * weightedCost R σ')

end UniformPrecSched.Makespan.Supplement


