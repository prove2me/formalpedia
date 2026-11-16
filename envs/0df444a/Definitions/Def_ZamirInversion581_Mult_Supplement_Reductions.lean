-- Prove2me | Definitions.Def_ZamirInversion581_Mult_Supplement_Reductions
-- name    : ZamirInversion581_Mult_Supplement_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:50:02.79713+00:00
-- url     : https://prove2.me/theorems/3acdbc0c-165a-462f-89fa-f30adc74d448
-- title:
--   Success probabilities and worst-case reduction guarantees
-- statement:
--   For a field-RAM program $A$, success on a matrix means a halting output of the required kind and value: integer one or zero for invertibility, an integer for rank, and a field element for determinant. Every other output counts as wrong. Average success averages this probability over uniform matrices; conditional determinant success $p_n$ averages over uniform invertible matrices.
--
--   Let $\varepsilon,\kappa>0$, $E=\lceil1/\varepsilon\rceil$, $K=\lceil1/\kappa\rceil$, and let $T$ be an arbitrary nonnegative time function. The rank-and-invertibility predicate asserts the existence of two finite programs and dimension thresholds. On every sufficiently large input dimension and every matrix, their success probabilities are at least $1-\kappa$, every run halts, and their respective costs are at most
--   $$
--   c\varepsilon^{-2}(T(n)+n^2)\log(2nEK)^a,\qquad c\varepsilon^{-2}(T(2n)+n^2)\log(2nEK)^a.
--   $$
--   The predicate does not assert either guarantee unless used as a theorem conclusion.
--
--   For coset recovery, a preprocessing program sees only $n,K$ and outputs an explicit subgroup list together with a state. Every run has cost at most $c(T(n)+n^2)\log(2nK)^a$. With probability at least $1-\kappa$ its outcome specifies a proper subgroup $H\le F^\times$ satisfying
--   $$
--   h\mid(q-1),\qquad h<\frac1{p_n-\varepsilon/4}<\min\{q-1,2/\varepsilon\},\quad h=|H|.
--   $$
--   On that same good preprocessing event, for every subsequent target $X$, the recovery program given the state and $X$ halts within the same bound on every run, and with probability at least $1-\kappa$ returns a field element $z$ with $zH=(\det X)H$ and $z^h=(\det X)^h$. The subgroup and state are fixed before any target is seen. The singular coset is $\{0\}$.
--
--   These predicates expose both conclusions and their costs while leaving every reduction program existentially quantified in the theorems. Constants remain explicit parameters so the theorems determine their allowed dependencies.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.3–4, 18, 23–24, Theorems 1.2–1.3, completion and calibration guarantees. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Supplement_Trapdoor

set_option autoImplicit false

namespace ZamirInversion581.Mult.Supplement

/-! Interfaces for the full conclusions of Theorems 1.2 and 1.3 (pp.3–4).
These are predicates on concrete programs, not assumed algorithmic capabilities.
Constants c and a remain arguments so their quantifier placement is visible. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Bit 1 means invertible; rank is an integer output. -/
noncomputable def invertibleAnswer {n : ℕ} (X : Mat F n) : Output F := by
  classical
  exact .index (if X.det = 0 then 0 else 1)

noncomputable def rankAnswer {n : ℕ} (X : Mat F n) : Output F := .index (X.rank : ℤ)

def detAnswer {n : ℕ} (X : Mat F n) : Output F := .field X.det

noncomputable def avgSuccess (P : Program F) (target : ∀ n, Mat F n → Output F) (n : ℕ) : ℝ :=
  unifMean (fun X : Mat F n => accepts P (matrixInput n [n] X) (fun o => o = target n X))

noncomputable def invertibleDetSuccess (D : Program F) (n : ℕ) : ℝ :=
  unifMean (fun Y : GL (Fin n) F =>
    accepts D (matrixInput n [n] (Y : Mat F n)) (fun o => o = .field (Y : Mat F n).det))

/-- The two baselines in Theorem 1.2 are deliberately different. -/
def AboveBaseline (A : Program F) (ε : ℝ) (N₀ : ℕ) : Prop :=
  (∀ n ≥ N₀, max (singularity F n) (1 - singularity F n) + ε ≤
    avgSuccess A (fun _ X => invertibleAnswer X) n) ∨
  (∀ n ≥ N₀, rankBaseline F n + ε ≤ avgSuccess A (fun _ X => rankAnswer X) n)

noncomputable def reductionBudget (c ε κ : ℝ) (a n : ℕ) (t : NNReal) : ℝ :=
  c * ε⁻¹ ^ 2 * (t + (n : ℝ) ^ 2) *
    Real.log (2 * (n : ℝ) * (⌈1 / ε⌉₊ : ℕ) * (⌈1 / κ⌉₊ : ℕ)) ^ a

/-- A worst-case decision program and a worst-case exact-rank program, each uniform in n.
The threshold and program may depend on the earlier parameters, not on the input matrix. -/
def RankAndInvertibility (c : ℝ) (a : ℕ) (ε κ : ℝ) (T : ℕ → NNReal) : Prop :=
  (∃ (B : Program F) (n₀ : ℕ), ∀ n ≥ n₀, ∀ X : Mat F n,
    let σ := matrixInput n [n, ⌈1 / ε⌉₊, ⌈1 / κ⌉₊] X
    HaltWithin B σ (reductionBudget c ε κ a n (T n)) ∧
    1 - κ ≤ accepts B σ (fun o => o = invertibleAnswer X)) ∧
  (∃ (B : Program F) (n₀ : ℕ), ∀ n ≥ n₀, ∀ X : Mat F n,
    let σ := matrixInput n [n, ⌈1 / ε⌉₊, ⌈1 / κ⌉₊] X
    HaltWithin B σ (reductionBudget c ε κ a n (T (2 * n))) ∧
    1 - κ ≤ accepts B σ (fun o => o = rankAnswer X))

noncomputable def cosetBudget (c κ : ℝ) (a n : ℕ) (t : NNReal) : ℝ :=
  c * (t + (n : ℝ) ^ 2) * Real.log (2 * (n : ℝ) * (⌈1 / κ⌉₊ : ℕ)) ^ a

/-- The recovery program sees the preprocessing state, then the target matrix.
The subgroup list is part of the state passed to recovery. -/
def recoveryInput (n K : ℕ) (hs τ : List F) (X : Mat F n) : Config F :=
  blockInput [n, K, hs.length, τ.length] (hs ++ τ ++ matrixBlock X)

/-- An explicit element-list encoding, permitting arbitrary enumeration order. -/
def encodesSubgroup (hs : List F) (H : Subgroup Fˣ) : Prop :=
  ∀ x : F, x ∈ hs ↔ ∃ h : H, (h.val : F) = x

/-- One good calibration event covers every subsequent input. No target is given to Pre.
Both the subgroup/coset and the equivalent power output guarantees are retained. -/
def CosetRecovery (c : ℝ) (a : ℕ) (ε κ : ℝ) (D : Program F) (T : ℕ → NNReal) : Prop :=
  ∃ (Pre Rec : Program F) (n₀ : ℕ), ∀ n ≥ n₀,
    let σ₀ : Config F := blockInput [n, ⌈1 / κ⌉₊] []
    let budget := cosetBudget c κ a n (T n)
    HaltWithin Pre σ₀ budget ∧
    1 - κ ≤ eventProb (finalLaw Pre σ₀) (fun σ =>
      ∃ (hs τ : List F) (H : Subgroup Fˣ),
        σ.status = .done (some (.blocks hs τ)) ∧ encodesSubgroup hs H ∧
        H ≠ ⊤ ∧
        (Nat.card H : ℝ) < 1 / (invertibleDetSuccess D n - ε / 4) ∧
        1 / (invertibleDetSuccess D n - ε / 4) <
          min (Fintype.card F - 1 : ℝ) (2 / ε) ∧
        Nat.card H ∣ Fintype.card F - 1 ∧
        ∀ X : Mat F n,
          let input := recoveryInput n ⌈1 / κ⌉₊ hs τ X
          HaltWithin Rec input budget ∧
          1 - κ ≤ accepts Rec input (fun o => ∃ z : F,
            o = .field z ∧ fieldCoset H z = fieldCoset H X.det ∧
            z ^ Nat.card H = X.det ^ Nat.card H))

end ZamirInversion581.Mult.Supplement


