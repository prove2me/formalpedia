-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_Problem
-- name    : BooleanHiddenPartition_LowerBounds_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:12.698592+00:00
-- url     : https://prove2.me/theorems/7775a6bb-094c-4b8e-a48a-f4de19f8d63d
-- title:
--   Ordered-block hidden partition promise and correlated hard distribution
-- statement:
--   A layout consists of positive k,n,m and alpha in (0,1) with k m = alpha n. Alice receives an n-bit cube point x. Bob receives a permutation sigma and m labels y. Block i has entries x(sigma(k i+j)) in the order j=0,...,k−1; no symmetry of f is assumed. The promise is either y_i=f(x^i) for all i (YES) or y_i=−f(x^i) for all i (NO). ClassicalSolves and QuantumSolves require success at least 2/3 on every promised input, with exactly the supplied protocol cost.
--
--   $$Q_\sigma(x)=2^{km-n}\prod_{i=0}^{m-1}q(x^i).$$
--
--   The hard law samples sigma uniformly, x according to this sigma-dependent mass, and an independent fair hidden bit to choose YES or NO labels. hardSuccess is the actual protocol success averaged under this law. The Boolean hidden bit true denotes YES; this choice is independent of the convention true=−1 for cube coordinates. General randomized encoders and decoders see only their own inputs. The exact equality in the layout preserves all admissible source lengths without rounding.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), pp. 3, 12, 14–15, definitions and conventions.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Scalar
import Definitions.Def_BooleanHiddenPartition_LowerBounds_OneWay

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Ordered blocks with exactly the admissible positive source parameters. -/
structure Layout (k n m : ℕ) (α : ℝ) where
  arity_pos : 0 < k
  length_pos : 0 < n
  blocks_pos : 0 < m
  alpha_pos : 0 < α
  alpha_lt : α < 1
  size_eq : (k : ℝ) * m = α * n

/-- The coordinate map is computed from the source's ordered blocks. -/
def blockPosition {k n m : ℕ} {α : ℝ} (L : Layout k n m α)
    (i : Fin m) (j : Fin k) : Fin n :=
  ⟨k * i.val + j.val, by
    have h : k * m < n := by
      have hr : (k : ℝ) * m < n := by
        rw [L.size_eq]
        have hn : (0 : ℝ) < n := by exact_mod_cast L.length_pos
        nlinarith [L.alpha_lt]
      exact_mod_cast hr
    have hi := i.isLt
    have hj := j.isLt
    nlinarith⟩

def block {k n m : ℕ} {α : ℝ} (L : Layout k n m α)
    (σ : Equiv.Perm (Fin n)) (x : Cube n) (i : Fin m) : Cube k :=
  fun j => x (σ (blockPosition L i j))

abbrev BobInput (n m : ℕ) := Equiv.Perm (Fin n) × Cube m

/-- True is YES; false is NO. The hidden bit is not an input to the encoder. -/
def Promised {k n m : ℕ} {α : ℝ} (L : Layout k n m α) (f : Cube k → Bool)
    (x : Cube n) (B : BobInput n m) (b : Bool) : Prop :=
  ∀ i, B.2 i = if b then f (block L B.1 x i) else !(f (block L B.1 x i))

def labels {k n m : ℕ} {α : ℝ} (L : Layout k n m α) (f : Cube k → Bool)
    (σ : Equiv.Perm (Fin n)) (x : Cube n) (b : Bool) : Cube m :=
  fun i => if b then f (block L σ x i) else !(f (block L σ x i))

def correctProb (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def ClassicalSolves {k n m c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (P : ClassicalProtocol (Cube n) (BobInput n m) c) : Prop :=
  ∀ x B b, Promised L f x B b → (2 / 3 : ℝ) ≤ correctProb (classicalAccept P x B) b

def QuantumSolves {k n m c : ℕ} {α : ℝ} {Ω : Type} [MeasurableSpace Ω]
    (L : Layout k n m α) (f : Cube k → Bool)
    (P : QuantumProtocol (Cube n) (BobInput n m) Ω c) : Prop :=
  ∀ x B b, Promised L f x B b →
    (2 / 3 : ℝ) ≤ correctProb (randomizedQuantumAccept P x B) b

/-- Counting mass Q_σ, not the uniform law independent of σ. -/
def hardMass {k n m : ℕ} {α : ℝ} (L : Layout k n m α) (q : Cube k → ℝ)
    (σ : Equiv.Perm (Fin n)) (x : Cube n) : ℝ :=
  (2 : ℝ) ^ (k * m) / (2 : ℝ) ^ n * ∏ i, q (block L σ x i)

def permMean {n : ℕ} (h : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ * ∑ σ, h σ

/-- Success under uniform σ, x~Q_σ, independent fair hidden bit. -/
def hardSuccess {k n m : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (q : Cube k → ℝ) (accept : Cube n → BobInput n m → ℝ) : ℝ :=
  permMean (fun σ => ∑ x, hardMass L q σ x *
    ((correctProb (accept x (σ, labels L f σ x true)) true +
      correctProb (accept x (σ, labels L f σ x false)) false) / 2))

end

end BooleanHiddenPartition.LowerBounds


