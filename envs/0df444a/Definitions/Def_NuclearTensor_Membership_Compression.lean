-- Prove2me | Definitions.Def_NuclearTensor_Membership_Compression
-- name    : NuclearTensor_Membership_Compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:15:26.243122+00:00
-- url     : https://prove2.me/theorems/d7b45097-7961-4adf-af82-30d08a1624c2
-- title:
--   Prefix spectral compression and discarded messages
-- statement:
--   At each prefix cut, retain precisely the left singular directions with singular value strictly greater than $\eta$. Set $V_0=\mathbb R$, $T_0=M$, and compute
--   $$T_{j+1}=(U_{j+1}^{\dagger}\otimes I)T_j,\qquad p_0=1,\quad p_{j+1}=U_{j+1}^{\dagger}(p_j\otimes x_{j+1}).$$
--   The definition records the actual ordinary-SVD selection and contraction. It does not assume a rank bound, a compression error, or an energy bound. Discarded tensors are $(I-UU^\dagger)T$ and discarded messages are $p_j\otimes x_{j+1}-U_{j+1}p_{j+1}$. Finite serialization contains every relevant rank, embedding, and intermediate tensor. This interface supplies the common objects for all compression results.
--
--   **Formalization Note** The record uses natural indices for convenience, but only the first $k$ layers and $k-1$ maps are queried or serialized. Its norm is Euclidean, not the tensor projective norm.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp.10–14, Lemma 3.2, Algorithm 1, Equation (4), and Theorem 3.1

import Definitions.Def_NuclearTensor_Membership_Computation

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NuclearTensor.Membership

def flatten {a b : ℕ} (M : Mat a b) : Vec (a * b) :=
  WithLp.toLp 2 (fun i => matEntry M (i.val / b) (i.val % b))

def contract {a b c : ℕ} (U : Mat a b) (T : Vec (a * c)) : Vec (b * c) :=
  WithLp.toLp 2 (fun i => ∑ t : Fin a,
    matEntry U t.val (i.val / c) * entry T (t.val * c + i.val % c))

def expand {a b c : ℕ} (U : Mat a b) (T : Vec (b * c)) : Vec (a * c) :=
  WithLp.toLp 2 (fun i => ∑ t : Fin b,
    matEntry U (i.val / c) t.val * entry T (t.val * c + i.val % c))

def kept {a b : ℕ} {M : Mat a b} (D : SVDResult a b M) (η : ℝ) : List (Fin (min a b)) :=
  ((Finset.univ : Finset (Fin (min a b))).filter (fun t => η < D.singular t)).sort (· ≤ ·)

def selectedEntry {a b : ℕ} {M : Mat a b} (D : SVDResult a b M)
    (η : ℝ) (i t : ℕ) : ℝ :=
  if h : t < (kept D η).length then matEntry D.left i ((kept D η)[t]).val else 0

/-- Finite output arrays at layers 0,...,k-1. Fields at later natural indices are
irrelevant and are never serialized or queried. r₀=1 is asserted by Algorithm 1. -/
structure PrefixData (ds : List ℕ) where
  rank : ℕ → ℕ
  embedding : (j : ℕ) → Mat (rank j * ds.getD j 0) (rank (j + 1))
  tensor : (j : ℕ) → Vec (rank j * (ds.drop j).prod)

def cutMatrix {ds : List ℕ} (C : PrefixData ds) (j : ℕ) :
    Mat (C.rank j * ds.getD j 0) ((ds.drop (j + 1)).prod) :=
  fun a b => entry (C.tensor j) (a.val * (ds.drop (j + 1)).prod + b.val)

/-- Exact operational description of Algorithm 1: full ordinary SVD at each cut,
retain precisely singular values strictly greater than η, and contract by U†.
No approximation or rank bound is assumed in this predicate. -/
def algorithm1 (σ : Spectral) {ds : List ℕ} (η : ℝ) (M : Tensor ds)
    (C : PrefixData ds) : Prop :=
  C.rank 0 = 1 ∧ (∀ i : Fin ds.prod, entry (C.tensor 0) i.val = M i) ∧
  ∀ j, j + 1 < ds.length →
    let D := σ _ _ (cutMatrix C j)
    C.rank (j + 1) = (kept D η).length ∧
    (∀ i t, C.embedding j i t = selectedEntry D η i.val t.val) ∧
    C.tensor (j + 1) = contract (C.embedding j) (flatten (cutMatrix C j))

def discardedTensor {ds : List ℕ} (C : PrefixData ds) (j : ℕ) :
    Vec ((C.rank j * ds.getD j 0) * (ds.drop (j + 1)).prod) :=
  flatten (cutMatrix C j) -
    expand (C.embedding j) (contract (C.embedding j) (flatten (cutMatrix C j)))

/-- All four source clauses, with the isometry inherited from spectral truncation. -/
def compressionInvariants {ds : List ℕ} (η : ℝ) (C : PrefixData ds) : Prop :=
  ∀ j, j + 1 < ds.length →
    flatten (cutMatrix C j) = expand (C.embedding j) (C.tensor (j + 1)) + discardedTensor C j ∧
    ‖C.tensor (j + 1)‖ ≤ 1 ∧
    (C.rank (j + 1) : ℝ) ≤ η ^ (-2 : ℤ) ∧
    (∀ (u : Vec (C.rank j * ds.getD j 0)) (v : Vec ((ds.drop (j + 1)).prod)),
      |inner ℝ (discardedTensor C j) (outer u v)| ≤ η * (‖u‖ * ‖v‖)) ∧
    orthonormalColumns (C.embedding j)

/-- Equation (4), with p₀=1 and zero-based local coordinates. -/
def message {ds : List ℕ} (C : PrefixData ds) (x : Tuple ds) : (j : ℕ) → Vec (C.rank j)
  | 0 => WithLp.toLp 2 (fun _ => 1)
  | j + 1 => mtv (C.embedding j) (outer (message C x j) (x j))

def discardedMessage {ds : List ℕ} (C : PrefixData ds) (x : Tuple ds) (j : ℕ) :
    Vec (C.rank j * ds.getD j 0) :=
  outer (message C x j) (x j) - mv (C.embedding j) (message C x (j + 1))

def terminalProduct {ds : List ℕ} (C : PrefixData ds) (x : Tuple ds) :
    Vec (C.rank (ds.length - 1) * (ds.drop (ds.length - 1)).prod) :=
  WithLp.toLp 2 (fun i => entry (message C x (ds.length - 1))
    (i.val / (ds.drop (ds.length - 1)).prod) *
    entry (x (ds.length - 1)) (i.val % (ds.drop (ds.length - 1)).prod))

def productTestError {ds : List ℕ} (M : Tensor ds) (C : PrefixData ds) (x : Tuple ds) : ℝ :=
  |inner ℝ M (product x) - inner ℝ (C.tensor (ds.length - 1)) (terminalProduct C x)|

def encodePrefixIntegers {ds : List ℕ} (C : PrefixData ds) : List ℤ :=
  (List.range ds.length).map fun j => (C.rank j : ℤ)

def encodePrefixReals {ds : List ℕ} (C : PrefixData ds) : List ℝ :=
  ((List.range (ds.length - 1)).map fun j => encodeMat (C.embedding j)).flatten ++
    ((List.range ds.length).map fun j => encodeVec (C.tensor j)).flatten

def outputsPrefix {ds : List ℕ} (s : Configuration) (C : PrefixData ds) : Prop :=
  outputIntegers s = encodePrefixIntegers C ∧ outputReals s = encodePrefixReals C

def inputSize (ds : List ℕ) : ℕ := 1 + ds.prod + ds.sum + ds.length

end NuclearTensor.Membership


