-- Prove2me | Definitions.Def_BipHamCount_Deterministic_Core
-- name    : BipHamCount_Deterministic_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:08.075489+00:00
-- url     : https://prove2.me/theorems/7421d973-48a5-4158-bd9b-93ca23ebd2a4
-- title:
--   Digraphs, ordered minors, cycle counts and the signed-sum specifications
-- statement:
--   Let $V$ be a finite ordered vertex set. A digraph is Boolean adjacency, and bipartiteness means that some two-colouring separates every arc. The directed Hamiltonian-cycle count is the number of single-cycle successor permutations whose support is all of $V$ and whose arcs are present. Empty and singleton carriers have count zero; a directed digon counts once.
--
--   For two sides indexed by $\mathrm{Fin}(m)$, $A$ records left-to-right arcs and $B$ records right-to-left arcs. Square submatrices list both index sets in increasing order; unequal-size determinant or permanent minors are zero, and the empty square minor is one. The definitions give $\sigma$, its restrictions $\sigma_{>k}$ and $\sigma_{\le k}$, and
--   $$w_i(X,Y)=\Big(\sum_{j\in X}A_{ij}\Big)\Big(\sum_{j\in Y}B_{ji}\Big).$$
--   The finite sum $F(X,Y)$ retains precisely $S\subseteq L\setminus\{v\}$, $|S|=|T|\le k$ and $X\cup Y\subseteq T$, with sign $(-1)^{|\bar S|+1}$. Also defined are the rectangular permanent as a sum over row-to-column bijections, the zero–one predicate, $\alpha=60909/100000$, $kOf(m)=\lfloor60909m/100000\rfloor$, and valid row sets.
--
--   These are mathematical specifications shared by all statements. The executable programs do not evaluate the specification sums or use a library determinant/permanent as an oracle.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), §§2–4, pp.4–9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib

open scoped BigOperators

namespace BipHamCount.Deterministic

/-! Koana–Kumabe, STOC 2027 submission #814 (October 2026), §§2–4, pp.4–9.
These finite sums are specifications, never executable determinant/permanent subroutines. -/

/-- Underlying undirected bipartiteness, pp.1–2. No colouring is supplied as input. -/
def IsBipartiteDigraph {V : Type*} (adj : V → V → Bool) : Prop :=
  ∃ c : V → Bool, ∀ u w, adj u w = true → c u ≠ c w

/-- Successor permutations of spanning directed cycles, Lemma 3.1, pp.5–6.
Empty and singleton carriers have count zero; a directed digon counts once. -/
noncomputable def hamCount {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun π : Equiv.Perm V =>
    π.IsCycle ∧ π.support = Finset.univ ∧ ∀ u, adj u (π u) = true).card

/-- Adjacency matrix, §3 p.5. -/
def adjMatrix {V : Type*} (adj : V → V → Bool) : Matrix V V ℤ :=
  fun i j => if adj i j then 1 else 0

/-- Square submatrix in the fixed increasing orders, §2 pp.4–5. -/
def squareSub {R I J : Type*} [LinearOrder I] [LinearOrder J]
    (M : Matrix I J R) (S : Finset I) (T : Finset J) (h : T.card = S.card) :
    Matrix (Fin S.card) (Fin S.card) R :=
  M.submatrix (S.orderEmbOfFin rfl) (T.orderEmbOfFin h)

/-- Ordered determinant minor, §2 pp.4–5. Unequal sizes return zero; empty square returns one. -/
noncomputable def minor {R I J : Type*} [CommRing R] [LinearOrder I] [LinearOrder J]
    (M : Matrix I J R) (S : Finset I) (T : Finset J) : R :=
  if h : T.card = S.card then (squareSub M S T h).det else 0

/-- Ordered permanent minor, §2 pp.4–5, with the same conventions as `minor`. -/
noncomputable def permMinor {R I J : Type*} [CommRing R] [LinearOrder I] [LinearOrder J]
    (M : Matrix I J R) (S : Finset I) (T : Finset J) : R :=
  if h : T.card = S.card then (squareSub M S T h).permanent else 0

/-- Zero–one entries, §2 p.4; needed for bit-cost estimates, not for ring identities. -/
def ZeroOne {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- The bipartite digraph encoded by A (left to right) and B (right to left), §2 p.4. -/
def bipDigraph {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) :
    (Fin m ⊕ Fin m) → (Fin m ⊕ Fin m) → Bool
  | .inl i, .inr j => decide (A i j = 1)
  | .inr j, .inl i => decide (B j i = 1)
  | _, _ => false

/-- One summand of σ, §3 p.5. Bars are complements in their respective sides. -/
noncomputable def sigmaTerm {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) : ℤ :=
  (-1) ^ (Sᶜ.card + 1) * permMinor A S T * permMinor B T S *
    minor A Sᶜ Tᶜ * minor B Tᶜ Sᶜ

/-- σ, Lemma 3.2, pp.5–6. -/
noncomputable def sigma {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) : ℤ :=
  ∑ S ∈ (Finset.univ.erase v).powerset,
    ∑ T ∈ Finset.univ.powerset.filter (fun T : Finset (Fin m) => T.card = S.card),
      sigmaTerm A B S T

/-- Large part, §4 p.6. -/
noncomputable def sigmaLarge {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (v : Fin m) (k : ℕ) : ℤ :=
  ∑ S ∈ (Finset.univ.erase v).powerset.filter (fun S => k < S.card),
    ∑ T ∈ Finset.univ.powerset.filter (fun T : Finset (Fin m) => T.card = S.card),
      sigmaTerm A B S T

/-- Small part, §4 p.6. -/
noncomputable def sigmaSmall {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (v : Fin m) (k : ℕ) : ℤ :=
  ∑ S ∈ (Finset.univ.erase v).powerset.filter (fun S => S.card ≤ k),
    ∑ T ∈ Finset.univ.powerset.filter (fun T : Finset (Fin m) => T.card = S.card),
      sigmaTerm A B S T

/-- wᵢ(X,Y), §4.2 p.7. -/
def w {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (X Y : Finset (Fin m)) (i : Fin m) : ℤ :=
  (∑ j ∈ X, A i j) * (∑ j ∈ Y, B j i)

/-- F(X,Y), §4.2 p.7; all restrictions on both summation indices are explicit. -/
noncomputable def Fval {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (v : Fin m) (k : ℕ) (X Y : Finset (Fin m)) : ℤ :=
  ∑ S ∈ (Finset.univ.erase v).powerset.filter (fun S => S.card ≤ k),
    ∑ T ∈ Finset.univ.powerset.filter
        (fun T : Finset (Fin m) => T.card = S.card ∧ X ∪ Y ⊆ T),
      (-1) ^ (Sᶜ.card + 1) * minor A Sᶜ Tᶜ * minor B Tᶜ Sᶜ * ∏ i ∈ S, w A B X Y i

/-- Exact decimal α, §4 p.6; entropy in the theorems uses natural logarithms. -/
noncomputable def alpha : ℝ := 60909 / 100000

/-- Integer reading of k=αm, §4 pp.6–7: floor(60909m/100000). -/
def kOf (m : ℕ) : ℕ := 60909 * m / 100000

/-- Valid row sets, §4.1 p.7. In zero-based indices, i ≥ k−|I|. -/
def Valid {m : ℕ} (k : ℕ) (I : Finset (Fin m)) : Prop :=
  k ≤ I.card ∨ ∀ i ∈ I, k - I.card ≤ i.val

/-- Permanent with independent row and column carriers, Lemma 2.1 p.5.
The sum is over all bijections. Both empty carriers give the single empty product. -/
noncomputable def rectPermanent {R I J : Type*} [CommRing R] [Fintype I] [Fintype J]
    (M : Matrix I J R) : R := by
  classical
  exact ∑ f : I ≃ J, ∏ i, M i (f i)

end BipHamCount.Deterministic


