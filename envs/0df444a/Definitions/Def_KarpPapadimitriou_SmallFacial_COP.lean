-- Prove2me | Definitions.Def_KarpPapadimitriou_SmallFacial_COP
-- name    : KarpPapadimitriou_SmallFacial_COP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:27:11.232792+00:00
-- url     : https://prove2.me/theorems/004f1f48-1d22-456c-ab56-f40f1ede65d0
-- title:
--   Combinatorial optimization problems, small facial descriptions, and the two classes of Lemma 1
-- statement:
--   A **combinatorial optimization problem** has a set $L$ of binary input strings. For each $z\in L$ it has a dimension $n(z)$ and a feasible set $S(z)\subseteq(\mathbb Z_{\ge0})^{n(z)}$. Write $\mathrm{CH}(S(z))$ for its convex hull in $\mathbb Q^{n(z)}$.
--
--   A **facial description** is a set $F$ of triples $\langle z,f,g\rangle$, with $z\in L$, $f\in\mathbb Z^{n(z)}$, and $g\in\mathbb Z$, such that for every $z\in L$ and rational vector $x$,
--   $$x\in\mathrm{CH}(S(z))\quad\Longleftrightarrow\quad f\cdot x\le g\text{ for every }\langle z,f,g\rangle\in F.$$
--   It is **small** if one polynomial $p$ bounds $|f_i|$ and $|g|$ by $2^{p(|z|+n(z))}$ for all its triples.
--
--   The two classes in Lemma 1 are **zero-one problems**, where every coordinate of every feasible vector is zero or one, and **integer-programming-type problems**, whose feasible vectors are exactly the nonnegative integer solutions of $A(z)x\le b(z)$ for an integral $m(z)\times n(z)$ matrix $A(z)$ and an integral $m(z)$-vector $b(z)$. The coefficient size $s(A,b)$ is the sum of $\lceil\log_2(1+|a|)\rceil$ over their entries.
--
--   These definitions let the same smallness condition cover both bounded zero-one hulls and possibly unbounded integer hulls.
--
--   **Formalization Note** The paper's $R$ means $\mathbb Q$ (p. 3 footnote). The complexity-language conditions in Definition 1(iii) are omitted: Lemma 1 uses none of them and consequently holds for every triple $(L,n,S)$ with nonnegative integral feasible vectors. The polynomial is represented as $p(t)=t^k+k$ with one $k$ before all inputs. For IP-type inputs, $s(A,b)\le |z|$ makes explicit that the input encodes its coefficients. The page calls $b$ an $n$-vector; it is indexed by the $m$ rows of $A$. Empty feasible sets and dimension zero are allowed.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), pp. 3–6, Definition 1, facial descriptions, the two classes preceding Lemma 1, and coefficient size in proof of Lemma 1; https://dspace.mit.edu/server/api/core/bitstreams/eb122126-c312-4445-a8d2-153e3e7d285f/content

import Mathlib
import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram

namespace KarpPapadimitriou.SmallFacial

/-- The data used by Lemma 1: feasible nonnegative integer vectors indexed by binary inputs.
The complexity conditions of Definition 1 are not needed for this lemma. -/
structure COP where
  L : Set (List Bool)
  n : List Bool → ℕ
  S : (z : List Bool) → Set (Fin (n z) → ℤ)
  S_nonneg : ∀ z ∈ L, ∀ x ∈ S z, ∀ i, 0 ≤ x i

/-- The paper's `CH(S(z))`, with its `R` interpreted as the rationals. -/
def hull (C : COP) (z : List Bool) : Set (Fin (C.n z) → ℚ) :=
  convexHull ℚ {x | ∃ y ∈ C.S z, x = fun i => (y i : ℚ)}

/-- A collection of input-indexed integral inequalities describes every rational hull. -/
def IsFacialDescription (C : COP)
    (F : Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ)) : Prop :=
  (∀ t ∈ F, t.1 ∈ C.L) ∧
  ∀ z ∈ C.L, ∀ x : Fin (C.n z) → ℚ,
    x ∈ hull C z ↔
      ∀ (f : Fin (C.n z) → ℤ) (g : ℤ),
        ⟨z, (f, g)⟩ ∈ F → (∑ i, (f i : ℚ) * x i) ≤ (g : ℚ)

/-- One polynomial bound works for all inputs and all inequalities. -/
def IsSmall (C : COP)
    (F : Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ)) : Prop :=
  ∃ k : ℕ, ∀ t ∈ F,
    (∀ i, Int.natAbs (t.2.1 i) ≤ 2 ^ ((t.1.length + C.n t.1) ^ k + k)) ∧
    Int.natAbs t.2.2 ≤ 2 ^ ((t.1.length + C.n t.1) ^ k + k)

/-- Every feasible vector has zero-one entries. -/
def IsZeroOne (C : COP) : Prop :=
  ∀ z ∈ C.L, ∀ x ∈ C.S z, ∀ i, x i = 0 ∨ x i = 1

/-- A vertex, equivalently an extreme point, of a rational convex set. -/
def IsVertex {n : ℕ} (Q : Set (Fin n → ℚ)) (v : Fin n → ℚ) : Prop :=
  v ∈ Q ∧ ∀ a ∈ Q, ∀ b ∈ Q, ∀ r : ℚ,
    0 < r → r < 1 → v = r • a + (1 - r) • b → a = v ∧ b = v

/-- A nonzero recession direction based at some point of a rational set. -/
def HasRay {n : ℕ} (Q : Set (Fin n → ℚ)) : Prop :=
  ∃ (v : Fin n → ℚ) (d : Fin n → ℚ),
    v ∈ Q ∧ d ≠ 0 ∧ ∀ r : ℚ, 0 ≤ r → v + r • d ∈ Q

/-- The binary length used on p. 6 for one integer entry. -/
def entrySize (a : ℤ) : ℕ := Nat.clog 2 (1 + a.natAbs)

/-- The paper's `s`, summed over every entry of the integer matrix and right-hand side. -/
def inputSize {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : ℕ :=
  (∑ i, ∑ j, entrySize (A i j)) + ∑ i, entrySize (b i)

/-- Inputs encode systems of integral inequalities, and feasible vectors are exactly their
nonnegative integer solutions. The length bound makes the binary encoding explicit. -/
def IsIPType (C : COP) : Prop :=
  ∃ (m : List Bool → ℕ)
    (A : ∀ z, Matrix (Fin (m z)) (Fin (C.n z)) ℤ)
    (b : ∀ z, Fin (m z) → ℤ),
    ∀ z ∈ C.L,
      inputSize (A z) (b z) ≤ z.length ∧
      C.S z = {x | (∀ j, 0 ≤ x j) ∧
        (fun j => (x j : ℚ)) ∈
          CookSensitivity.ChvatalRank.polyhedron (A z) (fun i => (b z i : ℚ))}

end KarpPapadimitriou.SmallFacial


