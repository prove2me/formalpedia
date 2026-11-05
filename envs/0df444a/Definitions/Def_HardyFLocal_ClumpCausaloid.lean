-- Prove2me | Definitions.Def_HardyFLocal_ClumpCausaloid
-- name    : HardyFLocal_ClumpCausaloid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:15.441991+00:00
-- url     : https://prove2.me/theorems/0efb7cb0-2b92-4e80-bfff-1e45f3511ba2
-- title:
--   Clumps and the clumped causaloid of the qubit lattice, (27)–(28)
-- statement:
--   Fix a finite set $O$ of vertices. On each qubit, the **clumps** of $O$ are the maximal runs of consecutive vertices of that qubit lying in $O$, in time order. Each vertex of $O$ lies in exactly two clumps, one on each of its qubits. A region is **interior** if none of its vertices is at the first or last position of a qubit.
--
--   Fiducial labels $L$ give, at each vertex, labels $L_x(a,b)$ with superoperator $\$_a\otimes\$_b$. From them and tables $T,E$ the **clumped causaloid** is built:
--
--   1. the elementary fiducial set at $x$ is the image of $L_x$, with elementary table $E_x$;
--   2. the fiducial set $\Omega_C(O)$ of the region is the set of families $L_x(a_x,b_x)$ on $O$ with $a_x=1$ unless $x$ is the first vertex of its clump on the right mover, and $b_x=1$ unless $x$ is the first vertex of its clump on the left mover;
--   3. for a family $l$ of labels and $k\in\Omega_C(O)$,
--   $$\Lambda^k_l=\prod_{\text{clumps }c}\mathrm{chain}\big(l\text{ along }c\big)_{k\text{ on the first vertex of }c},$$
--   a product of components, not of matrices.
--
--   The **causaloid of the lattice** takes $T$ to be the pair table at every pair and $E_x$ to be the elementary table of the label's superoperator: this is (27), and its symmetry is (28).
--
--   **Formalization Note** The tables are arguments so that F-locality is a statement about which entries a region reads. $\Lambda$ is computed from them, and is not characterized by what it must satisfy. The structure is the published `HardyCausaloid.Causaloid`. Its predicate `IsCausaloidOf` asks for fiducial-ness at every region, which fails here, and it is not used.
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eqs. (21)–(28) and the clumping method, pp.13–14

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Causaloid
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_Instrument
import Definitions.Def_HardyFLocal_Lattice
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

namespace HardyFLocal

open HardyCausaloid

variable {m n : ℕ}

/-- **The vertices of a qubit in time order**, Hardy, arXiv:0804.0054v1, §5, p.13 ("as it goes from
vertex (u, v) to the next vertex (u, v+1)") and p.14 ("For left moving qubits we have equations
(21-26) but with v replacing u").

**Formalization Note** The labelling sentence of p.12, read for two separated groups, would send a
right mover through decreasing `v`. The explicit statement of p.13 is followed; the two differ only
by reversing both labellings. -/
def qubitVertices : Q m n → List (X m n)
  | Sum.inl u => (List.finRange n).map fun v => (u, v)
  | Sum.inr v => (List.finRange m).map fun u => (u, v)

/-- **Clumps**, arXiv:0804.0054v1, §5, step 1 of the clumping method, p.14: the maximal runs of
consecutive vertices of the qubit `q` lying in `O`, in time order, each run in time order. -/
def clumps (O : Finset (X m n)) (q : Q m n) : List (List (X m n)) :=
  ((qubitVertices q).splitOnP (fun x => decide (x ∉ O))).filter (fun c => !c.isEmpty)

/-- **`x` is the first vertex of a clump of the qubit `q`**, arXiv:0804.0054v1, §5, eqs. (21)–(22),
p.13, where the earliest vertex of a clump carries the free label `k ∈ Ω²`. -/
def IsClumpStart (O : Finset (X m n)) (q : Q m n) (x : X m n) : Prop :=
  ∃ c ∈ clumps O q, c.head? = some x

/-- **Pairs of sequential vertices** ("RSV", "LSV"), arXiv:0804.0054v1, §5, eq. (27), p.14: `x'` comes
immediately after `x` on a right moving qubit, or on a left moving qubit. -/
def IsSequentialPair (x x' : X m n) : Prop :=
  (x.1 = x'.1 ∧ x.2.val + 1 = x'.2.val) ∨ (x.2 = x'.2 ∧ x.1.val + 1 = x'.1.val)

/-- **Regions with no vertex at either end of a qubit**: `O` has no vertex on the first or the last
position of any qubit.

**Formalization Note** This is the hypothesis of the correction of the paper's "arbitrary region"
(p.14) in the clauses on fiducial sets: a qubit's input at its first vertex is fixed, and its output
at its last vertex meets only the trace. -/
def Interior (O : Finset (X m n)) : Prop :=
  ∀ x ∈ O, 0 < x.1.val ∧ x.1.val + 1 < m ∧ 0 < x.2.val ∧ x.2.val + 1 < n

/-- The entry of a pair `(a, b)` of labels that belongs to the qubit `q`: `a` on the right mover and
`b` on the left mover. -/
def onQubit (q : Q m n) (p : Ω × Ω) : Ω :=
  match q with
  | Sum.inl _ => p.1
  | Sum.inr _ => p.2

/-- **`L` gives labels of the fiducial products**, arXiv:0804.0054v1, §5, eq. (20), p.12: at every
vertex, the superoperator of the label `L x (a, b)` is `$_a ⊗ $_b`. -/
def IsFiducialLabels (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) : Prop :=
  ∀ x p, labelOp (L x p) = prodOp (S.map p.1) (S.map p.2)

section Causaloid

variable (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)

open Classical in
/-- **The elementary fiducial set** `Ω_x`, arXiv:0804.0054v1, §5, eq. (20), p.12: the labels `L x p`,
`p ∈ Ω² × Ω²`. -/
noncomputable def omegaOne (x : X m n) : Finset (Label (Setting m n) (Outcome m n) x) :=
  Finset.univ.image (L x)

/-- The pair `(a, b)` naming a fiducial label of `x` (the inverse of `L x` on its image). -/
noncomputable def decode (x : X m n) (ℓ : Label (Setting m n) (Outcome m n) x) : Ω × Ω :=
  Function.invFun (L x) ℓ

/-- The pairs named by a family of fiducial labels on `O`, as a function on all vertices (`(0, 0)`
off `O`, where it is never read). -/
noncomputable def famPairs (O : Finset (X m n)) (l : ∀ x : O, omegaOne L x.1) : X m n → Ω × Ω :=
  fun x => if h : x ∈ O then decode L x (l ⟨x, h⟩).1 else (0, 0)

open Classical in
/-- **The fiducial set of a region**, arXiv:0804.0054v1, §5, eqs. (21)–(22), p.13: the families
`k = L x (a, b)` on `O` where `a = 1` (index `0`) unless `x` is the first vertex of its clump on the
right mover, and `b = 1` unless `x` is the first vertex of its clump on the left mover. -/
noncomputable def omegaC (O : Finset (X m n)) : Finset (∀ x : O, omegaOne L x.1) :=
  Finset.univ.filter fun k => ∀ x : X m n, x ∈ O →
    (¬ IsClumpStart O (Sum.inl x.1) x → (famPairs L O k x).1 = 0) ∧
    (¬ IsClumpStart O (Sum.inr x.2) x → (famPairs L O k x).2 = 0)

end Causaloid

/-- **The Λ component of one clump**, arXiv:0804.0054v1, §5, step 2 of the clumping method, p.14: for
the clump `c` of the qubit `q`, the entry of the clump's `chain` vector at the label `b` carries on
the first vertex of `c`, where `a` gives the labels along the clump. -/
noncomputable def clumpFactor (T : X m n → X m n → PairTable) (q : Q m n) (c : List (X m n))
    (a b : X m n → Ω × Ω) : ℝ :=
  match c with
  | [] => 1
  | x :: rest =>
      chain T ((x :: rest).map fun y => (y, onQubit q (a y))) (onQubit q (b x))

/-- **The Λ components of a region**, arXiv:0804.0054v1, §5, step 3 of the clumping method, p.14
("Multiply together all Λ matrix components for all circled clumps (note we are multiplying
components rather than performing matrix multiplication)"): the product of `clumpFactor` over all
clumps of all qubits. -/
noncomputable def clumpLambda (T : X m n → X m n → PairTable) (O : Finset (X m n))
    (a b : X m n → Ω × Ω) : ℝ :=
  ∏ q : Q m n, ((clumps O q).map fun c => clumpFactor T q c a b).prod

/-- **The clumped causaloid with given tables**, arXiv:0804.0054v1, §5, eq. (27) and the clumping
method, p.14. From fiducial labels `L`, a table `T x x'` per pair of vertices and a table `E x` per
vertex:

* `Ω₁ x = omegaOne L x` and `Λ₁ x α l = E x α (a, b)`, for `l = L x (a, b)`;
* `ΩC O = omegaC L O`;
* `Λ O l k = clumpLambda T O l k`.

**Formalization Note** The tables are arguments, so that F-locality is a statement about which
entries of the tables a region reads. `Λ` is computed by `chain` and a product over clumps; it is
not characterized by what it should satisfy. -/
noncomputable def clumpCausaloid
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (T : X m n → X m n → PairTable)
    (E : ∀ x : X m n, Label (Setting m n) (Outcome m n) x → Ω × Ω → ℝ) :
    Causaloid (Setting m n) (Outcome m n) where
  Ω₁ := omegaOne L
  Λ₁ x α l := E x α (decode L x l.1)
  ΩC := omegaC L
  Λ O l k := clumpLambda T O (famPairs L O l) (famPairs L O k.1)

/-- **The causaloid of the qubit lattice**, arXiv:0804.0054v1, §5, eqs. (27)–(28), p.14: the clumped
causaloid whose elementary table is the solution of (20), and whose pair table at every sequential
pair is the solution of (21). -/
noncomputable def actualCausaloid (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) :
    Causaloid (Setting m n) (Outcome m n) :=
  clumpCausaloid L (fun _ _ => pairTable S) (fun _ α => elemCoeff S (labelOp α))

end HardyFLocal


