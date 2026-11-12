-- Prove2me | Definitions.Def_EuclidCVRP_Main_Machine
-- name    : EuclidCVRP_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:32.847657+00:00
-- url     : https://prove2.me/theorems/79a77f3a-1065-4090-82af-d032543b1de4
-- title:
--   Binary encodings and polynomial-time approximation algorithms for Euclidean CVRP
-- statement:
--   The paper's algorithms are read in the bit model. Natural numbers are written in binary (self-delimited), integers with a sign bit, rationals as reduced numerator and denominator, lists entry by entry with terminators. A **rational instance** has rational depot and client coordinates; its encoding lists $Q$, the depot, and each client's location and demand, so $Q$ and the demands are in binary. A solution is encoded as the list of its tours, each a list of client indices.
--
--   A function $f$ on bit strings is **computed in polynomial time** if a Mathlib multi-stack Turing machine with finite stack alphabets, reading the input bits, outputs the encoding of $f(w)$ within $p(|w|)$ steps on every input $w$, for a polynomial $p$.
--
--   A **polynomial-time $\alpha$-approximation algorithm on a class $\mathcal P$** is such a machine whose output on the encoding of every valid rational instance $I\in\mathcal P$ encodes a feasible solution $\mathcal T$ of $I$ with
--
--   $$c(\mathcal T)\le\alpha\cdot c(\mathcal T')\quad\text{for every feasible solution }\mathcal T'\text{ of }I.$$
--
--   This is the notion of algorithm in Theorems 1, 3 and 4 and Lemma 2.
--
--   **Formalization Note** The machine is `Turing.TM2ComputableInPolyTime` with the identity input encoding over `Bool`, and its stack alphabets are finite (`RevRedSAT.FiniteAlphabets`), as in the published `SteinerAPX_NetworkApproximation`. Costs are the exact real Euclidean lengths of the rational points.
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), Theorem 1, p. 2 (polynomial-time approximation algorithm); Abstract, p. 1 (Q a positive integer, d(v) ≤ Q non-negative integers)

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_EuclidCVRP_Main_Instance

set_option autoImplicit false

namespace EuclidCVRP.Main

/-!
# Binary encodings, polynomial-time machines, and approximation algorithms for Euclidean CVRP

Blauth, Grandoni, Mátravölgyi, Mousavi, Ren, Salavatipour, STOC 2027 submission #1236 (October 2026),
Theorem 1, p. 2 ("polynomial time (3/2 + ε)-approximation algorithm"), Abstract p. 1 (Q a positive
integer, d(v) ≤ Q non-negative integers).

The paper fixes no machine model. An algorithm is a Mathlib `Turing.TM2ComputableInPolyTime`
machine over the Boolean alphabet, all of whose stack alphabets are finite
(`RevRedSAT.FiniteAlphabets`), reading the binary encoding of an instance with rational
coordinates (capacity and demands in binary) and writing the binary encoding of its output.
-/

/-- A natural number in binary (`Nat.bits`, little-endian), self-delimited: each bit `b` becomes
`true, b`, and a final `false` ends the number. -/
def natBits (k : ℕ) : List Bool := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- A natural number in unary, self-delimited. -/
def unaryBits (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- An integer: sign bit, then its absolute value in binary. -/
def intBits (z : ℤ) : List Bool := decide (z < 0) :: natBits z.natAbs

/-- A rational number: its reduced numerator, then its denominator. -/
def ratBits (q : ℚ) : List Bool := intBits q.num ++ natBits q.den

/-- A list: every entry is preceded by `true`, and a final `false` ends the list. -/
def listBits {α : Type} (f : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (fun x => true :: f x) ++ [false]

/-- A rational point of the plane. -/
def ptBits (p : ℚ × ℚ) : List Bool := ratBits p.1 ++ ratBits p.2

/-- A rational point as a point of the Euclidean plane. -/
noncomputable def toPt (p : ℚ × ℚ) : Pt := !₂[(p.1 : ℝ), (p.2 : ℝ)]

/-- **A Euclidean CVRP instance with rational coordinates**, the input of an algorithm. -/
structure RatInstance where
  /-- number of clients -/
  n : ℕ
  /-- the depot -/
  depot : ℚ × ℚ
  /-- client locations -/
  loc : Fin n → ℚ × ℚ
  /-- the capacity `Q` -/
  Q : ℕ
  /-- the demands -/
  dem : Fin n → ℕ

namespace RatInstance

/-- The instance in the Euclidean plane. -/
noncomputable def toInstance (J : RatInstance) : Instance :=
  ⟨J.n, toPt J.depot, fun v => toPt (J.loc v), J.Q, J.dem⟩

/-- `Q ≥ 1` and `0 ≤ d(v) ≤ Q`. -/
def Valid (J : RatInstance) : Prop := J.toInstance.Valid

end RatInstance

/-- The binary encoding of an instance: `Q`, the depot, then the list of clients (location and
demand); `n` is the length of that list. -/
def encInst (J : RatInstance) : List Bool :=
  natBits J.Q ++ ptBits J.depot ++
    listBits (fun v : Fin J.n => ptBits (J.loc v) ++ natBits (J.dem v)) (List.finRange J.n)

/-- The binary encoding of a collection of tours, each a list of client indices. -/
def solBits : List (List ℕ) → List Bool := listBits (listBits natBits)

/-- A solution written with client indices as natural numbers. -/
def Instance.rawSol (I : Instance) (S : List (List (Fin I.n))) : List (List ℕ) :=
  S.map (fun T => T.map Fin.val)

/-- `f` is computed in polynomial time (in the length of its input word) by a Mathlib multi-stack
Turing machine with finite stack alphabets, reading the input bits unchanged and writing `eb (f x)`. -/
def PolyTimeFn {β : Type} (eb : β → List Bool) (f : List Bool → β) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) eb f,
    RevRedSAT.FiniteAlphabets M.toTM2ComputableAux

/-- `out` encodes a feasible solution of `I` whose cost is at most `α` times the cost of every
feasible solution. -/
def Instance.IsApproxOutput (I : Instance) (α : ℝ) (out : List (List ℕ)) : Prop :=
  ∃ S : List (List (Fin I.n)), I.Feasible S ∧ I.rawSol S = out ∧
    ∀ S' : List (List (Fin I.n)), I.Feasible S' → I.cost S ≤ α * I.cost S'

/-- **A polynomial-time `α`-approximation algorithm on the instances satisfying `P`**: a
polynomial-time machine whose output, on the encoding of every valid rational instance satisfying `P`,
is a feasible solution of cost at most `α` times that of every feasible solution. -/
def IsApproxAlg (α : ℝ) (P : RatInstance → Prop) (alg : List Bool → List (List ℕ)) : Prop :=
  PolyTimeFn solBits alg ∧
    ∀ J : RatInstance, J.Valid → P J → J.toInstance.IsApproxOutput α (alg (encInst J))

end EuclidCVRP.Main


