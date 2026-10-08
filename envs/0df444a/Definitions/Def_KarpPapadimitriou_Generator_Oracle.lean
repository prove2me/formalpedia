-- Prove2me | Definitions.Def_KarpPapadimitriou_Generator_Oracle
-- name    : KarpPapadimitriou_Generator_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:28:08.638393+00:00
-- url     : https://prove2.me/theorems/ddc01fbe-4e00-4656-8932-9bed18c1cb76
-- title:
--   Generators of violated inequalities and their output families
-- statement:
--   Given a combinatorial optimization problem $C$, a **generator of violated inequalities** $G$ accepts every pair $(z,p)$ with $z\in L$ and $p\in\mathbb Q^{n(z)}$. It returns “O.K.” exactly when $p\in\mathrm{CH}(S(z))$. Otherwise it returns integers $f\in\mathbb Z^{n(z)}$, $g\in\mathbb Z$ satisfying
--   $$f\cdot p>g\qquad\text{and}\qquad f\cdot x\le g\quad\text{for every }x\in S(z).$$
--
--   Its output family is $F_G(C)=\{\langle z,f,g\rangle:\exists p,\ G(z,p)=(f,g)\}$. The generator is **small** when the coefficients of $F_G(C)$ have one uniform polynomial bit-length bound. It **runs in polynomial time** when one string function computed by Cook's polynomial-time Turing machine agrees with $G$ on every well-formed encoded query.
--
--   This is the oracle model that Theorem 2 turns into a decision procedure.
--
--   **Formalization Note** A rational coordinate is coded by its reduced numerator and positive denominator in binary; the query code includes $z$ and the dimension. “O.K.” and an inequality have disjoint output-code prefixes. The string function is arbitrary on malformed inputs. The facial-description property of $F_G(C)$ is stated separately as a milestone.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 9, §4, generator and F_G(C)

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_COP

namespace KarpPapadimitriou.Generator

/-- Each rational coordinate is written as its reduced numerator and positive denominator. -/
def encRat (q : ℚ) : List Sym :=
  ProjSchedTW.Complexity.encInt q.num ++ ProjSchedTW.Complexity.encNat q.den

/-- The complete binary code of a generator query `⟨z,p⟩`. -/
def encZP {n : ℕ} (z : List Bool) (p : Fin n → ℚ) : List Sym :=
  encZ z ++ ProjSchedTW.Complexity.encNat n ++ (List.ofFn p).flatMap encRat

/-- `O.K.` has a distinct one-symbol code; an inequality begins with `zero`. -/
def encOut {n : ℕ} : Option ((Fin n → ℤ) × ℤ) → List Sym
  | none => [ProjSchedTW.Complexity.BSym.one]
  | some (f, g) => ProjSchedTW.Complexity.BSym.zero ::
      (ProjSchedTW.Complexity.encInts (List.ofFn f) ++ ProjSchedTW.Complexity.encInt g)

/-- A total presentation of the generator; its values outside `L` are immaterial. -/
abbrev Oracle (C : COP) :=
  (z : List Bool) → (Fin (C.n z) → ℚ) → Option ((Fin (C.n z) → ℤ) × ℤ)

/-- On every valid instance, `none` means exactly hull membership. Every returned inequality
strictly separates the queried point and is valid on all feasible integer vectors. -/
def IsGenerator (C : COP) (gen : Oracle C) : Prop :=
  ∀ z ∈ C.L, ∀ p : Fin (C.n z) → ℚ,
    (gen z p = none ↔ p ∈ hull C z) ∧
    ∀ f g, gen z p = some (f, g) →
      (g : ℚ) < dotQ f p ∧ ∀ x ∈ C.S z, dotZ f x ≤ g

/-- The exact family of inequalities that the generator returns on some valid query. -/
def FG (C : COP) (gen : Oracle C) : Set (Triple C) :=
  {a | a.1 ∈ C.L ∧ ∃ p : Fin (C.n a.1) → ℚ, gen a.1 p = some a.2}

/-- The paper's small-generator condition: its output family has one uniform coefficient bound.
The fact that it describes the hull follows from the generator specification. -/
def IsSmallGenerator (C : COP) (gen : Oracle C) : Prop := IsSmall C (FG C gen)

/-- The generator's complete string function runs in Cook's polynomial time. The equality is
required on all well-formed inputs, including the bit lengths of the rational coordinates. -/
def RunsInPolyTime (C : COP) (gen : Oracle C) : Prop :=
  ∃ φ : List Sym → List Sym, CookPvsNP.PolyTimeComputable φ ∧
    ∀ z ∈ C.L, ∀ p : Fin (C.n z) → ℚ,
      φ (encZP z p) = encOut (gen z p)

end KarpPapadimitriou.Generator


