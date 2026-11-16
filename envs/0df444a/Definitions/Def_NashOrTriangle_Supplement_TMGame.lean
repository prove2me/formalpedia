-- Prove2me | Definitions.Def_NashOrTriangle_Supplement_TMGame
-- name    : NashOrTriangle_Supplement_TMGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:47:47.426442+00:00
-- url     : https://prove2.me/theorems/a1fceb73-27fd-44a3-982e-28c64c62833d
-- title:
--   Games given by Turing machines: instances, validity promises and polynomial time
-- statement:
--   In the Turing-machine model of Appendix B a game on the strategy sets $A=B=\mathbb N$ (strategies described in unary) is given by three programs: a **utility** program $u$, a **maximizing best-response** program and a **minimizing best-response** program. An instance is a natural number $I$ coding the triple; its **description length** is the binary length of $I$. The payoff $M_I(i,j)$ is the output of $u$ on $(i,j)$.
--
--   1. The utility program is **valid** if it is total and binary: on every $(i,j)$ it halts with $0$ or $1$.
--   2. The BR programs are **exact** if, given any finite rational column mixture $q$, the maximizing program halts with a row $a$ satisfying $M(a',q)\le M(a,q)$ for every row $a'$, and symmetrically the minimizing program returns a column minimizing $M(p,\cdot)$.
--   3. The BR programs **meet their accuracy parameter** if, given a finite rational mixture and a rational $\varepsilon>0$, they halt with an $\varepsilon$-best response: $M(a',q)\le M(a,q)+\varepsilon$ for every $a'$, and $M(p,b)\le M(p,b')+\varepsilon$ for every $b'$.
--   4. The instance is **polynomial-time** if the utility function and both BR functions are computed by Turing machines in time polynomial in the length of their input, strategies written in unary and rational weights in binary.
--
--   The promise of Theorems B.1 and B.2 is 1, 2 and 4; the promise of Theorem B.3 is 1 and 3. The **unary length** of a triangle with rows $a_1,\dots,a_t$ and columns $b_1,\dots,b_t$ is $\sum_i(a_i+1)+\sum_j(b_j+1)$.
--
--   **Formalization Note** Programs are Mathlib's partial recursive codes `Nat.Partrec.Code`, and the instance number is decoded bijectively into the triple. A mixture handed to a BR program is a list of (strategy, weight) pairs with nonnegative weights summing to $1$, passed as its standard code. Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` for the function the program computes, with the tape encodings `encMix` (mixtures) and unary (strategies); triangles are written on tape by `encTri`.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Appendix B, first paragraph, p.22 (PDF p.23); §1.1, p.4 (PDF p.5) for the BR conditions

import Mathlib

namespace NashOrTriangle.Supplement

open Nat.Partrec Computability

/-!
The Turing-machine model of Appendix B: a game whose utility and best-response functions are
given as programs.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix B, printed p. 22 (PDF p. 23):
"Here the utility and best-response functions are supplied as Turing machines promised to be
total and correct, and a BR Turing machine takes a rational accuracy parameter and is promised to
meet it. We start with Turing machines that run in polynomial time and strategy descriptions in
unary."; the BR oracles of §1.1, printed p. 4 (PDF p. 5).

**Formalization Note** An instance is a natural number `I`, decoded (bijectively, by Mathlib's
`Denumerable` instance) to a triple of `Nat.Partrec.Code`s: the utility program, the maximizing
BR program and the minimizing BR program. Strategies of both players are natural numbers. The
utility program is run on `Nat.pair i j`. A mixture handed to a BR program is a finite list of
(strategy, rational weight) pairs, nonnegative weights summing to `1`, repeated strategies adding
up, passed as its `Encodable` code; an approximate BR program receives the code of the pair
(mixture, accuracy `ε`). Polynomial time is Mathlib's `Turing.TM2ComputableInPolyTime` for the
function the program computes, with strategies in unary and rational weights in binary.
The description length of an instance is the binary length `Nat.size I` of its code.
-/

/-- The triple of programs (utility, maximizing BR, minimizing BR) coded by `I`. -/
def tmInstance (I : ℕ) : Code × Code × Code :=
  Denumerable.ofNat (Code × Code × Code) I

/-- The payoff `M(i, j)` of the game coded by `I`: `1` if the utility program outputs `1` on
`(i, j)`, and `0` otherwise. On a valid instance (`ValidUtility`) it is the program's output. -/
noncomputable def tmPayoff (I : ℕ) (i j : ℕ) : ℚ := by
  classical
  exact if (1 : ℕ) ∈ (tmInstance I).1.eval (Nat.pair i j) then 1 else 0

/-- A finite rational mixture given as a list of (strategy, weight) pairs: nonnegative weights
summing to `1`. -/
def IsMixList (l : List (ℕ × ℚ)) : Prop :=
  (∀ e ∈ l, 0 ≤ e.2) ∧ (l.map Prod.snd).sum = 1

/-- `M(a, q) = ∑_{(j, w) ∈ q} w · M(a, j)` for a column mixture given as a list. -/
noncomputable def mixRow (M : ℕ → ℕ → ℚ) (a : ℕ) (l : List (ℕ × ℚ)) : ℝ :=
  (l.map fun e => (e.2 : ℝ) * (M a e.1 : ℝ)).sum

/-- `M(p, b) = ∑_{(i, w) ∈ p} w · M(i, b)` for a row mixture given as a list. -/
noncomputable def mixCol (M : ℕ → ℕ → ℚ) (l : List (ℕ × ℚ)) (b : ℕ) : ℝ :=
  (l.map fun e => (e.2 : ℝ) * (M e.1 b : ℝ)).sum

/-- The utility program of `I` is total and binary: on every pair `(i, j)` it halts with `0` or
`1`. -/
def ValidUtility (I : ℕ) : Prop :=
  ∀ i j : ℕ, (tmInstance I).1.eval (Nat.pair i j) = Part.some 0 ∨
    (tmInstance I).1.eval (Nat.pair i j) = Part.some 1

/-- The BR programs of `I` are **exact** best responses: on every finite rational column mixture
`q` the maximizing program halts with a row `a` such that `M(a', q) ≤ M(a, q)` for every row `a'`
(so `M(a, q) = U(q)`), and on every row mixture `p` the minimizing program halts with a column
`b` such that `M(p, b) ≤ M(p, b')` for every column `b'` (so `M(p, b) = L(p)`). -/
def ExactBRValid (I : ℕ) : Prop :=
  (∀ l : List (ℕ × ℚ), IsMixList l → ∃ a ∈ (tmInstance I).2.1.eval (Encodable.encode l),
    ∀ a' : ℕ, mixRow (tmPayoff I) a' l ≤ mixRow (tmPayoff I) a l) ∧
  (∀ l : List (ℕ × ℚ), IsMixList l → ∃ b ∈ (tmInstance I).2.2.eval (Encodable.encode l),
    ∀ b' : ℕ, mixCol (tmPayoff I) l b ≤ mixCol (tmPayoff I) l b')

/-- The BR programs of `I` meet their **accuracy parameter**: on every finite rational column
mixture `q` and rational `ε > 0` the maximizing program halts with a row `a` such that
`M(a', q) ≤ M(a, q) + ε` for every row `a'` (so `M(a, q) ≥ U(q) − ε`), and symmetrically the
minimizing program returns a column `b` with `M(p, b) ≤ M(p, b') + ε` for every `b'`. -/
def ApproxBRValid (I : ℕ) : Prop :=
  (∀ (l : List (ℕ × ℚ)) (ε : ℚ), IsMixList l → 0 < ε →
    ∃ a ∈ (tmInstance I).2.1.eval (Encodable.encode (l, ε)),
      ∀ a' : ℕ, mixRow (tmPayoff I) a' l ≤ mixRow (tmPayoff I) a l + ε) ∧
  (∀ (l : List (ℕ × ℚ)) (ε : ℚ), IsMixList l → 0 < ε →
    ∃ b ∈ (tmInstance I).2.2.eval (Encodable.encode (l, ε)),
      ∀ b' : ℕ, mixCol (tmPayoff I) l b ≤ mixCol (tmPayoff I) l b' + ε)

/-- The tape encoding of a mixture list over the alphabet `{0, 1, #}` (`#` is `2 : Fin 3`): for
each entry, the strategy in unary, `#`, the sign bit of the weight, the binary numerator, `#`, the
binary denominator, `#`. -/
def encMix (l : List (ℕ × ℚ)) : List (Fin 3) :=
  l.flatMap fun e =>
    (unaryEncodeNat e.1).map (fun x => if x then 1 else 0) ++ [2] ++
      [if e.2 < 0 then 1 else 0] ++ (encodeNat e.2.num.natAbs).map (fun x => if x then 1 else 0) ++
      [2] ++ (encodeNat e.2.den).map (fun x => if x then 1 else 0) ++ [2]

/-- The programs of `I` compute **polynomial-time** functions, strategies in unary: the utility
program computes a function `(i, j) ↦ M(i, j) ∈ {0, 1}` that a Turing machine computes in time
polynomial in the unary length of `(i, j)`, and each BR program agrees, on every finite rational
mixture, with a function from mixtures to strategies that a Turing machine computes in time
polynomial in the length of `encMix`, writing the strategy in unary. -/
def PolyTimeInstance (I : ℕ) : Prop :=
  (∃ f : ℕ × ℕ → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime
      (encodingProd unaryEncodingNat unaryEncodingNat).encode encodeBool f) ∧
    ∀ i j : ℕ, (tmInstance I).1.eval (Nat.pair i j) = Part.some (if f (i, j) then 1 else 0)) ∧
  (∃ f : List (ℕ × ℚ) → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime encMix unaryEncodeNat f) ∧
    ∀ l : List (ℕ × ℚ), IsMixList l →
      (tmInstance I).2.1.eval (Encodable.encode l) = Part.some (f l)) ∧
  (∃ f : List (ℕ × ℚ) → ℕ,
    Nonempty (Turing.TM2ComputableInPolyTime encMix unaryEncodeNat f) ∧
    ∀ l : List (ℕ × ℚ), IsMixList l →
      (tmInstance I).2.2.eval (Encodable.encode l) = Part.some (f l))

/-- The promise of Theorems B.1 and B.2: a binary game with a total utility program and exact BR
programs, all running in polynomial time on unary strategy descriptions. -/
def ValidExactPoly (I : ℕ) : Prop :=
  ValidUtility I ∧ ExactBRValid I ∧ PolyTimeInstance I

/-- The promise of Theorem B.3: a binary game with a total utility program and BR programs that
meet their accuracy parameter (no time bound). -/
def ValidApprox (I : ℕ) : Prop :=
  ValidUtility I ∧ ApproxBRValid I

/-- The length of a triangle with rows `a` and columns `b` written in unary:
`∑ᵢ (aᵢ + 1) + ∑ⱼ (bⱼ + 1)` (each strategy and its separator). -/
def triLength {t : ℕ} (a b : Fin t → ℕ) : ℕ :=
  ∑ i, (a i + 1) + ∑ j, (b j + 1)

/-- The tape encoding of a triangle over `{0, 1, #}`: the rows `a₁, …, a_t`, then the columns
`b₁, …, b_t`, each in unary followed by `#`. Its length is `triLength a b`. -/
def encTri {t : ℕ} (a b : Fin t → ℕ) : List (Fin 3) :=
  (List.ofFn a ++ List.ofFn b).flatMap fun n =>
    (unaryEncodeNat n).map (fun x => if x then 1 else 0) ++ [2]

end NashOrTriangle.Supplement


