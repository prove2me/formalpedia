-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Supplement_AuxiliaryInput
-- name    : AutoregressiveCompression_Main_Supplement_AuxiliaryInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:10:34.978307+00:00
-- url     : https://prove2.me/theorems/da9fe347-d83c-482d-aa63-9e704daa9b12
-- title:
--   Uniform auxiliary-input families and strict inversion hardness
-- statement:
--   An auxiliary-input family has polynomial input and output lengths $p,q$ and maps $f_x:\{0,1\}^{p(|x|)}\to\{0,1\}^{q(|x|)}$ for every binary auxiliary string $x$. Efficiency means that one deterministic finite machine computes $f_x(u)$ from $x,u$ within a fixed polynomial bound. A randomized inverter is one finite machine with a fixed polynomial time bound and fair-coin bound; its mathematical output is pinned to actual execution on every input and tape.
--
--   For a polynomial denominator $r$ positive at every natural argument, inversion with error $1/r$ means
--
--   $$\forall x,\quad\Pr_{u,A}[f_x(A(x,f_x(u)))=f_x(u)]>1-\frac1{r(|x|)}.$$
--
--   The fresh $u$ is uniform and independent of the inverter's fair coins. An output with invalid preimage length fails, and any valid preimage counts as success. Auxiliary-input one-way functions exist precisely when an efficient family and such a denominator exist for which no uniform randomized polynomial-time inverter satisfies this strict all-$x$ criterion. The order is $\exists F\,\exists r\,\neg\exists A\,\forall x$. Empty inputs and zero input or output polynomial lengths remain included. Positive denominators exclude undefined tolerances, not hard instances.
--
--   This is the paper's Definition 7.2, distinct from published notions with negligible success or an infinitely-often hardness quantifier. Exact input and output lengths are natural-valued functions certified by rational polynomials, including negative coefficients such as n(n−1). Natural-coefficient polynomials suffice for upper resource bounds and for the existential positive hardness denominator: any source polynomial denominator is dominated by one of these, and increasing the denominator only strengthens the inversion requirement. Machine time is charged by the published finite-machine execution relation.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Definition 7.2, printed p.37 / PDF p.39

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks

noncomputable section

namespace AutoregressiveCompression.Main.Supplement

open scoped Classical

/-! Definition 7.2, printed p.37 / PDF p.39. Exact lengths are natural-valued
polynomials, including polynomials with negative coefficients. There is one uniform machine for the family, and one uniform
randomized machine for a putative inverter. The auxiliary input is every binary
string, not an advice string fixed once per length. -/

/-- A family with its exact polynomial input and output lengths. -/
structure AuxiliaryFamily where
  p : ℕ → ℕ
  q : ℕ → ℕ
  p_polynomial : ∃ P : Polynomial ℚ, ∀ n : ℕ, (p n : ℚ) = P.eval (n : ℚ)
  q_polynomial : ∃ Q : Polynomial ℚ, ∀ n : ℕ, (q n : ℚ) = Q.eval (n : ℚ)
  value : (x : Bits) → Word Bool (p x.length) → Word Bool (q x.length)

/-- The family is computed by one deterministic finite machine in polynomial
time from (x,u), without a table or oracle for f. -/
def AuxiliaryFamily.Efficient (F : AuxiliaryFamily) : Prop :=
  ∃ (P : Program) (time : Polynomial ℕ),
    ∀ (x : Bits) (u : Word Bool (F.p x.length)),
      P.OutputsWithin (frame [x, coinBits u]) (coinBits (F.value x u))
        (time.eval (x.length + F.p x.length))

/-- A uniformly randomized polynomial-time algorithm on a pair of binary
strings. Its output is exactly what the machine writes, for every coin tape.
The explicit time and coin polynomials are bounds on real execution. -/
structure RandomizedPairAlgorithm where
  program : Program
  time : Polynomial ℕ
  coins : Polynomial ℕ
  output : Bits → Bits → Bits → Bits
  runs : ∀ (x y : Bits) (ω : Fin (coins.eval (x.length + y.length)) → Bool),
    program.OutputsWithin (frame [x, y, coinBits ω]) (output x y (coinBits ω))
      (time.eval (x.length + y.length))

/-- Success means finding any preimage of the image of an independent uniform u.
The existential preimage also enforces exact output length; malformed outputs
fail. Both the uniform u and the inverter's independent coins are averaged. -/
def inversionSuccess (F : AuxiliaryFamily) (A : RandomizedPairAlgorithm) (x : Bits) : ℝ :=
  eventProbability
    (coinPairLaw (F.p x.length)
      (A.coins.eval (x.length + F.q x.length)))
    (fun pair => ∃ v : Word Bool (F.p x.length),
      A.output x (coinBits (F.value x pair.1)) (coinBits pair.2) = coinBits v ∧
        F.value x v = F.value x pair.1)

/-- The source's strict all-auxiliary-input inversion criterion. -/
def Inverts (F : AuxiliaryFamily) (r : Polynomial ℕ) (A : RandomizedPairAlgorithm) : Prop :=
  ∀ x : Bits, 1 - 1 / ((r.eval x.length : ℕ) : ℝ) < inversionSuccess F A x

/-- Existence in Definition 7.2: ∃ family, ∃ positive polynomial denominator,
¬∃ one PPT algorithm meeting the strict success threshold for every x.
The denominator is positive even at zero; no division-by-zero convention is used. -/
def AuxiliaryOneWayFunctionsExist : Prop :=
  ∃ F : AuxiliaryFamily, F.Efficient ∧ ∃ r : Polynomial ℕ,
    (∀ n, 0 < r.eval n) ∧ ¬ ∃ A : RandomizedPairAlgorithm, Inverts F r A

end AutoregressiveCompression.Main.Supplement


