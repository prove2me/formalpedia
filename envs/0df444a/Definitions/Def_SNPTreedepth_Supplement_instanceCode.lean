-- Prove2me | Definitions.Def_SNPTreedepth_Supplement_instanceCode
-- name    : SNPTreedepth_Supplement_instanceCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:54:22.255899+00:00
-- url     : https://prove2.me/theorems/c16c0b2d-3c9e-482b-afbd-eadb48b97f10
-- title:
--   Binary codes of graphs and of (structure, integer) instances
-- statement:
--   Complexity classes in Cook's sense are classes of languages over a finite alphabet, so the inputs of the decision problems of Theorems 55 and 56 are written as bit strings.
--
--   1. A graph $G$ on the vertex set $\{0,\dots,n-1\}$ is written as $n$ in unary (that is, $n$ ones followed by a zero), followed by its $n^2$ adjacency bits.
--   2. A relational structure $R$ on $\{0,\dots,n-1\}$ over a fixed signature, together with an integer $p$, is written as $n$ in unary, then for each relation $E_i$ its $n^{\mathrm{ar}(E_i)}$ membership bits, then a sign bit for $p$ followed by the binary digits of $|p|$.
--
--   Because the signature is fixed by the problem, both codes are uniquely decodable, and every polynomially equivalent code yields the same complexity statements.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Theorems 55 and 56, pp.52–53 (PDF pp.53–54)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure

set_option autoImplicit false

namespace SNPTreedepth.Supplement

open SNPTreedepth

/-- The **binary code of a graph** on `Fin n` (input of Theorem 55, Depian et al., *A Uniform
Algorithm for Strict NP on Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256
98e4e1a9…), p.52): `n` in unary (`n` ones and a zero), followed by the `n²` adjacency bits, the bit
of the pair `(u, v)` at position `n·u + v`.

**Formalization Note** Cook's classes are classes of languages over a finite alphabet, so the
instances are coded over `Bool`; any code polynomially equivalent to this one gives the same
complexity statement. -/
noncomputable def graphCode {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool := by
  classical
  exact List.replicate n true ++ false ::
    List.ofFn (fun m : Fin (n * n) =>
      decide (G.Adj (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2))

/-- The **binary code of a structure and an integer** `(R, p)` (input of Theorem 56, Depian et al.,
p.53): `n` in unary (`n` ones and a zero), then for each relation `E_i` in turn its `n^{ar(E_i)}`
membership bits (tuples ordered by `finFunctionFinEquiv`), then the sign bit of `p` (`true` iff
`p < 0`) followed by the binary digits of `|p|` (least significant first, `Nat.bits`).

**Formalization Note** The signature is fixed by the problem, so the code is uniquely decodable: the
unary prefix gives `n`, the signature gives the length of the relation part, and the rest is `p`,
written in binary as the integer input of a decision problem. Any polynomially equivalent code
gives the same complexity statement. -/
noncomputable def structureIntCode {σ : Signature} {n : ℕ} (R : Structure σ (Fin n)) (p : ℤ) :
    List Bool := by
  classical
  exact List.replicate n true ++ false ::
    ((List.finRange σ.b).flatMap (fun i =>
      List.ofFn (fun m : Fin (n ^ σ.ar i) => decide (finFunctionFinEquiv.symm m ∈ R.rel i))) ++
    (decide (p < 0) :: Nat.bits p.natAbs))

end SNPTreedepth.Supplement


