-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_TreePuzzle
-- name    : PPADSIS_SubexpSIS_TreePuzzle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:47:49.620212+00:00
-- url     : https://prove2.me/theorems/b74191bf-2287-4c7d-aa14-47a51cc97d00
-- title:
--   Average-case tree puzzles: syntax, efficiency and tree structure (Definition 4.3)
-- statement:
--   An **average-case tree puzzle** $(F,D)$ (§4.2) consists of a deterministic algorithm $F(t,x)\to y$, with a difficulty parameter $t\in\mathbb N$ and a string $x$, and a probabilistic algorithm $D(t,1^\lambda)\to x$. Its syntax bounds the lengths: $|F(t,x)|\le\mathrm{poly}(\log t,|x|)$ and $|x|\le\mathrm{poly}(\log t,\lambda)$ for outputs $x$ of $D(t,1^\lambda)$.
--
--   The **efficiency** property of Definition 4.3: $F(t,x)$ runs in time $t\cdot\mathrm{poly}(\log t,|x|)$, and $D(t,1^\lambda)$ runs in time $\mathrm{poly}(\log t,\lambda)$.
--
--   The **tree structure** property of Definition 4.3: for every $t=2^p$ and $x$, the value $F(t,x)$ is the output of a regular tree circuit $C_{t,x}=(p,C_0,\dots,C_p)$, and a deterministic algorithm computes the description of $C_{t,x}$ from $(t,x)$ in time $\mathrm{poly}(p,|x|)$.
--
--   (Definition 4.3 has a third property, average-case hardness against non-faulty solvers, which Theorem 4.7 replaces by its own hypothesis and which this mission does not use.)
--
--   **Formalization Note** $\mathrm{poly}(a,b)$ is $(a+b+2)^k$ for one $k$, $\log=\lfloor\log_2\rfloor$. The input $(t,1^\lambda)$ of $D$ is `encNat t` followed by $1^\lambda$ (length $\Theta(\log t+\lambda)$), and $D$ is probabilistic polynomial time on it. $F$'s running time is that of one Mathlib `FinTM2` machine on `encNat t ++ x`, bounded by $(t+1)\cdot(\log t+|x|+2)^k$; the factor $t+1$ instead of $t$ only matters at $t=0$, where $\log t$ is undefined. The tree-structure algorithm reads `encNat (2^p) ++ x`, of length $\Theta(p+|x|)$.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 25, §4.2 'Syntax'; p. 26, Definition 4.3 (efficiency, tree structure)

import Mathlib
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPADSIS_SubexpSIS_Algorithms
import Definitions.Def_PPADSIS_SubexpSIS_RegularTreeCircuit

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- The input `(t, 1^λ)` of a puzzle sampler: `encNat t` followed by `1^λ`. -/
def puzzleCode (tl : ℕ × ℕ) : List Bool := encNat tl.1 ++ unary tl.2

/-- **Average-case tree puzzle syntax** (Choudhuri, *PPAD Hardness from SIS*, STOC 2027 submission
(manuscript sha256 17abad73…), §4.2, p. 25): a deterministic algorithm `F(t, x) → y` with a
difficulty parameter `t ∈ ℕ` and a string `x`, and a probabilistic algorithm `D(t, 1^λ) → x`
(with explicit coins). -/
structure TreePuzzle where
  F : ℕ → List Bool → List Bool
  D : CoinAlg puzzleCode

/-- The **length bounds of the syntax** (p. 25): `|F(t, x)| ≤ poly(log t, |x|)` and every output
`x` of `D(t, 1^λ)` has `|x| ≤ poly(log t, λ)`; here `poly(a, b)` is `(a + b + 2)^k` for one `k`
and `log` is `Nat.log 2`. -/
def TreePuzzle.SyntaxBounds (Z : TreePuzzle) : Prop :=
  ∃ k : ℕ, (∀ t x, (Z.F t x).length ≤ (Nat.log 2 t + x.length + 2) ^ k) ∧
    ∀ t lam x, Z.D.InSupport (t, lam) x → x.length ≤ (Nat.log 2 t + lam + 2) ^ k

/-- The **efficiency** property of Definition 4.3 (p. 26):
- `F(t, x)` runs in time `t · poly(log t, |x|)`: one machine computes `F(t, x)` from
  `encNat t ++ x` within `(t + 1) · (log t + |x| + 2)^k` steps, for one `k`;
- `D(t, 1^λ)` runs in time `poly(log t, λ)`: it is probabilistic polynomial time on its input
  `encNat t ++ 1^λ`, whose length is `Θ(log t + λ)`, with polynomially many coins. -/
def TreePuzzle.Efficient (Z : TreePuzzle) : Prop :=
  (∃ k : ℕ, TimeBoundedOn (fun a : ℕ × List Bool => encNat a.1 ++ a.2) (fun a => Z.F a.1 a.2)
      (fun a => (a.1 + 1) * (Nat.log 2 a.1 + a.2.length + 2) ^ k)) ∧
  Z.D.IsPPT

/-- The **tree structure** property of Definition 4.3 (p. 26): for every `t = 2^p` and `x`, the
value `F(t, x)` is the output of a regular tree circuit `C_{t,x} = (p, C0, …, Cp)`, and a
deterministic algorithm computes the description of `C_{t,x}` from `(t, x)` (written
`encNat t ++ x`, of length `Θ(p + |x|)`) in time `poly(p, |x|)`. -/
def TreePuzzle.TreeStructured (Z : TreePuzzle) : Prop :=
  ∃ G : ℕ → List Bool → RTC,
    PPSLattice.PolyTimeOn (fun a : ℕ × List Bool => encNat (2 ^ a.1) ++ a.2)
      (fun a => (G a.1 a.2).enc) ∧
    ∀ (p : ℕ) (x : List Bool), (G p x).WF ∧ (G p x).p = p ∧ (G p x).output = Z.F (2 ^ p) x

end PPADSIS.SubexpSIS


