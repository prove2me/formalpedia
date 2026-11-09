-- Prove2me | Definitions.Def_HSElemKernel_IsCardEncoding
-- name    : HSElemKernel_IsCardEncoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:59.773423+00:00
-- url     : https://prove2.me/theorems/96acf6e7-e094-40f5-bdfb-c5ab3907412a
-- title:
--   Linear-size CNF encoding of $\sum_i x_i \bowtie b$
-- statement:
--   Let $N, b \in \mathbb N$, $\bowtie \in \{=, \le\}$ and $C \in \mathbb N$. A CNF formula $\varphi$ over the $N$ constrained variables $x_1, \dots, x_N$ and $a$ auxiliary variables $y_1, \dots, y_a$ is a **linear-size encoding** of $\sum_i x_i \bowtie b$ with constant $C$ if
--
--   1. an assignment $x \in \{0,1\}^N$ extends to a satisfying assignment $(x, y)$ of $\varphi$ if and only if $\sum_i x_i \bowtie b$;
--   2. $a \le C(N + 1)$ and $\varphi$ has at most $C(N + 1)$ clauses;
--   3. every clause of $\varphi$ has width at most three.
--
--   This is the guarantee of Lemma 3.2 for one constraint.
--
--   **Formalization Note** $O(N)$ is read as $C(N+1)$: at $N = 0$ and $b > 0$ the encoding still needs a clause. Formulas are the published `MantriCVQ.CNF` (a list of clauses, each a list of literals $(v, b)$, the literal $v$ for $b = 1$ and $\neg v$ for $b = 0$; satisfied when its evaluation is true).
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 3.2, p.7

import Mathlib
import Definitions.Def_MantriCVQ_CNF
import Definitions.Def_HSElemKernel_CardOp

namespace HSElemKernel

/-- `φ` is a linear-size CNF encoding, with constant `C`, of the cardinality constraint
`x₁ + ⋯ + x_N ▷◁ b` (Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…, Lemma 3.2,
p.7): `φ` (a CNF formula of the published `MantriCVQ.CNF`, satisfied by an assignment when
`MantriCVQ.CNF.eval` is `true`) has the `N` constrained variables `Sum.inl i` and `a` auxiliary variables `Sum.inr j`,
and
1. an assignment `x` of `x₁, …, x_N` extends to a satisfying assignment of `φ` iff
   `∑ xᵢ ▷◁ b`;
2. `a ≤ C(N + 1)` auxiliary variables and at most `C(N + 1)` clauses;
3. every clause has width at most three.

**Formalization Note** `O(N)` is read as `C(N + 1)`: at `N = 0` with `b > 0` the encoding still
needs a clause. -/
def IsCardEncoding (N b : ℕ) (op : CardOp) (a : ℕ) (φ : MantriCVQ.CNF (Fin N ⊕ Fin a))
    (C : ℕ) : Prop :=
  (∀ x : Fin N → Bool,
      (∃ y : Fin a → Bool, φ.eval (Sum.elim x y) = true) ↔ op.holds (∑ i, (x i).toNat) b) ∧
    a ≤ C * (N + 1) ∧ φ.length ≤ C * (N + 1) ∧ ∀ cl ∈ φ, cl.length ≤ 3

end HSElemKernel


