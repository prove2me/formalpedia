-- Prove2me | Definitions.Def_FanInSemigroup_HasConstDepthPolySize
-- name    : FanInSemigroup_HasConstDepthPolySize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:47.115652+00:00
-- url     : https://prove2.me/theorems/d1212992-0665-45ef-aa77-527a35a3f453
-- title:
--   Constant-depth, polynomial-size circuits computing a semigroup
-- statement:
--   Let $S$ be a semigroup and $e:S\to\{0,1\}^k$ an encoding of its elements by $k$ bits. A circuit with $kn$ inputs and $k$ outputs **computes the semigroup** on $n$ elements if, whenever the inputs are fed the encodings of elements $a_1,\dots,a_n$, the output is the encoding of the product $a_1a_2\cdots a_n$.
--
--   There are **constant depth, polynomial size circuits** computing $S$ under $e$ if there are constants $D,c$ such that for every $n\ge 1$ some circuit computes the $n$-fold product with depth at most $D$ and size at most
--
--   $$
--   c\cdot n^{c}.
--   $$
--
--   This is the left side of the mission's characterization.
--
--   **Formalization Note** The family is non-uniform, one circuit per $n\ge 1$; the paper states no uniformity condition. The constants may depend on $S$ and $e$, never on $n$. An input that is not a tuple of encodings is unconstrained, as on the page. The form $c\cdot n^c$ is equivalent at $n\ge 1$ to any polynomial bound, and does not collapse to $1$ at $n=1$.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, p.54

import Definitions.Def_FanInSemigroup_Circuit
import Definitions.Def_FanInSemigroup_wordProd

set_option autoImplicit false

namespace FanInSemigroup

variable {S : Type*} [Semigroup S]

/-- The circuit `C` with `kn` inputs and `k` outputs computes the `n`-fold product of `S` under
the encoding `e`. Chandra, Fortune, Lipton, STOC 1983, §2, p.54: "Suppose S is a semigroup and
suppose an encoding of the elements of S using k bits is fixed. Then a circuit with kn inputs and
k outputs computes the semigroup if whenever the inputs are fed the encodings of elements
a1,...,an, the output is the encoding of the product a1a2...an."

**Formalization Note.** The variable `(i, j)` carries bit `j` of the `i`-th element. Correctness
is required on tuples of codewords only: as on the page, an input that is not a tuple of encodings
is unconstrained. -/
def ComputesProduct {k n : ℕ} (e : S → Fin k → Bool) (hn : 1 ≤ n)
    (C : Circuit (Fin n × Fin k) (Fin k)) : Prop :=
  ∀ a : Fin n → S, C.eval (fun v => e (a v.1) v.2) = e (tupleProd hn a)

/-- "There are constant depth, polynomial size circuits computing" the semigroup `S` under the
encoding `e` (Chandra, Fortune, Lipton, STOC 1983, Theorem 2.1, p.54): one depth bound `D` and one
size constant `c` such that every `n ≥ 1` has a circuit computing the `n`-fold product, of depth
at most `D` and size at most `c · n^c`.

**Formalization Note.** A non-uniform family, one circuit per `n ≥ 1`; the paper states no
uniformity condition and imposes no bound on fan-in. `D` and `c` may depend on `S` and `e`, never
on `n`. The bound `c · n^c` is equivalent at `n ≥ 1` to any polynomial bound, and does not reduce
to `1` at `n = 1`. -/
def HasConstDepthPolySize {k : ℕ} (e : S → Fin k → Bool) : Prop :=
  ∃ D c : ℕ, ∀ (n : ℕ) (hn : 1 ≤ n), ∃ C : Circuit (Fin n × Fin k) (Fin k),
    ComputesProduct e hn C ∧ C.depth ≤ D ∧ C.size ≤ c * n ^ c

end FanInSemigroup


