-- Prove2me | Definitions.Def_NoSignalPA_Box
-- name    : NoSignalPA_Box
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:34.580687+00:00
-- url     : https://prove2.me/theorems/9404e511-fcfc-4348-9de5-24f8d29cb439
-- title:
--   Box $P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z}$ shared by Alice, Bob and Eve
-- statement:
--   A **box** is a conditional probability distribution $P_{\mathbf a,\mathbf b,e\mid\mathbf x,\mathbf y,z}$: for each choice of inputs it gives a probability distribution of the outputs. Alice holds $N_r$ one-bit systems with inputs $\mathbf x\in\{0,1\}^{N_r}$ and outputs $\mathbf a\in\{0,1\}^{N_r}$; Bob's systems, taken as a single system, have input $\mathbf y$ and output $\mathbf b$ in $\{0,1\}^{N_r}$; Eve has one system with input $z\in Z$ and output $e\in E$, for arbitrary sets $Z$ and $E$.
--
--   This is the object on which the security statement quantifies: the eavesdropper may hold any system, constrained only by no signaling.
--
--   **Formalization Note** For fixed inputs $(\mathbf x,\mathbf y,z)$, $P$ is a Mathlib probability mass function on triples $(\mathbf a,\mathbf b,e)$, so $e$ has countable support; no measure theory is used.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, p.2 (Alice has N systems, Bob has N systems, Eve has one 'big' system, jointly distributed according to P_{a,b,e|x,y,z})

import Mathlib
import Definitions.Def_NoSignalPA_Str

namespace NoSignalPA

/-- **A box shared by Alice, Bob and Eve: the conditional distribution `P_{a,b,e|x,y,z}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, p. 2 ("Alice has N systems, Bob has N systems and, without loss of generality, Eve has one
'big' system, jointly distributed according to an arbitrary (unknown) `P_{a,b,e|x,y,z}`"),
printed p. 2 = PDF p. 2.

`P x y z` is a probability distribution on triples `(a, b, e)`: `P x y z (a, b, e)` is
`P_{a,b,e|x,y,z}`. Alice's `Nr` systems have inputs `x` and outputs `a` in `{0,1}^{Nr}`;
Bob's systems, taken as one system, have input `y` and output `b` in `{0,1}^{Nr}`; Eve's system
has input `z ∈ Z` and output `e ∈ E`.

**Formalization Note.** The paper fixes no alphabet for Eve. `Z` and `E` are arbitrary types and
`P x y z` is a Mathlib `PMF` (so `e` has countable support). No measure theory is used. -/
abbrev Box.{u} (Nr : ℕ) (Z E : Type u) : Type u :=
  Str Nr → Str Nr → Z → PMF (Str Nr × Str Nr × E)

end NoSignalPA


