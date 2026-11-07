-- Prove2me | Definitions.Def_DDNNFNeg_NNF
-- name    : DDNNFNeg_NNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:51.948189+00:00
-- url     : https://prove2.me/theorems/c808b459-d22e-4af6-ab98-81db164232fe
-- title:
--   Negation normal form circuit (gate array in topological order)
-- statement:
--   An **NNF** (negation normal form circuit, also called a De Morgan circuit) over a finite set of variables $X$ is a Boolean circuit with fan-in-two $\wedge$ and $\vee$ gates whose input gates are labelled by literals. Here it is given by its number of gates $\mathrm{size}$, the gates $g_0, \dots, g_{\mathrm{size}-1}$ listed in topological order (both children of an $\wedge$/$\vee$ gate $g_k$ have index smaller than $k$), and a designated output gate.
--
--   The **size** of the circuit is its number of gates, input gates included.
--
--   **Formalization Note** The array is a directed acyclic graph, so subcircuits may be shared: this is circuit size, not formula size. Gates that are not reachable from the output only add to the size, so minimum sizes are those of the paper.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §3.1, p.8

import Mathlib
import Definitions.Def_DDNNFNeg_Gate

namespace DDNNFNeg

/-- A Boolean circuit in negation normal form over the variable set `X`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §3.1, p.8): `size` gates indexed by `Fin size` in topological order (both children
of an `∧`/`∨` gate have a smaller index than the gate), with a designated output gate `out`.

**Formalization Note** This is a DAG, so subcircuits may be shared: it is a circuit, not a
formula. The size of the circuit is `size`, the number of all its gates including input
gates ("The size of an NNF is its number of gates"). The topological array with a designated
output is an encoding of a rooted DAG; gates not reachable from `out` only add to the size, so
minimum sizes are unchanged. -/
structure NNF (X : Type*) where
  /-- the number of gates -/
  size : ℕ
  /-- the gate at each index -/
  gate : Fin size → Gate size X
  /-- the output gate -/
  out : Fin size
  /-- children precede their parent -/
  wf : ∀ k i j : Fin size, (gate k = .and i j ∨ gate k = .or i j) → i < k ∧ j < k

end DDNNFNeg


