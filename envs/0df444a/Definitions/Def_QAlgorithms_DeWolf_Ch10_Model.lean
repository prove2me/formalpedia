-- Prove2me | Definitions.Def_QAlgorithms_DeWolf_Ch10_Model
-- name    : QAlgorithms_DeWolf_Ch10_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:39:20.936117+00:00
-- url     : https://prove2.me/theorems/c91e815e-e977-4336-8f3c-abe2ea510bc4
-- title:
--   DeWolf Ch10: supporting definitions
-- statement:
--   de Wolf, Chapter 10: the HHL algorithm
--
--   ## QAlgorithms.DeWolf.twoQubitGates
--
--   This is the set of all gates $g$ with natural-number arity equal to $2$ and a complex matrix indexed by pairs of Boolean bits that belongs to the unitary group; equivalently its matrix $M$ satisfies $M^*M=MM^*=I$. No additional restriction is placed on its entries.
--
--   ## QAlgorithms.DeWolf.qlspArity
--
--   For arbitrary natural numbers $N,b$, put $a=\operatorname{clog}_2(N)$, the natural-number ceiling logarithm base $2$. This defines the function on the three indices $0,1,2$ with values $2a,2a+b,a$, respectively. No positivity restriction is imposed on $N$ or $b$; the natural-number ceiling logarithm is $0$ at $N=0$ and $N=1$, so those cases give $(0,b,0)$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/DeWolf/Ch10.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_LinearSystems
/-!
# de Wolf, Chapter 10: the HHL algorithm

de Wolf §10.1–10.3 (PDF pp.95–98) states the HHL bounds only roughly ("roughly `κ²s/ε` queries").
The topic node is therefore stated as Childs–Kothari–Somma 2017 (arXiv:1511.02306v2, cited
"CKS p.N", PDF pages): Problem 1 (QLSP, CKS p.3) and Theorem 2 (HHL algorithm, CKS p.4), in the
cost model of CKS p.3 (query complexity = uses of `P_A`; gate complexity = number of 2-qubit
gates; gate-efficient = gate complexity `O(Q poly(log Q, log N))`).
-/

namespace QAlgorithms.DeWolf

/-- CKS p.3 ("by gate complexity, we mean the total number of 2-qubit gates used in the
algorithm"): the gate set of all 2-qubit unitary gates. Chunk-local. -/
def twoQubitGates : Set Gate :=
  {g | g.arity = 2 ∧ g.IsUnitary}

/-- The register sizes of the three black boxes of the QLSP for an `N × N` matrix whose entries
are written in `b` bits, with `n = ⌈log₂ N⌉`: black box `0` is the column map (1) of `P_A`
(`2n` qubits), black box `1` is the entry map (2) of `P_A` (`2n + b` qubits), black box `2` is
`P_B` (`n` qubits). Chunk-local. -/
def qlspArity (N b : ℕ) : Fin 3 → ℕ :=
  ![Nat.clog 2 N + Nat.clog 2 N, Nat.clog 2 N + Nat.clog 2 N + b, Nat.clog 2 N]


end QAlgorithms.DeWolf


