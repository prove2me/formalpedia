-- Prove2me | Definitions.Def_HybridXorLift_HybridAlg
-- name    : HybridXorLift_HybridAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:02.932794+00:00
-- url     : https://prove2.me/theorems/7acdb25e-e5fb-4d85-8af1-febd26a11a14
-- title:
--   Hybrid algorithm (Definition 2.1)
-- statement:
--   A **hybrid algorithm** with input index set $\iota$ is a finite classical decision tree. Each internal node runs a quantum subroutine and each leaf carries an output. A subroutine with $T$ queries and workspace dimension $w$ consists of an input-independent unit state $|\phi\rangle$ on the query register $\iota \times \{0,1\}$ and the workspace $[w]$, and input-independent unitaries $U_0,\dots,U_T$; on input $x \in \{0,1\}^\iota$ it produces
--   $$
--   U_T\, O_x\, U_{T-1} \cdots U_1\, O_x\, U_0\, |\phi\rangle, \qquad O_x|k,b,w\rangle = (-1)^{b x_k}|k,b,w\rangle ,
--   $$
--   with the **controlled phase oracle** $O_x$ (2.1) acting on the query register, and then measures the whole register in the computational basis. The outcome selects the child node.
--
--   A query with control bit $b = 0$ is inactive but still counts as a query.
--
--   **Formalization Note** Subroutines are in the refined form of §2.2: a pure start state and a complete measurement in a fixed basis with one child per outcome. The paper notes that purifying every preparation and dilating every measurement to an isometry followed by a complete measurement changes neither the cost nor the output distribution, so this is the paper's class of algorithms. The number of nodes, the number of rounds and the workspace size are unrestricted.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.1, p.9 (PDF p.11); refinement of §2.2, p.10 (PDF p.12)

import Definitions.Def_QAlgorithms_Defs_Query

namespace HybridXorLift

/-- A hybrid algorithm (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.1, p.9 (PDF p.11), with the refinement of §2.2,
p.10 (PDF p.12)): a finite classical decision tree whose internal nodes run quantum subroutines
and whose leaves carry outputs. A node `round T w A next` runs the subroutine `A`: it starts from
the input-independent unit state `A.start` on the query register `ι × Bool` and the workspace
`Fin w`, applies the input-independent unitaries `U_0, …, U_T` with the controlled phase oracle
(2.1) `O_x |k, b, w⟩ = (−1)^{b x_k} |k, b, w⟩` between consecutive ones (exactly `T` oracle
calls), and measures the whole register in the computational basis; the outcome `z` selects the
child `next z`. A leaf `halt a` outputs `a`.

**Formalization Note** The subroutine is in the refined form of §2.2 ("Without changing the cost
or the output distribution, we purify every preparation, dilate every measurement to an isometry
followed by a complete measurement in a fixed basis"): a pure start state and a complete
measurement in the computational basis with one child per outcome. A mixed start state is
purified and a general measurement is dilated into a larger workspace `Fin w`, so the class of
algorithms is the paper's. The number of rounds and the workspace size are unrestricted. The
tree is finite because every outcome type is finite and the inductive type is well founded. -/
inductive HybridAlg (ι : Type) [Fintype ι] [DecidableEq ι] (α : Type) : Type where
  /-- a leaf with output `a` -/
  | halt (a : α)
  /-- an internal node running a `T`-query subroutine with workspace `Fin w` -/
  | round (T w : ℕ) (A : QAlgorithms.QueryAlg ι Bool (Fin w) T)
      (next : (ι × Bool) × Fin w → HybridAlg ι α)

end HybridXorLift


