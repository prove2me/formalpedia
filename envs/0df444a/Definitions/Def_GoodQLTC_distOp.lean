-- Prove2me | Definitions.Def_GoodQLTC_distOp
-- name    : GoodQLTC_distOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:41.863369+00:00
-- url     : https://prove2.me/theorems/50daa53f-3ef5-4c1d-b983-e012169964d7
-- title:
--   Quantum Hamming-distance operator $D_Q$
-- statement:
--   For $0\le a\le N$ let $\Pi_{\le a}$ be the orthogonal projection onto
--   $$
--   Q_{\le a}=\mathrm{span}_{\mathbb C}\{P\psi:\ \psi\in Q,\ P\in\mathcal P_N,\ \mathrm{wt}(P)\le a\}.
--   $$
--   The **quantum Hamming-distance operator** is
--   $$
--   D_Q=\sum_{a=0}^{N-1}(I-\Pi_{\le a}). \tag{3.2}
--   $$
--   $\mathrm{Tr}(\varrho D_Q)$ is the distance of a state from the code.
--
--   **Formalization Note** The span ranges over $P=X^xZ^z$ (phases do not change a span); $N$ is the number of qubits and the sum runs over $a\in\{0,\dots,N-1\}$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.3, Equation (3.2), p.14 (PDF p.17)

import Mathlib
import Definitions.Def_GoodQLTC_pauliX
import Definitions.Def_GoodQLTC_codeSpace

namespace GoodQLTC

/-- The space `Q_{≤a} := span_ℂ{Pψ : ψ ∈ Q, P ∈ P_N, wt(P) ≤ a}`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §3.3, p.14.

**Formalization Note.** The span ranges over `P = X^x Z^z` with `wt(P) = |supp x ∪ supp z| ≤ a`;
the phases `i^c` of `P_N` are nonzero scalars and do not change the span. -/
noncomputable def lowWeightSpan {ι κX κZ : Type} [Fintype ι] [DecidableEq ι]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) (a : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (ι → ZMod 2)) :=
  Submodule.span ℂ {φ | ∃ ψ ∈ codeSpace HX HZ, ∃ x z : ι → ZMod 2, pauliWeight x z ≤ a ∧
    φ = Matrix.toEuclideanLin (pauliX x * pauliZ z) ψ}

/-- The orthogonal projection `Π_{≤a}` onto `Q_{≤a}`, as a matrix (arXiv:2609.20780, §3.3,
p.14). -/
noncomputable def lowWeightProj {ι κX κZ : Type} [Fintype ι] [DecidableEq ι]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) (a : ℕ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  Matrix.toEuclideanLin.symm ((lowWeightSpan HX HZ a).starProjection : _ →ₗ[ℂ] _)

/-- The **quantum Hamming-distance operator** `D_Q := ∑_{a=0}^{N−1} (I − Π_{≤a})`, Gay–Jeronimo,
arXiv:2609.20780 (held version), §3.3, Equation (3.2), p.14, where `N` is the number of qubits.

**Formalization Note.** `N = |ι|`; the sum runs over `a ∈ {0, …, N−1}` (`Finset.range N`), with
`Q_{≤0} = Q` since the identity is the only Pauli of weight `0` up to phase. -/
noncomputable def distOp {ι κX κZ : Type} [Fintype ι] [DecidableEq ι]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ a ∈ Finset.range (Fintype.card ι), (1 - lowWeightProj HX HZ a)

end GoodQLTC


