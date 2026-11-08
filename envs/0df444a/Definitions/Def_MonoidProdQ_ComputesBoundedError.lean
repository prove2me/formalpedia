-- Prove2me | Definitions.Def_MonoidProdQ_ComputesBoundedError
-- name    : MonoidProdQ_ComputesBoundedError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:46:50.607776+00:00
-- url     : https://prove2.me/theorems/2cc9604c-aeca-4d62-be69-045fdd2b4b81
-- title:
--   Bounded-error computation by a quantum query algorithm
-- statement:
--   Let $I$ be a finite index set, $\Sigma$ a finite input alphabet, $D\subseteq\Sigma^I$ a promise domain and $f$ a function on inputs. A $T$-query algorithm $\mathcal A$ starts from a fixed unit vector, applies input-independent unitaries $U_0,O_x,U_1,O_x,\dots,O_x,U_T$, measures its whole register in the computational basis and applies a fixed output map to the outcome. Here $O_x$ is the standard query $|i,y\rangle\mapsto|i,y+e_{x_i}\rangle$ (tensored with the identity on the workspace), which reveals the whole letter $x_i$. The algorithm **computes $f$ on $D$ with error at most $1/3$** if
--
--   $$\Pr[\mathcal A \text{ outputs } f(x) \text{ on input } x]\ \ge\ \tfrac23\qquad\text{for every } x\in D.$$
--
--   The error bound is required on every input, not on average.
--
--   **Formalization Note** The algorithm model, the oracle and the output probability are the platform's shared definitions `QAlgorithms.QueryAlg`, `QAlgorithms.xorOracle` and `QueryAlg.outputProb`. Values of $f$ outside $D$ are never read.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Query model, pp.21–22

import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_MonoidProdQ_oneHot
open QAlgorithms

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, "Query model", pp.21–22: the `T`-query algorithm `A` (the platform's
`QAlgorithms.QueryAlg`: an input-independent unit start state and unitaries `U₀, …, U_T`, with
the oracle applied between consecutive unitaries) computes `f` on the promise domain `D` "with
error probability at most 1/3 on every input": for every `x ∈ D` (not on average), measuring
the whole register in the computational basis and applying `out` to the outcome gives `f x` with
probability at least `2/3`. The oracle is the standard query `|i, y⟩ ↦ |i, y + e_{xᵢ}⟩`, which
returns the whole letter `xᵢ` (one-hot encoded, `oneHot`). Values of `f` outside `D` are never
read. -/
def ComputesBoundedError {I Sig Out W : Type*} [Fintype I] [DecidableEq I] [Fintype Sig]
    [DecidableEq Sig] [DecidableEq Out] [Fintype W] [DecidableEq W] {T : ℕ}
    (f : (I → Sig) → Out) (D : Finset (I → Sig)) (A : QueryAlg I (Sig → ZMod 2) W T)
    (out : (I × (Sig → ZMod 2)) × W → Out) : Prop :=
  ∀ x ∈ D, (2 : ℝ) / 3 ≤ A.outputProb (xorOracle fun i => oneHot (x i)) out (f x)

end MonoidProdQ


