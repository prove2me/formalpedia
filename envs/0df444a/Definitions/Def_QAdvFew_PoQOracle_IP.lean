-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_IP
-- name    : QAdvFew_PoQOracle_IP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:46.551422+00:00
-- url     : https://prove2.me/theorems/345ca40a-dfaf-4e70-8f11-5fd2e47d28ac
-- title:
--   $\mathsf{IP}^O$
-- statement:
--   A language $L$ is in $\mathsf{IP}^O$ if there is a PPT oracle verifier $V^O$ in a polynomial-round protocol with classical communication such that, for every $x$: if $x\in L$, some unbounded prover makes $V^O$ accept $x$ with probability at least $2/3$; and if $x\notin L$, every unbounded prover makes it accept with probability at most $1/3$. Both parties have access to $O$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.8, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_CVerifier
import Definitions.Def_QAdvFew_PoQOracle_UProver

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The class `IP^O` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity
Implications*, arXiv:2611.05303v1, Definition 3.8, p. 13 (PDF p. 15)): `L ∈ IP^O` if there is a PPT
oracle verifier `V^O` in a polynomial-round protocol with classical communication such that, for
every `x`: if `x ∈ L`, some unbounded prover makes `V` accept `x` with probability `≥ 2/3`; if
`x ∉ L`, every unbounded prover makes it accept with probability `≤ 1/3`. Both parties have access
to `O`.

**Formalization Note** The verifier is a `CVerifier` on common input `x`, with rounds, message length
and coins polynomial in `|x|`; provers are deterministic functions (`UProver`). -/
def IP (O : Oracle) : Set (Set Str) :=
  {L | ∃ V : CVerifier, ∀ x : Str,
    (x ∈ L → ∃ P : UProver, (2 : ℝ) / 3 ≤
      acceptProb (V.R.eval x.length) (V.ℓ.eval x.length) (V.lik O x x.length) (P.lik x)) ∧
    (x ∉ L → ∀ P : UProver,
      acceptProb (V.R.eval x.length) (V.ℓ.eval x.length) (V.lik O x x.length) (P.lik x) ≤
        (1 : ℝ) / 3)}

end QAdvFew.PoQOracle


