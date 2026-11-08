-- Prove2me | Definitions.Def_MantriCVQ_SigmaPi
-- name    : MantriCVQ_SigmaPi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:19.695297+00:00
-- url     : https://prove2.me/theorems/01ebbdb4-f9bd-4646-a04d-7917c1dec14c
-- title:
--   The classes $\Sigma_k^{p,O}$ and $\Pi_k^{p,O}$
-- statement:
--   A language $L$ is in $\Sigma_k^{p,O}$ (flag true) or $\Pi_k^{p,O}$ (flag false) if there are a deterministic oracle machine $V$, polynomials $p_1,\dots,p_k$ and a polynomial clock $q$ such that $V^O$ halts within $q(|s|)$ steps on every input $s$ and
--   $$w\in L\iff Q_1y_1\cdots Q_ky_k\;[V^O(w,y_1,\dots,y_k)=1],\qquad |y_i|=p_i(|w|),$$
--   with alternating quantifiers starting with $\exists$ or $\forall$ respectively.
--
--   **Formalization Note** The clock is required for this oracle $O$ only, which admits more machines than a clock valid for every oracle and so makes $L\notin\mathsf{PH}^O$ the stronger statement. $V$ reads its tuple through the injective encoding `tup`.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_AvgPHETH_AltLen
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The classes `Σ_k^{p,O}` (flag `true`) and `Π_k^{p,O}` (flag `false`) (Mantri, arXiv:2610.37635
(PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)): languages
`{w : Q₁y₁ ⋯ Q_k y_k [V^O(w, y₁, …, y_k) = 1]}`, where `V` is a deterministic polynomial-time oracle
machine, `|y_i| = p_i(|w|)` for polynomials `p_i` and the quantifiers alternate.

**Formalization Note** The polynomial clock `q` holds on every input string, for this oracle `O`
only: this admits more machines than a clock valid for all oracles, so `L ∉ PH^O` is the stronger
statement. `V` reads the tuple through the injective encoding `tup`. The alternating quantifiers
are the published `AvgPHETH.AltLen` (exact lengths, first quantifier `∃` for `true`). -/
def SigmaPi (O : Oracle) (start : Bool) (k : ℕ) : Set (Set Str) :=
  {L | ∃ (V : OTM) (q : Polynomial ℕ) (ps : List (Polynomial ℕ)), ps.length = k ∧
    (∀ s : Str, (V.result O s (q.eval s.length)).isSome) ∧
    ∀ w : Str, w ∈ L ↔ AvgPHETH.AltLen (ps.map fun p => p.eval w.length) start
      (fun ys => V.result O (tup (w :: ys)) (q.eval (tup (w :: ys)).length) = some true)}

end MantriCVQ


