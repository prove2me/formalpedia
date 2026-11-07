-- Prove2me | Definitions.Def_KTUnitary_Synth_PromisePSPACE
-- name    : KTUnitary_Synth_PromisePSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:46.074146+00:00
-- url     : https://prove2.me/theorems/ab95ebd0-b2ac-48e4-b27c-bd567883e627
-- title:
--   $\mathsf{PSPACE}^L$ on promise problems
-- statement:
--   A promise problem $(Y,N)$ is in $\mathsf{PSPACE}^L$ if there are a deterministic $L$-oracle Turing machine $M$ and a polynomial $p$ such that on every input $x$ the run of $M^L$ halts, visits at most $p(|x|)$ cells (the oracle query tape included), accepts if $x\in Y$ and rejects if $x\in N$.
--
--   On languages this is the published class `QAdvFew.PoQOracle.PSPACE`: $(A,A^{\mathrm c})\in\mathsf{PSPACE}^L$ exactly when $A\in\mathsf{PSPACE}^L$. Proposition 4.8 and Theorem 6.17 compare it with quantum space classes, which are classes of promise problems.
--
--   **Formalization Note** Counting the query tape is the convention of footnote 6, p. 15 (an exponentially long oracle tape is not allowed).
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Proposition 4.8, p. 15; Theorem 6.17, p. 30

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_KTUnitary_Synth_PromiseProblem

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **`PSPACE^L` on promise problems** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Proposition 4.8, p. 15, and Theorem 6.17, item 7,
p. 30, where `PSPACE^L` contains the promise problems `BQPSPACE^L` and `UEntryApx`): a promise
problem `(Y, N)` is in it if some deterministic `L`-oracle machine `M` and polynomial `p` are
such that on every input `x` the run halts at some step `T`, visits at most `p(|x|)` cells (query
tape included), and accepts if `x ∈ Y` and rejects if `x ∈ N`.

**Formalization Note** The machine model and the space measure are those of the published
`QAdvFew.PoQOracle.PSPACE` (oracle query tape counted, as footnote 6, p. 15 requires). On a
language `A`, `(A, Aᶜ) ∈ PromisePSPACE L ↔ A ∈ QAdvFew.PoQOracle.PSPACE L`. -/
def PromisePSPACE (L : Oracle) : Set PromiseProblem :=
  {pr | ∃ (M : OTM) (p : Polynomial ℕ), ∀ x : Str, ∃ T : ℕ,
    M.result L x T ≠ none ∧ M.space L x T ≤ p.eval x.length ∧
    (x ∈ pr.1 → M.result L x T = some true) ∧ (x ∈ pr.2 → M.result L x T = some false)}

end KTUnitary.Synth


