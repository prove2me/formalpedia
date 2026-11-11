-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_TimeUniformVerifiers
-- name    : UnitaryQIPPSPACE_TimeUniformVerifiers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:48.550192+00:00
-- url     : https://prove2.me/theorems/4b19a6fb-b8d2-497a-bd79-08592a2b6b19
-- title:
--   Time-uniform verifier families (Definition 2.6)
-- statement:
--   A family of verifiers $\{V_n\}$, $V_n$ with $k(n)$ rounds, is **time uniform** if there are a deterministic Turing machine $M$ and a polynomial $p$ such that for every $n$: the number of rounds $k(n)$ and the size of $V_n$ are at most $p(n)$, and $M$ on input $1^n$ halts within $p(n)$ steps with the description of $V_n$ (register sizes and the circuits $V_{n,1},\dots,V_{n,k(n)}$).
--
--   This is the efficiency requirement on the verifier of $\mathsf{unitaryQIP}$.
--
--   **Formalization Note** One polynomial bounds rounds, size and time (equivalent to three). Machines are the published `QAdvFew.PoQOracle.OTM` with the empty oracle.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Definition 2.6, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_UnitaryQIPPSPACE_Verifier
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- **Time-uniform verifier family** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, Definition 2.6, p. 11 (PDF p. 13)): "A family of
quantum verifiers `{V_n}`, where `V_n = (V_{n,i})_{i=1}^{k(n)}` is a `k(n)`-round quantum verifier, is
polynomial-size if there exists a polynomial `p` such that, for every `n ∈ ℕ`, both the number of
rounds `k(n)` and the size of `V_n` are at most `p(n)`. We say that `{V_n}` is time-uniform if it is
polynomial-size and there exists a deterministic Turing machine running in time polynomial in `n`
that, on input `1^n`, outputs the descriptions of `V_{n,1}, …, V_{n,k(n)}`."

Here one machine `M` and one polynomial `p`: `k(n) ≤ p(n)`, `size(V_n) ≤ p(n)`, and `M` on `1^n` has
halted after `p(n)` steps with the description of `V_n` (register sizes and rounds) on its work
tape.

**Formalization Note** Machines are the published `QAdvFew.PoQOracle.OTM` with the empty oracle.
A single polynomial bounding rounds, size and time is equivalent to three polynomials (take their
sum). -/
def TimeUniformVerifiers (V : ℕ → Verifier) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ n : ℕ,
    (V n).rounds.length ≤ p.eval n ∧ (V n).size ≤ p.eval n ∧
    M.result noOracle (unary n) (p.eval n) ≠ none ∧
    M.output noOracle (unary n) (p.eval n) = (V n).code

end UnitaryQIPPSPACE


