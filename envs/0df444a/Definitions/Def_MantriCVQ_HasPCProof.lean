-- Prove2me | Definitions.Def_MantriCVQ_HasPCProof
-- name    : MantriCVQ_HasPCProof
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:49.272216+00:00
-- url     : https://prove2.me/theorems/69754c86-c80c-4c8b-8284-211a05d833e8
-- title:
--   The proof-system clause of Theorem 1.1
-- statement:
--   Relative to $O$, the language $L$ has a public-coin proof with verifier $V$ if:
--
--   1. a uniform polynomial-size quantum prover over $\{H,X,\mathrm{Toffoli}\}$ makes $V$ accept every $w\in L$ with probability exactly $1$;
--   2. every prover strategy makes $V$ accept every $w\notin L$ with probability at most $1/4$;
--   3. $V$ uses at most $\log_2 n/4$ slots on input $1^n$, for every $n\ge1$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.1, pp. 2–3 (PDF pp. 4–5); §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_G0
import Definitions.Def_MantriCVQ_acceptProb
import Definitions.Def_MantriCVQ_QProver

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The proof-system clause of Theorem 1.1 (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33),
Theorem 1.1, pp. 2–3 (PDF pp. 4–5); §3.1, p. 14 (PDF p. 16)): the language `L` has a public-coin proof
with the verifier `V`, a uniform polynomial-size quantum honest prover over `{H, X, Toffoli}` with
perfect completeness, soundness error at most `1/4` against every prover strategy, and at most
`log₂ n / 4` messages on input `1^n`. -/
def HasPCProof (O : Oracle) (L : Set Str) (V : PCVerifier) : Prop :=
  (∃ P : QProver G0, P.Uniform ∧ P.PolyBounded ∧
      ∀ w ∈ L, acceptProb O V (P.toStrategy O) w = 1) ∧
    (∀ w, w ∉ L → ∀ σ : Strategy, acceptProb O V σ w ≤ 1 / 4) ∧
    ∀ n : ℕ, 1 ≤ n → (V.S (unary n) : ℝ) ≤ Real.logb 2 n / 4

end MantriCVQ


