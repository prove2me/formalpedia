-- Prove2me | Definitions.Def_LawLocalComp_PolyLawMap
-- name    : LawLocalComp_PolyLawMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:58.462097+00:00
-- url     : https://prove2.me/theorems/6b8d1c3c-c836-4755-87e5-b6212cec326f
-- title:
--   Polynomial-time parametrized law map
-- statement:
--   A family of maps $\Phi_p$ indexed by parameters $p$ is **polynomial-time on the class $\mathcal C$** if a single Turing machine, with running time bounded by one polynomial in the input length, sends every input $(p,\ell)$ to a list representing $\Phi_p(X)$ whenever $\ell$ represents a law $X\in\mathcal C$.
--
--   **Formalization Note** The machine model is Mathlib's `Turing.TM2ComputableInPolyTime`, with the input encoding `lawInputEnc` and the output encoding `encPairs`. Since the machine must be correct on every list representing the law, it computes a function of the law; outputs are rational since the machine returns rationals.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; Lemmas 4.1–4.3; Proposition 7.3

import Mathlib
import Definitions.Def_LawLocalComp_lawInputEnc
import Definitions.Def_LawLocalComp_IsListRep

namespace LawLocalComp

/-- **A parametrized law map computable in polynomial time.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2 ("They … are polynomial in input bits, 1/ε and logarithmic supplied
resources"); Lemmas 4.1–4.3, pp.6–7; Proposition 7.3, p.13.

`PolyLawMap params pad cls Φ`: one Turing machine, running in time polynomial in the input length,
maps the input `(p, ℓ)` (encoded by `lawInputEnc params pad`) to a list representing `Φ p X`, for
every parameter `p` and every list `ℓ` representing a law `X` in the class `cls`.

**Formalization Note.** Mathlib's `Turing.TM2ComputableInPolyTime` fixes a polynomial for all inputs.
The machine must be correct on every list representing the law (any order, repeated atoms), so it
computes a function of the law. Outputs are rational because the machine returns rationals. -/
def PolyLawMap {P : Type} (params : P → List ℚ) (pad : P → ℕ) (cls : Law → Prop)
    (Φ : P → Law → Law) : Prop :=
  ∃ f : P × List (ℚ × ℚ) → List (ℚ × ℚ),
    Nonempty (Turing.TM2ComputableInPolyTime (lawInputEnc params pad) encPairs f) ∧
      ∀ (p : P) (l : List (ℚ × ℚ)) (X : Law), cls X → IsListRep l X → IsListRep (f (p, l)) (Φ p X)

end LawLocalComp


