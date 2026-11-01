-- Prove2me | Definitions.Def_WildeQIT_EADamping_EACode_errorProb
-- name    : WildeQIT_EADamping_EACode_errorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:38:10.734931+00:00
-- url     : https://prove2.me/theorems/79a86345-059a-47be-9116-4dd67f05897f
-- title:
--   Error probability $p_e(m)$ of an entanglement-assisted code
-- statement:
--   For an entanglement-assisted classical code over a channel $\mathcal N$ and a message $m$, the **probability of error** is
--
--   $$
--   p_e(m)\equiv\operatorname{Tr}\bigl\{(I-\Lambda^m_{B^nT_B})\,\mathcal N_{A'^n\to B^n}(\mathcal E^m_{T_A\to A'^n}(\Psi_{T_AT_B}))\bigr\},\qquad \mathcal N_{A'^n\to B^n}\equiv(\mathcal N_{A'\to B})^{\otimes n},
--   $$
--
--   the probability that Bob's decoding POVM does not return $m$ when Alice sends $m$.
--
--   **Formalization Note** $\Psi$ enters as $|\Psi\rangle\langle\Psi|$ (`QAlgorithms.pureDensity`); the encoder and the $n$ channel uses act on the left factor through `leftApply`, with the Kraus families of $\mathcal E^m$ and of $\mathcal N^{\otimes n}$ (`powKraus`). The trace of a positive semidefinite operator is real, and its real part is taken.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.1, p. 589, (21.5)–(21.7)

import Definitions.Def_WildeQIT_EADamping_EACode
import Definitions.Def_WildeQIT_EADamping_leftApply
import Definitions.Def_WildeQIT_EADamping_powKraus

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.1, p. 589, (21.5)–(21.7)
(the error probability of a message under an entanglement-assisted code).
-/

namespace WildeQIT.EADamping

/-- **Error probability `p_e(m)` of message `m`** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, §21.1, p. 589, (21.7)):
`p_e(m) ≡ Tr{(I − Λ^m_{Bⁿ T_B}) N_{A′ⁿ→Bⁿ}(E^m_{T_A→A′ⁿ}(Ψ_{T_A T_B}))}`, with
`N_{A′ⁿ→Bⁿ} ≡ (N_{A′→B})^{⊗n}` acting on the encoded systems `A′ⁿ` and `T_B` untouched.

**Formalization Note.** The state `Ψ` is `QAlgorithms.pureDensity c.Ψ`; the encoder and the `n`
channel uses act on the left factor via `leftApply`, with Kraus families `(c.enc m).K` and
`powKraus N n`. The trace of a positive semidefinite operator is real; the real part is taken. -/
noncomputable def EACode.errorProb {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] {n k : ℕ} (c : EACode a b n k) (N : QChannel a b) (m : Fin k) : ℝ :=
  ((1 - c.dec m) *
    leftApply (powKraus N n) (leftApply (c.enc m).K (QAlgorithms.pureDensity c.Ψ))).trace.re

end WildeQIT.EADamping


