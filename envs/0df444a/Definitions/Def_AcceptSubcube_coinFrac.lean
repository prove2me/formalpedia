-- Prove2me | Definitions.Def_AcceptSubcube_coinFrac
-- name    : AcceptSubcube_coinFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:45.780628+00:00
-- url     : https://prove2.me/theorems/76031e08-a94e-4ef7-aa4a-91fd5c6ecd30
-- title:
--   Probability over fair coin strings, and computation within a per-input time bound
-- statement:
--   A randomized algorithm is a deterministic machine that reads its input and a string of fair coins. For a coin length $N$ and a property $\mathrm{good}$ of coin strings,
--   $$\mathrm{coinFrac}(N,\mathrm{good})=\frac{\#\{w\in\{0,1\}^N:\mathrm{good}(w)\}}{2^N},$$
--   the exact probability that a uniform coin string of length $N$ is good. For an instance $\mathcal I$ and a polynomial $p$, $\mathrm{coinProb}$ uses the length $N=p(|\mathrm{enc}(\mathcal I)|)$.
--
--   **Computation within a per-input time bound** $T$ on a class $D$ of inputs means: one TM2 machine that, on every input $a\in D$, outputs the encoding of $f(a)$ from the encoding of $a$ within $T(a)$ steps. It expresses running times such as $m^{O_\ell(1+K^{1/\ell})}$ or $(k(1+\delta)/\delta)^r\,\mathrm{poly}(\cdot)$ that are not functions of the input length alone.
--
--   **Formalization Note** "Uniform choices are implemented by rejection sampling from random bits" (p.28): fixed-length fair coin strings are the paper's own model of randomness. The per-input form mirrors Mathlib's `Turing.TM2ComputableInTime`; outside $D$ the machine is unconstrained.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4 (probability); §5.4, p.28 (random bits); Lemma 3.1 p.12, Lemma 3.6 p.14, Theorem 4.1 p.15, Theorem 5.1 p.25 (running times)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_encInst

namespace AcceptSubcube

open Classical in
/-- **Probability over fair coins**: the exact fraction of the `2^N` coin strings of length `N`
satisfying `good`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.1, p.4 ("randomized … with
probability at least"); §5.4, p.28: "Uniform choices are implemented by rejection sampling from
random bits".

**Formalization Note.** A randomized algorithm is a deterministic machine reading its input and a
coin string; its success probability is this fraction, for a coin length fixed by the input. -/
noncomputable def coinFrac (N : ℕ) (good : List Bool → Prop) : ℝ :=
  ((Finset.univ.filter (fun w : Fin N → Bool => good (List.ofFn w))).card : ℝ) / 2 ^ N

/-- The coin probability for an instance `I` with coin length `p(|enc I|)` (Theorem 1.1). -/
noncomputable def coinProb (I : GInst) (p : Polynomial ℕ) (good : List Bool → Prop) : ℝ :=
  coinFrac (p.eval (encInst I).length) good

/-- **Computation within a per-input time bound**: one TM2 machine that, on every input `a` with
`D a`, outputs `eb (f a)` from `ea a` in at most `T a` steps (Mathlib's `Turing.TM2OutputsInTime`,
the per-input form of `Turing.TM2ComputableInTime`).

Cai, Jiang, Liu, STOC 2027 submission (manuscript sha256 66626baf…): used for the running times of
Lemma 3.1 (p.12), Lemma 3.6 (p.14), Theorem 4.1 (p.15) and Theorem 5.1 (p.25), which are not
functions of the input length alone.

**Formalization Note.** `D` is the class of inputs the paper's statement is about (outside it the
machine is unconstrained). The machine's input and output alphabets are identified with `αΓ`, `βΓ`
as in Mathlib's `Turing.TM2ComputableAux`. -/
def ComputesWithinOn {α β αΓ βΓ : Type} (D : α → Prop) (ea : α → List αΓ) (eb : β → List βΓ)
    (f : α → β) (T : α → ℕ) : Prop :=
  ∃ aux : Turing.TM2ComputableAux αΓ βΓ, ∀ a, D a →
    Nonempty (Turing.TM2OutputsInTime aux.tm (List.map aux.inputAlphabet.invFun (ea a))
      (some (List.map aux.outputAlphabet.invFun (eb (f a)))) (T a))

end AcceptSubcube


