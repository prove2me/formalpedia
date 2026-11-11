-- Prove2me | Definitions.Def_UnitalMIP_MIP
-- name    : UnitalMIP_MIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:09.150972+00:00
-- url     : https://prove2.me/theorems/e01dfc34-9476-4046-bf7e-6f739566f1f6
-- title:
--   The classical multi-prover class MIP
-- statement:
--   A **classical multi-prover verifier** consists of a question program, a decision program and a polynomial $P$; on an input $z$, $N=P(|z|)$ bounds the number of provers, the number of rounds, the length of the verifier's random seed and the length of every message. In round $j$ the verifier sends prover $i$ a question computed from $z$, its seed and all earlier answers; each prover answers as a function of its own question history; at the end the decision program accepts or rejects. Both programs run in time polynomial in the length of their input. A language is in **MIP** if, for some such verifier and constants $s<c$,
--
--   $$
--   z\in L\Rightarrow \sup_{\pi}\Pr[\text{accept}]\ge c,\qquad z\notin L\Rightarrow \sup_{\pi}\Pr[\text{accept}]\le s,
--   $$
--
--   the supremum over the provers' strategies $\pi$ and the probability over the seed.
--
--   By Babai, Fortnow and Lund, MIP = NEXP; the main theorem states that the noisy fixed-resource class equals both in the first regime.
--
--   **Formalization Note** This is the general class of [BFL91], not the two-prover one-round class: the paper distinguishes them. Provers are deterministic (randomized provers do not increase the value). Programs and running times are those of the published MIPRE cost model; answers are cut to $N$ bits.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 1.1, p.4; proof of Proposition 3.9, p.70

import Mathlib
import Definitions.Def_MIPRE_Foundations_ClassMIPStar

namespace UnitalMIP

open MIPRE MIPRE.Cost

/-- A **classical multi-prover verifier** (the class MIP of Babai, Fortnow, Lund, cited as [BFL91] in
arXiv:2609.39318, version of 2026-11-03, Theorem 1.1, p.4, and Proposition 3.9's proof, p.70): a
closed question program, a closed decision program and one polynomial `P`. On an input `z`,
`N z = P(|z|)` is the number of provers, the number of rounds, the length of the verifier's
random seed and the bound on the length of every message. -/
structure ClassicalVerifier where
  /-- The question program; its input is `(z, seed, i, j)` followed by all earlier answers. -/
  ask : Prog
  /-- It is closed. -/
  ask_closed : ask.WellScoped 1
  /-- The decision program; its input is `(z, seed)` followed by all answers. -/
  decide : Prog
  /-- It is closed. -/
  decide_closed : decide.WellScoped 1
  /-- The polynomial bound `P`. -/
  bound : Polynomial ℕ

namespace ClassicalVerifier

variable (V : ClassicalVerifier)

/-- `N z = P(|z|)`. -/
def N (z : BitStr) : ℕ := V.bound.eval z.length

/-- The data a program reads: a head value followed by a list of strings. -/
def input (head : Data) (l : List BitStr) : Data := Data.cons head (Data.ofList encode l)

open Classical in
/-- The output of a program on a data input, if it halts with (the encoding of) a string;
`[]` otherwise. -/
noncomputable def out (p : Prog) (x : Data) : BitStr :=
  if h : ∃ (r : BitStr) (t : ℕ), p.Runs x (encode r) t then h.choose else []

/-- The question of round `j` to prover `i`, computed from the input, the seed and all answers of
the earlier rounds (in the order round `0` provers `0, …, N−1`, round `1`, …). -/
noncomputable def question (z seed : BitStr) (i j : ℕ) (prev : List BitStr) : BitStr :=
  out V.ask (input (encode (z, (seed, (i, j)))) prev)

/-- The state after `j` rounds against prover strategies `π`: each prover's question history and
the flat list of all answers so far. Prover `i` answers with `π i` applied to its own question
history (its earlier questions and the current one); answers are cut to `N z` bits. -/
noncomputable def run (z seed : BitStr) (π : ℕ → List BitStr → BitStr) :
    ℕ → (ℕ → List BitStr) × List BitStr
  | 0 => (fun _ => [], [])
  | j + 1 =>
    let st := run z seed π j
    let hist : ℕ → List BitStr := fun i => st.1 i ++ [V.question z seed i j st.2]
    (hist, st.2 ++ (List.range (V.N z)).map fun i => (π i (hist i)).take (V.N z))

/-- The verifier accepts on seed `seed` against `π`: after `N z` rounds the decision program halts
with output `1` on `(z, seed)` and all answers. -/
def Accepts (z seed : BitStr) (π : ℕ → List BitStr → BitStr) : Prop :=
  ∃ t, V.decide.Runs (input (encode (z, seed)) (V.run z seed π (V.N z)).2) (encode true) t

open Classical in
/-- The acceptance probability of `π`: the fraction of seeds of length `N z` on which the verifier
accepts. -/
noncomputable def acceptProb (z : BitStr) (π : ℕ → List BitStr → BitStr) : ℝ :=
  ((Data.bitStrsOfLen (V.N z)).filter fun seed => Decidable.decide (V.Accepts z seed π)).length /
    (2 : ℝ) ^ V.N z

/-- The value of the protocol on `z`: the supremum over deterministic prover strategies. -/
noncomputable def value (z : BitStr) : ℝ := ⨆ π : ℕ → List BitStr → BitStr, V.acceptProb z π

/-- **Efficiency** on `z`: on every seed of length `N z`, every prover `i < N z`, every round
`j < N z` and every list of earlier answers of the right shape, the question program halts within
`P(size of its input)` steps with a question of length at most `N z`; and on every complete list of
answers the decision program halts within `P(size of its input)` steps. -/
structure Efficient (z : BitStr) : Prop where
  ask_runs : ∀ seed : BitStr, seed.length = V.N z → ∀ i j : ℕ, i < V.N z → j < V.N z →
    ∀ prev : List BitStr, prev.length = j * V.N z → (∀ a ∈ prev, a.length ≤ V.N z) →
      ∃ (q : BitStr) (t : ℕ), q.length ≤ V.N z ∧
        t ≤ V.bound.eval (input (encode (z, (seed, (i, j)))) prev).size ∧
        V.ask.Runs (input (encode (z, (seed, (i, j)))) prev) (encode q) t
  decide_time : ∀ seed : BitStr, seed.length = V.N z →
    ∀ answers : List BitStr, answers.length = V.N z * V.N z →
      (∀ a ∈ answers, a.length ≤ V.N z) →
        HaltsWithin V.decide (input (encode (z, seed)) answers)
          (V.bound.eval (input (encode (z, seed)) answers).size)

end ClassicalVerifier

/-- **MIP**, the class of languages with classical multi-prover interactive proofs (Babai, Fortnow,
Lund [BFL91], cited in arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…, Theorem 1.1, p.4:
"MIPψ[poly, poly] = NEXP = MIP"; Proposition 3.9's proof, p.70): polynomially many
noncommunicating classical provers, polynomially many rounds, a randomized polynomial-time
verifier, and a constant completeness–soundness gap `s < c`.

**Formalization Note** This is the general class, not the two-prover one-round class
`MIP[poly, poly]`: the source distinguishes the two ("MIP[poly, O(1)] = MIP[poly, poly] = NEXP =
MIP", p.70). Provers are deterministic functions of their own question history (randomized provers
do not increase the value, an average of deterministic ones). The gap convention is that of
`MIPPsi`: fixed real constants `s < c`. -/
def MIP (L : Set BitStr) : Prop :=
  ∃ (V : ClassicalVerifier) (c s : ℝ), s < c ∧ (∀ z, V.Efficient z) ∧
    ∀ z, (z ∈ L → c ≤ V.value z) ∧ (z ∉ L → V.value z ≤ s)

end UnitalMIP


