-- Prove2me | Definitions.Def_QSampVerif_ClassicalVerifier
-- name    : QSampVerif_ClassicalVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:36:42.250131+00:00
-- url     : https://prove2.me/theorems/033935db-24cb-4900-9f14-bdc2298d0c21
-- title:
--   Classical PPT verifiers, $D_{\mathrm{real}}$, the acceptance probability $p$, $D_{\mathrm{ideal}}$ and total variation distance
-- statement:
--   A **classical verifier** is given by functions of the common input $x$ (the number of rounds, the number of private coins, a message-length bound $\ell(x)$) and by a next-message function and an output function of its *view*. The view is $\langle x,r,\mathrm{tr}\rangle$, where $r$ are the private coins (drawn once, uniformly) and every transcript entry is cut to $\ell(x)$ bits; the verifier's own messages are also cut to $\ell(x)$ bits. The verifier speaks first in every round. It is **probabilistic polynomial time (PPT)** when the next-message and output functions are polynomial-time computable on the view, the three counts are polynomial-time computable (in unary), and all three are bounded by one polynomial in $|x|$.
--
--   For a verifier $V$, a prover $P$, a security parameter $\lambda$ and a target circuit $C$:
--
--   1. $D_{\mathrm{real}}=\mathrm{outDist}(V,P,\lambda,C)$ is the distribution of the verifier's output, including rejection: the average over $V$'s coins of the interaction semantics on common input $\langle 1^\lambda,\langle C\rangle\rangle$.
--   2. $p=\sum_{s}D_{\mathrm{real}}(s)$ is the protocol's actual acceptance probability.
--   3. $D_{\mathrm{ideal}}$ returns a fresh sample of $P_C$ with probability $p$ and $\bot$ with probability $1-p$:
--   $$D_{\mathrm{ideal}}(\bot)=1-p,\qquad D_{\mathrm{ideal}}(s)=p\,P_C(s).$$
--   4. $\mathrm{TV}(\mu,\nu)=\tfrac12\sum_z|\mu(z)-\nu(z)|$.
--
--   **Formalization Note** Cutting prover replies to $\ell(x)$ bits keeps the view, and hence the verifier's running time, polynomial in $|x|$ whatever the prover sends.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Theorem 14.5, p.189 (PDF 190); Theorem 14.2, p.185 (PDF 186); Dideal, p.184 (PDF 185); paper.md decisions 5, 7, 9

import Definitions.Def_QSampVerif_ClassicalParty

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Theorem 14.5, p.189 (PDF 190): "a classical PPT verifier".

A classical verifier, given by functions of the common input `x` (number of rounds, number of
private coins, message-length bound) and of its view (next message, final output). The view is
`⟨x, r, transcript⟩` with every transcript entry cut to `msgBound x` bits; the verifier's own
messages are cut to `msgBound x` bits as well. The verifier speaks first in every round (an empty
message is allowed). The output is `none` (`⊥`, rejection) or an accepted string.

**Formalization Note.** Cutting prover replies to `msgBound x` bits keeps the view, and so the
verifier's running time, polynomial in `|x|` however long the prover's replies are. -/
structure ClassicalVerifier where
  /-- Number of rounds on common input `x`. -/
  rounds : Str → ℕ
  /-- Number of private coins on common input `x`. -/
  coinLen : Str → ℕ
  /-- Message-length bound on common input `x`. -/
  msgBound : Str → ℕ
  /-- The next message as a function of the view. -/
  next : Str → Str
  /-- The final output as a function of the view (`none` is `⊥`). -/
  output : Str → Option Str

namespace ClassicalVerifier

/-- The verifier's view on common input `x` with coins `r` after transcript `tr`. -/
def view (V : ClassicalVerifier) (x r : Str) (tr : List (Str × Str)) : Str :=
  tup [x, r, tup (tr.flatMap fun p => [p.1.take (V.msgBound x), p.2.take (V.msgBound x)])]

/-- The verifier with common input `x` and coins `r` fixed, as a classical party (it draws no
fresh coins: its private coins `r` were drawn at the start). -/
def party (V : ClassicalVerifier) (x r : Str) : ClassicalParty where
  coins := fun _ => 0
  msg := fun tr _ => (V.next (V.view x r tr)).take (V.msgBound x)
  out := fun tr => V.output (V.view x r tr)

/-- A classical probabilistic polynomial-time verifier (paper.md decision 5): next message and
output are polynomial-time computable functions of the view, the round count, coin count and
message bound are polynomial-time computable (in unary), and all three are bounded by one
polynomial in `|x|`. -/
def IsPPT (V : ClassicalVerifier) : Prop :=
  PolyTimeComputable V.next ∧ PolyTimeComputable (fun s => encOpt (V.output s)) ∧
  PolyTimeComputable (fun x => unary (V.rounds x)) ∧
  PolyTimeComputable (fun x => unary (V.coinLen x)) ∧
  PolyTimeComputable (fun x => unary (V.msgBound x)) ∧
  ∃ p : Polynomial ℕ, ∀ x : Str, V.rounds x + V.coinLen x + V.msgBound x ≤ p.eval x.length

end ClassicalVerifier

/-- The verifier's output distribution `D_real` (Theorem 14.2, p.185: "the distribution of the
verifier's output, including rejection") when `V` interacts with the prover `P` on security
parameter `λ` and target circuit `C`: the average over the verifier's coins of the interaction
semantics `runParty`. -/
noncomputable def outDist (V : ClassicalVerifier) (P : Prover) (lam : ℕ) (C : TargetCircuit)
    (z : Option Str) : ℝ :=
  ((2 : ℝ) ^ V.coinLen (commonInput lam C))⁻¹ *
    ∑ r : Qubits (V.coinLen (commonInput lam C)),
      runParty (V.party (commonInput lam C) (List.ofFn r)) P (V.rounds (commonInput lam C)) z

/-- The protocol's actual acceptance probability `p` (p.184, p.189): the probability that the
output is not `⊥`. -/
noncomputable def acceptProb (V : ClassicalVerifier) (P : Prover) (lam : ℕ) (C : TargetCircuit) :
    ℝ :=
  ∑' s : Str, outDist V P lam C (some s)

/-- The ideal experiment `D_ideal` (p.184, p.189): "return a fresh sample from P_C with
probability p, return ⊥ with probability 1 − p", where `p` is the actual acceptance probability of
the same verifier, prover, `λ` and `C`. -/
noncomputable def idealDist (V : ClassicalVerifier) (P : Prover) (lam : ℕ) (C : TargetCircuit) :
    Option Str → ℝ
  | none => 1 - acceptProb V P lam C
  | some s => acceptProb V P lam C * C.pushSome (some s)

/-- The total variation distance `½ Σ_z |μ(z) − ν(z)|` of two distributions on verifier outputs. -/
noncomputable def tvDist (μ ν : Option Str → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' z : Option Str, |μ z - ν z|

end QSampVerif


