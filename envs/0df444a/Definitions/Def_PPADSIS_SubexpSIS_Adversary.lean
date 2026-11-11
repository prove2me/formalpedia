-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_Adversary
-- name    : PPADSIS_SubexpSIS_Adversary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:46:39.326221+00:00
-- url     : https://prove2.me/theorems/b52935b1-e38b-4db3-be16-7a1126140c31
-- title:
--   Non-uniform families of probabilistic circuits with string output, their size and success probability
-- statement:
--   An **adversary** is a non-uniform family $A=\{A_\lambda\}$ of probabilistic Boolean circuits with string output (§3, p. 20). A probabilistic circuit is a Boolean circuit whose input wires are the challenge $x$ followed by a number of random coins; on $x$ and coins $c$ it outputs $C(x\,c)$ if it has exactly $|x|+\#\text{coins}$ inputs, and otherwise its run fails. $\Pr[E(A_\lambda(x))]$ is the fraction of coin strings for which the run succeeds with an output satisfying $E$.
--
--   In the formalization $A_{\lambda,\ell}$ is the circuit used at security parameter $\lambda$ on challenges of length $\ell$. The adversary has **size at most $b$ at $\lambda$** if every $A_{\lambda,\ell}$ is well formed with $|A_{\lambda,\ell}|\le b$ (inputs plus gates), **size $s(\lambda)$** if this holds with $b=s(\lambda)$ at every $\lambda$, and **polynomial size** if it has size $(\lambda+2)^c$ for one $c$.
--
--   These are the adversaries of every hardness statement: "Unless stated otherwise, adversaries are non-uniform families $A=\{A_\lambda\}_{\lambda\in\mathbb N}$ of probabilistic polynomial-size circuits ... All probabilities are taken over the adversary's coins as well as over the sampling shown in the experiment."
--
--   **Formalization Note** One circuit per $(\lambda,\ell)$ instead of one per $\lambda$: a circuit of size $s$ reads at most $s$ bits, so at a fixed $\lambda$ only $\ell\le s(\lambda)$ matter and the circuits combine into a single circuit of size $O(s(\lambda)^2)$ reading a padded challenge; for polynomial size bounds, and for fixed-length challenges (SIS), the two models give the same hardness notions. No machine generates the circuits.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 20, §3 'Adversaries'

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Circuit
import Definitions.Def_PPADSIS_SubexpSIS_Algorithms

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- A **probabilistic circuit**: a Boolean circuit whose input wires are the challenge followed by
`coins` random coins. -/
structure ProbCircuit where
  circ : Circuit
  coins : ℕ

/-- The output of a probabilistic circuit on challenge `x` with coins `c`: the circuit's output on
`x ++ c` when it has exactly `|x| + coins` input wires, and `none` (a failed run) otherwise. -/
def ProbCircuit.out (B : ProbCircuit) (x : List Bool) (c : Fin B.coins → Bool) :
    Option (List Bool) :=
  if B.circ.nIn = x.length + B.coins then some (B.circ.eval (x ++ List.ofFn c)) else none

open Classical in
/-- `Pr[E(B(x))]` over uniform coins; a failed run counts as failure. -/
noncomputable def ProbCircuit.prob (B : ProbCircuit) (x : List Bool) (E : List Bool → Prop) : ℝ :=
  coinAvg B.coins (fun c => match B.out x c with
    | some y => if E y then 1 else 0
    | none => 0)

/-- An **adversary** (Choudhuri, *PPAD Hardness from SIS*, STOC 2027 submission (manuscript sha256
17abad73…), §3 Adversaries, p. 20: "non-uniform families `A = {A_λ}_{λ∈ℕ}` of probabilistic
polynomial-size circuits"; "All probabilities are taken over the adversary's coins as well as over
the sampling shown in the experiment"): a non-uniform family of probabilistic circuits with
string output. `A λ ℓ` is the circuit used at security parameter `λ` on challenges of length `ℓ`.

**Formalization Note** One circuit per `(λ, ℓ)` rather than one per `λ`: a size bound applies to
every `A λ ℓ`, and a circuit of size `s` reads at most `s` bits, so at a fixed `λ` only lengths
`ℓ ≤ s(λ)` matter and the circuits combine into one of size `O(s(λ)²)`; for polynomial and for
`2^{n^ν}` size bounds with fixed-length challenges (SIS) the two models coincide. No machine
generates the circuits. -/
def Adversary : Type := ℕ → ℕ → ProbCircuit

/-- `Pr[E(A_λ(x))]` over the adversary's coins. -/
noncomputable def Adversary.prob (A : Adversary) (lam : ℕ) (x : List Bool)
    (E : List Bool → Prop) : ℝ :=
  (A lam x.length).prob x E

/-- At security parameter `λ` the adversary has **size at most `b`**: every circuit `A λ ℓ` is well
formed and has size (inputs plus gates) at most `b`. -/
def Adversary.SizeAtMost (A : Adversary) (lam : ℕ) (b : ℝ) : Prop :=
  ∀ ℓ, (A lam ℓ).circ.WF ∧ ((A lam ℓ).circ.size : ℝ) ≤ b

/-- The adversary has **size `s(λ)`**: size at most `s λ` at every `λ`. -/
def Adversary.SizeLE (A : Adversary) (s : ℕ → ℝ) : Prop := ∀ lam, A.SizeAtMost lam (s lam)

/-- The adversary has **polynomial size**: size at most `(λ + 2)^c` for one exponent `c`. -/
def Adversary.PolySize (A : Adversary) : Prop :=
  ∃ c : ℕ, A.SizeLE (fun lam => ((lam : ℝ) + 2) ^ c)

end PPADSIS.SubexpSIS


