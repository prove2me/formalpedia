-- Prove2me | Definitions.Def_NovyPQZK_Main_Argument
-- name    : NovyPQZK_Main_Argument
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:54.897509+00:00
-- url     : https://prove2.me/theorems/3fb132bd-5654-45cf-a394-e41683afbb59
-- title:
--   Interactive argument systems (Definition 15) and post-quantum perfect zero knowledge (Definition 16)
-- statement:
--   An interactive protocol $(P,V)$ for a relation $R$: on security parameter $n$, the verifier $V(1^n,x)$ speaks first in each of $\mathrm{rounds}(n,x)$ rounds, the prover $P(1^n,x,w)$ answers, and $V$ outputs $1$ or not.
--
--   - **Efficient**: $P$ and $V$ are PPT parties and $\mathrm{rounds}$ is computable in polynomial time from $(1^n,x)$.
--   - **Complete**: there is a negligible $\mu$ with $\Pr[1\leftarrow[P(1^n,x,w)\rightleftarrows V(1^n,x)]]\ge 1-\mu(n)$ for every $n$ and $(x,w)\in R$.
--   - **Sound argument with error $s(n)$**: for every QPT prover family $\{P^*_n\}$ (its quantum advice is its auxiliary input) and every sequence of inputs $x_n$ of length polynomial in $n$, there is $n_0$ such that for every $n\ge n_0$ with $x_n\notin L_R$,
--   $$\Pr[1\leftarrow[P^*_n(1^n,x_n)\rightleftarrows V(1^n,x_n)]]\le s(n).$$
--   - **Post-quantum perfect zero knowledge** (Def. 16): for every QPT verifier $V^*$ there is a QPT simulator $S_{V^*}$ with the same numbers of auxiliary input and output qubits such that, for every $n$ and every $(x,w)\in R$, $\Phi^n_{x,w} = \Psi^n_x$ as channels: $\Phi^n_{x,w}(\rho)$ is the state of $V^*$'s whole register $VW$ after $[P(1^n,x,w)\rightleftarrows V^*(1^n,x,\rho)]$ and $\Psi^n_x(\rho)$ is the output of $S_{V^*}$ on $(1^n,x,\rho)$, for every density matrix $\rho$ on $V$.
--
--   **Formalization Note** The soundness clause is the eventual form the proof of Theorem 8 gives (finding I2). It is uniform over polynomially bounded input sequences: requiring it only for each fixed $x$ would allow $V$ to decide $x$ by brute force once $n\ge 2^{\mathrm{poly}(|x|)}$.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7, Definition 15 p. 43 and Definition 16 with Fig. 4 p. 49

import Mathlib
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_NovyPQZK_Main_Fidelity
import Definitions.Def_NovyPQZK_Main_Quantum

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §7:
interactive argument systems (Definition 15, p. 43) and post-quantum perfect zero knowledge
(Definition 16 and Fig. 4, p. 49).

A classical interactive protocol `(P, V)` for a relation `R`: the verifier `V` (input
`(1^n, x)`) speaks first in each of `rounds n x` rounds, the prover `P` (input `(1^n, x, w)`)
answers, and after the last round `V` outputs `1` (the string `[true]`) or not.

Readings (findings I2, I3 and the goal's efficiency clause):
* Soundness with error `s(n)` against QPT provers is stated in the eventual form the proof of
  Theorem 8 gives: for every QPT prover family (with its quantum advice, which is its auxiliary
  input) and every polynomially bounded sequence of inputs `x_n`, `Pr[accept] ≤ s(n)` for all large
  `n` with `x_n` outside the language. (Taking `n₀` per fixed `x` alone would let a verifier decide
  `x` by brute force once `n ≥ 2^{poly(|x|)}`, making the goal hold unconditionally.)
* Honest parties: classical uniform PPT with exact uniform sampling (`Party.IsPPT`), and a number
  of rounds computable in polynomial time.
-/

open QAlgorithms

/-- A classical interactive protocol for a relation. -/
structure ArgSystem where
  /-- The honest prover, input `proverInput n x w`. -/
  prover : Party
  /-- The honest verifier, input `commonInput n x`. -/
  verifier : Party
  /-- The number of rounds on security parameter `n` and input `x`. -/
  rounds : ℕ → Bits → ℕ

/-- Efficient honest parties: both are uniform PPT and the number of rounds is computable in
polynomial time from `(1^n, x)`. -/
def ArgSystem.IsEfficient (A : ArgSystem) : Prop :=
  A.prover.IsPPT ∧ A.verifier.IsPPT ∧
    PolyTimeNat (fun s => match unpack s with
      | [a, x] => A.rounds a.length x
      | _ => 0)

/-- `Pr[1 ← [P(1^n, x, w) ⇄ V(1^n, x)]]`. -/
noncomputable def ArgSystem.honestAccept (A : ArgSystem) (n : ℕ) (x w : Bits) : ℝ :=
  acceptProbCC A.verifier A.prover (commonInput n x) (proverInput n x w) (A.rounds n x)

/-- `Pr[1 ← [P*(1^n, x) ⇄ V(1^n, x)]]` for a quantum prover `P*` (at this `n`). -/
noncomputable def ArgSystem.cheatAccept (A : ArgSystem) (Ps : QStrategy) (n : ℕ) (x : Bits) : ℝ :=
  acceptProbQ A.verifier (commonInput n x) Ps (commonInput n x) (A.rounds n x)

/-- Definition 15 (p. 43), completeness: a negligible `μ` with
`Pr[1 ← [P(1^n, x, w) ⇄ V(1^n, x)]] ≥ 1 − μ(n)` for every `n` and every `(x, w) ∈ R`. -/
def ArgSystem.IsComplete (A : ArgSystem) (R : Bits → Bits → Bool) : Prop :=
  ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧
    ∀ n x w, R x w = true → A.honestAccept n x w ≥ 1 - μ n

/-- Definition 15 (p. 43), soundness error `s(n)` against all QPT provers (an argument system),
in the eventual reading the proof of Theorem 8 gives (findings I2): for every QPT prover family
`Ps` (quantum advice included, which is its auxiliary input) and every sequence of inputs `xs n`
of length polynomial in `n`, for all sufficiently large `n`, if `xs n` has no witness then
`Pr[1 ← [Ps n (1^n, xs n) ⇄ V(1^n, xs n)]] ≤ s(n)`. A fixed input `x` is the constant sequence. -/
def ArgSystem.IsSoundArgument (A : ArgSystem) (R : Bits → Bits → Bool) (s : ℕ → ℝ) : Prop :=
  ∀ Ps : ℕ → QStrategy, IsQPT Ps →
    ∀ xs : ℕ → Bits, (∃ p : Polynomial ℕ, ∀ n, (xs n).length ≤ p.eval n) →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, (∀ w, R (xs n) w = false) → A.cheatAccept (Ps n) n (xs n) ≤ s n

/-- `Φⁿ_{x,w}(ρ)` (Fig. 4): the state of the whole register `VW` of the quantum verifier `Vs`
after `[P(1^n, x, w) ⇄ Vs(1^n, x, ρ)]`, on auxiliary input `ρ` (register `V`). -/
noncomputable def ArgSystem.realChannel (A : ArgSystem) (Vs : QStrategy) (n : ℕ) (x w : Bits)
    (ρ : Matrix (Qubits Vs.inQ) (Qubits Vs.inQ) ℂ) : Matrix (Qubits Vs.N) (Qubits Vs.N) ℂ :=
  interactionChannel A.prover (proverInput n x w) Vs (commonInput n x) (A.rounds n x) ρ

/-- Definition 16 (p. 49): `(P, V)` is post-quantum perfect zero-knowledge for `R`: for every QPT
verifier `Vs` there is a QPT simulator `Sim` with (1) the same numbers of auxiliary input and output
qubits as `Vs`, and (2) for every `n` and every `(x, w) ∈ R`, `Φⁿ_{x,w} = Ψⁿ_x` as channels, where
`Ψⁿ_x(ρ)` is the output of `Sim` on `(1^n, x, ρ)`. -/
def ArgSystem.IsPQPerfectZK (A : ArgSystem) (R : Bits → Bits → Bool) : Prop :=
  ∀ Vs : ℕ → ℕ → QStrategy, IsQPT₂ Vs →
    ∃ Sim : ℕ → ℕ → QChannelAlg, IsQPTChan₂ Sim ∧
      ∀ n ℓ, ∃ (hin : (Vs n ℓ).inQ = (Sim n ℓ).inQ) (hout : (Sim n ℓ).outQ = (Vs n ℓ).N),
        ∀ x w : Bits, x.length = ℓ → R x w = true →
          ∀ ρ : Matrix (Qubits (Vs n ℓ).inQ) (Qubits (Vs n ℓ).inQ) ℂ, IsDensity ρ →
            qcast hout ((Sim n ℓ).channel (commonInput n x) (qcast hin ρ)) =
              A.realChannel (Vs n ℓ) n x w ρ

end NovyPQZK.Main


