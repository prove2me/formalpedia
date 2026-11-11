-- Prove2me | Definitions.Def_UnitalMIP_MIPPsi
-- name    : UnitalMIP_MIPPsi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:51.426833+00:00
-- url     : https://prove2.me/theorems/f45320c9-555f-41cb-b42c-fcd784f54fb0
-- title:
--   Fixed-resource classes $\mathrm{MIP}^\psi[q,a]$, $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$, $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$
-- statement:
--   Fix a bipartite state $\psi$ and an answer bound $a:\mathbb N\to\mathbb N$. A language $L\subseteq\{0,1\}^*$ belongs to $\mathrm{MIP}^\psi[\mathrm{poly},a]$ if there are a uniform polynomial-time classical randomized verifier for two noncommunicating provers in one round, and constants $s<c$, such that on every input $z$ the verifier rejects every answer longer than $a(|z|)$ bits and, writing $G_z$ for the game it plays on $z$,
--
--   $$
--   z\in L\ \Longrightarrow\ \omega^*_\infty(G_z,\psi)\ge c,\qquad z\notin L\ \Longrightarrow\ \omega^*_\infty(G_z,\psi)\le s .
--   $$
--
--   The provers share arbitrarily many finite copies of $\psi$ and no other quantum resource. $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ allows a polynomial answer bound and $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$ a constant one.
--
--   These are the proof systems whose power the main theorem classifies.
--
--   **Formalization Note** The verifier is the published `MIPRE.PolyVerifier` (closed sampler and decider programs, one polynomial $P$, seed and question length at most $P(|z|)$, decider time polynomial in the total input length, overlong strings rejected), efficient on every input; its game is `MIPRE.PolyVerifier.game`. Questions are therefore polynomial. The answer bound is a rejection clause, and "a constant completeness–soundness gap" is read as fixed real constants $s<c$, as the paper's proofs use them.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Definition 2.15, p.15; §1.1, p.4; (17), p.15

import Mathlib
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_UnitalMIP_omegaInf

open scoped Matrix

namespace UnitalMIP

open MIPRE MIPRE.Cost

/-- **Fixed-resource `MIP^ψ[q, a]`** (arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…,
Definition 2.15, p.15, with (17), p.15): a language `L ⊆ {0,1}*` belongs to `MIP^ψ[·, ans]` if there
are a uniform polynomial-time two-prover one-round verifier and constants `s < c` such that, on
every input `z`, the verifier is efficient, it rejects every answer longer than `ans(|z|)` bits,
`z ∈ L` implies `ω*_∞(G_z, ψ) ≥ c`, and `z ∉ L` implies `ω*_∞(G_z, ψ) ≤ s`; here `G_z` is the
game the verifier plays on `z` and `ω*_∞` is the value with any finite number of copies of the
fixed state `ψ` and nothing else.

**Formalization Note**
* The verifier is the published `MIPRE.PolyVerifier` with its efficiency clause
  `MIPRE.PolyVerifier.Efficient` and its game `MIPRE.PolyVerifier.game`: a closed sampler and a
  closed decider on the ambient cost model, one polynomial `P`, seed length `B z = P(|z|)`, the
  question pair the sampler's output on a uniform seed, decider time polynomial in the total input
  length, and every string longer than `B z` rejected. Questions therefore have polynomial length
  `≤ B z`; the question bound `q` of the source is this polynomial.
* The answer bound `a` is the clause "the decider rejects whenever an answer is longer than
  `ans(|z|)`". A strategy can replace every overlong answer by a short one without lowering its
  value, so this is the game restricted to answers of length `≤ ans(|z|)`.
* "A constant completeness–soundness gap" is read as fixed real constants `s < c`, independent of
  the input, as the source's proofs use them (proof of Theorem 3.11, p.75: "completeness c,
  soundness s < c"; §4.5, p.65). Completeness is stated for the supremum `ω*_∞`.
* Shared classical randomness is not modelled separately: by the source's last sentence it does
  not change the value. -/
def MIPPsi {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (ψ : Matrix (dA × dB) (dA × dB) ℂ) (ans : ℕ → ℕ) (L : Set BitStr) : Prop :=
  ∃ (V : PolyVerifier) (c s : ℝ), s < c ∧ (∀ z, V.Efficient z) ∧
    (∀ z x y a b : BitStr, ans z.length < a.length ∨ ans z.length < b.length →
      ¬ V.Accepts z x y a b) ∧
    ∀ z, (z ∈ L → c ≤ omegaInf (V.game z) ψ) ∧ (z ∉ L → omegaInf (V.game z) ψ ≤ s)

/-- `MIP^ψ[poly, poly]` (arXiv:2609.39318, version of 2026-11-03, §1.1 and Theorem 1.1, p.4): some
polynomial bounds the answer length (the questions are polynomial by the verifier model of
`MIPPsi`). -/
def MIPPsiPolyPoly {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (ψ : Matrix (dA × dB) (dA × dB) ℂ) (L : Set BitStr) : Prop :=
  ∃ p : Polynomial ℕ, MIPPsi ψ (fun N => p.eval N) L

/-- `MIP^ψ[poly, O(1)]` (arXiv:2609.39318, version of 2026-11-03, Corollary 3.7, p.30; Theorem
3.10, p.31): one constant bounds the answer length on every input. -/
def MIPPsiPolyConst {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (ψ : Matrix (dA × dB) (dA × dB) ℂ) (L : Set BitStr) : Prop :=
  ∃ k : ℕ, MIPPsi ψ (fun _ => k) L

end UnitalMIP


