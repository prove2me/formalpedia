-- Prove2me | Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm
-- name    : ExtremalForrelation_Nonadaptive_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:28.048005+00:00
-- url     : https://prove2.me/theorems/830e146a-8b7f-4815-82e5-66582d44f298
-- title:
--   Extremal Forrelation and randomized non-adaptive query algorithms
-- statement:
--   **The problem (Definition 4, $\varepsilon=1$).** An input is a pair of Boolean functions $\chi_f,\chi_g:\mathbb F_2^n\to\{-1,1\}$, given through $f,g:\mathbb F_2^n\to\mathbb F_2$. It is a **yes-instance** if $\mathrm{forr}(\chi_f,\chi_g)=1$ and a **no-instance** if $\mathrm{forr}(\chi_f,\chi_g)=-1$; with answer bit $b$, the promise reads $\mathrm{forr}(\chi_f,\chi_g)=(-1)^b$.
--
--   **Algorithms.** A deterministic non-adaptive algorithm chooses a set $Q\subseteq\mathbb F_2^n$ of query points before it sees any answer, receives both values $(f(x),g(x))$ at each $x\in Q$, and maps this transcript to an output bit. A **randomized non-adaptive algorithm making at most $q$ queries** is a finite probability distribution $(w_\omega)$ over seeds $\omega$, each seed determining a query set $Q_\omega$ with $|Q_\omega|\le q$ and a decision rule; the seed is drawn independently of the input.
--
--   **Success.** The success probability on $(f,g)$ with answer $b$ is $\sum_\omega w_\omega\mathbf 1[\text{rule}_\omega(\text{transcript at }Q_\omega)=b]$. The algorithm **solves extremal Forrelation with probability at least $2/3$** if this is at least $2/3$ on every promised input.
--
--   This is the model of the paper's lower bound (p. 3), in which each query returns both oracle values (footnote 2: this changes the query count by at most a factor $2$).
--
--   **Formalization Note.** The promise is stated as an equality; since $|\mathrm{forr}|\le1$, it is the same set of inputs as the paper's $\mathrm{forr}\ge1$ / $\mathrm{forr}\le-1$. A finite seed space represents every distribution over the finitely many deterministic algorithms with a given query budget.
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Definition 4 p. 7, p. 3 (non-adaptive algorithms, transcripts, footnote 2), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Basic

open Classical

noncomputable section

namespace ExtremalForrelation.Nonadaptive

/-!
# Extremal Forrelation and randomized non-adaptive query algorithms

Canonne–Chen–Mestre, STOC 2027 submission #61 (October 2026), Definition 4 p. 7 (extremal
Forrelation, `ε = 1`), p. 3 (non-adaptive algorithms, transcripts, footnote 2).

An input is a pair of Boolean functions given as bits `f, g : 𝔽₂ⁿ → 𝔽₂`; the oracles are
`χ_f = (−1)^f`, `χ_g = (−1)^g`. It is promised with answer bit `b` when
`forr(χ_f, χ_g) = (−1)^b`: `b = 0` is a yes-instance (`forr = 1`) and `b = 1` a no-instance
(`forr = −1`).

A deterministic non-adaptive algorithm fixes a set `Q` of query locations before seeing any
answer; at every `x ∈ Q` it receives both values `(f(x), g(x))` (the paper's strengthened model,
footnote 2), and a decision rule maps the transcript to an output bit. A randomized one is a
finite probability distribution over such pairs (query set, decision rule), drawn independently
of the input; it makes at most `q` queries if every query set in the support has at most `q`
points.
-/

/-- The promise of extremal Forrelation with answer `b` (Definition 4 with `ε = 1`). -/
def IsPromised {n : ℕ} (f g : V n → ZMod 2) (b : ZMod 2) : Prop :=
  forr (chi f) (chi g) = (-1 : ℝ) ^ b.val

/-- A randomized non-adaptive algorithm making at most `q` (paired) queries on `𝔽₂ⁿ`. -/
structure RandNonadaptiveAlg (n q : ℕ) where
  /-- The finite set of random seeds. -/
  Ω : Type
  [fin : Fintype Ω]
  /-- The probability of each seed. -/
  w : Ω → ℝ
  w_nonneg : ∀ ω, 0 ≤ w ω
  w_sum : ∑ ω, w ω = 1
  /-- The query set chosen on seed `ω`, fixed before any answer is seen. -/
  queries : Ω → Finset (V n)
  card_le : ∀ ω, (queries ω).card ≤ q
  /-- The decision rule on seed `ω`: a map from the answers `(f(x), g(x))_{x ∈ Q}` to a bit. -/
  decide : (ω : Ω) → ((queries ω) → ZMod 2 × ZMod 2) → ZMod 2

attribute [instance] RandNonadaptiveAlg.fin

/-- The probability that `A` outputs `b` on input `(f, g)`. -/
def successProb {n q : ℕ} (A : RandNonadaptiveAlg n q) (f g : V n → ZMod 2) (b : ZMod 2) : ℝ :=
  ∑ ω, A.w ω * (if A.decide ω (fun x => (f x.1, g x.1)) = b then 1 else 0)

/-- `A` solves extremal Forrelation with probability at least `2/3`: on every promised input it
outputs the correct answer with probability at least `2/3`. -/
def Solves {n q : ℕ} (A : RandNonadaptiveAlg n q) : Prop :=
  ∀ (f g : V n → ZMod 2) (b : ZMod 2), IsPromised f g b → (2 : ℝ) / 3 ≤ successProb A f g b

end ExtremalForrelation.Nonadaptive


