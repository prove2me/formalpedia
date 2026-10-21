-- Prove2me | Definitions.Def_GeomScoring_Characterization_Model
-- name    : GeomScoring_Characterization_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:56.851185+00:00
-- url     : https://prove2.me/theorems/0cfccf20-85a7-45f5-8f27-2f054ed360d7
-- title:
--   Definitions 1, 3, 5, pp. 5–7 — scoring rules, profiles, unanimous winners/losers, independence axioms, affine equivalence, geometric scores
-- statement:
--   This file sets up the model of Kondratev, Ianovski and Nesterov's §3: athletes, races, positional scoring rules and the two independence axioms.
--
--   **Scoring rules (Definition 1).** Let $M\in\{0,1,2,\dots\}\cup\{\infty\}$ be the number of potential athletes. A *scoring rule* $s$ assigns to every number $m$ of athletes a sequence of $m$ real scores $s^m_1,\dots,s^m_m$; $s^m_j$ is the score for finishing in position $j$.
--
--   **Races and profiles.** For a finite set $A$ of athletes with $|A|=m$, a *race* is a strict ranking of $A$, i.e. a bijection assigning every athlete a position in $\{1,\dots,m\}$. A *profile* is a finite sequence of $n$ races. The *total score* of an athlete $a$ in a profile $P$ is
--   $$S_a(P)=\sum_{i=1}^{n} s^{m}_{\mathrm{pos}_i(a)},$$
--   and the *overall ranking* is the weak order of athletes by total score (higher total score ranks higher, equal totals rank equally).
--
--   **Unanimous losers and winners (Definition 3).** An athlete $x$ is a *unanimous loser* of $P$ if it is ranked last in every race, and a *unanimous winner* if it is ranked first in every race. Removing a unanimous loser from every race leaves every other athlete in its position; removing a unanimous winner moves every other athlete up by one position. Either way the result is a profile of $n$ races on $A\setminus\{x\}$, scored with the vector for $m-1$ athletes.
--
--   A scoring rule satisfies *independence of unanimous losers* (for $M$ potential athletes) if for every set $A$ of at most $M$ athletes and every profile $P$ with $n\ge1$ races, every unanimous loser $x$ of $P$ has a strictly smaller total score than every other athlete, and for any two other athletes $a,b$,
--   $$S_a(P)\le S_b(P)\iff S_a(P')\le S_b(P'),$$
--   where $P'$ is $P$ with $x$ removed. *Independence of unanimous winners* is the same with "unanimous winner" and "strictly larger total score".
--
--   **Affine equivalence (p. 6).** Two score sequences $s_1,\dots,s_k$ and $t_1,\dots,t_k$ are *affinely equivalent* if there are $\alpha>0$ and $\beta$ with $s_j=\alpha t_j+\beta$ for all $j$. The file also defines the first $k$ entries $s^m_1,\dots,s^m_k$ and the last $k$ entries $s^m_{m-k+1},\dots,s^m_m$ of a length-$m$ sequence ($k\le m$).
--
--   **Geometric scores (Definition 5).** For a parameter $p>0$, the geometric scores for $m$ athletes are
--   $$g^m_j(p)=\begin{cases}p^{m-j} & 1<p,\\ m-j & p=1,\\ 1-p^{m-j} & 0<p<1.\end{cases}$$
--   A *geometric scoring rule* with parameter $p$ is a scoring rule whose score vector for every $m$ is affinely equivalent to $g^m(p)$.
--
--   These are the objects of Proposition 4 and Theorem 6; every theorem of the mission is stated in their terms.
--
--   **Formalization Note.** Positions are 0-based in Lean: Lean's position $j$ is the paper's position $j+1$, so the paper's exponent $m-j$ is `m - 1 - j`. Athletes form an arbitrary finite type `α`, and $M$ is an element of `ℕ∞` (`⊤` for $M=\infty$). A race is an equivalence `α ≃ Fin |α|`. The removed profile is not constructed: the axioms quantify over every profile `Q` on `{a // a ≠ x}` related to `P` by the removal relation (others keep their position, resp. move up by one), and such a `Q` exists and is unique. "Ranked last/first" in the overall ranking is read strictly, and the axioms range over profiles with at least one race (with no races all totals are $0$ and no athlete is strictly last). The first-$k$/last-$k$ helpers return $0$ outside the range $k\le m$, which no statement uses. `geomScore` returns $1-p^{m-1-j}$ for every $p<1$; it is only used with $p>0$.
-- source:
--   Kondratev, Ianovski & Nesterov, How should we score athletes and candidates: geometric scoring rules, arXiv:1907.05082v5, pp. 5–7, Definitions 1, 3, 5 and the definition of affine equivalence (p. 6)

import Mathlib

namespace GeomScoring.Characterization

/-- Definition 1 (p. 5): a (positional) scoring rule assigns to every number `m` of athletes a
sequence of `m` real scores. Positions are 0-based: `s m j` is the score of the paper's
position `j + 1`, so `s m 0` is the score for first place and `s m ⟨m - 1, _⟩` for last place. -/
abbrev ScoringRule := (m : ℕ) → Fin m → ℝ

/-- A race (an individual ranking) of the finite athlete set `α`: a strict ranking, given as the
bijection sending each athlete to its 0-based position. -/
abbrev Race (α : Type) [Fintype α] := α ≃ Fin (Fintype.card α)

/-- A profile of `n` races on the athlete set `α`. -/
abbrev Profile (α : Type) [Fintype α] (n : ℕ) := Fin n → Race α

/-- Definition 1: the total score of athlete `a`, the sum over all races of the score of the
position `a` takes in that race (with the score vector for `m = |α|` athletes). The overall
ranking is the weak order of athletes by total score. -/
def totalScore (s : ScoringRule) {α : Type} [Fintype α] {n : ℕ} (P : Profile α n) (a : α) : ℝ :=
  ∑ i, s (Fintype.card α) (P i a)

/-- Definition 3: `x` is a unanimous loser of `P` if it is ranked last in every race. -/
def IsUnanimousLoser {α : Type} [Fintype α] {n : ℕ} (P : Profile α n) (x : α) : Prop :=
  ∀ i, ((P i x : Fin (Fintype.card α)) : ℕ) + 1 = Fintype.card α

/-- Definition 3: `x` is a unanimous winner of `P` if it is ranked first in every race. -/
def IsUnanimousWinner {α : Type} [Fintype α] {n : ℕ} (P : Profile α n) (x : α) : Prop :=
  ∀ i, ((P i x : Fin (Fintype.card α)) : ℕ) = 0

/-- `Q` is the profile obtained from `P` by removing the (unanimous loser) athlete `x` from every
race: every other athlete keeps its position. -/
def IsLoserRemoval {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (P : Profile α n) (x : α)
    (Q : Profile {a // a ≠ x} n) : Prop :=
  ∀ i (a : {a // a ≠ x}),
    ((Q i a : Fin (Fintype.card {a // a ≠ x})) : ℕ) = ((P i a.1 : Fin (Fintype.card α)) : ℕ)

/-- `Q` is the profile obtained from `P` by removing the (unanimous winner) athlete `x` from every
race: every other athlete moves up by one position. -/
def IsWinnerRemoval {α : Type} [Fintype α] [DecidableEq α] {n : ℕ} (P : Profile α n) (x : α)
    (Q : Profile {a // a ≠ x} n) : Prop :=
  ∀ i (a : {a // a ≠ x}),
    ((Q i a : Fin (Fintype.card {a // a ≠ x})) : ℕ) + 1 = ((P i a.1 : Fin (Fintype.card α)) : ℕ)

/-- Definition 3, independence of unanimous losers, for `M` potential athletes (`M = ⊤` means
`M = ∞`): for every set of at most `M` athletes and every profile with at least one race, a
unanimous loser is ranked strictly last overall, and removing it from every race leaves the
overall (weak) ranking of the other athletes unchanged. -/
def IndepUnanimousLosers (M : ℕ∞) (s : ScoringRule) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α], (Fintype.card α : ℕ∞) ≤ M →
  ∀ (n : ℕ), 0 < n → ∀ (P : Profile α n) (x : α), IsUnanimousLoser P x →
    (∀ a, a ≠ x → totalScore s P x < totalScore s P a) ∧
    ∀ Q : Profile {a // a ≠ x} n, IsLoserRemoval P x Q → ∀ a b : {a // a ≠ x},
      (totalScore s P a.1 ≤ totalScore s P b.1 ↔ totalScore s Q a ≤ totalScore s Q b)

/-- Definition 3, independence of unanimous winners, for `M` potential athletes: for every set of
at most `M` athletes and every profile with at least one race, a unanimous winner is ranked
strictly first overall, and removing it from every race leaves the overall (weak) ranking of the
other athletes unchanged. -/
def IndepUnanimousWinners (M : ℕ∞) (s : ScoringRule) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α], (Fintype.card α : ℕ∞) ≤ M →
  ∀ (n : ℕ), 0 < n → ∀ (P : Profile α n) (x : α), IsUnanimousWinner P x →
    (∀ a, a ≠ x → totalScore s P a < totalScore s P x) ∧
    ∀ Q : Profile {a // a ≠ x} n, IsWinnerRemoval P x Q → ∀ a b : {a // a ≠ x},
      (totalScore s P a.1 ≤ totalScore s P b.1 ↔ totalScore s Q a ≤ totalScore s Q b)

/-- Affine equivalence (p. 6): `u` and `v` are affinely equivalent if `u j = α * v j + β` for
all `j`, for some `α > 0` and some `β`. -/
def AffEquiv {k : ℕ} (u v : Fin k → ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ ∀ j, u j = a * v j + b

/-- The first `k` entries of a length-`m` vector (only used for `k ≤ m`; the default `0` is never
reached in that range). -/
def initSeg {m : ℕ} (v : Fin m → ℝ) (k : ℕ) : Fin k → ℝ :=
  fun j => if h : j.1 < m then v ⟨j.1, h⟩ else 0

/-- The last `k` entries of a length-`m` vector, i.e. entries `m - k, …, m - 1` (only used for
`k ≤ m`; the default `0` is never reached in that range). -/
def finalSeg {m : ℕ} (v : Fin m → ℝ) (k : ℕ) : Fin k → ℝ :=
  fun j => if h : j.1 + (m - k) < m then v ⟨j.1 + (m - k), h⟩ else 0

/-- Definition 5 (p. 7), the geometric scores for `m` athletes with parameter `p`, 0-based: the
paper's exponent `m - j` for 1-based position `j` is `m - 1 - j` here. The three cases are
`p ^ (m-1-j)` for `1 < p`, `m - 1 - j` for `p = 1`, and `1 - p ^ (m-1-j)` for `p < 1` (the paper
takes `0 < p < 1`; the parameter is required positive wherever this is used). -/
noncomputable def geomScore (p : ℝ) (m : ℕ) : Fin m → ℝ := fun j =>
  if 1 < p then p ^ (m - 1 - j.1)
  else if p = 1 then ((m - 1 - j.1 : ℕ) : ℝ)
  else 1 - p ^ (m - 1 - j.1)

end GeomScoring.Characterization


