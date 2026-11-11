-- Prove2me | Definitions.Def_RankingBeats_General_Structures
-- name    : RankingBeats_General_Structures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:27:19.012489+00:00
-- url     : https://prove2.me/theorems/be07b8b8-967c-4572-a83b-3582ba2b561e
-- title:
--   Victim and blocker (Def. 3.4), backup (Def. 3.5), better and worse off (Def. 3.6), candidate matches CM (Lemma 4.10)
-- statement:
--   Fix a rank vector $\vec x$ of the graph $G$.
--
--   1. (**Victim and blocker**, Definition 3.4.) $u$ is the victim of $v$ in $R(\vec x)$, and $v$ a blocker of $u$, if $u$ is unmatched in $R(\vec x)$ and matched in $R(\vec x_{-v})$.
--   2. (**Backup**, Definition 3.5.) If $u$ is matched to $m$ in $R(\vec x_{-S})$, $b$ is the backup of $u$ with respect to $\vec x_{-S}$ when $(u,b)\in R(\vec x_{-(S\cup\{m\})})$; when no such $b$ exists, $u$ has no backup. $S=\emptyset$ is "with respect to $\vec x$", $S=\{v\}$ "with respect to $\vec x_{-v}$".
--   3. (**Better and worse off**, Definition 3.6.) $u$ is better off in $M_1$ (ranks $\vec r^1$) than in $M_2$ (ranks $\vec r^2$), equivalently worse off in $M_2$, if either its match $v_1$ in $M_1$ and its match $v_2$ in $M_2$ satisfy $r^1_{v_1}<r^2_{v_2}$, or $u$ is matched in $M_1$ and unmatched in $M_2$.
--   4. (**Candidate matches**, Lemma 4.10.) For a vertex $w$ and a rank $y$, $\mathrm{CM}_{\vec x_{-w}}(y)$ is the set of neighbours $v$ of $w$ that are unmatched in $R(\vec x_{-w})$ or whose match in $R(\vec x_{-w})$ has rank $>y$.
--
--   These are the matching structures of §4: the facts about the alternating path describe backups, victims and blockers along it, and Lemma 4.10 describes the match of an inserted vertex through $\mathrm{CM}$.
--
--   **Formalization Note** "$u$ is matched to $v$ in $R$" is `s(u, v) ∈ R`. `HasBackup G S x u` is `∃ b, IsBackup G S x u b`, and "$u$ has no backup" is its negation, so an unmatched or removed vertex has no backup (Definition 3.5 defines backups for matched vertices only). `BetterOff M₁ r₁ M₂ r₂ u` takes the two rank vectors explicitly because the comparison may cross rank vectors (footnote 7).
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 12 Definition 3.4; pp. 12–13 Definition 3.5; p. 13 Definition 3.6; p. 15 Lemma 4.10 (CM)

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking

open Classical

namespace RankingBeats.General

/-!
# Victims and blockers, backups, better and worse off, candidate matches

Derakhshan, Yu, *Ranking Beats 1-1/e on General Graphs*, STOC 2027 submission (manuscript sha256
6715d477…), p. 12 Definition 3.4, pp. 12–13 Definition 3.5, p. 13 Definition 3.6, p. 15
Lemma 4.10 (`CM_{x_{-w}}(y)`).

* "`u` is matched to `v` in `R`" is `s(u, v) ∈ R`.
* Backup (Definition 3.5), with respect to a run with removed set `S`: `b` is the backup of `u`
  when `u` is matched to some `m` in `R(x_{-S})` and to `b` in `R(x_{-(S ∪ {m})})`. "`u` has no
  backup" is the negation of `HasBackup`; in particular an unmatched or removed vertex has no
  backup. `S = ∅` is "with respect to `x`", `S = {v}` is "with respect to `x_{-v}`".
* Better / worse off (Definition 3.6) compares two matchings `M₁`, `M₂` with their rank vectors
  `r₁`, `r₂` (the comparison is numerical and may cross rank vectors, footnote 7).
-/

variable {V : Type*}

/-- Definition 3.4: `u` is the victim of `v` in `R(x)` (and `v` is a blocker of `u`): `u` is
unmatched in `R(x)` and matched in `R(x_{-v})`. -/
def IsVictim [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ) (u v : V) : Prop :=
  ¬ IsMatched (ranking G ∅ x) u ∧ IsMatched (ranking G {v} x) u

/-- Definition 3.5: `b` is the backup of `u` with respect to `x_{-S}`: `u` is matched in
`R(x_{-S})` to some `m`, and `(u, b) ∈ R(x_{-(S ∪ {m})})`. -/
def IsBackup [Fintype V] [LinearOrder V] (G : SimpleGraph V) (S : Finset V) (x : V → ℝ)
    (u b : V) : Prop :=
  ∃ m, s(u, m) ∈ ranking G S x ∧ s(u, b) ∈ ranking G (insert m S) x

/-- `u` has a backup with respect to `x_{-S}`. -/
def HasBackup [Fintype V] [LinearOrder V] (G : SimpleGraph V) (S : Finset V) (x : V → ℝ)
    (u : V) : Prop :=
  ∃ b, IsBackup G S x u b

/-- Definition 3.6: `u` is better off in `M₁` (ranks `r₁`) than in `M₂` (ranks `r₂`),
equivalently worse off in `M₂`: either its match `v₁` in `M₁` and its match `v₂` in `M₂` satisfy
`r₁ v₁ < r₂ v₂`, or `u` is matched in `M₁` and unmatched in `M₂`. -/
def BetterOff (M₁ : Finset (Sym2 V)) (r₁ : V → ℝ) (M₂ : Finset (Sym2 V)) (r₂ : V → ℝ) (u : V) :
    Prop :=
  (∃ v₁ v₂, s(u, v₁) ∈ M₁ ∧ s(u, v₂) ∈ M₂ ∧ r₁ v₁ < r₂ v₂) ∨
    (IsMatched M₁ u ∧ ¬ IsMatched M₂ u)

/-- Lemma 4.10: `CM_{x_{-w}}(y)`, the candidate matches of `w` at rank `y`: the neighbours `v` of
`w` that are unmatched in `R(x_{-w})` or whose match in `R(x_{-w})` has rank `> y`. -/
noncomputable def candidateMatches [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (w : V) (y : ℝ) : Finset V :=
  Finset.univ.filter fun v => G.Adj w v ∧
    (¬ IsMatched (ranking G {w} x) v ∨ ∃ m, s(v, m) ∈ ranking G {w} x ∧ y < x m)

end RankingBeats.General


