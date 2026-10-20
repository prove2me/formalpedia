-- Prove2me | Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens
-- name    : AtomicDynRouting_ResidenceTime_Tokens
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:24.205+00:00
-- url     : https://prove2.me/theorems/ee8836a7-9dcb-4376-a9d8-36a739800cf4
-- title:
--   §3.2, (s1)–(s2), pp. 8–9 — the multi-token process of the focal agent ζ from time r0, token holders, and the departure bound of Lemma 1
-- statement:
--   This file fixes the multi-token construction of §3.2 (pp. 8–9) for an ADR run, a focal agent $\zeta$ and an integer time $r_0$.
--
--   **The buffer of $\zeta$.** For an integer time $s$, $U_{\zeta,s}$ is the edge whose buffer $\zeta$ is in at time $s$; it is defined when $\zeta$ is inside $G$ at $s$.
--
--   **Token production and movement.** Tokens are indexed $1,2,\dots$; each token is at any integer time in the buffer of some edge, or not (yet, or any longer) inside $G$.
--
--   1. At time $r_0$, if $\zeta$ is inside $G$, he produces token $1$ in $U_{\zeta,r_0}$; there are no other tokens.
--   2. (s2) During $(s,s+1)$, in every buffer $e$ containing tokens, the token with the **smallest index** is held by the agent $a$ who leaves $e$ at time $s$ and moves with him: at $s+1$ it is in the buffer of the next edge of $a$'s route, or it exits $G$ with $a$ if $e$ was his last edge. The other tokens stay in $e$.
--   3. (s1) At time $s+1$, if $U_{\zeta,s+1}$ is defined and contains no token, $\zeta$ produces there a new token whose index is one plus the number of tokens produced so far.
--
--   An agent $a$ **holds** token $k$ during $(s,s+1)$ if $k$ is the smallest token in some buffer $e$ at time $s$ and $a$ leaves $e$ at time $s$.
--
--   **Departure bound.** Write $L=L_{o_\zeta d_\zeta}$. For a token $k\ge1$, the statement $\mathrm{DB}(k)$ says: whenever token $k$ is at some time $s_0$ in the buffer of an edge $e$ of $G_\zeta$, it departs from $v=\operatorname{tail}(e)$ along $e$ at a time $s\ge s_0$ (it stays in $e$ during $[s_0,s]$ and is no longer in $e$ at $s+1$) with
--   $$s\le r_0+(L-L_{v d_\zeta}+k-1),$$
--   and if after this move token $k$ is not in a buffer of $G_\zeta$ (so $w=\operatorname{head}(e)$ is the sink of $T_k\cap G_\zeta$, reached at $s+1$), then also $s+1\le r_0+(L-L_{w d_\zeta}+k-1)$. This is the conclusion of Lemma 1 for token $k$.
--
--   **Formalization Note.** `tokState d` gives, at time $r_0+d$ after that time's production, the number of tokens produced so far and the buffer of each token (`none`: not produced or out of $G$). `tokAt s k` is token $k$'s buffer at time $s$ (`none` for $s<r_0$), `produced s` the number of tokens produced by $s$, `zBuf s` is $U_{\zeta,s}$ and `leaver e s` the agent (with the position of $e$ on his route) leaving buffer $e$ at $s$. The page's "largest existing token index plus one" is read as one plus the number of tokens ever produced, so indices are never reused, as the induction on the index in Lemma 1 presupposes. `zBuf` and `leaver` pick their witness by choice; under (A2) the witness is unique. The bounds of `DepartBound` are written additively, $s+L_{vd_\zeta}+1\le r_0+L+k$, which is the same inequality over the integers, so no truncated subtraction occurs.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 8 (PDF 9), §3.2 token production and movement, (s1), (s2); p. 9 (PDF 10), motion trail Tk, departure from a vertex, Lemma 1

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Model

namespace AtomicDynRouting.ResidenceTime

open Classical

variable {ι E V : Type}

/-- `U_{ζ,s}` (§3.2, p. 8): the edge whose buffer agent `ζ` is in at time `s`, or `none` if `ζ` is
not inside `G` at `s`. Under `IsADR` the position `j` with `inBuf ζ j s` is unique. -/
noncomputable def zBuf (R : RunData ι E V) (ζ : ι) (s : ℕ) : Option E :=
  if h : ∃ j, R.inBuf ζ j s then (R.route ζ)[Classical.choose h]? else none

/-- The agent who leaves the buffer of edge `e` at time `s`, with the position of `e` on his route,
or `none` if nobody leaves it. Under (A2) (`IsADR`) this agent is unique, so the choice is
harmless. -/
noncomputable def leaver (R : RunData ι E V) (e : E) (s : ℕ) : Option (ι × ℕ) :=
  if h : ∃ p : ι × ℕ, p.2 < (R.route p.1).length ∧ (R.route p.1)[p.2]? = some e ∧
      R.leave p.1 p.2 = (s : ℕ∞)
  then some (Classical.choose h) else none

/-- Token movement (s2) during `(s, s + 1)`: `pos k` is the buffer of token `k` at time `s`
(`none`: not produced yet, or already out of `G`). In every buffer `e` the token with the smallest
index moves with the agent `a` leaving `e` at `s` to his next buffer, the one of the `(j+1)`-th edge
of his route, or out of `G` with him (`none`) if `e` is his last edge. All other tokens stay. -/
noncomputable def moveTokens (R : RunData ι E V) (s : ℕ) (pos : ℕ → Option E) : ℕ → Option E :=
  fun k =>
    match pos k with
    | none => none
    | some e =>
      if ∀ h < k, pos h ≠ some e then
        match leaver R e s with
        | some (a, j) => (R.route a)[j + 1]?
        | none => some e
      else some e

/-- The token process of §3.2 (pp. 8–9) for the focal agent `ζ` and the start time `r0`, at time
`r0 + d`, after that time's production: the number of tokens produced so far, and the buffer of
every token (`none`: not yet produced or already out of `G`). Tokens are indexed `1, 2, …`.
* At `r0`, `ζ` produces token `1` in `U_{ζ,r0}` (if `ζ` is inside `G` at `r0`).
* From `r0 + d` to `r0 + d + 1`: the tokens move by (s2) (`moveTokens`); then (s1): if `U_{ζ,r0+d+1}`
  is defined and holds no token, `ζ` produces there a new token whose index is one plus the number of
  tokens produced so far. -/
noncomputable def tokState (R : RunData ι E V) (ζ : ι) (r0 : ℕ) : ℕ → ℕ × (ℕ → Option E)
  | 0 =>
    match zBuf R ζ r0 with
    | some U => (1, fun k => if k = 1 then some U else none)
    | none => (0, fun _ => none)
  | d + 1 =>
    let c := (tokState R ζ r0 d).1
    let moved := moveTokens R (r0 + d) (tokState R ζ r0 d).2
    match zBuf R ζ (r0 + d + 1) with
    | some U =>
      if ∀ k, moved k ≠ some U then (c + 1, Function.update moved (c + 1) (some U))
      else (c, moved)
    | none => (c, moved)

/-- The buffer in which token `k` is at time `s` (after the production at `s`); `none` if `s < r0`,
if token `k` has not been produced by time `s`, or if it has exited `G`. -/
noncomputable def tokAt (R : RunData ι E V) (ζ : ι) (r0 s k : ℕ) : Option E :=
  if r0 ≤ s then (tokState R ζ r0 (s - r0)).2 k else none

/-- The number of tokens produced by time `s` (`0` before `r0`). -/
noncomputable def produced (R : RunData ι E V) (ζ : ι) (r0 s : ℕ) : ℕ :=
  if r0 ≤ s then (tokState R ζ r0 (s - r0)).1 else 0

/-- Agent `a` holds token `k` during `(s, s + 1)` ((s2), p. 8): token `k` is in some buffer `e` at
time `s`, it has the smallest index among the tokens in `e`, and `a` is the agent leaving `e` at
`s`. -/
def holds (R : RunData ι E V) (ζ : ι) (r0 : ℕ) (a : ι) (k s : ℕ) : Prop :=
  ∃ (e : E) (j : ℕ), tokAt R ζ r0 s k = some e ∧ (∀ h < k, tokAt R ζ r0 s h ≠ some e) ∧
    leaver R e s = some (a, j)

/-- The conclusion of Lemma 1 (p. 9) for token `k`, with `L = L_{oζdζ}`. Whenever token `k` is in
the buffer of an edge `e` of `Gζ` at a time `s₀`, it departs from `v = tail e` along `e` at some
time `s ≥ s₀` (it stays in `e` during `[s₀, s]` and is not in `e` at `s + 1`) with
`s ≤ r0 + (L − L_{v dζ} + k − 1)`, written additively; and if after that move token `k` is not in a
buffer of `Gζ` (so `head e` is the sink of `Tₖ ∩ Gζ`, which `k` reaches at `s + 1`), then
`s + 1 ≤ r0 + (L − L_{head e, dζ} + k − 1)`. -/
def DepartBound (N : Network V E) (R : RunData ι E V) (ζ : ι) (r0 k : ℕ) : Prop :=
  ∀ (e : E) (s₀ : ℕ), e ∈ Gz N R ζ → tokAt R ζ r0 s₀ k = some e →
    ∃ s, s₀ ≤ s ∧ (∀ t, s₀ ≤ t → t ≤ s → tokAt R ζ r0 t k = some e) ∧
      tokAt R ζ r0 (s + 1) k ≠ some e ∧
      s + N.longest (N.tail e) (R.dest ζ) + 1 ≤ r0 + N.longest (R.orig ζ) (R.dest ζ) + k ∧
      ((∀ e', tokAt R ζ r0 (s + 1) k = some e' → e' ∉ Gz N R ζ) →
        s + 1 + N.longest (N.head e) (R.dest ζ) + 1 ≤ r0 + N.longest (R.orig ζ) (R.dest ζ) + k)

end AtomicDynRouting.ResidenceTime


