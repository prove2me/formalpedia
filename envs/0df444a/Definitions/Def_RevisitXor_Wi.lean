-- Prove2me | Definitions.Def_RevisitXor_Wi
-- name    : RevisitXor_Wi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:26.893345+00:00
-- url     : https://prove2.me/theorems/e806722e-2ca7-4d66-a97e-9d8ed38fb7e2
-- title:
--   Conditional expectations $W_i$, $\mathbb E[W_i]$, $\operatorname{var}W_i$
-- statement:
--   Fix $h$, a valid outcome $x_{<i}=(x_1,\dots,x_{i-1})$ of the first $i-1$ edges ($1\le i\le M/2$), and let $R$ be the set of $r=M-2(i-1)$ vertices not touched by $x_{<i}$. For a pair $e=\{U,V\}\subseteq R$, $U\ne V$, let
--
--   $$W_i(e)=\mathbb E_{X_{>i}}\,w(x_1,\dots,x_{i-1},e,X_{i+1},\dots,X_{M/2}),$$
--
--   the average of $W$ over all valid sequences that begin with $x_{<i}$ followed by $e$. This is the conditional expectation of $W$ given $X_{<i}=x_{<i}$ and $X_i=e$. Given $x_{<i}$ the next edge $X_i$ is uniform among the $\binom r2$ pairs of $R$, and
--
--   $$\mathbb E[W_i]=\binom r2^{-1}\sum_{e}W_i(e),\qquad \operatorname{var}W_i=\binom r2^{-1}\sum_e\big(W_i(e)-\mathbb E[W_i]\big)^2 .$$
--
--   The differences $W_i-\mathbb E[W_i]$ are the increments of the Doob martingale of $W$ along the edge sequence.
--
--   **Formalization Note** The index $i$ is 1-based. The outcome $x_{<i}$ is given as the first $i-1$ edges of a valid sequence `ys`; every valid prefix extends to one. The module defines `remaining ys i` ($R$), `pairsIn R`, `completions ys i e`, `Wi`, `EWi` and `varWi`.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Lemma 6, p.7

import Mathlib
import Definitions.Def_RevisitXor_validSeqs

namespace RevisitXor

open Classical in
/-- The set `R` of vertices of `[2]^m` not touched by the first `i - 1` edges `x_{<i}` of `ys`
(the paper's 1-based index `i`). -/
noncomputable def remaining {m : ℕ} (ys : Fin (2 ^ m / 2) → Sym2 (Cube m)) (i : ℕ) :
    Finset (Cube m) :=
  Finset.univ.filter fun v => ∀ j : Fin (2 ^ m / 2), j.val + 1 < i → v ∉ ys j

open Classical in
/-- The edges `{x, y}` with `x ≠ y` and `x, y ∈ R`: the 2-element subsets of `R`. -/
noncomputable def pairsIn {m : ℕ} (R : Finset (Cube m)) : Finset (Sym2 (Cube m)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ R

open Classical in
/-- The valid edge sequences that agree with `ys` on the first `i - 1` edges `x_{<i}` and whose
`i`-th edge is `e`. -/
noncomputable def completions {m : ℕ} (ys : Fin (2 ^ m / 2) → Sym2 (Cube m)) (i : ℕ)
    (e : Sym2 (Cube m)) : Finset (Fin (2 ^ m / 2) → Sym2 (Cube m)) :=
  (validSeqs m).filter fun xs =>
    (∀ j : Fin (2 ^ m / 2), j.val + 1 < i → xs j = ys j) ∧
      ∀ j : Fin (2 ^ m / 2), j.val + 1 = i → xs j = e

/-- **`W_i`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25,
2026, sha256 3b49e10d…716), Lemma 6, p.7: "conditioned on any fixed outcome x<i of X<i, the variable
Wi := E_{X>i} w(x1, x2, . . . , xi−1, Xi, Xi+1, . . . , XM/2)".

`Wi h ys i e` is the average of `W` over the valid sequences whose first `i - 1` edges are those of
`ys` and whose `i`-th edge is `e`: the conditional expectation of `W` given `X_{<i} = x_{<i}` and
`X_i = e`.

**Formalization Note.** The index `i` is 1-based as printed. The fixed outcome `x_{<i}` is given as
the first `i - 1` edges of a valid sequence `ys`; every valid prefix extends to a valid sequence, so
this covers every outcome. `W_i` is a completion average, not `W` itself. -/
noncomputable def Wi {m : ℕ} (h : Cube m × Cube m → ZMod 2)
    (ys : Fin (2 ^ m / 2) → Sym2 (Cube m)) (i : ℕ) (e : Sym2 (Cube m)) : ℝ :=
  avg (completions ys i e) (W h)

/-- **`E[W_i]`** (Lemma 6, p.7): the average of `Wi h ys i e` over the next edge `e`, uniform among
the pairs of the remaining set `R`. Under the uniform law on valid sequences, `X_i` given `x_{<i}` is
uniform on these pairs. -/
noncomputable def EWi {m : ℕ} (h : Cube m × Cube m → ZMod 2)
    (ys : Fin (2 ^ m / 2) → Sym2 (Cube m)) (i : ℕ) : ℝ :=
  avg (pairsIn (remaining ys i)) (Wi h ys i)

/-- **`var W_i`** (Lemma 6, p.7: "varWi := vi"): the variance of `Wi h ys i e` over the next edge
`e`, uniform among the pairs of the remaining set `R`. -/
noncomputable def varWi {m : ℕ} (h : Cube m × Cube m → ZMod 2)
    (ys : Fin (2 ^ m / 2) → Sym2 (Cube m)) (i : ℕ) : ℝ :=
  avg (pairsIn (remaining ys i)) fun e => (Wi h ys i e - EWi h ys i) ^ 2

end RevisitXor


