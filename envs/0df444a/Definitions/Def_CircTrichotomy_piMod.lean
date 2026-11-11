-- Prove2me | Definitions.Def_CircTrichotomy_piMod
-- name    : CircTrichotomy_piMod
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:54.855813+00:00
-- url     : https://prove2.me/theorems/a167c268-aab2-4faa-8227-c9f5c63a3595
-- title:
--   Residue-class subwords $\pi_{i,k}(w)$, contents and counts; the middle factor $\kappa_k(u)$
-- statement:
--   For $k\ge1$, a residue $i$ and a word $w=a_0\cdots a_{n-1}$,
--   $$\pi_{i,k}(w)=\prod_{j\in[0,n-1],\ j\equiv_k i}a_j$$
--   is the subword of letters at positions congruent to $i$ modulo $k$, in increasing order. Its content is $\mathrm{cont}_{i,k}(w)$, and $|\pi_{i,k}(w)|_a$ counts the occurrences of the letter $a$ in it. For $|u|>2k$, $\kappa_k(u)$ is the middle factor of $u=\alpha_k(u)\,\kappa_k(u)\,\omega_k(u)$, where $\alpha_k(u)$ and $\omega_k(u)$ are the prefix and suffix of length $k$.
--
--   These are the building blocks of the congruences $\approx_k$, $\mathcal C^t_k$, $\mathcal C^{t,d}_k$ and $\simeq_k$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (29), p.21 and p.24

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **`π_{i,k}(w)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (29), p.21): "π_{i,k}(w) = ∏_{j ∈ [0,n−1], j ≡_k i} a_j, where
concatenation is done in increasing order" — the subword of the letters of `w` at the positions
`j ≡ i (mod k)`. -/
def piMod {α : Type} (k i : ℕ) (w : List α) : List α :=
  (List.range w.length).filterMap (fun j => if j % k = i % k then w[j]? else none)

/-- `cont_{i,k}(w) = cont(π_{i,k}(w))` (p.21): the set of letters at positions `≡ i (mod k)`. -/
def contMod {α : Type} (k i : ℕ) (w : List α) : Set α := {a | a ∈ piMod k i w}

open Classical in
/-- `|π_{i,k}(w)|_a`: the number of occurrences of the letter `a` at positions `≡ i (mod k)`
(p.16, p.21). -/
noncomputable def cntMod {α : Type} (k i : ℕ) (a : α) (w : List α) : ℕ :=
  (piMod k i w).count a

/-- `κ_k(u)` (p.24): for `|u| > 2k`, the factor with `u = α_k(u) · κ_k(u) · ω_k(u)`, where `α_k(u)`,
`ω_k(u)` are the prefix and suffix of length `k`. -/
def kappa {α : Type} (k : ℕ) (u : List α) : List α := (u.drop k).take (u.length - 2 * k)

end CircTrichotomy


