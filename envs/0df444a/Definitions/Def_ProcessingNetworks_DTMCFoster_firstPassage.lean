-- Prove2me | Definitions.Def_ProcessingNetworks_DTMCFoster_firstPassage
-- name    : ProcessingNetworks_DTMCFoster_firstPassage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:30.739182+00:00
-- url     : https://prove2.me/theorems/3880cea5-4244-491e-9eb4-9466a0a4efb2
-- title:
--   First passage time $T_C=\inf\{k\ge1: X_k\in C\}$, eq. (C.16)
-- statement:
--   Let $X=\{X_k:k\in\mathbb Z_+\}$ be an $\mathcal S$-valued process and $C\subseteq\mathcal S$. The **first passage time of $X$ into $C$** is
--   $$
--   T_C := \inf\{k\ge 1 : X_k\in C\},
--   $$
--   with $T_C=\infty$ when $X_k\notin C$ for every $k\ge 1$. The search starts at time $1$, also when $X_0\in C$, so for $C=\{i\}$ and $X_0=i$ it is the return time $\tau_i$ of §C.4.
--
--   This is the random time in Lemma C.23 (finite expected return times to a finite set give positive recurrence) and in Lemma C.25 (expected cost accumulated before $T_C$).
--
--   **Formalization Note** The value lies in $\mathbb N_\infty$; the infimum of the empty set is $\top=\infty$, the book's convention for a passage that never occurs.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability (pre-publication draft 2020-4-2, spnbook.org), Appendix C, eq. (C.16) in Lemma C.23, p.280 (PDF p.296); kept in force for §C.8, p.283 (PDF p.299)

import Mathlib

namespace ProcessingNetworks.DTMCFoster

/-- **First passage time into a set**, eq. (C.16) (Dai & Harrison, *Processing Networks*,
pre-publication draft 2020-4-2, spnbook.org, Appendix C, Lemma C.23, p.280, PDF p.296):
"`T_C := inf{k ≥ 1 : X_k ∈ C}`", the first passage time of `X` into `C`; it stays in force for the
rest of §C.8 (p.283, PDF p.299).

`firstPassage X C ω` is the least `k ≥ 1` with `X_k(ω) ∈ C`, and `∞` when there is no such `k`.

**Formalization Note** The value lies in `ℕ∞`; the infimum of the empty set is `⊤ = ∞`, which is
the book's convention for a first passage time that never occurs (cf. `τᵢ = ∞` if `X` never visits
`i`, §C.4, p.277, PDF p.293). The search starts at `k = 1`, also when `X₀ ∈ C`. -/
noncomputable def firstPassage {S Ω : Type*} (X : ℕ → Ω → S) (C : Set S) (ω : Ω) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | 1 ≤ k ∧ X k ω ∈ C})

end ProcessingNetworks.DTMCFoster


