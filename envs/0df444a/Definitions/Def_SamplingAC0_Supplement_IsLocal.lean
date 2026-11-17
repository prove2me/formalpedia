-- Prove2me | Definitions.Def_SamplingAC0_Supplement_IsLocal
-- name    : SamplingAC0_Supplement_IsLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:38:00.352347+00:00
-- url     : https://prove2.me/theorems/b6f18565-91e8-4eb0-bfc3-eaf18c6abaa5
-- title:
--   $d$-local map
-- statement:
--   Let $\iota$ and $\kappa$ be index sets and $\alpha$, $\beta$ alphabets. A map $G:\alpha^\iota\to\beta^\kappa$ is **$d$-local** if every output symbol depends on at most $d$ input symbols: for every output position $i\in\kappa$ there is a set $S\subseteq\iota$ with $|S|\le d$ such that
--   $$u|_S=v|_S\ \Longrightarrow\ G(u)_i=G(v)_i\qquad\text{for all }u,v\in\alpha^\iota.$$
--
--   With $\alpha=\{0,1\}$ this is the locality of a map between bit strings (Theorem 2's $k$-local map $G:\{0,1\}^r\to\{0,1\}^m$). With $\alpha=[n]$ it is the non-adaptive cell-probe model of Theorem 6, in which the input consists of cells of $\log n$ bits and locality is counted in cells.
--
--   **Formalization Note** The set $S$ may depend on the output position but not on the input, so the probes are non-adaptive.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Notation p.2; Theorem 2 p.3; Theorem 6 p.4

import Mathlib
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- **`d`-local map.** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027 submission
(manuscript sha256 99c33d30…), Notation, p.2: "every output symbol depends on ≤ d input bits"; p.3
(Theorem 2, "a k-local map G from {0, 1}^r to {0, 1}^m"); p.4 (Theorem 6, "each output bit depends on
≤ d input cells", "a d-local function").

A map `G : (ι → α) → (κ → β)` is `d`-local if for every output position `i` there is a set `S` of at
most `d` input positions such that the `i`-th output is the same on any two inputs that agree on `S`.

**Formalization Note.** The input alphabet `α` is arbitrary: `α = Bool` gives the bit model of
Theorem 2, `α = Fin n` the cell-probe model of Theorem 6 (cells of `log n` bits, locality counted in
cells). The set `S` may depend on `i` but not on the input (non-adaptive). -/
def IsLocal {ι α κ β : Type} (d : ℕ) (G : (ι → α) → (κ → β)) : Prop :=
  ∀ i : κ, ∃ S : Finset ι, S.card ≤ d ∧ ∀ u v : ι → α, (∀ j ∈ S, u j = v j) → G u i = G v i

end SamplingAC0.Supplement


