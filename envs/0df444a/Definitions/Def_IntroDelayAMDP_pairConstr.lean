-- Prove2me | Definitions.Def_IntroDelayAMDP_pairConstr
-- name    : IntroDelayAMDP_pairConstr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:16.910737+00:00
-- url     : https://prove2.me/theorems/2b70df76-cfd4-4e59-960f-17a8fb054b8d
-- title:
--   Empirical Bernstein constraints of one pair, Eq. (16)
-- statement:
--   For a pair of layer $h$ with observation list of length $N$, a vector $q$ satisfies the constraints of (16) if for every $s'$ of layer $h+1$ and every $1\le n\le N$,
--   $$|q(s')-\hat P_n(s')|\le 2\sqrt{\hat P_n(s')\beta/n}+5\beta/n.$$
--
--   **Formalization Note** For a last-layer pair there is no non-terminal $s'$ in layer $H$, so there is no constraint. With the terminal states merged into one (p.30), the paper's constraint there holds for every transition.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Eq. (16), p.14

import Mathlib
import Definitions.Def_IntroDelayAMDP_LayeredSpace
import Definitions.Def_IntroDelayAMDP_empDist

namespace IntroDelayAMDP

/-- **Empirical Bernstein constraints of one pair** (Eq. (16), p.14). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.14, Eq. (16):
"`|P′(s′ | s, a) − P̂_n(s′ | s, a)| ≤ 2√(P̂_n(s′ | s, a)β/n) + 5β/n`, `∀ 0 ≤ h < H,
(s, a, s′) ∈ S_h × A × S_{h+1}, 1 ≤ n ≤ N_k(s, a)`".

For a pair `(s, a)` with `s` in layer `h`, whose observed next states are the list `obs` (so
`N_k(s, a) = length obs`), `pairConstr L β obs h q` says that the vector `q = P′(· | s, a)`
satisfies every constraint of (16): for every `s′` of layer `h + 1` and every `1 ≤ n ≤ N_k(s,a)`,
`|q(s′) − P̂_n(s′)| ≤ 2√(P̂_n(s′)β/n) + 5β/n`.

**Formalization Note.** For a last-layer pair there is no non-terminal `s′` in layer `H`, so no
constraint; with terminal states merged into one (p.30), the paper's constraint there holds for
every transition. -/
noncomputable def pairConstr {St : Type} [DecidableEq St] {H : ℕ} (L : LayeredSpace St H) (β : ℝ)
    (obs : List St) (h : ℕ) (q : St → ℝ) : Prop :=
  ∀ s', L.layer s' = h + 1 → ∀ n : ℕ, 1 ≤ n → n ≤ obs.length →
    |q s' - empDist obs n s'| ≤ 2 * Real.sqrt (empDist obs n s' * β / n) + 5 * β / n

end IntroDelayAMDP


