-- Prove2me | Definitions.Def_ReentrantScheduling_LBFS_Constants
-- name    : ReentrantScheduling_LBFS_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:37.15199+00:00
-- url     : https://prove2.me/theorems/af423a48-3400-4f3b-a4a6-998b855425f2
-- title:
--   (8)–(9), p. 1410 — the constants $c^{(k)}(\varepsilon)$ and $c(\varepsilon)=c^{(1)}(\varepsilon)$; parts in $B^{(k)}$ and parts ahead
-- statement:
--   The explicit constants of the LBFS delay estimate, defined by downward recursion from the last buffer. For $\varepsilon > 0$,
--
--   $$
--   c^{(l)}(\varepsilon) = \overline\tau + \tau_l \quad (8),
--   $$
--
--   $$
--   c^{(k)}(\varepsilon) = c^{(k+1)}(\varepsilon) + \max\Big\{ 2l\overline\tau,\ \big(w^{(k+1)} + \varepsilon\big)\Big\lceil \frac{2c^{(k+1)}(\varepsilon/2)}{\varepsilon} \Big\rceil + 2\overline\tau,\ c^{(k+1)}(\varepsilon) \Big\} \quad (9)
--   $$
--
--   for $k = l-1, \dots, 1$, and $c(\varepsilon) = c^{(1)}(\varepsilon)$, the constant of Theorem 2. Here $\overline\tau = \max_j \tau_j$ and $w^{(k)}$ is (6). The constants depend only on the line and on $\varepsilon$: not on the arrivals, the run or the number of parts.
--
--   The file also names the notions the induction of §V speaks about. At time $t$, a part is *in the system* if it has been released and has not exited; it is *in buffer $b_i$* if it has arrived there and its service there has not ended; it is *in $B^{(k)} = \{b_k, \dots, b_l\}$* if it is in some $b_i$ with $i \ge k$. The parts *ahead* of $\pi$ at time $t$ are the parts in the system that precede $\pi$ in line order. Theorem 2's "parts in the system when $\pi$ arrives" are the other parts in the system at time $\alpha(\pi)$.
--
--   **Formalization Note.** Buffers are 0-based. `cAux d ε` is $c^{(l-d)}(\varepsilon)$, so `cAux 0` is (8) and `cAux (d+1)` is (9) with $w^{(k+1)}$ at Lean index $l-1-d$; `c k ε` is the paper's $c^{(k+1)}(\varepsilon)$ for 0-based $k$, and `cLBFS ε = cAux (l-1) ε` is $c^{(1)}(\varepsilon)$. The brackets in (9) and (12) are ceilings and are encoded with `Nat.ceil`, whose argument is nonnegative for $\varepsilon > 0$.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1410, (7)–(9); p. 1411, (10)–(12); p. 1412, c(ε) := c^(1)(ε)

import Mathlib
import Definitions.Def_ReentrantScheduling_LBFS_Model

namespace ReentrantScheduling.LBFS

namespace Line

variable (L : Line)

/-- The constants `c^(k)(ε)` of (8)–(9), p. 1410, indexed by the distance `d = l − k` from the
end of the line (`k` 1-based):
* `cAux 0 ε = τ̄ + τ_l`, which is (8);
* `cAux (d+1) ε = cAux d ε + max {2lτ̄, (w^(k+1) + ε)⌈2 cAux d (ε/2) / ε⌉ + 2τ̄, cAux d ε}`,
  which is (9) with `k = l − d − 1`; the buffer `b_{k+1} = b_{l−d}` has Lean index `l − 1 − d`. -/
noncomputable def cAux : ℕ → ℝ → ℝ
  | 0, _ => L.τbar + L.τ L.last
  | d + 1, ε =>
      cAux d ε +
        max (2 * (L.l : ℝ) * L.τbar)
          (max ((L.wk ⟨L.l - 1 - d, by have := L.l_pos; omega⟩ + ε) *
                  (⌈2 * cAux d (ε / 2) / ε⌉₊ : ℝ) + 2 * L.τbar)
            (cAux d ε))

/-- `c^(k)(ε)` for the 0-based buffer index `k` (the paper's `c^(k+1)(ε)`). -/
noncomputable def c (k : Fin L.l) (ε : ℝ) : ℝ := L.cAux (L.l - 1 - k.val) ε

/-- `c(ε) := c^(1)(ε)`, the constant of Theorem 2 (p. 1412). -/
noncomputable def cLBFS (ε : ℝ) : ℝ := L.cAux (L.l - 1) ε

end Line

namespace Run

variable {L : Line} (R : Run L)

/-- Part `p` is in the system at time `t`: released by `t` and not yet exited. -/
def inSystem (p : R.Part) (t : ℝ) : Prop :=
  R.α p ≤ t ∧ (t : WithTop ℝ) < R.exit p

/-- Part `p` is in buffer `i` at time `t` (waiting there or in service there). -/
def inBuffer (p : R.Part) (i : Fin L.l) (t : ℝ) : Prop :=
  R.entry p ≤ i ∧ R.arrive p i ≤ (t : WithTop ℝ) ∧
    (t : WithTop ℝ) < R.start p i + ((L.τ i : ℝ) : WithTop ℝ)

/-- Part `p` is in the truncated system `B^(k) = {b_k, …, b_l}` at time `t` (0-based `k`). -/
def inBlock (p : R.Part) (k : Fin L.l) (t : ℝ) : Prop :=
  ∃ i, k ≤ i ∧ R.inBuffer p i t

/-- The parts ahead of `p` at time `t`: the parts in the system that precede it in line order. -/
def ahead (p : R.Part) (t : ℝ) : Set R.Part :=
  {q | R.inSystem q t ∧ R.ord q < R.ord p}

/-- The other parts in the system at the release time of `p` (Theorem 2's `x`). -/
def othersAtArrival (p : R.Part) : Set R.Part :=
  {q | q ≠ p ∧ R.inSystem q (R.α p)}

end Run

end ReentrantScheduling.LBFS


