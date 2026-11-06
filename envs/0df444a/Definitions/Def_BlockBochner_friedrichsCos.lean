-- Prove2me | Definitions.Def_BlockBochner_friedrichsCos
-- name    : BlockBochner_friedrichsCos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:43.826793+00:00
-- url     : https://prove2.me/theorems/1e55e772-9568-4031-9b45-dc0503a73e1b
-- title:
--   Cosine of the Friedrichs angle $\cos(U,W)$
-- statement:
--   For subspaces $U,W$ of a real Hilbert space,
--   $$\cos(U,W)=\sup_{\substack{u\in U,\,w\in W,\ u,w\ne0\\ u,w\perp U\cap W}}\frac{\langle u,w\rangle}{\|u\|\,\|w\|}.$$
--
--   **Formalization Note** A real supremum; the ratios lie in $[-1,1]$. When no admissible pair exists ($U\subseteq W$, $W\subseteq U$, or one of them is $0$) the value is $0$, which is $\|P_UP_W-P_{U\cap W}\|$ in those cases.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.1.1, pp.14–15

import Mathlib

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Cosine of the Friedrichs angle `cos(U, W)`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.1.1, pp.14–15:
`cos(U, W) = sup ⟨u, w⟩ / (‖u‖ ‖w‖)` over non-zero `u ∈ U`, `w ∈ W` with `u, w ⊥ U ∩ W`.

**Formalization Note** A real supremum (`sSup`). The set of ratios lies in `[−1, 1]`, so it is
bounded. When it is empty (`U ⊆ W`, `W ⊆ U`, or one of them is `0`) the value is `sSup ∅ = 0`, which
agrees with `‖P_U P_W − P_{U∩W}‖ = 0` in those cases (Lemma 11). -/
noncomputable def friedrichsCos (U W : Submodule ℝ H) : ℝ :=
  sSup {r | ∃ u ∈ U, ∃ w ∈ W, u ≠ 0 ∧ w ≠ 0 ∧ u ∈ (U ⊓ W)ᗮ ∧ w ∈ (U ⊓ W)ᗮ ∧
    r = inner ℝ u w / (‖u‖ * ‖w‖)}

end BlockBochner


