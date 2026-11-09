-- Prove2me | Definitions.Def_HierADA_potential
-- name    : HierADA_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:00:12.21433+00:00
-- url     : https://prove2.me/theorems/ba98f016-ecb0-4cce-a698-fbf5559b1468
-- title:
--   Potential $\Psi=\sum_j4^{j-1}(\Phi_j(G_j)-(\frac\tau4\langle G_j,u_j\rangle-R_j(u_j)))$
-- statement:
--   For score vectors $G$ and fixed reference vectors $u$, the **potential** is
--
--   $$
--   \Psi=\sum_{j=1}^{p-1}4^{j-1}\Big(\Phi_j(G_j)-\Big(\frac\tau4\langle G_j,u_j\rangle-R_j(u_j)\Big)\Big),
--   $$
--
--   the weighted sum over the learned blocks of the gap between the best objective value and that of the reference vector. Each gap is nonnegative, and Proposition 3.4 shows that every correction lowers $\Psi$ by a fixed amount.
--
--   **Formalization Note** 0-based: the sum is over the blocks $j$ with $j+1<p$, with multiplier $4^j$.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), p.21 (definition of Ψ)

import Mathlib
import Definitions.Def_HierADA_Params
import Definitions.Def_HierADA_Phi

set_option autoImplicit false

namespace HierADA

/-- **The potential `Ψ`** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data Analysis and
Adversarial Robustness on Insertion-Deletion Streams*, preprint (version of 2026-11-03, sha256
f220ae51…), p.21:
$$\Psi=\sum_{j=1}^{p-1}4^{j-1}\Bigl(\Phi_j(G_j)-\Bigl(\frac\tau4\langle G_j,u_j\rangle-R_j(u_j)\Bigr)\Bigr),$$
for score vectors `G` and fixed reference vectors `u`, over the learned blocks.

**Formalization Note.** 0-based: the sum is over `j` with `j + 1 < p`, with multiplier `4^j`. -/
noncomputable def potential (prm : Params) (n : Fin prm.p → ℕ)
    (u G : (j : Fin prm.p) → Fin (n j) → ℝ) : ℝ :=
  ∑ j : Fin prm.p, if j.val + 1 < prm.p then
    (4 : ℝ) ^ j.val * (Phi prm.τ (n j) (G j) - objective prm.τ (n j) (G j) (u j)) else 0

end HierADA


