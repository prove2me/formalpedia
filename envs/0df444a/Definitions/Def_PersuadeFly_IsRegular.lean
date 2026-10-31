-- Prove2me | Definitions.Def_PersuadeFly_IsRegular
-- name    : PersuadeFly_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:53.123394+00:00
-- url     : https://prove2.me/theorems/3dbe6269-3f58-4f04-b4af-cea4aad6aedf
-- title:
--   Assumption 1 (regularity) with constants $D$ and $p_0$
-- statement:
--   An instance satisfies the **regularity conditions** with constants $D$ and $p_0$ if
--
--   1. $D>0$ and, for each $a\in A$, there is $\eta_a\in\mathcal P_a$ with $\mathsf B_1(\eta_a,D)\subseteq\mathcal P_a$;
--   2. $p_0>0$ and $\min_\omega\mu(\omega)\ge p_0$ for every $\mu\in\mathcal B_0$.
--
--   The first condition gives every region $\mathcal P_a$ a nonempty relative interior; the second keeps the prior away from the boundary of the simplex.
--
--   **Formalization Note** The paper takes $D$ to be the *largest* radius for which condition 1 holds. Here $D$ is any such radius and $p_0$ any such lower bound. The largest radius is one of them and the paper's bounds decrease in $D$, so a result proved for every admissible $D$ contains the paper's. The balls are the paper's $\mathsf B_1$, inside the simplex.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Assumption 1, p.24

import Mathlib
import Definitions.Def_PersuadeFly_ball1
import Definitions.Def_PersuadeFly_prefSet

namespace PersuadeFly

/-- **Assumption 1 (regularity conditions), with constants `D` and `p₀`.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Assumption 1, p.24:
1. every `P_a` contains an `ℓ₁`-ball `B₁(η_a, D) ⊆ P_a` with `η_a ∈ P_a`, `D > 0`;
2. `min_ω μ(ω) ≥ p₀ > 0` for all `μ ∈ B₀`.

**Formalization Note** The paper lets `D` be the *largest* admissible radius. Here `D` is any
admissible radius: the largest one is admissible, and every bound of the paper is decreasing in `D`,
so a theorem for every admissible `D` gives the paper's statement (and still says something when no
largest radius exists, e.g. when every `P_a = Δ(Ω)`). Likewise `p₀` is any lower bound. The ball is the
paper's `B₁`, intersected with the simplex. -/
def IsRegular {Ω A : Type} [Fintype Ω] (I : Instance Ω A) (D p0 : ℝ) : Prop :=
  0 < D ∧ (∀ a : A, ∃ η ∈ prefSet I a, ball1 η D ⊆ prefSet I a) ∧
    0 < p0 ∧ ∀ μ ∈ I.B0, ∀ ω, p0 ≤ μ ω

end PersuadeFly


