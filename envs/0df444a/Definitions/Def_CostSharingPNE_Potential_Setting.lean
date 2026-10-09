-- Prove2me | Definitions.Def_CostSharingPNE_Potential_Setting
-- name    : CostSharingPNE_Potential_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:27.403978+00:00
-- url     : https://prove2.me/theorems/e0116ced-b7bf-498e-af83-c265a6c54a17
-- title:
--   §2, Tables 1–2, Appendix C — welfare sharing games and generalized weighted potentials
-- statement:
--   A **welfare sharing game** has a finite player set $N$, a finite resource set $R$, and an action set $\mathcal A_i\subseteq 2^R$ for each player $i$. If $a_i$ is the set of resources selected by $i$ and $\{a\}_r=\{j:r\in a_j\}$, a resource's distribution rule $f^r$ gives utility
--
--   $$U_i(a)=\sum_{r\in a_i}f^r(i,\{a\}_r).$$
--
--   A **weight system** $\omega=(\lambda,\Sigma)$ consists of positive player weights $\lambda_i$ and an ordered partition $\Sigma$ of $N$. The first occupied block of a nonempty coalition $T$ determines $\bar T$. For a welfare function $W:2^N\to\mathbb R$, the Möbius coefficient is
--
--   $$q_T^W=\sum_{B\subseteq T}(-1)^{|T|-|B|}W(B).$$
--
--   The module defines the generalized weighted Shapley value and generalized weighted marginal contribution rules of Table 1, the marginal contribution basis rule of Table 2, and the closed-form local potential $\phi_r(S)_c=W''_r(\bar S_{K-c+1})$ of (85). It also defines the vector-potential identity (80) for a positive-dimensional vector, with a fixed component for each player and equality of all earlier components under that player's deviations. These definitions give the common language for the mission's three milestones and goal.
--
--   **Formalization Note** Players and resources are `Fin n` and `Fin m`; a coalition or action is a finite set. An ordered partition is a map from players to $K$ zero-based blocks, and empty blocks are allowed. The potential predicate explicitly requires $K>0$, as Definition 1 does. Components are zero-based and reverse the block order. The paper's phrase “first nonzero term” in Definition 1 is false for some deviations; the fixed per-player component is the reading established by its Theorem 3 proof. The rule value outside its coalition is zero. No budget-balance or welfare normalization is imposed.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, §2 pp. 3–4; Table 1 p. 5; Table 2 p. 8; Definition 1 p. 57; (80)–(82), (85) pp. 57–58

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem

namespace CostSharingPNE.Potential

/-- Table 2's generalized weighted marginal contribution basis rule, (9). -/
def gwmcBasis {n : ℕ} (ω : CostSharingPNE.Char.WeightSystem n) (T : Finset (Fin n)) : CostSharingPNE.Char.Rule n :=
  fun i S => if i ∈ CostSharingPNE.Char.tbar ω T ∧ T ⊆ S then ω.lam i else 0

/-- Section 2's separable player utility, (81). -/
def utility {n m : ℕ} (F : Fin m → CostSharingPNE.Char.Rule n) (a : Fin n → Finset (Fin m)) (i : Fin n) : ℝ :=
  ∑ r ∈ a i, F r i (CostSharingPNE.Char.players a r)

/-- The closed-form local potential (85), with components in reverse block order. -/
def localPotential {n : ℕ} (ω : CostSharingPNE.Char.WeightSystem n) (W : CostSharingPNE.Char.Welfare n)
    (S : Finset (Fin n)) : Fin ω.K → ℝ :=
  fun c => W (CostSharingPNE.Char.sbar ω S c.rev)

/-- Definition 1 / (80), with a fixed per-player component. Earlier components do not
change under that player's deviation. This is the corrected reading supported by the
proof of Theorem 3; the printed "first nonzero" wording is false in degenerate moves. -/
def IsGenWeightedPotential {n m K : ℕ}
    (A : Fin n → Finset (Finset (Fin m)))
    (U : Fin n → (Fin n → Finset (Fin m)) → ℝ)
    (Φ : (Fin n → Finset (Fin m)) → Fin K → ℝ)
    (w : Fin n → ℝ) : Prop :=
  0 < K ∧ (∀ i, 0 < w i) ∧
    ∃ idx : Fin n → Fin K,
      ∀ i (a : Fin n → Finset (Fin m)),
        (∀ j, j ≠ i → a j ∈ A j) →
        ∀ b' ∈ A i, ∀ b'' ∈ A i,
          (∀ c, c < idx i →
            Φ (Function.update a i b') c = Φ (Function.update a i b'') c) ∧
          U i (Function.update a i b') - U i (Function.update a i b'') =
            w i * (Φ (Function.update a i b') (idx i) -
              Φ (Function.update a i b'') (idx i))

end CostSharingPNE.Potential


