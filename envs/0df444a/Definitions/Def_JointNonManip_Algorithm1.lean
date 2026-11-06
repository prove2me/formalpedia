-- Prove2me | Definitions.Def_JointNonManip_Algorithm1
-- name    : JointNonManip_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:17.228084+00:00
-- url     : https://prove2.me/theorems/0fb6e44e-a5de-4c48-92b9-f4497480213f
-- title:
--   Algorithm 1: auxiliary-game equilibria and the approachability profile
-- statement:
--   Algorithm 1 of Collina, Fullerton, Liu & Weinberg (§3, pp.8–9).
--
--   Given the cumulative discrepancy $U^{(t)}=\sum_{\tau<t}(k^{(\tau)}-s^{(\tau)})\in\mathbb R^{|A|}$ (with $U^{(1)}=0$), the **auxiliary game** $\widetilde G^{(t)}$ keeps the learners' utilities $u_1,\dots,u_{n-1}$ and gives the optimizer the utility
--   $$
--   \widetilde u_0^{(t)}(y,x_1,\dots,x_{n-1})=\big\langle U^{(t)},\,y\otimes x_1\otimes\cdots\otimes x_{n-1}\big\rangle .
--   $$
--   A mixed Nash equilibrium $(\widetilde y^{(t)},\widetilde x^{(t)})$ of $\widetilde G^{(t)}$ means: $\widetilde y^{(t)}$ maximizes $\langle U^{(t)},y\otimes q^{(t)}\rangle$ over $y\in\Delta(A_0)$, where $q^{(t)}=\bigotimes_i\widetilde x_i^{(t)}$, and $\widetilde x^{(t)}$ is a mixed Nash equilibrium of the induced learner game $G_{\mathcal L}(\widetilde y^{(t)})$.
--
--   In round $t$ each learner plays $x_i^{(t)}=\widetilde x_i^{(t)}$; after the optimizer's action $c^{(t)}$, Algorithm 1 sets $k^{(t)}=e_{c^{(t)}}\otimes q^{(t)}$, $s^{(t)}=\widetilde y^{(t)}\otimes q^{(t)}$ and $U^{(t+1)}=U^{(t)}+k^{(t)}-s^{(t)}$. The learners' strategies depend only on the optimizer's past actions.
--
--   **Formalization Note** The equilibrium condition is written out (`IsAuxNE`), which is exactly the Nash condition of $\widetilde G^{(t)}$. Algorithm 1 does not fix which equilibrium is computed, so the run is defined for an arbitrary selector `AuxNESelector` and results about Algorithm 1 quantify over all selectors. The profile `alg1Profile` does not depend on the horizon.
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), §3, pp.8–9 (auxiliary game G̃(t), Algorithm 1)

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip

/-!
# Algorithm 1: the auxiliary-game approachability algorithm

Collina, Fullerton, Liu & Weinberg, *Non-manipulability and Approachability Beyond Two-Player
Games* (manuscript, STOC 2027 submission), §3, pp.8–9 (the auxiliary game `G̃(t)` and
Algorithm 1).

**Formalization Note**
* "(ỹ, x̃₁, …, x̃_{n−1}) is a mixed Nash equilibrium of the auxiliary game `G̃`", in which the
  optimizer's utility is `ũ₀(y, x₁, …, x_{n−1}) = ⟨U, y ⊗ x₁ ⊗ ⋯ ⊗ x_{n−1}⟩` and the learners keep
  `u₁, …, u_{n−1}`, is written out (`IsAuxNE`): `ỹ` is a lottery that is a best response, among all
  lotteries on `A₀`, to `q = ⊗ᵢ x̃ᵢ`, and `x̃` is a mixed Nash equilibrium of the induced learner
  game `G_L(ỹ)`. This is exactly the Nash condition of `G̃`, since learner `i`'s expected payoff
  in `G̃` against `ỹ` and `x̃_{−i}` is its payoff in `G_L(ỹ)`.
* Algorithm 1 does not fix which equilibrium is computed; the run is defined for an arbitrary
  selector (`AuxNESelector`) returning an equilibrium for every `U`, and statements about
  Algorithm 1 quantify over all selectors.
* `U` is indexed from `0`: `alg1U S t h` is the paper's `U(t+1) = ∑_{τ ≤ t} (k(τ) − s(τ))` after
  the optimizer history `h = (c(1), …, c(t))`; `alg1U S 0 _ = 0` is `U(1) = 0`.
-/

open Finset

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-- `(ỹ, x̃)` is a **mixed Nash equilibrium of the auxiliary game** `G̃` with optimizer utility
`ũ₀(y, x) = ⟨U, y ⊗ ⊗ᵢ xᵢ⟩` and learner utilities `u₁, …, u_{n−1}` (p.8). -/
def IsAuxNE (u : L → A0 × ((i : L) → Act i) → ℝ) (U : A0 × ((i : L) → Act i) → ℝ)
    (yt : A0 → ℝ) (xt : (i : L) → Act i → ℝ) : Prop :=
  AGT.IsLottery yt ∧
    (∀ y' : A0 → ℝ, AGT.IsLottery y' →
      pairing U (otimes y' (AGT.profileProb xt)) ≤ pairing U (otimes yt (AGT.profileProb xt))) ∧
    AGT.IsMixedNash (inducedUtility u yt) xt

/-- A rule that computes, for every cumulative discrepancy `U`, a mixed Nash equilibrium
`(ỹ, x̃)` of the auxiliary game `G̃` (Algorithm 1, p.9, "Compute a mixed Nash equilibrium"). -/
structure AuxNESelector (u : L → A0 × ((i : L) → Act i) → ℝ) where
  /-- The equilibrium computed for the discrepancy `U`. -/
  sel : (A0 × ((i : L) → Act i) → ℝ) → (A0 → ℝ) × ((i : L) → Act i → ℝ)
  /-- It is an equilibrium of the auxiliary game. -/
  isNE : ∀ U, IsAuxNE u U (sel U).1 (sel U).2

/-- The cumulative discrepancy of Algorithm 1 (p.9) after the optimizer history
`h = (c(1), …, c(n))`: `U(1) = 0` and `U(t+1) = U(t) + k(t) − s(t)`, where
`(ỹ(t), x̃(t))` is the selected equilibrium of `G̃(t)`, `q(t) = ⊗ᵢ x̃ᵢ(t)`,
`k(t) = e_{c(t)} ⊗ q(t)` and `s(t) = ỹ(t) ⊗ q(t)`. -/
def alg1U {u : L → A0 × ((i : L) → Act i) → ℝ} (S : AuxNESelector u) :
    (n : ℕ) → (Fin n → A0) → (A0 × ((i : L) → Act i) → ℝ)
  | 0, _ => 0
  | n + 1, h =>
      alg1U S n (Fin.init h) +
        (otimes (pointMass (h (Fin.last n))) (AGT.profileProb (S.sel (alg1U S n (Fin.init h))).2) -
          otimes (S.sel (alg1U S n (Fin.init h))).1
            (AGT.profileProb (S.sel (alg1U S n (Fin.init h))).2))

/-- **Algorithm 1** (p.9) as a profile of learner algorithms: in round `t`, after the optimizer
history `h`, learner `i` plays `x̃ᵢ(t)`, its factor of the selected equilibrium of the
auxiliary game `G̃(t)` built from `U(t)`. It does not depend on the horizon. -/
def alg1Profile {u : L → A0 × ((i : L) → Act i) → ℝ} (S : AuxNESelector u) :
    Profile A0 Act where
  x := fun _ t h => (S.sel (alg1U S t h)).2
  isLottery := fun _ t h i => (S.isNE (alg1U S t h)).2.2.1 i

end JointNonManip


