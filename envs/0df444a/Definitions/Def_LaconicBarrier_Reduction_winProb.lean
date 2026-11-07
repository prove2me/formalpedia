-- Prove2me | Definitions.Def_LaconicBarrier_Reduction_winProb
-- name    : LaconicBarrier_Reduction_winProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:41:01.976704+00:00
-- url     : https://prove2.me/theorems/16fdd3cd-9b16-419d-b372-0b0dd9fa2f58
-- title:
--   The winning probability of a reduction against the target game
-- statement:
--   Let $\mathcal R$ be a reduction, $(\mathcal C, c)$ a game, and $O_j$ the oracle answering the $j$-th query. For a distribution $F$ on advice strings,
--   $$
--   \Pr\bigl[\mathcal R^{O}(1^\lambda, x, z) \text{ wins } \mathcal C(1^{f(1^\lambda,|x|)}) : z \leftarrow F\bigr]
--   $$
--   is the probability over the advice, the reduction's coins, the challenger's coins and the fresh coins of each oracle call, all independent. The execution starts with the challenger's first action and alternates as the reduction decides.
--
--   This is the quantity $\delta'(\lambda)$ of Definition 4.13 (before subtracting $c$), and the winning probability of the honest-prover reduction $\mathcal R \circ \mathcal P$ of Definition 6.1.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.13, p.21

import Mathlib
import Definitions.Def_LaconicBarrier_Reduction
import Definitions.Def_LaconicBarrier_Game

namespace LaconicBarrier

/-- One target-game execution of the reduction `R` against the challenger of `G` at
`λ′ = R.f λ |x|`, with reduction coins `ρ`, challenger coins `σ` and at most `k` more reduction
actions; `evs` is the reduction's view and `ams` the messages it has sent to the challenger. The
`j`-th oracle query `q` (counting from `0`) is answered by a fresh sample of `O j q`. -/
noncomputable def Reduction.exec (R : Reduction) (G : Game)
    (O : ℕ → List Bool → PMF (List Bool)) (lam : ℕ) (x z : List Bool)
    (ρ : Fin (R.coins lam x.length) → Bool) (σ : Fin (G.coins (R.f lam x.length)) → Bool) :
    ℕ → List Ev → List (List Bool) → PMF Bool
  | 0, _, _ => PMF.pure false
  | k + 1, evs, ams =>
    match R.next lam x z ρ evs with
    | .halt => PMF.pure false
    | .query q => (O (evs.countP Ev.isReply) q).bind fun a =>
        R.exec G O lam x z ρ σ k (evs ++ [.reply a]) ams
    | .toChal m =>
      if (ams ++ [m]).length < G.fuel (R.f lam x.length) then
        match G.next (R.f lam x.length) σ (ams ++ [m]) with
        | .win => PMF.pure true
        | .lose => PMF.pure false
        | .send m' => R.exec G O lam x z ρ σ k (evs ++ [.fromChal m']) (ams ++ [m])
      else PMF.pure false

/-- A full execution: the challenger speaks first; then `R.exec` with the reduction's fuel. -/
noncomputable def Reduction.run (R : Reduction) (G : Game) (O : ℕ → List Bool → PMF (List Bool))
    (lam : ℕ) (x z : List Bool) (ρ : Fin (R.coins lam x.length) → Bool)
    (σ : Fin (G.coins (R.f lam x.length)) → Bool) : PMF Bool :=
  if 0 < G.fuel (R.f lam x.length) then
    match G.next (R.f lam x.length) σ [] with
    | .win => PMF.pure true
    | .lose => PMF.pure false
    | .send m => R.exec G O lam x z ρ σ (R.fuel lam x.length) [.fromChal m] []
  else PMF.pure false

/-- The probability that the reduction `R^O(1^λ, x, z)`, with advice `z` drawn from `adv`, wins the
target game `C(1^{f(1^λ, |x|)})` (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), Definition 4.13, p.21: `Pr[A′_{λ,z_λ}(1^λ) wins C(1^{f(1^λ,|x_λ|)}) : z_λ ← F(1^λ, x_λ)]`).
The advice, the reduction's coins, the challenger's coins and each oracle call's coins are
independent. -/
noncomputable def Reduction.winProb (R : Reduction) (G : Game)
    (O : ℕ → List Bool → PMF (List Bool)) (lam : ℕ) (x : List Bool) (adv : PMF (List Bool)) : ℝ :=
  ((adv.bind fun z =>
    (PMF.uniformOfFintype (Fin (R.coins lam x.length) → Bool)).bind fun ρ =>
    (PMF.uniformOfFintype (Fin (G.coins (R.f lam x.length)) → Bool)).bind fun σ =>
      R.run G O lam x z ρ σ) true).toReal

end LaconicBarrier


