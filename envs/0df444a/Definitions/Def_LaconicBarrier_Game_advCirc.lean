-- Prove2me | Definitions.Def_LaconicBarrier_Game_advCirc
-- name    : LaconicBarrier_Game_advCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:37.302212+00:00
-- url     : https://prove2.me/theorems/0d7a1305-1fd3-423d-8403-5108e15f71cb
-- title:
--   Advantage of an adversary circuit
-- statement:
--   Let $A$ be a circuit with $n$ inputs. Played against the challenger of $(\mathcal C, c)$ at parameter $\lambda$, $A$ answers each challenger message with its output on the padded code of all challenger messages so far. Its **advantage** is
--   $$
--   \mathrm{Adv}_{(\mathcal C,c)}(A;\lambda) = \max\Bigl\{0,\ \Pr\bigl[A(1^\lambda) \text{ wins } \mathcal C(1^\lambda)\bigr] - c\Bigr\},
--   $$
--   the probability over the challenger's coins.
--
--   **Formalization Note** Adversary circuits are deterministic (fixing the best coins of a randomized circuit never lowers its winning probability and never increases its size) and compute each next message from the whole transcript with one circuit whose input length they choose.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.1, p.15

import Mathlib
import Definitions.Def_LaconicBarrier_Game
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_coinAvg

namespace LaconicBarrier

/-- The challenger played against a deterministic adversary strategy `A` (challenger messages so far
↦ reply), with coins `ρ` and at most `k` more challenger actions; `cms`, `ams` are the challenger's
and the adversary's messages so far. Running out of actions is `lose`. -/
def Game.playDet (G : Game) (lam : ℕ) (ρ : Fin (G.coins lam) → Bool)
    (A : List (List Bool) → List Bool) : ℕ → List (List Bool) → List (List Bool) → Bool
  | 0, _, _ => false
  | k + 1, cms, ams =>
    match G.next lam ρ ams with
    | .win => true
    | .lose => false
    | .send m => G.playDet lam ρ A k (cms ++ [m]) (ams ++ [A (cms ++ [m])])

/-- The strategy of an adversary circuit with `n` inputs: on the challenger messages so far it reads
their tuple code, padded or cut to `n` bits (`padIn`), and replies with its decoded output
(`unpadOut`). -/
def circStrategy {n : ℕ} (C : MCircuit n) : List (List Bool) → List Bool :=
  fun cms => unpadOut (C.eval (padIn n (QAdvFew.PoQOracle.tup cms)))

/-- The **advantage** of an adversary circuit `A` in the game `(C, c)` at parameter `λ` (Jain,
Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.1, p.15):
`max{0, Pr[A(1^λ) wins C(1^λ)] − c}`, the probability over the challenger's coins.

**Formalization Note** A non-uniform adversary of Definition 4.2 is a circuit; it is taken to be
deterministic (fixing its best coins never lowers its winning probability and never increases its
size) and to compute its next message from the whole transcript with one circuit, whose input length
it chooses. -/
noncomputable def Game.advCirc (G : Game) (lam : ℕ) (A : Σ n, MCircuit n) : ℝ :=
  max 0 (coinAvg (G.coins lam)
    (fun ρ => if G.playDet lam ρ (circStrategy A.2) (G.fuel lam) [] [] then 1 else 0) - G.c)

end LaconicBarrier


