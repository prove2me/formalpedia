-- Prove2me | Definitions.Def_OnlineRandomization_Simulation_Winning
-- name    : OnlineRandomization_Simulation_Winning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:16:14.204956+00:00
-- url     : https://prove2.me/theorems/e9414f72-41ae-48a4-9f31-5a7c9b36e6ef
-- title:
--   Finite-horizon winning positions for the request player
-- statement:
--   A position consists of equally long request and answer strings $(r,a)$. It is **immediately winning** for the request player when the algorithm's incurred cost strictly exceeds the transformed off-line optimum. It is winning within $k$ further rounds if the request player can force an immediate win within that uniform finite bound, regardless of the answers:
--
--   $$\operatorname{Win}(r,a)\iff \exists k\geq0\;\operatorname{WinWithin}_k(r,a).$$
--
--   The uniform bound captures the paper's requirement that the adaptive adversary stop after finitely many requests.
--
--   **Formalization Note** The definition is meaningful on equal-length lists, the only positions used in play (P5). It allows an immediate win at $k=0$, including the empty position, and relies on the real-valued optimum and finite nonempty answer set (P1–P2).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 9–10, §2, proof of Theorem 2.1

import Definitions.Def_OnlineRandomization_Simulation_Model

namespace OnlineRandomization.Simulation

/-- The request player can force an immediately winning position within
`k` further rounds, including a win at the current position. -/
def WinsWithin {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) : ℕ → List R → List A → Prop
  | 0, r, a => α (F.opt r) < F.cost r a
  | k + 1, r, a =>
    α (F.opt r) < F.cost r a ∨
      ∃ x : R, ∀ y : A, WinsWithin F α k (r ++ [x]) (a ++ [y])

/-- The paper's winning positions: one finite uniform bound works against
all answer paths. `k = 0` permits an immediate win, including at `([],[])`. -/
def IsWinning {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A) : Prop :=
  ∃ k : ℕ, WinsWithin F α k r a

end OnlineRandomization.Simulation


