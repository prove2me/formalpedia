-- Prove2me | Definitions.Def_FakeUserRanking_FORC_Supplement_UCB
-- name    : FakeUserRanking_FORC_Supplement_UCB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:28:52.897807+00:00
-- url     : https://prove2.me/theorems/b3d9be00-c307-44b7-8197-ce208360caa5
-- title:
--   (27), p. 45 — the UCB algorithm of Theorem 1 for two products
-- statement:
--   The UCB algorithm used in Theorem 1 (Section 4 and Appendix B), for an instance with two products $\{1,2\}$.
--
--   In every round $t$ UCB keeps, for each product $i$, the **feedback count** $\eta_i$ (the number of past rounds in which product $i$ was placed at a position no lower than the last position the user examined) and the **empirical mean** $\hat\mu_i$, the number of clicks on $i$ divided by $\eta_i$. With horizon $T$ it computes the upper confidence bounds
--
--   $$\mathrm{UCB}_i=\hat\mu_i+\sqrt{\frac{\log T}{\eta_i}},\qquad i\in\{1,2\},\qquad(27)$$
--
--   with $\mathrm{UCB}_i=+\infty$ while $\eta_i=0$, and places the product with the larger index in the first position and the other product in the second. When the two indices are equal, an arbitrary **tie-breaking rule**, a function of UCB's own past observations, names the product placed first.
--
--   UCB is deterministic, and it never sees whether a user was fake. It is the algorithm that Theorem 1 shows to be non-robust to fake users.
--
--   **Formalization Note** Products are `Fin 2`, so Lean product $0$ is product 1 and Lean product $1$ is product 2. UCB is an `Alg 2 1` of the published model (one internal label drawn with probability 1). Its state is recomputed from its own history of observations; the observation of a round is the last examined position and whether the product there was clicked. The logarithm is natural. The index is compared in `WithTop ℝ`, with $\top$ for an unsampled product.
--
--   Differences from the source:
--   - encoding: Products, positions and rounds use 1-based indices → Fin indices are 0-based; the state after t rounds uses the first t observations; reason: Relabelling preserves every source instance and round.
--   - reading: Equation (27) divides by the feedback count and does not state its zero-count branch → An unsampled product has index +∞; reason: Appendix B p. 45 item 1 requires the smaller-count product to be selected when both empirical means are zero; this supplies the usual unsampled-arm convention.
--   - encoding: The empirical means and counts are updated after each observation → The state stores click counts and recomputes rankings and feedback from the observation history; reason: Clicks divided by feedback count gives the same empirical mean; one internal label of weight 1 encodes a deterministic algorithm.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 45, (27); pp. 14–15 and 44–45 (Section 4, Appendix B); feedback as defined on p. 16

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model

namespace FakeUserRanking.FORC.Supplement

/-! ### The UCB algorithm of Theorem 1 (§4, p. 14; App. B, (27), p. 45)

Two products, `Fin 2`, 0-based: Lean product `0` is paper product 1, Lean product `1` is paper
product 2. UCB is deterministic: it uses one internal label (`Fin 1`) drawn with weight `1`. -/

/-- UCB's state: the feedback count `η_i` (`cnt`) and the number of clicks (`clk`) of each
product, so that the empirical mean is `μ̂_i = clk_i / η_i`. -/
structure UcbState where
  cnt : Fin 2 → ℕ
  clk : Fin 2 → ℕ

/-- No feedback yet. -/
def UcbState.init : UcbState := ⟨fun _ => 0, fun _ => 0⟩

/-- Update after a round with ranking `π` and observation `o = (last examined position, clicked?)`:
every product placed at a position `≤ o.1` receives one feedback (p. 16), and the product at
position `o.1` receives one click if the user clicked. -/
def UcbState.update (st : UcbState) (π : Equiv.Perm (Fin 2)) (o : Obs 2) : UcbState :=
  ⟨fun i => if π.symm i ≤ o.1 then st.cnt i + 1 else st.cnt i,
   fun i => if o.2 = true ∧ i = π o.1 then st.clk i + 1 else st.clk i⟩

/-- The index (27): `UCB_i = μ̂_i + √(log T / η_i)` with the horizon `T` and the natural logarithm,
and `UCB_i = +∞` while `η_i = 0` (an unsampled product is preferred, p. 45, item 1). -/
noncomputable def ucbIndex (T : ℕ) (st : UcbState) (i : Fin 2) : WithTop ℝ :=
  if st.cnt i = 0 then ⊤ else
    (((st.clk i : ℝ) / st.cnt i + Real.sqrt (Real.log T / st.cnt i) : ℝ) : WithTop ℝ)

/-- The ranking that puts product `top` in the first position and the other product second. -/
def topFirst (top : Fin 2) : Equiv.Perm (Fin 2) :=
  if top = 0 then 1 else Equiv.swap 0 1

open Classical in
/-- UCB's ranking: the product with the strictly larger index goes first; on equal indices the
tie-breaking rule `tb`, a function of UCB's own past `h`, names the product placed first. -/
noncomputable def ucbRankOf (T : ℕ) (tb : List (Fin 1 × Obs 2) → Fin 2)
    (h : List (Fin 1 × Obs 2)) (st : UcbState) : Equiv.Perm (Fin 2) :=
  topFirst (if ucbIndex T st 1 < ucbIndex T st 0 then 0
    else if ucbIndex T st 0 < ucbIndex T st 1 then 1 else tb h)

/-- UCB's state after processing its own past `h` (labels and observations, oldest first): the
past rankings are recomputed round by round. -/
noncomputable def ucbState (T : ℕ) (tb : List (Fin 1 × Obs 2) → Fin 2)
    (h : List (Fin 1 × Obs 2)) : UcbState :=
  (h.foldl (fun (acc : List (Fin 1 × Obs 2) × UcbState) (x : Fin 1 × Obs 2) =>
      (acc.1 ++ [x], acc.2.update (ucbRankOf T tb acc.1 acc.2) x.2))
    ([], UcbState.init)).2

/-- The UCB algorithm for two products with horizon `T` and tie-breaking rule `tb`. It does not
know the instance, the fakeness budget, or which users are fake. -/
noncomputable def ucb (T : ℕ) (tb : List (Fin 1 × Obs 2) → Fin 2) : Alg 2 1 where
  w := fun _ _ => 1
  rank := fun h _ => ucbRankOf T tb h (ucbState T tb h)

end FakeUserRanking.FORC.Supplement


