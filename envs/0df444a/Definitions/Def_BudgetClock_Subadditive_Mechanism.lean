-- Prove2me | Definitions.Def_BudgetClock_Subadditive_Mechanism
-- name    : BudgetClock_Subadditive_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:34.753066+00:00
-- url     : https://prove2.me/theorems/3468b665-b68b-4ca7-941f-d1f622f28c2c
-- title:
--   Mechanism 4, p. 15 — the deterministic budget-feasible clock auction for subadditive valuations, with an abstract 2-approximate demand oracle
-- statement:
--   This file defines Mechanism 4 of the paper, a clock auction for procurement under a budget. There are $n$ bidders $N$; bidder $i$ has a private cost $c_i \ge 0$ and accepts an offered price $p$ exactly when $c_i \le p$. The auctioneer has a budget $B > 0$ and a valuation $v : 2^N \to \mathbb{R}_{\ge 0}$.
--
--   **The oracle.** In phase $t$ every candidate bidder is offered the same price $B/t$, so a set $Y$ of candidates can be paid within the budget, $|Y| \cdot B/t \le B$, exactly when $|Y| \le t$. The subroutine of line 8 (the algorithm of Badanidiyuru, Dobzinski and Oren) is abstracted as a map $\mathrm{alg}(t, X)$ with the property `IsTwoApproxOracle`: for every $t \in \mathbb{N}$ and every pool $X \subseteq N$,
--   1. $\mathrm{alg}(t,X) \subseteq X$ and $|\mathrm{alg}(t,X)| \le t$;
--   2. $v(Y) \le 2\, v(\mathrm{alg}(t,X))$ for every $Y \subseteq X$ with $|Y| \le t$.
--
--   **The mechanism.** Start with active bidders $A = N$, two solutions $S_{\mathrm{prev}} = S_{\mathrm{curr}} = \emptyset$, phase counter $t = 0$, and all prices equal to $B$. While $A \setminus (S_{\mathrm{prev}} \cup S_{\mathrm{curr}}) \neq \emptyset$, run a phase:
--   1. $t \leftarrow t + 1$;
--   2. $S_{\mathrm{prev}} \leftarrow \arg\max_{S \in \{S_{\mathrm{prev}}, S_{\mathrm{curr}}\}} v(S)$, keeping $S_{\mathrm{prev}}$ on a tie;
--   3. each bidder $i \in A \setminus S_{\mathrm{prev}}$ is offered the price $p_i = B/t$; if $c_i > B/t$ the bidder rejects and leaves $A$ permanently. Bidders of $S_{\mathrm{prev}}$ keep their prices;
--   4. $S_{\mathrm{curr}} \leftarrow \mathrm{alg}(t, A \setminus S_{\mathrm{prev}})$ with the updated $A$.
--
--   After the loop, the mechanism returns
--   $$S_{\mathrm{final}} = \arg\max_{S \in \{S_{\mathrm{prev}}, S_{\mathrm{curr}}\}} v(S)$$
--   (again keeping $S_{\mathrm{prev}}$ on a tie), and pays each $i \in S_{\mathrm{final}}$ its current price $p_i$.
--
--   The paper bounds neither the number of phases nor the loop's termination: bidders of cost $0$ never reject and the oracle need not select them, so the loop can run forever. The definition therefore takes a fuel $F \in \mathbb{N}$: the loop is stopped after at most $F$ phases, or earlier when its condition fails, and `mechanism4 v c B alg F` is the output of that run.
--
--   The offered prices $B, B/1, B/2, \dots$ never increase and a rejecting bidder never returns, so this is a clock auction by construction.
--
--   **Formalization Note** The price vector is returned for all bidders; only its entries on $S_{\mathrm{final}}$ are payments. The tie rule of both argmax steps is "keep the first listed set", which the pseudocode leaves open. The initial price $B$ is never paid before a phase reprices the bidder, because $S_{\mathrm{prev}}$ and $S_{\mathrm{curr}}$ are empty until then.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 15, Mechanism 4 (lines 1–10); feasibility at the current price level from p. 15, proof of Theorem 8

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Setting

namespace BudgetClock.Subadditive

/-- The guarantee of the subroutine of line 8 of Mechanism 4 (the 2-approximation algorithm of
Badanidiyuru, Dobzinski and Oren, run with demand queries), kept abstract.
In phase `t` every candidate bidder is offered `B / t`, so a subset of the candidates is feasible
at the current price level, `|Y| · B / t ≤ B`, exactly when `|Y| ≤ t`. The oracle `alg t X`
returns a subset of the candidate pool `X` with at most `t` members whose value is at least half
the value of every subset of `X` with at most `t` members. -/
def IsTwoApproxOracle {n : ℕ} (v : Finset (Fin n) → ℝ)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) : Prop :=
  ∀ (t : ℕ) (X : Finset (Fin n)),
    alg t X ⊆ X ∧ (alg t X).card ≤ t ∧
      ∀ Y ⊆ X, Y.card ≤ t → v Y ≤ 2 * v (alg t X)

/-- The state of Mechanism 4 between phases: the active bidders `A`, the two maintained
solutions `Sprev` and `Scurr`, the phase counter `t`, and the current offered prices `p`. -/
structure State (n : ℕ) where
  A : Finset (Fin n)
  Sprev : Finset (Fin n)
  Scurr : Finset (Fin n)
  t : ℕ
  p : Fin n → ℝ

/-- Line 1: `A = N`, `Sprev = Scurr = ∅`, `t = 0`. The pseudocode sets no initial price; every
bidder starts at the price `B`, which is never paid before line 5 reprices the bidder. -/
def initState (n : ℕ) (B : ℝ) : State n :=
  ⟨Finset.univ, ∅, ∅, 0, fun _ => B⟩

/-- `argmax_{S ∈ {S₁, S₂}} v(S)` of lines 4 and 9; a tie keeps the first listed set `S₁`. -/
noncomputable def better {n : ℕ} (v : Finset (Fin n) → ℝ) (S₁ S₂ : Finset (Fin n)) :
    Finset (Fin n) :=
  if v S₁ < v S₂ then S₂ else S₁

/-- One phase of Mechanism 4 (lines 3–8):
1. `t ← t + 1`;
2. `Sprev ← argmax_{S ∈ {Sprev, Scurr}} v(S)`;
3. every active bidder `i ∈ A \ Sprev` is offered the price `B / t`; the bidder accepts iff
   `c i ≤ B / t`, and a rejecting bidder is removed from `A` for good. Bidders in `Sprev` keep
   their prices;
4. `Scurr ← alg t (A \ Sprev)` with the updated `A`. -/
noncomputable def phase {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (s : State n) : State n :=
  let t : ℕ := s.t + 1
  let Sprev := better v s.Sprev s.Scurr
  let R := s.A \ Sprev
  let p : Fin n → ℝ := fun i => if i ∈ R then B / (t : ℝ) else s.p i
  let A := s.A \ R.filter (fun i => B / (t : ℝ) < c i)
  ⟨A, Sprev, alg t (A \ Sprev), t, p⟩

/-- The while-loop of line 2 with a fuel of `F` phases: a phase is run while
`A \ (Sprev ∪ Scurr) ≠ ∅`, and the loop stops for good once the condition fails or after `F`
phases. The paper gives no bound on the number of phases (zero-cost bidders never reject, and the
oracle need not select them), so the run is cut after `F` phases. -/
noncomputable def run {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) : ℕ → State n → State n
  | 0, s => s
  | F + 1, s =>
    if (s.A \ (s.Sprev ∪ s.Scurr)).Nonempty then run v c B alg F (phase v c B alg s) else s

/-- Mechanism 4 with fuel `F` (lines 1–10): the run from the initial state, then
`Sfinal = argmax_{S ∈ {Sprev, Scurr}} v(S)`. The output is `Sfinal` together with the price
vector; bidder `i ∈ Sfinal` is paid `p i`. -/
noncomputable def mechanism4 {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (F : ℕ) :
    Finset (Fin n) × (Fin n → ℝ) :=
  let s := run v c B alg F (initState n B)
  (better v s.Sprev s.Scurr, s.p)

end BudgetClock.Subadditive


