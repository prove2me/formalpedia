-- Prove2me | Definitions.Def_CausalFailureRank_rank
-- name    : CausalFailureRank_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:45.235123+00:00
-- url     : https://prove2.me/theorems/443a6039-4f2d-4b3a-8481-8a5199e447d0
-- title:
--   Causal failure rank $\rho(i,R)$, defined by the allocation game
-- statement:
--   Let $R\subseteq U$ be the unused tools at stage $i$. An error adversary declares each stage correct, or spends one unit to declare an error; the allocator must then irrevocably consume a tool of $S_j\cap R$ not yet used. The allocator **handles** budget $k$ when one causal strategy succeeds against every declaration pattern with at most $k$ errors from stage $i$ on. The **causal failure rank** is
--   $$\rho(i,R)=\inf\{k:\ \text{no causal allocator handles budget } k\},$$
--   with $\rho(i,R)=\infty$ if every budget is handled. Also $d_b(i,R)=\max_{r\in S_i\cap R}\rho(i+1,R\setminus\{r\})$, which is $0$ if $S_i\cap R=\emptyset$.
--
--   This is the structural parameter of the price law. It is defined by the game, and the recursion (1) is a theorem about it.
--
--   **Formalization Note** A causal allocator reads the declarations from stage $i$ up to and including the current error, so a future declaration is unreadable. For a pure strategy an adaptive adversary and "for all patterns" coincide, since the adversary can simulate the strategy. The allocator returns an optional tool because no function into an empty tool set exists at $q=0$.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §2, p.5

import Mathlib

namespace CausalFailureRank

/-- The declarations made on stages `i, …, j` of a pattern `e`: what a causal allocator may read
when it allocates at stage `j`. -/
def declPrefix (e : ℕ → Bool) (i j : ℕ) : List Bool :=
  (List.range (j - i + 1)).map fun n => e (i + n)

/-- **Some causal allocator handles every pattern of at most `k` future errors.** Zang, Li, Jin, Xu,
*Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of
2026-11-03, sha256 721c8b0d…), §2, p.5: "ρ(i, R) > k means that some allocator handles every adaptive
pattern of at most k future errors".

**Formalization Note.** A causal allocator is `σ : List Bool → Option (Fin q)`, reading the
declarations from stage `i` up to and including the current error, so a future declaration is
unreadable; `none` is "no tool" (`Option`, because for `q = 0` no function into `Fin q` exists). It
handles `e` when every error stage `j ≥ i` gets a tool of `S j ∩ R`, different from the tool of
every earlier error stage. For a pure causal `σ`, an adaptive adversary and "for all patterns"
coincide, since the adversary can simulate `σ`; this is `∃ σ, ∀ e`, not the offline condition
`∀ e, ∃` matching. -/
def Handles {N q : ℕ} (S : Fin N → Finset (Fin q)) (i : ℕ) (R : Finset (Fin q)) (k : ℕ) : Prop :=
  ∃ σ : List Bool → Option (Fin q), ∀ e : ℕ → Bool,
    (Finset.univ.filter fun j : Fin N => i ≤ j.val ∧ e j.val = true).card ≤ k →
    ∀ j : Fin N, i ≤ j.val → e j.val = true →
      ∃ r, σ (declPrefix e i j.val) = some r ∧ r ∈ S j ∧ r ∈ R ∧
        ∀ j' : Fin N, i ≤ j'.val → j'.val < j.val → e j'.val = true →
          σ (declPrefix e i j'.val) ≠ some r

/-- **The causal failure rank `ρ(i, R)` of the compatibility sets `S`**, §2, p.5: the smallest error
budget forcing failure against an optimal causal allocator, `⊤` if this is impossible.

**Formalization Note.** Defined by the game (`Handles`), never by the recursion (1), which is a
milestone. Healthy termination `i ≥ N` has rank `⊤`, because no pattern has an error stage. Stages
are 0-based, so the paper's `ρ(1, U)` is `gameRank S 0 Finset.univ`. -/
noncomputable def gameRank {N q : ℕ} (S : Fin N → Finset (Fin q)) (i : ℕ) (R : Finset (Fin q)) : ℕ∞ :=
  ⨅ (k : ℕ), ⨅ (_ : ¬ Handles S i R k), (k : ℕ∞)

/-- The best rank after a current error is corrected, or zero if no correction is possible:
`d_b` of eq. (1), p.6, also `b_i` of eq. (4). A supremum over the empty set of `ℕ∞` is `0`, as
printed; the supremum may be `⊤`. -/
noncomputable def gameBadRank {N q : ℕ} (S : Fin N → Finset (Fin q)) (i : Fin N)
    (R : Finset (Fin q)) : ℕ∞ :=
  (S i ∩ R).sup fun r => gameRank S (i.val + 1) (R.erase r)

end CausalFailureRank


