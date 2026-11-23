-- Prove2me | Definitions.Def_FakeUserRanking_FORC_Supplement_FAR
-- name    : FakeUserRanking_FORC_Supplement_FAR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:29:55.956799+00:00
-- url     : https://prove2.me/theorems/b3d1fb3f-6c4e-4220-8adb-6c89dd3c1b84
-- title:
--   Algorithm 1, p. 17 — the Fake-Aware Ranking (FAR) algorithm with the edge condition (4)
-- statement:
--   The Fake-Aware Ranking algorithm (Algorithm 1), which knows the fakeness budget $F$.
--
--   FAR takes as input the fakeness budget $F$ and the horizon $T$, and sets $\delta=1/(nT)$. It keeps, for every product $i\in[n]$, a **feedback count** $\eta_i$ and an **average reward** $r_i$ (clicks on $i$ divided by $\eta_i$; $r_i=0$ while $\eta_i=0$), and a **product-ordering graph** $G$ on $[n]$, initially without edges. An edge $(i,j)$ records that product $j$ dominates product $i$. In each round $t=1,\dots,T$:
--
--   1. **Ranking decision.** Display $\pi_t=\textsc{GraphRankSelect}(\eta,G)$ (Algorithm 2) and observe the clicked product, if any, and the last examined position $j$.
--   2. **Update.** Increase $\eta_i$ by one for every product $i\in\{\pi_t(1),\dots,\pi_t(j)\}$, and update the averages so that $r_i$ remains the fraction of these feedbacks that were clicks.
--   3. **Add edges.** For every $i,k\in[n]$ with $\eta_i,\eta_k>0$ and
--   $$r_i+\sqrt{\frac{\log(2nT/\delta)}{\eta_i}}+\frac{F}{\eta_i}\;\le\;r_k-\sqrt{\frac{\log(2nT/\delta)}{\eta_k}}-\frac{F}{\eta_k},\qquad(4)$$
--   add the directed edge $(i,k)$ to $G$. Edges are never removed.
--
--   FAR never observes whether a user is fake. The term $F/\eta_i$ widens the confidence interval by the largest distortion that $F$ fake users can cause in $r_i$.
--
--   **Formalization Note** Products and positions are `Fin n`, indexed from $0$. FAR is an `Alg n 1` of the published model. Its state is recomputed from its own history of observations, and the state stores click counts, so that $r_i$ is the ratio of clicks to feedbacks; Step 6's incremental formulas compute exactly this ratio. The ranking is the published `graphRankSelect`. Algorithm 2 leaves two choices unspecified: the tie-break among the candidates with the smallest $\eta$, and the "arbitrary ranking" returned when $G$ has a cycle. They are the parameters `tb` and `fb`, functions of FAR's own past. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: Products, positions and rounds use 1-based indices → Fin indices are 0-based; the state after t rounds uses the first t observations; reason: Relabelling preserves every source instance and round.
--   - encoding: Algorithm 1 stores empirical averages and updates them incrementally → FarState stores integer click counts and feedback counts; avg is their ratio, or 0 initially; reason: Step 6 and p. 16 define exactly this empirical mean.
--   - encoding: GraphRankSelect has unspecified valid tie choices and an arbitrary ranking on cyclic graphs → tb and fb are history-dependent parameters; valid FAR uses tb h S ∈ S for every nonempty tied set; reason: This exposes all source choices. The total function also accepts invalid tb and then uses the published fallback; Lemma 4 and Theorem 2 impose the valid-choice contract, while Lemmas 2 and 3 explicitly generalize it.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 17, Algorithm 1; p. 16, (4); p. 19, Algorithm 2

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm

namespace FakeUserRanking.FORC.Supplement

variable {n : ℕ}

/-! ### The FAR algorithm (Algorithm 1, p. 17, with the edge condition (4), p. 16)

Products and positions are `Fin n`, 0-based (Lean product `i` is paper product `i + 1`). FAR is
deterministic: one internal label (`Fin 1`) drawn with weight `1`. -/

/-- FAR's state: feedback counts `η_i` (`cnt`), click counts (`clk`, so that the average reward is
`r_i = clk_i / η_i`), and the product-ordering graph `G`, a set of directed edges; an edge `(i, k)`
records that product `k` dominates product `i` (p. 16). -/
structure FarState (n : ℕ) where
  cnt : Fin n → ℕ
  clk : Fin n → ℕ
  graph : Finset (Fin n × Fin n)

/-- Step 3: all counts zero and no edges. -/
def FarState.init : FarState n := ⟨fun _ => 0, fun _ => 0, ∅⟩

/-- Step 3: `δ = 1/(nT)`. -/
noncomputable def farDelta (n T : ℕ) : ℝ := 1 / ((n : ℝ) * T)

/-- The average reward `r_i = clk_i / η_i`, and `0` while `η_i = 0` (Step 3). Step 6's incremental
updates compute exactly this ratio. -/
noncomputable def FarState.avg (st : FarState n) (i : Fin n) : ℝ :=
  if st.cnt i = 0 then 0 else (st.clk i : ℝ) / st.cnt i

/-- The fakeness-robust radius of (4): `√(log(2nT/δ)/η_i) + F/η_i`, natural logarithm. It is used
only where `η_i > 0`. -/
noncomputable def farRadius (n T F : ℕ) (st : FarState n) (i : Fin n) : ℝ :=
  Real.sqrt (Real.log (2 * n * T / farDelta n T) / st.cnt i) + (F : ℝ) / st.cnt i

/-- Condition (4) / Step 7 for the ordered pair `(i, k)`: `η_i, η_k > 0` and
`r_i + √(log(2nT/δ)/η_i) + F/η_i ≤ r_k − √(log(2nT/δ)/η_k) − F/η_k`. -/
def farEdgeCond (n T F : ℕ) (st : FarState n) (i k : Fin n) : Prop :=
  0 < st.cnt i ∧ 0 < st.cnt k ∧
    st.avg i + farRadius n T F st i ≤ st.avg k - farRadius n T F st k

open Classical in
/-- Steps 6–7 of one round, given the displayed ranking `π` and the observation
`o = (last examined position, clicked?)`.
* Step 6: every product at a position `≤ o.1` gets one more feedback; the product at position `o.1`
  gets one more click if the user clicked.
* Step 7: with the updated counts and averages, every ordered pair `(i, k)` satisfying (4) is added
  to `G` as the edge `(i, k)`. Edges are never removed. -/
noncomputable def FarState.update (n T F : ℕ) (st : FarState n) (π : Equiv.Perm (Fin n))
    (o : Obs n) : FarState n :=
  let cnt' : Fin n → ℕ := fun i => if π.symm i ≤ o.1 then st.cnt i + 1 else st.cnt i
  let clk' : Fin n → ℕ := fun i => if o.2 = true ∧ i = π o.1 then st.clk i + 1 else st.clk i
  let st1 : FarState n := ⟨cnt', clk', st.graph⟩
  ⟨cnt', clk', st.graph ∪ Finset.univ.filter (fun e : Fin n × Fin n => farEdgeCond n T F st1 e.1 e.2)⟩

/-- Step 5: `π_t = GraphRankSelect(η, G)` (Algorithm 2, the published `graphRankSelect`). The
unspecified choices of Algorithm 2 (ties among the smallest `η`, and the "arbitrary ranking" when
`G` has a cycle) are the parameters `tb` and `fb`, functions of FAR's own past `h`. -/
noncomputable def farRank (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)) (h : List (Fin 1 × Obs n))
    (st : FarState n) : Equiv.Perm (Fin n) :=
  graphRankSelect (tb h) (fb h) st.cnt st.graph

/-- FAR's state after processing its own past `h` (labels and observations, oldest first): the
past rankings are recomputed round by round. -/
noncomputable def farState (n T F : ℕ) (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)) (h : List (Fin 1 × Obs n)) : FarState n :=
  (h.foldl (fun (acc : List (Fin 1 × Obs n) × FarState n) (x : Fin 1 × Obs n) =>
      (acc.1 ++ [x], acc.2.update n T F (farRank tb fb acc.1 acc.2) x.2))
    ([], FarState.init)).2

/-- The FAR algorithm (Algorithm 1, p. 17) for `n` products, horizon `T` and fakeness budget `F`,
which it knows. It does not know `μ`, `q`, or which users are fake. -/
noncomputable def far (n T F : ℕ) (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)) : Alg n 1 where
  w := fun _ _ => 1
  rank := fun h _ => farRank tb fb h (farState n T F tb fb h)

end FakeUserRanking.FORC.Supplement


