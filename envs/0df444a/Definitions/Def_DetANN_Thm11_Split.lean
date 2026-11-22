-- Prove2me | Definitions.Def_DetANN_Thm11_Split
-- name    : DetANN_Thm11_Split
-- status  : Definition
-- author  : @milia
-- created : 2026-11-21T08:46:11.250614+00:00
-- url     : https://prove2.me/theorems/ec3da82b-a80f-4fd0-9712-39e589d03d98
-- title:
--   Interfaces for the top-level reduction of Theorem 1.1: structures with a general answer property, and local answers
-- statement:
--   Two definitions for splitting Theorem 1.1 into a machine part and a mathematical part.
--   - $\mathrm{IsDetStructure}(\mathrm{Pre},\mathrm{Qry},Y,\theta,\mathrm{Ans},T_{\mathrm{pre}},S,T_q)$ is exactly `IsDetANNStructure` (definition `DetANN_DataStructure`) with the answer condition "the answer $k$ is a $c$-approximate nearest neighbor of $q$" replaced by an arbitrary predicate $\mathrm{Ans}(q,k)$. The machine, input and query layouts, the time measure (work) and the space measure (distinct cells stored to) are the same.
--   - $\mathrm{LocalAnswer}(C_0,k,P,\varepsilon,q,a)$ for $P:[n]\to\mathbb R^d$ holds when there are candidates $x:[2^k]\to[n]$, one for each tuple $v$ of the walk family $\mathrm{annTuples}\,k\,\varepsilon$, such that:
--     - they satisfy the local guarantee (25) with $\alpha=1+\varepsilon/100$ for the blocks $\mathrm{annBlocks}\,C_0\,k\,P\,\varepsilon$, the padded point set and the padded query: for all $v$ and all $y$ in the padded set, $\|\mathcal A_v(\bar q-\bar P_{x_v})\|^2\le\alpha^2\|\mathcal A_v(\bar q-y)\|^2$;
--     - $\|q-P_a\|\le\|q-P_{x_v}\|$ for every $v$.
--
--     By `theorem_1_1_correctness`, a local answer is a $(1+\varepsilon)$-approximate nearest neighbor whenever $C_0$ is large enough.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as the top-level reduction of DetANN.theorem_1_1 (Feng, Indyk, STOC 2027 submission, Theorem 1.1, p.2; the construction of §7.4, p.19). The machine is PNormReg (definition PNormReg_Machine) with the conventions of DetANN_DataStructure.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

namespace Thm11

/-!
# Interfaces for the top-level reduction of Theorem 1.1

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.4, p.19.

The data structure of Theorem 1.1 runs one Lemma 3.3 structure per tuple `v` on the superblock
projections `𝒜_v P` and answers with the best of the `d′ = 2^k` candidates. The reduction separates
the machine part (building and querying these structures) from the mathematics (the local guarantee
implies a `(1 + ε)`-approximate answer, `theorem_1_1_correctness`).
-/

/-- `IsDetANNStructure` with an arbitrary answer property `Ans q k` in place of
"`k` is a `c`-approximate nearest neighbor of `q`". Same machine, layouts and cost measures. -/
def IsDetStructure (Pre Qry : PNormReg.Program) {N m : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m))
    (θ : ℝ) (Ans : EuclideanSpace ℝ (Fin m) → Fin N → Prop) (Tpre Space Tq : ℝ) : Prop :=
  ∃ t : ℕ,
    (PNormReg.run Pre (inputState Y θ) detTape t).halted = true ∧
    ((PNormReg.run Pre (inputState Y θ) detTape t).work : ℝ) ≤ Tpre ∧
    ((cellsWritten Pre (inputState Y θ) t).card : ℝ) ≤ Space ∧
    ∀ q : EuclideanSpace ℝ (Fin m), ∃ t' : ℕ,
      (PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y θ) detTape t) q)
        detTape t').halted = true ∧
      ((PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y θ) detTape t) q)
        detTape t').work : ℝ) ≤ Tq ∧
      ∃ k : Fin N,
        (PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y θ) detTape t) q)
          detTape t').core.ptrs 0 = (k : ℤ) ∧ Ans q k

/-- The answer `a` of the composed structure: there are candidates `x_v` (one per tuple `v` of the
walk family on `Fin (2^k)`) satisfying the local guarantee (25) with `α = 1 + ε/100` for the blocks
`annBlocks C₀ k P ε`, and `a` is at least as close to `q` as every candidate. -/
def LocalAnswer {d n : ℕ} (C₀ : ℝ) (k : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin d)) (ε : ℝ)
    (q : EuclideanSpace ℝ (Fin d)) (a : Fin n) : Prop :=
  ∃ x : Fin (2 ^ k) → Fin n,
    LocalGuarantee (annBlocks C₀ k P ε) (annTuples k ε) (paddedSet k P) (padVec (2 ^ k) q)
      (fun v => padVec (2 ^ k) (P (x v))) (1 + ε / 100) ∧
    ∀ v, ‖q - P a‖ ≤ ‖q - P (x v)‖

end Thm11

end DetANN


