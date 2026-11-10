-- Prove2me | Definitions.Def_CNFLearnMQ_learnCNF
-- name    : CNFLearnMQ_learnCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:37.795685+00:00
-- url     : https://prove2.me/theorems/09f6ab6c-8d13-4b18-ad10-c87b08a50568
-- title:
--   LearnCNF$(\varepsilon,\delta)$ (Algorithm 3) as an oracle program, with its execution log
-- statement:
--   LearnCNF$(\varepsilon,\delta)$ draws $N_{\mathrm{seed}}$ seed samples $X_i$ and a pool of $N_{\mathrm{pool}}$ samples $Y_i$; recovers the cores of each $X_i$ with LearnCore$(X_i,\delta/(6N_{\mathrm{seed}}))$; builds the seed queue $Q$ and sets $\mathrm{cnt}=|Q|$. While $Q$ is nonempty: if $\mathrm{cnt}>N_{\mathrm{tot}}$ it returns $\bot$; otherwise it removes the first candidate $s=(S,\sigma_S)$, computes the pool frequency $\widehat q_s$ of samples violating $s$, accepts $s$ if $\widehat q_s\le 2\eta$, and if $\widehat q_s>2\eta$ and $|S|<k$ enqueues the extensions returned by ExtendSubclause$(s,Y)$, increasing $\mathrm{cnt}$ by their number. When the queue is empty it returns $\widehat\Phi=(V,\widehat C)$.
--
--   The logged version also returns ghost data: the seed samples, the pool, the seed cores, the initial queue, the record of every ExtendSubclause call, and the final counter (the total number of enqueued candidates, seeds included). The log is used to state Lemmas 5.8 and 5.20; it adds no charge.
--
--   Charges: $9$ for the parameters, $1$ for initialization, $1$ per loop test, $|S|+1$ per dequeue, $N_{\mathrm{pool}}(|S|+1)$ for $\widehat q_s$, $|S|+1$ per acceptance, $k+1$ per enqueued extension, $|\widehat C|(k+1)$ for the output.
--
--   **Formalization Note** LearnCNF receives only $n,k,d,t,\varepsilon,\delta$. The loop bound (fuel $N_{\mathrm{tot}}+2$) is never reached. Extensions are enqueued in a fixed order.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), §5.2, pp.23–25; Algorithm 3, p.25

import Mathlib
import Definitions.Def_CNFLearnMQ_buildSeedQueue
import Definitions.Def_CNFLearnMQ_extendSubclause

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant OProg

variable {n : ℕ}

/-- The empirical violation frequency `q̂_s = Σᵢ 1[(Yᵢ)_S = σ_S]/N_pool` of a subclause `s` in the
sample pool `Y` (Feng, Yu, Zhang, STOC 2027 submission (manuscript sha256 519ee6d4…), Algorithm 3
line 8, p.25); the denominator is the pool length `|Y| = N_pool`. -/
noncomputable def qhatPool (Y : List (Assignment n)) (s : Clause n) : ℝ := by
  classical
  exact ((Y.filter fun Z => decide (Violates s Z)).length : ℝ) / Y.length

/-- The record of one execution of LearnCNF, kept as ghost data (it adds no charge): the seed
samples `X`, the pool `Y`, the recovered seed cores `R`, the initial queue, the record of every call
to ExtendSubclause in order, and the final value of the counter `cnt` (the total number of
candidate subclauses enqueued, initial seeds included). -/
structure Log (n : ℕ) where
  seedSamples : List (Assignment n)
  pool : List (Assignment n)
  seedCores : Finset (Finset (Fin n))
  seedQueue : List (Clause n)
  calls : List (ExtCall n)
  enqueued : ℕ

/-- Lines 4–14 of Algorithm 3 (p.25): the queue loop, with queue `Q`, accepted set `Ĉ`, counter
`cnt` and the list of ExtendSubclause records so far. Before each dequeue, `cnt > N_tot` returns ⊥
(`none`). A dequeued `s` is accepted if `q̂_s ≤ 2η`; if `q̂_s > 2η` and `|S| < k` its extensions are
enqueued at the back (in a fixed order) and `cnt` grows by their number; otherwise it is discarded.
When the queue is empty the CNF formula `Ĉ` is returned.

Charges: `1` per loop test; `|S| + 1` per dequeue; `|Y|·(|S| + 1)` for `q̂_s`; `|S| + 1` per
acceptance; `k + 1` per enqueued extension; `|Ĉ|·(k + 1)` for the output.

**Formalization Note** The fuel argument bounds the number of iterations; with fuel `N_tot + 2` it is
never exhausted (each processed candidate is one of at most `cnt ≤ N_tot` queue entries), and an
exhausted fuel returns ⊥. -/
noncomputable def mainLoop (n k d : ℕ) (t ε δ : ℝ) (Y : List (Assignment n)) :
    ℕ → List (Clause n) → CNF n → ℕ → List (ExtCall n) →
      OProg n (Option (CNF n) × List (ExtCall n) × ℕ)
  | 0, _, _, cnt, calls => OProg.pure (none, calls, cnt)
  | _ + 1, [], C, cnt, calls => do
    charge (C.card * (k + 1))
    return (some C, calls, cnt)
  | fuel + 1, s :: Q, C, cnt, calls => do
    charge 1
    if Ntot n k d t ε < cnt then return (none, calls, cnt) else do
      charge (width s + 1)
      charge (Y.length * (width s + 1))
      let qh := qhatPool Y s
      let C' := if qh ≤ 2 * eta n k d t ε then insert s C else C
      charge (if qh ≤ 2 * eta n k d t ε then width s + 1 else 0)
      if 2 * eta n k d t ε < qh ∧ width s < k then do
        let call ← extendSubclause n k d t ε δ s Y
        let new := call.accepted.toList
        charge (new.length * (k + 1))
        mainLoop n k d t ε δ Y fuel (Q ++ new) C' (cnt + new.length) (calls ++ [call])
      else mainLoop n k d t ε δ Y fuel Q C' cnt calls

/-- LearnCNF(ε, δ) (Algorithm 3, p.25) with parameters `n, d, k, t`, sample access to `µ_Φ` and
membership-query access to `Φ`, returning its output (`none` = ⊥) together with the ghost log of the
execution.

Line 1 draws `X = (X_1, …, X_{N_seed})` and then `Y = (Y_1, …, Y_{N_pool})`; line 2 runs
LearnCore(Xᵢ, δ/(6N_seed)) and takes the union `R`; line 3 builds the seed queue and sets
`cnt = |Q|`; lines 4–14 are `mainLoop`. Charges: `9` for computing the parameters `T, N_tot, η,
N_seed, N_pool, ϕ, N_ext, ζ, Ξ(t)` (unit-cost real arithmetic) and `1` for initializing `Ĉ, cnt`.

**Formalization Note** The learner receives only `n, k, d, t, ε, δ`; it never receives `Φ`. -/
noncomputable def learnCNFLogged (n k d : ℕ) (t ε δ : ℝ) : OProg n (Option (CNF n) × Log n) := do
  charge 9
  let Xs ← drawList (Nseed n k d δ)
  let Y ← drawList (Npool n k d t ε δ)
  let fams ← Xs.mapM fun X => learnCore n k d X (δ / (6 * (Nseed n k d δ : ℝ)))
  let R := fams.foldr (· ∪ ·) ∅
  let Q ← buildSeedQueue k t R
  charge 1
  let res ← mainLoop n k d t ε δ Y (Ntot n k d t ε + 2) Q ∅ Q.length []
  return (res.1, ⟨Xs, Y, R, Q, res.2.1, res.2.2⟩)

/-- LearnCNF(ε, δ) (Algorithm 3, p.25): the output of `learnCNFLogged`, either a CNF formula
`Φ̂ = (V, Ĉ)` (`some Ĉ`) or the failure symbol ⊥ (`none`). -/
noncomputable def learnCNF (n k d : ℕ) (t ε δ : ℝ) : OProg n (Option (CNF n)) :=
  Prod.fst <$> learnCNFLogged n k d t ε δ

end CNFLearnMQ


