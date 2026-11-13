-- Prove2me | Definitions.Def_MultiThinkCoT_alg1
-- name    : MultiThinkCoT_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:44:08.474177+00:00
-- url     : https://prove2.me/theorems/51d438a8-d38d-4e64-8289-570a52d13e54
-- title:
--   Algorithm 1: boosting under the active and adaptive protocol, with cost accounting
-- statement:
--   **Algorithm 1** receives the training set $S_{\mathrm{e2e}}=\{(x^{(i)},y^{(i)})\}_{i=1}^m$, the number of rounds $K$, the per-source budget $M_\star$ and $\delta\in(0,1)$, a Consistent oracle and an adversary.
--
--   1. Initialize $D^{(1)}=(1/m,\dots,1/m)$.
--   2. For $k=1,\dots,K$, make up to $\lceil\log_2(2K/\delta)\rceil$ attempts. In each attempt:
--      - draw $i_1,\dots,i_{M_\star}$ i.i.d. from $D^{(k)}$ and set $S_{k,\ell}=\{i_1,\dots,i_{M_\star}\}$;
--      - obtain the CoTs $f_{k,\ell}^{\mathrm{CoT}\text{-}T}(x^{(i)})$, $i\in S_{k,\ell}$, from the source $f_{k,\ell}$ chosen by the adversary;
--      - fit $\hat f_{k,\ell}$ with the oracle on their prefix–next-token pairs;
--      - compute $\epsilon_{k,\ell}=\sum_i D^{(k)}_i\,\mathbf 1[\hat f_{k,\ell}^{\mathrm{e2e}\text{-}T}(x^{(i)})\neq y^{(i)}]$, and stop the attempts once $\epsilon_{k,\ell}\le0.25$.
--   3. With $\hat f_k,\epsilon_k$ from the last attempt: if $\epsilon_k>0.25$ return the constant $0$; if $\epsilon_k=0$ return $\hat f_k^{\mathrm{e2e}\text{-}T}$. Otherwise set
--   $$
--   \alpha_k=\tfrac12\log\frac{1-\epsilon_k}{\epsilon_k},\qquad D^{(k+1)}_i\propto D^{(k)}_i\,e^{\pm\alpha_k},
--   $$
--   with $+$ on misclassified indices, normalized to sum $1$.
--   4. Return $\hat h_K(x)=\arg\max_{b}\sum_k\alpha_k\mathbf 1[\hat f_k^{\mathrm{e2e}\text{-}T}(x)=b]$, ties to $1$.
--
--   The definition is the distribution over runs of this procedure. Each run records:
--   - the returned predictor, as a representation that can be evaluated;
--   - the errors $\epsilon_k$ of the executed rounds;
--   - the number $\kappa$ of sources queried;
--   - the largest requested subset;
--   - the total cost.
--
--   **Cost model.** Cost accrues line by line inside the definition:
--   - $m$ for line 1;
--   - $M_\star(m+1)$ for the draws and the set of line 4;
--   - $|S_{k,\ell}|\,T$ for reading CoT bits;
--   - one unit per bit of each prefix–next-token pair;
--   - $\mathrm{oc}(n,N)$ for an oracle call on $N$ pairs of maximal length $n$;
--   - for every evaluation of $\hat f^{\mathrm{e2e}\text{-}T}(x)$, $\mathrm{ec}(|z|)$ per next-token evaluation on the current string $z$ plus one unit per appended bit and one for reading the last bit;
--   - unit cost for every real arithmetic operation (including $\log$ and $\exp$), comparison and return.
--
--   **Formalization Note**
--   - The only randomness is the index draws.
--   - $\log$ is natural and $\log_2$ is the base-2 logarithm.
--   - $D^{(k)}$ is a real vector; drawing from it uses the masses $D^{(k)}_i$, which form a probability vector along every run when $m\ge1$. If they do not, which can only happen for $m=0$, the draw returns no indices.
--   - If a round had no attempt ($\lceil\log_2(2K/\delta)\rceil=0$, impossible for $K\ge1$, $\delta<1$), it fails as in line 12 with $\epsilon_k$ recorded as $1$.
--   - The accuracy $\varepsilon$ is not used by any line and is not an input.
--   - The adversary's own computation is not charged to the learner.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Algorithm 1, p.24 (PDF p.24); runtime model §6.1 p.17 and Definition 1.1 p.3

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e
import Definitions.Def_MultiThinkCoT_IsConsistentOracle
import Definitions.Def_MultiThinkCoT_IsStrictAdversary

namespace MultiThinkCoT

/-!
# Algorithm 1 (boosting under the active and adaptive protocol), with cost accounting

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), Algorithm 1, p.24 (PDF p.24); runtime model
of §6.1, p.17 and Definition 1.1, p.3.

Algorithm 1 receives the training set `S_e2e = {(x(i), y(i))}_{i=1}^m`, the number `K` of
boosting rounds, the per-source budget `M⋆` and the confidence `δ`. Line 1 sets
`D⁽¹⁾ = (1/m, …, 1/m)`. For `k = 1, …, K` (line 2) it makes at most `⌈log₂(2K/δ)⌉` attempts
(line 3); in each it draws `i_1, …, i_{M⋆}` i.i.d. from `D⁽ᵏ⁾` and sets `S_{k,ℓ} = {i_1, …, i_{M⋆}}`
(line 4), obtains the CoTs `f_{k,ℓ}^{CoT-T}(x(i))`, `i ∈ S_{k,ℓ}`, from the source `f_{k,ℓ}`
chosen by the adversary (line 5), applies the Consistent oracle to their prefix–next-token pairs
to get `f̂_{k,ℓ}` (line 6), computes `ϵ_{k,ℓ} = Σ_i D⁽ᵏ⁾_i 1[f̂_{k,ℓ}^{e2e-T}(x(i)) ≠ y(i)]`
(line 7), and stops the attempts once `ϵ_{k,ℓ} ≤ 0.25` (lines 8–9). With `f̂_k`, `ϵ_k` from the
last attempt (line 10): if `ϵ_k > 0.25` it returns the constant-0 predictor (lines 11–12); if
`ϵ_k = 0` it returns `f̂_k^{e2e-T}` (lines 13–14); otherwise `α_k = ½ log((1 − ϵ_k)/ϵ_k)`
(line 15) and `D⁽ᵏ⁺¹⁾_i ∝ D⁽ᵏ⁾_i e^{±α_k}`, `+` on the misclassified indices, normalized to sum
`1` (line 16). After the loop it returns the weighted majority
`ĥ_K(x) = argmax_b Σ_k α_k 1[f̂_k^{e2e-T}(x) = b]`, ties to `1` (line 17).

**Formalization Note.**
* The algorithm is a probability distribution `PMF Outcome` over its runs. The only randomness is
  the index draws of line 4; the oracle `O` and the adversary `adv` are deterministic functions
  (the adversary of a run is `A xs` for a strategy `A`, see `IsStrictAdversary`).
* `D⁽ᵏ⁾` is a real vector `Fin m → ℝ`. A draw from it uses the PMF with masses `D⁽ᵏ⁾_i`, which
  exists when every entry is positive and the entries sum to `1` (`IsProbVec`). That invariant
  holds along every run for `m ≥ 1`; if it failed (only for `m = 0`) the draw returns the empty
  list.
* Line 4: `S_{k,ℓ}` is the *set* of drawn indices, so `|S_{k,ℓ}| ≤ M⋆`. Line 5: the learner
  only uses the CoTs on `S_{k,ℓ}`; the pair `(S_{k,ℓ}, f_{k,ℓ})` is appended to the history the
  adversary sees. Line 6: the oracle receives the prefix–next-token pairs of the CoTs, by
  increasing index `i`. If `⌈log₂(2K/δ)⌉ = 0` (impossible for `K ≥ 1`, `δ ∈ (0,1)`) a round has
  no attempt; it then fails as in line 12, with `ϵ_k` recorded as `1`.
* `log` is the natural logarithm; `⌈log₂(2K/δ)⌉` is `⌈Real.logb 2 (2K/δ)⌉₊`.
* The predictor is returned as a representation: `const0` (line 12), `single f̂_k` (line 14) or
  `vote [(α_1, f̂_1), …, (α_K, f̂_K)]` (line 17); `Pred.eval T` evaluates it on a string. The
  accuracy parameter `ε` of the Require line is not used by any line and is omitted.
* The outcome also records the errors `ϵ_k` of the executed outer rounds (`errs`), the number
  `κ` of sources queried (one per attempt), the largest `|S_{k,ℓ}|`, and the cost.
* **Cost model (unit-cost real arithmetic).** The paper names no machine model; the cost accrues
  line by line inside the definition:
  - line 1: `m` (one write per entry);
  - line 4: `M⋆ (m + 1)` (one unit per draw, plus at most `m` comparisons to insert the index in
    the set);
  - line 5: `|S_{k,ℓ}| · T` (one unit per CoT bit read);
  - line 6: one unit per bit written while building each pair plus one per pair
    (`Σ_pairs (|prefix| + 1)`), and `oc n N` for the oracle call on `N` pairs of maximal length
    `n` (Definition 1.1: the oracle's running time);
  - every evaluation of `f̂^{e2e-T}(x)` (lines 7, 16, and evaluating the output) runs the `T`
    autoregressive steps, charging `ec |z|` for the next-token evaluation of `f̂` on the current
    string `z` (the p.17 assumption that `f(z)` takes time `poly(d, |z|)`) and `1` for appending
    the bit, then `1` for reading the last bit;
  - line 7: per index one evaluation plus `3` (compare, multiply, add); line 8: `1`;
  - lines 11 and 13: `1` each; line 15: `4` (subtract, divide, log, multiply);
  - line 16: per index one evaluation plus `3` (compare, exponential, multiply), plus `2m` for the
    normalization (sum and divisions);
  - a return: `1`.
  The cost functions `oc` and `ec` are inputs; the runtime theorems bound them by polynomials.
-/

/-- The returned predictor, as a representation. -/
inductive Pred where
  /-- The constant-0 predictor (line 12). -/
  | const0 : Pred
  /-- `f̂_k^{e2e-T}` (line 14). -/
  | single : Gen → Pred
  /-- The weighted majority `Σ_k α_k 1[f̂_k^{e2e-T}(x) = b]` with ties to `1` (line 17). -/
  | vote : List (ℝ × Gen) → Pred

/-- The total weight voting for `b` at `x`: `Σ_k α_k 1[f_k^{e2e-T}(x) = b]`. -/
noncomputable def voteScore (T : ℕ) (ens : List (ℝ × Gen)) (b : Bool) (x : List Bool) : ℝ :=
  (ens.map fun p => if e2e p.2 T x = b then p.1 else 0).sum

/-- Evaluation of a returned predictor on a string. -/
noncomputable def Pred.eval (T : ℕ) : Pred → List Bool → Bool
  | .const0, _ => false
  | .single f, x => e2e f T x
  | .vote ens, x => decide (voteScore T ens false x ≤ voteScore T ens true x)

/-- `t` autoregressive steps of `f` from `x`, with their cost: `ec |z|` for evaluating `f` on the
current string `z` and `1` for appending the bit. -/
def runC (ec : ℕ → ℕ) (f : Gen) : ℕ → List Bool → List Bool × ℕ
  | 0, x => (x, 0)
  | t + 1, x => let r := runC ec f t x; (step f r.1, r.2 + ec r.1.length + 1)

/-- `f^{e2e-T}(x)` computed with its cost (the steps, then `1` for reading the last bit). -/
def e2eC (ec : ℕ → ℕ) (f : Gen) (T : ℕ) (x : List Bool) : Bool × ℕ :=
  let r := runC ec f T x
  (r.1.getLastD false, r.2 + 1)

/-- The cost of evaluating a returned predictor on `x`. -/
def Pred.evalCost (ec : ℕ → ℕ) (T : ℕ) : Pred → List Bool → ℕ
  | .const0, _ => 1
  | .single f, x => (e2eC ec f T x).2
  | .vote ens, x => (ens.map fun p => (e2eC ec p.2 T x).2 + 2).sum + 1

/-- `D⁽¹⁾ = (1/m, …, 1/m)` (line 1). -/
noncomputable def initW (m : ℕ) : Fin m → ℝ := fun _ => 1 / (m : ℝ)

/-- A probability vector: positive entries summing to `1`. -/
def IsProbVec {m : ℕ} (w : Fin m → ℝ) : Prop := (∀ i, 0 < w i) ∧ ∑ i, w i = 1

/-- The distribution on `[m]` with masses `w_i`. -/
noncomputable def drawOne {m : ℕ} (w : Fin m → ℝ) (h : IsProbVec w) : PMF (Fin m) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (w i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (h.1 i).le), h.2, ENNReal.ofReal_one])

open Classical in
/-- `n` i.i.d. draws from `w` (line 4). -/
noncomputable def drawList {m : ℕ} (w : Fin m → ℝ) : ℕ → PMF (List (Fin m))
  | 0 => PMF.pure []
  | n + 1 =>
    if h : IsProbVec w then (drawOne w h).bind fun i => (drawList w n).map (List.cons i)
    else PMF.pure []

/-- The weighted error `Σ_i w_i 1[f^{e2e-T}(x(i)) ≠ y(i)]` (line 7). -/
noncomputable def wErr (T : ℕ) {m : ℕ} (xs : Fin m → List Bool) (ys : Fin m → Bool)
    (w : Fin m → ℝ) (f : Gen) : ℝ :=
  ∑ i, w i * if e2e f T (xs i) ≠ ys i then 1 else 0

/-- `α = ½ log((1 − ϵ)/ϵ)` (line 15). -/
noncomputable def alpha (ε : ℝ) : ℝ := 1 / 2 * Real.log ((1 - ε) / ε)

/-- The reweighting of line 16: `w_i e^{+α}` on misclassified indices, `w_i e^{−α}` otherwise,
normalized to sum `1`. -/
noncomputable def updW (T : ℕ) {m : ℕ} (xs : Fin m → List Bool) (ys : Fin m → Bool)
    (w : Fin m → ℝ) (α : ℝ) (f : Gen) : Fin m → ℝ :=
  let u : Fin m → ℝ := fun i => w i * Real.exp (if e2e f T (xs i) ≠ ys i then α else -α)
  fun i => u i / ∑ j, u j

/-- Lines 11–16 after a round's last attempt `f̂_k` with error `ϵ_k`: either a return
(`Sum.inl`: line 12 or line 14), or the next weights and the ensemble extended by `(α_k, f̂_k)`
(`Sum.inr`). -/
noncomputable def roundStep (T : ℕ) {m : ℕ} (xs : Fin m → List Bool) (ys : Fin m → Bool)
    (w : Fin m → ℝ) (ens : List (ℝ × Gen)) (f : Gen) (ε : ℝ) :
    Pred ⊕ ((Fin m → ℝ) × List (ℝ × Gen)) :=
  if 1 / 4 < ε then Sum.inl Pred.const0
  else if ε = 0 then Sum.inl (Pred.single f)
  else Sum.inr (updW T xs ys w (alpha ε) f, ens ++ [(alpha ε, f)])

/-- The boosting recursion of lines 10–17 applied to a given sequence `f̂_1, f̂_2, …` of round
predictors, from weights `w` and ensemble `ens`: returns the output predictor and the errors
`ϵ_k` of the executed rounds. -/
noncomputable def boostRun (T : ℕ) {m : ℕ} (xs : Fin m → List Bool) (ys : Fin m → Bool) :
    (Fin m → ℝ) → List (ℝ × Gen) → List Gen → Pred × List ℝ
  | _, ens, [] => (Pred.vote ens, [])
  | w, ens, f :: fs =>
    match roundStep T xs ys w ens f (wErr T xs ys w f) with
    | Sum.inl p => (p, [wErr T xs ys w f])
    | Sum.inr q => let r := boostRun T xs ys q.1 q.2 fs; (r.1, wErr T xs ys w f :: r.2)

/-- The fixed inputs of a run of Algorithm 1. -/
structure Cfg (m : ℕ) where
  /-- generation length -/
  T : ℕ
  /-- the Consistent oracle -/
  O : List (List Bool × Bool) → Gen
  /-- cost of one oracle call on `N` pairs of maximal length `n`: `oc n N` -/
  oc : ℕ → ℕ → ℕ
  /-- cost of one next-token evaluation on a string of length `ℓ`: `ec ℓ` -/
  ec : ℕ → ℕ
  /-- per-source budget `M⋆` -/
  Mst : ℕ
  /-- inputs `x(1), …, x(m)` -/
  xs : Fin m → List Bool
  /-- labels `y(1), …, y(m)` -/
  ys : Fin m → Bool
  /-- the adversary's choice of source from the history and the current subset -/
  adv : History m → Finset (Fin m) → Gen

/-- The state between attempts. -/
structure St (m : ℕ) where
  /-- current weights `D⁽ᵏ⁾` -/
  w : Fin m → ℝ
  /-- `(α_j, f̂_j)` of the completed rounds -/
  ens : List (ℝ × Gen)
  /-- `ϵ_j` of the completed rounds -/
  errs : List ℝ
  /-- the protocol history -/
  hist : History m
  /-- number of sources queried so far -/
  kappa : ℕ
  /-- largest subset requested so far -/
  maxS : ℕ
  /-- cost so far -/
  cost : ℕ

/-- The outcome of a run. -/
structure Outcome where
  /-- the returned predictor -/
  pred : Pred
  /-- `ϵ_k` of the executed outer rounds -/
  errs : List ℝ
  /-- number of sources (generators) queried, `κ` -/
  kappa : ℕ
  /-- the largest `|S_{k,ℓ}|` -/
  maxS : ℕ
  /-- total cost of the run -/
  cost : ℕ

/-- One attempt, lines 4–8: draw `S`, get the CoTs from the adversary's source, fit `f̂` with the
oracle, compute its weighted error. Returns the new state and `(f̂, ϵ)`. -/
noncomputable def attempt {m : ℕ} (c : Cfg m) (s : St m) : PMF (St m × (Gen × ℝ)) :=
  ((drawList s.w c.Mst).map List.toFinset).bind fun S =>
    let f := c.adv s.hist S
    let idx := (List.finRange m).filter fun i => decide (i ∈ S)
    let ps := idx.flatMap fun i => prefixPairs (c.xs i) (cot f c.T (c.xs i))
    let fhat := c.O ps
    let ε := wErr c.T c.xs c.ys s.w fhat
    let cost := c.Mst * (m + 1) + S.card * c.T + (ps.map fun p => p.1.length + 1).sum
      + c.oc ((ps.map fun p => p.1.length).foldr max 0) ps.length
      + (∑ i, ((e2eC c.ec fhat c.T (c.xs i)).2 + 3)) + 1
    PMF.pure (⟨s.w, s.ens, s.errs, s.hist ++ [(S, f)], s.kappa + 1, max s.maxS S.card,
      s.cost + cost⟩, (fhat, ε))

/-- The inner loop, lines 3–9, with `l` attempts left; returns the state and the last attempt. -/
noncomputable def innerLoop {m : ℕ} (c : Cfg m) :
    ℕ → St m → Option (Gen × ℝ) → PMF (St m × Option (Gen × ℝ))
  | 0, s, last => PMF.pure (s, last)
  | l + 1, s, _ => (attempt c s).bind fun r =>
    if r.2.2 ≤ 1 / 4 then PMF.pure (r.1, some r.2) else innerLoop c l r.1 (some r.2)

/-- The outer loop, lines 2–17, with `r` rounds left and `L` attempts per round. -/
noncomputable def outerLoop {m : ℕ} (c : Cfg m) (L : ℕ) : ℕ → St m → PMF Outcome
  | 0, s => PMF.pure ⟨Pred.vote s.ens, s.errs, s.kappa, s.maxS, s.cost + 1⟩
  | r + 1, s => (innerLoop c L s none).bind fun q =>
    match q.2 with
    | none => PMF.pure ⟨Pred.const0, q.1.errs ++ [1], q.1.kappa, q.1.maxS, q.1.cost + 1⟩
    | some (f, ε) =>
      match roundStep c.T c.xs c.ys q.1.w q.1.ens f ε with
      | Sum.inl p => PMF.pure ⟨p, q.1.errs ++ [ε], q.1.kappa, q.1.maxS,
          q.1.cost + (if 1 / 4 < ε then 2 else 3)⟩
      | Sum.inr nw => outerLoop c L r ⟨nw.1, nw.2, q.1.errs ++ [ε], q.1.hist, q.1.kappa, q.1.maxS,
          q.1.cost + 2 + 4 + (∑ i, ((e2eC c.ec f c.T (c.xs i)).2 + 3)) + 2 * m⟩

/-- **Algorithm 1** on the training set `(xs, ys)` with `K` rounds, per-source budget `Mst`,
confidence `δ`, oracle `O` (cost `oc`), next-token cost `ec`, generation length `T` and
adversary `adv`, as a distribution over its runs. -/
noncomputable def alg1 (T : ℕ) (O : List (List Bool × Bool) → Gen) (oc : ℕ → ℕ → ℕ)
    (ec : ℕ → ℕ) (K Mst : ℕ) (δ : ℝ) {m : ℕ} (xs : Fin m → List Bool) (ys : Fin m → Bool)
    (adv : History m → Finset (Fin m) → Gen) : PMF Outcome :=
  outerLoop ⟨T, O, oc, ec, Mst, xs, ys, adv⟩ ⌈Real.logb 2 (2 * K / δ)⌉₊ K
    ⟨initW m, [], [], [], 0, 0, m⟩

end MultiThinkCoT


