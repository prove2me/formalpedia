-- Prove2me | Definitions.Def_SchedComplexity_NoWait_Construction
-- name    : SchedComplexity_NoWait_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:02:07.661698+00:00
-- url     : https://prove2.me/theorems/a0314be4-c966-4c14-9f9c-b9c8ab4c5cd6
-- title:
--   The constructions of Theorem 5 (machine assignment ι, partial sums q_ℓi, processing times) and of Theorem 2(d)
-- statement:
--   The constructions in the proofs of Theorem 5 (pp. 24–25) and Theorem 2(d) (p. 14) of Brucker, Lenstra & Rinnooy Kan.
--
--   Given a directed graph $G=(V,A)$ with $n=|V|$, the no-wait flow shop of Theorem 5 has $n$ jobs (one per vertex) and $m=n(n-1)+2$ machines.
--
--   1. An **admissible assignment** $\iota$ maps every ordered pair $(j,k)$ of distinct jobs to a machine index $\iota(j,k)\in\{2,\dots,m-1\}$, bijectively, such that "for no $J_\ell$ some $M_{\iota(j,\ell)}$ directly follows an $M_{\iota(\ell,k)}$", i.e. never $\iota(j,\ell)=\iota(\ell,k)+1$ (also when $j=k$).
--   2. For parameters $\lambda,\mu\in\mathbb N$, the **partial sums** are
--   $$q_{\ell i}=\begin{cases}i\mu+\lambda&\text{if } i=\iota(\ell,k)\text{ and }(\ell,k)\in A\\ i\mu+\lambda+1&\text{if } i=\iota(\ell,k)\text{ and }(\ell,k)\notin A\\ i\mu-\lambda&\text{if } i+1=\iota(j,\ell)\text{ and }(j,\ell)\in A\\ i\mu-\lambda-1&\text{if } i+1=\iota(j,\ell)\text{ and }(j,\ell)\notin A\\ i\mu&\text{otherwise,}\end{cases}$$
--   with the cases tested in this order.
--   3. The **processing times** are $p_{\ell 1}=q_{\ell 1}$ and $p_{\ell i}=q_{\ell i}-q_{\ell,i-1}$ for $i=2,\dots,m$.
--   4. The graph of **Theorem 2(d)**: given $G'=(V',A')$ and a vertex $v'\in V'$, let $V=V'\cup\{v''\}$ with a new vertex $v''$ and
--   $$A=\{(u,v)\mid (u,v)\in A',\ v\ne v'\}\cup\{(u,v'')\mid (u,v')\in A'\}.$$
--
--   **Formalization Note** The machine indices $\iota(j,k)$ and the index $i$ of $q_{\ell i}$ are the paper's $1$-based indices; the processing time of machine `r : Fin m` is the paper's $p_{\ell,r+1}$. The partial sums and processing times are computed in $\mathbb Z$ (the "$-\lambda$" cases). The instance's processing times are their conversion to $\mathbb N$ (`Int.toNat`); a separate theorem shows they are all $\ge1$ under the paper's hypotheses, so the conversion is exact there. The paper's property of $\iota$ is what makes the cases of $q_{\ell i}$ mutually exclusive; the definition does not assume it and simply tests the cases in the printed order. The new vertex $v''$ of Theorem 2(d) is the last vertex `Fin.last n`.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), pp. 24–25, proof of Theorem 5(a); p. 14, proof of Theorem 2(d)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop

namespace SchedComplexity.NoWait

/-! # The constructions of Theorem 5 (pp. 24–25) and Theorem 2(d) (p. 14) -/

/-- The number of machines `m = n(n − 1) + 2` of the construction of Theorem 5(a), p. 24. -/
def numMachines (n : ℕ) : ℕ := n * (n - 1) + 2

theorem numMachines_pos (n : ℕ) : 0 < numMachines n := by
  unfold numMachines; omega

/-- An admissible assignment `ι` of machines to ordered pairs of distinct jobs (p. 24): `ι j k`
is the (1-based) index of the machine `M_{ι(j,k)}` that corresponds to the pair `(J_j, J_k)`,
`j ≠ k` (values of `ι` on the diagonal are ignored). Admissible means
1. `ι` takes values in the middle machines `{2, …, m − 1} = {2, …, n(n−1)+1}`,
2. `ι` is injective on ordered pairs of distinct jobs,
3. every middle machine is `ι(j,k)` for some pair (so `ι` is a bijection onto them),
4. "for no `J_ℓ` some `M_{ι(j,ℓ)}` directly follows an `M_{ι(ℓ,k)}`": never
   `ι(j,ℓ) = ι(ℓ,k) + 1` (here `j = k` is allowed). -/
def Admissible (n : ℕ) (ι : Fin n → Fin n → ℕ) : Prop :=
  (∀ j k : Fin n, j ≠ k → 2 ≤ ι j k ∧ ι j k ≤ n * (n - 1) + 1) ∧
  (∀ j k j' k' : Fin n, j ≠ k → j' ≠ k' → ι j k = ι j' k' → j = j' ∧ k = k') ∧
  (∀ i : ℕ, 2 ≤ i → i ≤ n * (n - 1) + 1 → ∃ j k : Fin n, j ≠ k ∧ ι j k = i) ∧
  (∀ j ℓ k : Fin n, j ≠ ℓ → ℓ ≠ k → ι j ℓ ≠ ι ℓ k + 1)

/-- The partial sums `q_{ℓ i}` of the construction (display on p. 24), in `ℤ`, for the graph
`adj`, the assignment `ι` and the parameters `λ`, `μ`; the cases are tested in the order printed:
`iμ + λ` if `i = ι(ℓ,k)` and `(ℓ,k) ∈ A`; `iμ + λ + 1` if `i = ι(ℓ,k)` and `(ℓ,k) ∉ A`;
`iμ − λ` if `i + 1 = ι(j,ℓ)` and `(j,ℓ) ∈ A`; `iμ − λ − 1` if `i + 1 = ι(j,ℓ)` and `(j,ℓ) ∉ A`;
`iμ` otherwise (always with `k ≠ ℓ`, `j ≠ ℓ`). -/
def partialSum {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ)
    (ℓ : Fin n) (i : ℕ) : ℤ :=
  if ∃ k : Fin n, k ≠ ℓ ∧ i = ι ℓ k ∧ adj ℓ k = true then (i : ℤ) * mu + lam
  else if ∃ k : Fin n, k ≠ ℓ ∧ i = ι ℓ k ∧ adj ℓ k = false then (i : ℤ) * mu + lam + 1
  else if ∃ j : Fin n, j ≠ ℓ ∧ i + 1 = ι j ℓ ∧ adj j ℓ = true then (i : ℤ) * mu - lam
  else if ∃ j : Fin n, j ≠ ℓ ∧ i + 1 = ι j ℓ ∧ adj j ℓ = false then (i : ℤ) * mu - lam - 1
  else (i : ℤ) * mu

/-- The processing times of the construction, in `ℤ` (p. 25): `p_{ℓ1} = q_{ℓ1}` and
`p_{ℓi} = q_{ℓi} − q_{ℓ,i−1}` for `i = 2, …, m`. Machine `r : Fin m` is the paper's `M_{r+1}`. -/
def procTimeInt {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ)
    (ℓ : Fin n) (r : Fin (numMachines n)) : ℤ :=
  if r.val = 0 then partialSum adj ι lam mu ℓ 1
  else partialSum adj ι lam mu ℓ (r.val + 1) - partialSum adj ι lam mu ℓ r.val

/-- The no-wait flow shop instance of Theorem 5 (p. 25): `n` jobs, `numMachines n` machines and
processing times `procTimeInt`, converted to `ℕ` with `Int.toNat`. Theorem 5's
milestone on positivity shows that every `procTimeInt` is `≥ 1` for admissible `ι`, `λ ≥ 1`,
`μ ≥ 2λ + 3`, so the conversion changes nothing there. -/
def procTimes {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ) :
    Fin n → Fin (numMachines n) → ℕ :=
  fun ℓ r => (procTimeInt adj ι lam mu ℓ r).toNat

/-- The graph `G = (V, A)` of Theorem 2(d), p. 14, built from `G' = (V', A')` on `Fin n` and a
chosen vertex `v'`: `V = V' ∪ {v''}` with `v''` the new last vertex `Fin.last n`, and
`A = {(u,v) | (u,v) ∈ A', v ≠ v'} ∪ {(u,v'') | (u,v') ∈ A'}`. No arc leaves `v''`. -/
def hcToHpGraph {n : ℕ} (adj' : Fin n → Fin n → Bool) (v' : Fin n) :
    Fin (n + 1) → Fin (n + 1) → Bool :=
  fun a b =>
    if ha : a = Fin.last n then false
    else if hb : b = Fin.last n then adj' (a.castPred ha) v'
    else adj' (a.castPred ha) (b.castPred hb) && decide (b.castPred hb ≠ v')

end SchedComplexity.NoWait


