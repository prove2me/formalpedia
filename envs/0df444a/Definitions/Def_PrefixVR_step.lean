-- Prove2me | Definitions.Def_PrefixVR_step
-- name    : PrefixVR_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:50.752594+00:00
-- url     : https://prove2.me/theorems/8696a5a6-f998-4c05-8503-2c410c6be509
-- title:
--   One update of Algorithm 1 (prefix-corrected recursive gradient method)
-- statement:
--   This module defines the state, the initialization and one update of **Algorithm 1** (prefix-corrected recursive gradient method).
--
--   *State.* Before update $t$ the method retains four vectors of $\mathbb R^d$: the current point $x_t$, the active estimate $v_t$, the prefix accumulator $h$ (one accumulator, whose successive values are $h_{s,r}$), and the saved output $x_{\mathrm{out}}$.
--
--   *Initialization (line 1).* $v_1=\frac1n\sum_{i=1}^n\nabla f_i(x_1)$, using $n$ component-gradient queries at $x_1$; $h=0$.
--
--   *Update $t\ge1$ (lines 3–20).* Let $s=\lfloor (t-1)/n\rfloor$ and $r=t-sn\in\{1,\dots,n\}$.
--
--   1. If $t=\tau$, save $x_t$ as $x_{\mathrm{out}}$.
--   2. $x_{t+1}=x_t-\eta v_t$ (3).
--   3. If $r=1$: $h_{s,1}=\nabla f_1(x_{t+1})/n$. Otherwise, with a draw $j_t\in[r-1]$,
--   $$
--   h_{s,r}=h_{s,r-1}+\frac{r-1}{n}\big[\nabla f_{j_t}(x_{t+1})-\nabla f_{j_t}(x_t)\big]+\frac1n\nabla f_r(x_{t+1}).\qquad(5)
--   $$
--   4. If $r<n$: with a draw $i_t\in[n]$, $v_{t+1}=v_t+\nabla f_{i_t}(x_{t+1})-\nabla f_{i_t}(x_t)$ (6). If $r=n$: $v_{t+1}=h_{s,n}$ (7).
--
--   The draws are used only after $x_{t+1}$ has been computed.
--
--   **Formalization Note** The programs `init` and `step` are written in an arbitrary monad and reach the gradients only through an oracle argument `oracle i x` $=\nabla f_i(x)$; instantiating the monad with a logging monad records every component-gradient query. Components are `Fin n`: the paper's component $r$ is `Fin.ofNat n (r − 1)`, and the draw $j_t\in\{1,\dots,r-1\}$ is passed as $j_t-1$. Times are 1-based. The structure `State` has exactly four fields of type $\mathbb R^d$, which is how the "$O(d)$ working memory" of §3.4 is read.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), Algorithm 1, p.5 (PDF p.5), with (3) p.4 and (5)–(7) p.5; state: §3.4, p.7

import Mathlib

namespace PrefixVR

/-- **The estimator state of Algorithm 1** (the vectors it retains between updates).
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), §3.4, p.7: "The implementation
retains the current point, active estimate, prefix accumulator, a constant number of temporary
vectors, and the sampled output. The notation h_{s,r} denotes successive values of one
accumulator, not separately stored vectors."

Before update `t` the state holds the current point `x = x_t`, the active estimate `v = v_t`,
the prefix accumulator `h` (its last value), and the saved output `xout`.

**Formalization Note.** The state has exactly four fields of type `ℝᵈ` and no field whose size
grows with `n` or `T`; temporaries of an update are local `let`s inside `step`, and the counter
`t` and the sampled indices are arguments of `step`. This is how the paper's "O(d) working
memory" is read (structurally): the algorithm is the iteration of `step` on this record. -/
structure State (d : ℕ) where
  /-- the current point `x_t` -/
  x : EuclideanSpace ℝ (Fin d)
  /-- the active estimate `v_t` -/
  v : EuclideanSpace ℝ (Fin d)
  /-- the prefix accumulator (successive values `h_{s,r}`) -/
  h : EuclideanSpace ℝ (Fin d)
  /-- the saved output `x_out` -/
  xout : EuclideanSpace ℝ (Fin d)

/-- The position `r = t − sn` of update `t ≥ 1` in its cycle, with `s = ⌊(t − 1)/n⌋`
(Algorithm 1, line 3, p.5; §3.1, p.4). For `t ≥ 1` and `n ≥ 1`, `1 ≤ r ≤ n`. -/
def cyclePos (n t : ℕ) : ℕ := t - ((t - 1) / n) * n

/-- **Initialization of Algorithm 1** (line 1, p.5): `v₁ = (1/n) ∑_{i=1}^n ∇fᵢ(x₁)`, computed with
`n` component-gradient queries at `x₁`, in the order `i = 1, …, n`.

The oracle `oracle i x` returns `∇fᵢ(x)` in an arbitrary monad `m`; the program can reach the
gradients only through it, so instantiating `m` with a logging monad records every query.
The accumulator starts at `0` and the saved output at `x₁` (it is overwritten at `t = τ`).

**Formalization Note.** Components are `Fin n` (paper index `i` is `i − 1`). The sum is
accumulated in one running vector as its gradients are queried (App. C, "Query and memory
counts", p.16: "Each sum can be accumulated as its gradients are queried"), so the
initialization, like `step`, retains no object whose size grows with `n`. -/
noncomputable def init {m : Type → Type} [Monad m] {n d : ℕ}
    (oracle : Fin n → EuclideanSpace ℝ (Fin d) → m (EuclideanSpace ℝ (Fin d)))
    (x₁ : EuclideanSpace ℝ (Fin d)) : m (State d) := do
  let s ← (List.finRange n).foldlM (fun acc i => do
      let a ← oracle i x₁
      pure (acc + a)) 0
  pure ⟨x₁, (n : ℝ)⁻¹ • s, 0, x₁⟩

/-- **One update of Algorithm 1** (lines 3–20, p.5, with (3), (5), (6), (7), pp.4–5).
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), Algorithm 1 "Prefix-corrected
recursive gradient method".

Update `t ≥ 1` with stepsize `η`, output index `τ`, prefix draw `j` and active draw `i`, from
the state `(x_t, v_t, h, x_out)`:
1. `r = t − ⌊(t − 1)/n⌋ n`; if `t = τ`, save `x_t` as `x_out` (lines 7–8);
2. `x_{t+1} = x_t − η v_t` (line 10, (3)); the draws are not used here;
3. if `r = 1`, `h_{s,1} = ∇f₁(x_{t+1})/n` (line 12, i.e. (5) from `h_{s,0} = 0` with the middle
   term omitted); otherwise, with `j_t = j + 1 ∈ [r − 1]`,
   `h_{s,r} = h_{s,r−1} + ((r − 1)/n)[∇f_{j_t}(x_{t+1}) − ∇f_{j_t}(x_t)] + (1/n)∇f_r(x_{t+1})` (5);
4. if `r < n`, `v_{t+1} = v_t + ∇f_{i_t}(x_{t+1}) − ∇f_{i_t}(x_t)` (6); otherwise
   `v_{t+1} = h_{s,n}` (line 19, (7)).

Every gradient is obtained by a call `oracle i x`, in the order written; nothing else touches
the gradients.

**Formalization Note.** Components are `Fin n`: the paper's component `r` is `Fin.ofNat n (r − 1)`,
the paper's `j_t ∈ {1, …, r − 1}` is passed as `j = j_t − 1 ∈ {0, …, r − 2}` (`Fin.ofNat n j`),
and `i : Fin n` is `i_t − 1`. Times are 1-based. The value of `j` is ignored when `r = 1` and the
value of `i` when `r = n` (the paper draws nothing there). The step `x_{t+1} = x_t − ηv_t` is
computed before, and independently of, the draws (p.4). -/
noncomputable def step {m : Type → Type} [Monad m] {n d : ℕ} [NeZero n]
    (oracle : Fin n → EuclideanSpace ℝ (Fin d) → m (EuclideanSpace ℝ (Fin d)))
    (η : ℝ) (t τ j : ℕ) (i : Fin n) (st : State d) : m (State d) := do
  let r := cyclePos n t
  let xout := if t = τ then st.x else st.xout
  let xnew := st.x - η • st.v
  let hnew ← if r = 1 then do
      let a ← oracle (Fin.ofNat n 0) xnew
      pure ((n : ℝ)⁻¹ • a)
    else do
      let a ← oracle (Fin.ofNat n j) xnew
      let b ← oracle (Fin.ofNat n j) st.x
      let c ← oracle (Fin.ofNat n (r - 1)) xnew
      pure (st.h + (((r - 1 : ℕ) : ℝ) / n) • (a - b) + (n : ℝ)⁻¹ • c)
  let vnew ← if r < n then do
      let a ← oracle i xnew
      let b ← oracle i st.x
      pure (st.v + (a - b))
    else pure hnew
  pure ⟨xnew, vnew, hnew, xout⟩

end PrefixVR


