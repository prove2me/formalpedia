-- Prove2me | Definitions.Def_PrefixVR_Supplement_step2
-- name    : PrefixVR_Supplement_step2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:49:54.064949+00:00
-- url     : https://prove2.me/theorems/1cd42bd6-496f-43ae-9434-f7e960593099
-- title:
--   One update of Algorithm 2 (batched prefix estimator with proximal updates)
-- statement:
--   One update of **Algorithm 2** (batched prefix estimator with proximal updates). Fix a batch size $b$, let $q=\lceil n/b\rceil$, $A_r=[\min\{rb,n\}]$, $B_r=A_r\setminus A_{r-1}$, $k_r=|A_{r-1}|$, $A_0=\emptyset$ (18). Update $t$ is written $t=sq+r$ with $1\le r\le q$. From the current point $x_t$, active estimate $v_t$, prefix accumulator $h$ and saved output, it
--   1. computes $x_{t+1}=\operatorname{prox}_{\eta g}(x_t-\eta v_t)$ (17) with one call of the proximal oracle, and saves $x_{t+1}$ as $x_{\rm out}$ if $t=\tau$;
--   2. resets $h_{s,0}=0$ when $r=1$ and sets
--   $$
--   h_{s,r}=h_{s,r-1}+\frac{k_r}{nb}\sum_{\ell=1}^b\big[\nabla f_{j_{t,\ell}}(x_{t+1})-\nabla f_{j_{t,\ell}}(x_t)\big]+\frac1n\sum_{i\in B_r}\nabla f_i(x_{t+1}),\qquad(19)
--   $$
--   with $j_{t,\ell}$ drawn uniformly from $A_{r-1}$ (the correction is omitted when $k_r=0$);
--   3. if $r<q$, sets $v_{t+1}=v_t+\frac1b\sum_{\ell=1}^b[\nabla f_{i_{t,\ell}}(x_{t+1})-\nabla f_{i_{t,\ell}}(x_t)]$ (20) with $i_{t,\ell}$ uniform on $[n]$; at $r=q$ it sets $v_{t+1}=h_{s,q}$.
--
--   The module also defines $q$ (`numBlocks n b`$=\lceil n/b\rceil$) and $|A_r|$ (`blockEnd n b r`$=\min\{rb,n\}$).
--
--   **Formalization Note** The update is generic in a monad and reaches the gradients only through an oracle `oracle i x` and the proximal map only through `proxO z`, so a logging monad counts both. Each batch sum is streamed through one running vector, and the state is the base record `PrefixVR.State d` of four vectors (current point, active estimate, accumulator, saved output); this is how "the gradient estimator uses $O(d)$ working memory" is read. Components are `Fin n`; a prefix draw $j\in A_{r-1}$ is passed as $j-1<k_r$, an active draw as `Fin n`; the new block $B_r$ is the Lean indices $k_r,\dots,\min\{rb,n\}-1$. Draws are ignored where the paper draws nothing.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §6, Eqs. (17)–(20), p.9, and Algorithm 2, lines 4–17, p.10 (PDF pp.9–10)

import Mathlib
import Definitions.Def_PrefixVR_step

namespace PrefixVR.Supplement

open PrefixVR

/-- The number of updates per cycle, `q = ⌈n/b⌉` (§6, Eq. (18), p.9). -/
noncomputable def numBlocks (n b : ℕ) : ℕ := ⌈(n : ℝ) / b⌉₊

/-- The size of the prefix `A_r = [min{rb, n}]`, i.e. `|A_r| = min{rb, n}` (§6, Eq. (18), p.9).
`blockEnd n b 0 = 0` (`A₀ = ∅`); `k_r = |A_{r−1}| = blockEnd n b (r − 1)`; the new block is
`B_r = A_r \ A_{r−1}`, the paper indices `k_r + 1, …, |A_r|`. -/
def blockEnd (n b r : ℕ) : ℕ := min (r * b) n

/-- **One update of Algorithm 2** (lines 4–17, p.10, with (17), (19), (20), pp.9–10).
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), Algorithm 2 "Batched prefix
estimator with proximal updates".

Update `t ≥ 1` with stepsize `η`, batch size `b`, output index `τ`, prefix draws
`jd ℓ` and active draws `id ℓ` (`ℓ = 1, …, b`), from the state `(x_t, v_t, h, x_out)`, with
`q = ⌈n/b⌉`, `r = t − ⌊(t − 1)/q⌋ q`, `k_r = |A_{r−1}|`:
1. `x_{t+1} = prox_{ηg}(x_t − η v_t)` (17), one call of the proximal oracle `proxO`;
2. if `t = τ`, save `x_{t+1}` as `x_out` (lines 9–10);
3. `h_{s,r−1}` is `0` if `r = 1` (line 6), else the stored accumulator; then
   `h_{s,r} = h_{s,r−1} + (k_r/(nb)) ∑_ℓ [∇f_{j_{t,ℓ}}(x_{t+1}) − ∇f_{j_{t,ℓ}}(x_t)]
   + (1/n) ∑_{i ∈ B_r} ∇f_i(x_{t+1})` (19), the prefix correction only when `k_r > 0`;
4. if `r < q`, `v_{t+1} = v_t + (1/b) ∑_ℓ [∇f_{i_{t,ℓ}}(x_{t+1}) − ∇f_{i_{t,ℓ}}(x_t)]` (20);
   otherwise `v_{t+1} = h_{s,q}` (line 16).

Every gradient is obtained by a call `oracle i x` and every proximal point by a call `proxO z`,
in the order written; nothing else touches them. Each batch sum is streamed through one running
vector (`foldlM`), so no batch of `b` vectors is stored.

**Formalization Note.** Components are `Fin n`: a prefix draw `j_{t,ℓ} ∈ A_{r−1} = [k_r]` is
passed as `jd ℓ = j_{t,ℓ} − 1 < k_r` and used as `Fin.ofNat n (jd ℓ)`; an active draw
`i_{t,ℓ} ∈ [n]` is passed as `id ℓ = i_{t,ℓ} − 1 : Fin n`; the new block `B_r` is the paper
indices `k_r + 1, …, min{rb, n}`, i.e. the Lean indices `k_r, …, min{rb, n} − 1`. The draws are
ignored where the paper draws nothing (`jd` when `k_r = 0`, `id` when `r = q`). Times are 1-based.
The proximal step is computed before, and independently of, the draws (p.9: "After choosing
`x_{t+1}`, draw …"). The state is the base record `PrefixVR.State d` of four vectors of `ℝᵈ`. -/
noncomputable def step2 {m : Type → Type} [Monad m] {n d : ℕ} [NeZero n]
    (oracle : Fin n → EuclideanSpace ℝ (Fin d) → m (EuclideanSpace ℝ (Fin d)))
    (proxO : EuclideanSpace ℝ (Fin d) → m (EuclideanSpace ℝ (Fin d)))
    (η : ℝ) (b t τ : ℕ) (jd : Fin b → ℕ) (id : Fin b → Fin n) (st : State d) :
    m (State d) := do
  let q := numBlocks n b
  let r := cyclePos q t
  let k := blockEnd n b (r - 1)
  let k' := blockEnd n b r
  let xnew ← proxO (st.x - η • st.v)
  let xout := if t = τ then xnew else st.xout
  let hprev := if r = 1 then (0 : EuclideanSpace ℝ (Fin d)) else st.h
  let pc ← if 0 < k then
      (List.finRange b).foldlM (fun (acc : EuclideanSpace ℝ (Fin d)) ℓ => do
        let a ← oracle (Fin.ofNat n (jd ℓ)) xnew
        let c ← oracle (Fin.ofNat n (jd ℓ)) st.x
        pure (acc + (a - c))) 0
    else pure 0
  let nb ← (List.range' k (k' - k)).foldlM (fun (acc : EuclideanSpace ℝ (Fin d)) i => do
      let a ← oracle (Fin.ofNat n i) xnew
      pure (acc + a)) 0
  let hnew := hprev + ((k : ℝ) / ((n : ℝ) * b)) • pc + (n : ℝ)⁻¹ • nb
  let vnew ← if r < q then do
      let s ← (List.finRange b).foldlM (fun (acc : EuclideanSpace ℝ (Fin d)) ℓ => do
        let a ← oracle (id ℓ) xnew
        let c ← oracle (id ℓ) st.x
        pure (acc + (a - c))) 0
      pure (st.v + (b : ℝ)⁻¹ • s)
    else pure hnew
  pure ⟨xnew, vnew, hnew, xout⟩

end PrefixVR.Supplement


