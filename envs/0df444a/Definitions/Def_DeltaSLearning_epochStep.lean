-- Prove2me | Definitions.Def_DeltaSLearning_epochStep
-- name    : DeltaSLearning_epochStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:59.826051+00:00
-- url     : https://prove2.me/theorems/f9d62a38-3b1b-487e-a812-64521b50c0b4
-- title:
--   One epoch of the $(\delta,S)$ learning algorithm
-- statement:
--   One epoch $n$ of the $(\delta,S)$ learning algorithm (Algorithm 1), with $J$ grid points, step size $\eta^n$ and confidence size $\Delta^n$, run on the demand path.
--
--   1. Choose $j^n$ by (13), the gap $\delta^n=\delta_{j^n}$, the target $S^n=\max(x^n,S^n_{j^n})$ (14), and $\bar\delta^n=\max_{j\in\mathcal A^n}\delta_j$ (15).
--   2. In the first period of the epoch order up to $S^n$; afterwards apply the $(\delta^n,S^n)$ rule of Definition 3: order up to $S^n$ when the beginning inventory is $\le S^n-\delta^n$. Inventory evolves as $x_{t+1}=(y_t-d_t)^+$ and sales are $\min(d_t,y_t)$.
--   3. The while-loop ends at the first period at which the epoch's cumulative sales exceed $\bar\delta^n$; these sales form the data $\mathcal D^n$.
--   4. The current cycle is completed: the epoch ends at the first later period that ends with inventory $\le S^n-\delta^n$.
--   5. For each active $j$, one $(\delta_j,S^n_j)$ cycle is simulated on $\mathcal D^n$, giving $G^n_j$, $L^n_j$ and $\tilde\nabla^n_j$.
--   6. SGD: $S^{n+1}_j=\mathrm{Proj}_{[\delta_j,\beta]}(S^n_j-\eta^n\tilde\nabla^n_j)$, with $\mathrm{Proj}_{[a,b]}(x)=\max\{a,\min\{x,b\}\}$.
--   7. $\hat G^n_j=\hat G^{n-1}_j+G^n_j$ and $\hat L^n_j=\hat L^{n-1}_j+L^n_j$ (16).
--   8. Pruning (17): $\mathcal A^{n+1}=\{j\in\mathcal A^n:\ \hat G^n_j/\hat L^n_j-\min_{j'\in\mathcal A^n}\hat G^n_{j'}/\hat L^n_{j'}\le\Delta^n\}$.
--
--   The pseudo costs of the epoch's periods are added to the running total.
--
--   **Formalization Note** (a) The first period of an epoch orders up to $S^n$ even if $x^n>S^n-\delta^n$, as the proof assumes ("forced to take $x^{n+1}$ instead", p.26; the term $c(S^{n+1}-S^n)$, p.19). (b) The simulation uses the realized sales, as Algorithm 1 appends "the realized sales"; the data are padded with zeros, which the simulated cycles never reach. (c) First-passage times are infima on $\mathbb N$, junk only on a null set. (d) The minimum in (17) is over $\mathcal A^n$, as in Algorithm 1.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 steps (1a)–(2c), eqs. (13)–(17), pp.13–14; Algorithm 1, p.15; Definition 3, p.9

import Mathlib
import Definitions.Def_DeltaSLearning_pseudoCost
import Definitions.Def_DeltaSLearning_cycleCost
import Definitions.Def_DeltaSLearning_cycleGrad
import Definitions.Def_DeltaSLearning_grid
import Definitions.Def_DeltaSLearning_leader

namespace DeltaSLearning

/-- One epoch `n` of the `(δ, S)` learning algorithm, with `J` grid points, step sizes `η` and
confidence sizes `Δ`, run on the demand path `d` (`d t` is the demand of period `t`, 0-based),
from the state `st` at the beginning of the epoch to the state at the beginning of epoch `n + 1`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), §3.3 steps
(1a)–(2c), eqs. (13)–(17), pp.13–14, and Algorithm 1, p.15.

1. `jⁿ := leader st` (13), `δⁿ := δ_{jⁿ}`, `Sⁿ := max(xⁿ, Sⁿ_{jⁿ})` (14),
   `δ̄ⁿ := max_{j ∈ 𝒜ⁿ} δ_j` (15).
2. Real dynamics. In the `k`-th period of the epoch (`k = 0, 1, …`, real period `st.t + k`) the
   beginning inventory is `x_k` and the after-order level `y_k`: `x_0 = xⁿ`, `y_0 = Sⁿ`;
   `x_{k+1} = (y_k - d)⁺`, and `y_{k+1} = Sⁿ` if `x_{k+1} ≤ Sⁿ - δⁿ`, else `y_{k+1} = x_{k+1}`
   (Definition 3). Sales are `s_k = min(d, y_k)`.
3. While-loop: `m` is the first `k` with `s_0 + ⋯ + s_k > δ̄ⁿ`; the epoch's data are
   `𝒟ⁿ = (s_0, …, s_m)`.
4. Cycle completion: the epoch ends after the first period `e ≥ m` with `x_{e+1} ≤ Sⁿ - δⁿ`. The
   next epoch starts at period `st.t + e + 1` with inventory `x_{e+1}`.
5. SAAP: for each `j ∈ 𝒜ⁿ`, one `(δ_j, Sⁿ_j)` cycle is simulated on the sales `𝒟ⁿ`, giving
   `Gⁿ_j`, `Lⁿ_j` and `∇̃ⁿ_j`.
6. SGD (2a): `Sⁿ⁺¹_j := Proj_{[δ_j, β]}(Sⁿ_j - ηⁿ ∇̃ⁿ_j)` for `j ∈ 𝒜ⁿ`.
7. (16): `Ĝⁿ_j := Ĝⁿ⁻¹_j + Gⁿ_j`, `L̂ⁿ_j := L̂ⁿ⁻¹_j + Lⁿ_j` for `j ∈ 𝒜ⁿ`.
8. (17): `𝒜ⁿ⁺¹ := {j ∈ 𝒜ⁿ : Ĝⁿ_j/L̂ⁿ_j - min_{j' ∈ 𝒜ⁿ} Ĝⁿ_{j'}/L̂ⁿ_{j'} ≤ Δⁿ}`.

The pseudo costs (7) of the periods `0, …, e` are added to `cost`.

**Formalization Note** (a) In the first period of an epoch the firm orders up to `Sⁿ` (so
`y_0 = Sⁿ`, order `Sⁿ - xⁿ ≥ 0`), even if `xⁿ > Sⁿ - δⁿ`: this is the paper's "forced to take
xⁿ⁺¹ instead" (p.26) and the term `c(Sⁿ⁺¹ - Sⁿ)` (p.19); afterwards the `(δⁿ, Sⁿ)` rule applies.
(b) The simulation uses the sales, as Algorithm 1 appends "the realized sales" to `𝒟ⁿ`; the
sequence is padded with zeros after `s_m`, which the simulated cycles never reach because
`s_0 + ⋯ + s_m > δ̄ⁿ ≥ δ_j`. (c) `m` and `e` are first-passage times written with `sInf` on `ℕ`;
they are junk (`0`) only on the null set where the demands stop accumulating. (d) The minimum in
(17) is over `j' ∈ 𝒜ⁿ` as in Algorithm 1, encoded as `sInf` of a finite set; on an empty active
set the junk values are irrelevant since the filter is empty. `Proj_{[a,b]}(x) = max{a, min{x, b}}`
(p.7). -/
noncomputable def epochStep (cp : Params) (J : ℕ) (η Δ : ℕ → ℝ) (n : ℕ) (d : ℕ → ℝ)
    (st : AlgState) : AlgState :=
  let j := leader st
  let δn := grid cp.β J j
  let Sn := max st.x (st.S j)
  let δbar := if h : st.A.Nonempty then st.A.sup' h (fun i => grid cp.β J i) else 0
  let xy : ℕ → ℝ × ℝ := fun k => Nat.rec (motive := fun _ => ℝ × ℝ) (st.x, Sn)
    (fun k q =>
      (max (q.2 - d (st.t + k)) 0,
        if max (q.2 - d (st.t + k)) 0 ≤ Sn - δn then Sn else max (q.2 - d (st.t + k)) 0)) k
  let sales : ℕ → ℝ := fun k => min (d (st.t + k)) (xy k).2
  let m : ℕ := sInf {k : ℕ | δbar < ∑ i ∈ Finset.range (k + 1), sales i}
  let e : ℕ := sInf {k : ℕ | m ≤ k ∧ (xy (k + 1)).1 ≤ Sn - δn}
  let data : ℕ → ℝ := fun k => if k ≤ m then sales k else 0
  let Ghat : ℕ → ℝ := fun i =>
    if i ∈ st.A then st.Ghat i + cycleCost cp (grid cp.β J i) (st.S i) data else st.Ghat i
  let Lhat : ℕ → ℝ := fun i =>
    if i ∈ st.A then st.Lhat i + (cycleLength (grid cp.β J i) data : ℝ) else st.Lhat i
  let Vhat : ℕ → ℝ := fun i => Ghat i / Lhat i
  { t := st.t + e + 1
    x := (xy (e + 1)).1
    S := fun i =>
      if i ∈ st.A then
        max (grid cp.β J i)
          (min (st.S i - η n * cycleGrad cp (grid cp.β J i) (st.S i) data) cp.β)
      else st.S i
    Ghat := Ghat
    Lhat := Lhat
    A := st.A.filter (fun i => Vhat i - sInf (Vhat '' (st.A : Set ℕ)) ≤ Δ n)
    cost := st.cost +
      ∑ k ∈ Finset.range (e + 1), pseudoCost cp (xy k).1 (xy k).2 (d (st.t + k)) }

end DeltaSLearning


