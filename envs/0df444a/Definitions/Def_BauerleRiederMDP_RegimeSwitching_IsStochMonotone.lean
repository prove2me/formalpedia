-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsStochMonotone
-- name    : BauerleRiederMDP_RegimeSwitching_IsStochMonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:57.831516+00:00
-- url     : https://prove2.me/theorems/2d5bdc75-da3e-4c2b-8974-8aa6014c8dd6
-- title:
--   Stochastically monotone finite Markov chain (Definition B.3.13)
-- statement:
--   Let $(Y_n)$ be a Markov chain on a finite ordered state space $E_Y$ with transition probabilities $p_{jk}$. The chain is **stochastically monotone** if for every increasing $v:E_Y\to\mathbb R$ the function
--
--   $$
--   j\;\mapsto\;\sum_{k\in E_Y}p_{jk}\,v(k)
--   $$
--
--   is increasing. On $E_Y=\{1,\dots,m\}$ this is the tail-sum criterion $\sum_{\nu\ge k}p_{i\nu}\le\sum_{\nu\ge k}p_{j\nu}$ for $i\le j$: a better environment today makes better environments tomorrow more likely.
--
--   **Formalization Note** On a finite state space every integral exists, so the book's qualifier "whenever the integral exists" is void.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition B.3.13, p.363 (PDF p.369)

import Mathlib

namespace BauerleRiederMDP.RegimeSwitching

/-- A Markov chain on a finite ordered state space `E_Y` with transition probabilities
`p = (p_{jk})` is **stochastically monotone** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition B.3.13, p.363, PDF p.369): for
every increasing `v : E_Y → ℝ` the function `j ↦ ∫ v(k) Q(dk | j) = ∑_k p_{jk} v(k)` is
increasing. (On `E_Y = {1, …, m}` this is the tail-sum criterion `∑_{ν ≥ k} p_{iν} ≤
∑_{ν ≥ k} p_{jν}` for `i ≤ j`, p.363.)

**Formalization Note.** On a finite state space every integral `∫ v dQ(·|j)` exists, so the
book's qualifier "whenever the integral exists" is void. -/
def IsStochMonotone {EY : Type*} [Fintype EY] [Preorder EY] (p : EY → EY → ℝ) : Prop :=
  ∀ v : EY → ℝ, Monotone v → Monotone (fun j => ∑ k, p j k * v k)

end BauerleRiederMDP.RegimeSwitching


