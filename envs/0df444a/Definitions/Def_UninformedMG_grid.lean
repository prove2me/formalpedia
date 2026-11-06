-- Prove2me | Definitions.Def_UninformedMG_grid
-- name    : UninformedMG_grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:15.146626+00:00
-- url     : https://prove2.me/theorems/d2d7e209-96c0-4583-b681-dc48b2b0d2bd
-- title:
--   The candidate grid $\mathcal V$ of Eq. (19)
-- statement:
--   For $H\ge2$ and $K\ge1$, the **candidate grid** is
--   $$\mathcal V=\Big\{v\in[0,1]^S:\ v_1(s)=0\ \ \forall s\in S_1,\quad v_h(s)\in\Big\{0,\tfrac1{HK},\dots,\tfrac{H-h+1}{H}\Big\}\ \ \forall h=2,\dots,H,\ s\in S_h\Big\},$$
--   with $v_{H+1}(s_{H+1})=0$ for every $v\in\mathcal V$. Its size is $N=|\mathcal V|=\prod_{h=2}^H\big(K(H-h+1)+1\big)^{|S_h|}$.
--
--   This is the class on which Algorithm 1 runs. $N$ enters the constant $C_\delta$ of Theorem 2.1.
--
--   **Formalization Note** A grid point is a numerator table $n_h(s)\in\{0,\dots,K(H-h+1)\}$ with $v_h(s)=n_h(s)/(HK)$. In 0-based Lean layers $h$ the numerator bound is $K(H-h)$ for $1\le h\le H-1$ and $0$ at the first and terminal layers.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Eq. (19), p.10 (PDF p.12), and the sentence after it, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_UninformedMG_CandClass

namespace UninformedMG

variable {H : ℕ}

/-- Largest grid numerator at Lean layer `h`: `0` at the first layer (paper step 1) and
`K (H − h)` otherwise, so that the largest grid value `K(H − h)/(HK) = (H − h)/H` is the paper's
`(H − h' + 1)/H` at paper step `h' = h + 1`. At the terminal layer `h = H` it is `0`. -/
def gridBound (H K : ℕ) (h : Fin (H + 1)) : ℕ :=
  if h.val = 0 then 0 else K * (H - h.val)

/-- A grid point: a numerator table `n_h(s) ∈ {0, 1, …, gridBound H K h}` on every layer. -/
abbrev GridPt (G : Game H) (K : ℕ) := (h : Fin (H + 1)) → G.St h → Fin (gridBound H K h + 1)

/-- The value `v_h(s) = n_h(s) / (HK)` of a grid point. -/
noncomputable def gridVal (G : Game H) (K : ℕ) (n : GridPt G K) (h : Fin (H + 1))
    (s : G.St h) : ℝ :=
  ((n h s : ℕ) : ℝ) / ((H : ℝ) * K)

/-- **The candidate grid** (Eq. (19), p.10 = PDF p.12):
`V = {v ∈ [0,1]^S : v_1(s) = 0 ∀ s ∈ S_1, v_h(s) ∈ {0, 1/(HK), …, (H − h + 1)/H} ∀ h = 2, …, H,
s ∈ S_h}`, with `v_{H+1}(S_{H+1}) = 0` for every `v ∈ V` (p.11).

**Formalization Note.** A grid point is its numerator table `n` with `v = n/(HK)`; the map
`n ↦ v` is injective for `H, K ≥ 1`, so `N = |V|` is `Fintype.card (GridPt G K)`. Lean layer
`h` is paper step `h + 1`: layer `0` is forced to `0`, layers `1, …, H − 1` range over
`{0, …, K(H − h)}/(HK)`, and the terminal layer `H` is forced to `0`. -/
noncomputable def grid (G : Game H) (K : ℕ) : CandClass G where
  C := GridPt G K
  val := gridVal G K

end UninformedMG


