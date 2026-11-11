-- Prove2me | Definitions.Def_OptimalLCA_Matching_Proposals
-- name    : OptimalLCA_Matching_Proposals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:00.283213+00:00
-- url     : https://prove2.me/theorems/2cd932b1-2ca2-4915-bb2c-2f8a26ab61b1
-- title:
--   §7.2 — parameters (7.2), K independent proposals per vertex, N_v and S = Σ_v min{K, N_v}
-- statement:
--   Parameters (7.2): $\delta=\varepsilon/32$, $\tau=\varepsilon/(64\Delta)$, $K=2^{\lceil\log_2(4096/\varepsilon^2)\rceil}$.
--
--   Given a proposal law $\tilde q\in Q$, each vertex $u$ makes $K$ independent proposals $(u,j)$, $j=1,\dots,K$, each landing on $v\in N(u)$ with probability $\tilde q_{uv}$ and on the dummy otherwise. $N_v$ counts the proposals received by $v$; $v$ keeps $\min\{K,N_v\}$ of them, and the kept multigraph has
--   $$S=\sum_v\min\{K,N_v\}$$
--   edges. `expectedKept G q K` is $\mathbb E S$, written as the finite sum over all outcomes $\omega:V\times[K]\to V\cup\{\perp\}$ weighted by $\prod_{(u,j)}\tilde q_{u,\omega(u,j)}$.
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 38–40, §7.1–§7.2, (7.2)

import Mathlib
import Definitions.Def_OptimalLCA_Matching_SaddlePoint

/-!
# Kept proposals (Cohen–Roghani, §7.1–§7.2)

* The parameters (7.2): `paramDelta ε = ε/32`, `paramTau Δ ε = ε/(64Δ)`,
  `paramK ε = 2^⌈log₂(4096/ε²)⌉`.
* Each vertex `u` makes `K` independent proposals `(u, j)`, `j ∈ Fin K` (the paper's
  `j = 1, …, K`), each drawn from the proposal law `q_u` on `I_u`: an outcome is
  `ω : V × Fin K → Option V` (`some v` a real proposal to `v`, `none` the dummy), of
  probability `∏_{(u,j)} propWeight G q u (ω (u, j))`.
* `incomingCount K ω v = N_v` counts the proposals received by `v`;
  `keptCount K ω = S = ∑_v min{K, N_v}`, the number of edges of the kept multigraph `H`.
* `expectedKept G q K = E S`, the expectation over the `K |V|` independent proposals
  (a finite sum).
-/

namespace OptimalLCA.Matching

open Finset

/-- `δ = ε/32` (7.2). -/
noncomputable def paramDelta (ε : ℝ) : ℝ := ε / 32

/-- `τ = ε/(64Δ)` (7.2). -/
noncomputable def paramTau (Δ : ℕ) (ε : ℝ) : ℝ := ε / (64 * (Δ : ℝ))

/-- `K = 2^⌈log₂(4096/ε²)⌉` (7.2). -/
noncomputable def paramK (ε : ℝ) : ℕ := 2 ^ ⌈Real.logb 2 (4096 / ε ^ 2)⌉₊

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The probability that a proposal of `u` drawn from `q_u` has outcome `a`
(`none` = the dummy `⊥_u`, `some v` = the neighbour `v`; non-neighbours have weight `0`). -/
noncomputable def propWeight (G : SimpleGraph V) [DecidableRel G.Adj] (q : Idx G → ℝ)
    (u : V) : Option V → ℝ
  | none => q (Sum.inl u)
  | some v => if h : G.Adj u v then q (Sum.inr ⟨(u, v), h⟩) else 0

/-- `N_v`: the number of proposals `(u, j)` with outcome `v`. -/
def incomingCount (K : ℕ) (ω : V × Fin K → Option V) (v : V) : ℕ :=
  (univ.filter (fun p : V × Fin K => ω p = some v)).card

/-- `S = ∑_v min{K, N_v}`. -/
def keptCount (K : ℕ) (ω : V × Fin K → Option V) : ℕ :=
  ∑ v, min K (incomingCount K ω v)

/-- `E S` when every proposal `(u, j)` is drawn independently from `q_u`. -/
noncomputable def expectedKept (G : SimpleGraph V) [DecidableRel G.Adj] (q : Idx G → ℝ)
    (K : ℕ) : ℝ :=
  ∑ ω : V × Fin K → Option V,
    (∏ p : V × Fin K, propWeight G q p.1 (ω p)) * (keptCount K ω : ℝ)

end OptimalLCA.Matching


