-- Prove2me | Definitions.Def_MinorFreeSTC_Main_CopConstant
-- name    : MinorFreeSTC_Main_CopConstant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:19:56.311194+00:00
-- url     : https://prove2.me/theorems/480f72e0-bd7c-4e28-8819-e945b3b1333f
-- title:
--   “c₀ is the constant of Corollary 1”: the statement of Corollary 1 with a given c₀ (existence and polynomial-time high-probability construction)
-- statement:
--   Lemma 12 and Theorem 9 refer to "the universal constant $c_0\ge1$ from Corollary 1". For a real $c_0$, **$\mathrm{CopConstant}(c_0)$** is the statement of Corollary 1 with this constant:
--
--   **(E)** for every $\Delta>0$, every finite connected $K_r$-minor-free weighted graph $G$ (weights in $[1,n^k]$) and every partition $\mathcal P$ of $V$ into parts of strong diameter at most $\delta$ with
--   $$\delta\cdot c_0\, r\log n\le\Delta,$$
--   $G$ has a $\mathcal P$-tiled $\Delta$-radius $\Delta/(2r)$-buffered $(r-1)$-width cop decomposition; and
--
--   **(A)** for every $c>1$ there is one admissible oracle-free program such that for all $r,k$ there are $C,K$ with: on every such input $(G,\Delta,r,\mathcal P)$ in the input layout, every run halts within $Cn^K+C$ steps and outputs such a decomposition except on a set of coin tapes of measure at most $n^{-c}$.
--
--   Corollary 1 is the assertion that some $c_0\ge1$ satisfies $\mathrm{CopConstant}(c_0)$; Lemma 12 and Theorem 9 hold for every such $c_0$.
--
--   **Formalization Note.** $\delta\le\Delta/(c_0r\log n)$ is written multiplied out, so that $\log 1=0$ needs no division.
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 22, Corollary 1; pp. 29–30 (Lemma 12 and Theorem 9 cite its c₀)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Structures
import Definitions.Def_MinorFreeSTC_Main_Machine

set_option autoImplicit false

namespace MinorFreeSTC.Main

open ARTreeCover

/-!
# "`c₀` is the constant of Corollary 1"

Filtser, Fletcher, Hershkowitz, Milenković, *(1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free
Graphs with Size O(log log n)*, STOC 2027 submission (manuscript sha256 f475e254…), Corollary 1
(p. 22, PDF 24). Lemma 12 (p. 29) and Theorem 9 (p. 29) use "the universal constant `c₀ ≥ 1`
from Corollary 1"; `CopConstant c₀` says that `c₀` is such a constant, i.e. that the statement of
Corollary 1 holds with this `c₀`, both its existence clause and its algorithmic clause.
-/

/-- The statement of Corollary 1 with the constant `c₀`. **(E)** For every `∆ > 0`, every finite
connected `K_r`-minor-free weighted graph `G` (with `w(e) ∈ [1, n^k]`) and every partition `P` of
`V` into parts of strong diameter at most `δ`, where `δ · c₀ · r · log n ≤ ∆` (the paper's
`δ ≤ ∆/(c₀ · r · log n)`), `G` has a `P`-tiled `∆`-radius `∆/(2r)`-buffered `(r − 1)`-width cop
decomposition. **(A)** For every `c > 1` one program, given `G`, `∆`, `r` and `P` (as a vertex
labelling), runs in at most `C n^K + C` steps on every coin tape and outputs such a decomposition
except on a set of coin tapes of measure at most `n^{−c}`; `C, K` depend only on `r`, `k`, `c`. -/
def CopConstant (c₀ : ℝ) : Prop :=
  (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ) (Δ δ : ℝ)
      (P : Finset (Finset V)),
      Connected G → MinorFree G r → AspectBounded G k → 0 < Δ → IsTiling G P δ →
      δ * (c₀ * r * Real.logb 2 (Fintype.card V)) ≤ Δ →
      ∃ D : CopData G, IsCopDecomposition G D Δ (Δ / (2 * r)) (r - 1) ∧ IsTiledBy D P) ∧
  (∀ c : ℝ, 1 < c → ∃ A : Program, Admissible A ∧ NoOracle A ∧
    ∀ r k : ℕ, ∃ C K : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V)
      (Δ δ : ℝ) (P : Finset (Finset V)) (L : V → ℝ) (E : Encoding G),
      Connected G → MinorFree G r → AspectBounded G k → 0 < Δ → IsTiling G P δ →
      δ * (c₀ * r * Real.logb 2 (Fintype.card V)) ≤ Δ → labelPartition L = P →
      ComputesWHP A noOracle (E.cells ++ [Δ, (r : ℝ)] ++ E.labelCells L)
        (CopOut E fun D => IsCopDecomposition G D Δ (Δ / (2 * r)) (r - 1) ∧ IsTiledBy D P)
        (C * (Fintype.card V : ℝ) ^ K + C) ((Fintype.card V : ℝ) ^ (-c)))

end MinorFreeSTC.Main


