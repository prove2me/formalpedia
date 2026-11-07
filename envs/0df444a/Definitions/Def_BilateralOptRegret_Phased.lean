-- Prove2me | Definitions.Def_BilateralOptRegret_Phased
-- name    : BilateralOptRegret_Phased
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:16.962048+00:00
-- url     : https://prove2.me/theorems/5359ea3b-3285-4c8f-a672-4878a5c81a48
-- title:
--   (5) and Algorithm 1 — the parameters and phased successive elimination
-- statement:
--   For a horizon $T\ge 2$, the parameters (5) are
--   $$K=2^{\lceil\log_2(T^{1/3})\rceil}+1,\quad H=1+\lceil\log_8T\rceil,\quad\delta=\frac{T^{-3}}{H},\quad\varepsilon_\star=4\sqrt{A(K,\delta)}\,T^{-1/3}.$$
--   **Algorithm 1** works as follows. If $\varepsilon_\star\ge 1/8$, it plays $x=(1,0)$ in all rounds. Otherwise let $m=\lfloor\log_8(1/\varepsilon_\star)\rfloor$, $G_0=\mathcal X_K$, $\hat F_0\equiv 0$, $\varepsilon_0=1$; for $i=0,\dots,m-1$ it runs Refine$(G_i,\hat F_i,\varepsilon_i,\delta)$, takes the output as $(G_{i+1},\hat F_{i+1})$, and sets $\varepsilon_{i+1}=\varepsilon_i/8$. It then commits to some $x^\star\in\arg\max_{x\in G_m}(1-x_1-x_2)\hat F_m(x)$ for all remaining rounds.
--
--   This is the outer algorithm of the paper; the main theorem instantiates Refine with Algorithm 3.
--
--   **Formalization Note** The output of the program is the action to commit to. Refine and $A$ are parameters, as Theorem 4.2 needs. $\log_2$ and $\log_8$ are the paper's explicit bases. The choice of $x^\star$ is a selection rule. For $T\ge2$ one has $K\ge3$.
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), (5), p.15; Algorithm 1, p.16

import Mathlib
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program
import Definitions.Def_BilateralOptRegret_Oracle

namespace BilateralOptRegret

open BilateralProfit

/-! # The parameters (5) and Algorithm 1, phased successive elimination

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), display (5), p.15, and Algorithm 1, p.16.

**Formalization Note.** `K = 2^⌈log₂(T^{1/3})⌉ + 1` is `Kof (nOf T)`, and `nOf T ≥ 1` for `T ≥ 2`. The
logarithms here are the paper's explicit `log₂` and `log₈`. The program takes `Refine` and `A` as
parameters. The first branch (`ε⋆ ≥ 1/8`) outputs `x = (1, 0)`, which `policyOf` plays for all rounds.
The choice of `x⋆ ∈ argmax` is a selection rule `pick`; on an empty `G_m` the value `pick ∅` is arbitrary
(the paper shows `G_m` is never empty when `Refine` is Algorithm 3). -/

/-- `n` with `K = 2^n + 1` in (5): `n = ⌈log₂(T^{1/3})⌉`. -/
noncomputable def nOf (T : ℕ) : ℕ := ⌈Real.logb 2 ((T : ℝ) ^ ((1 : ℝ) / 3))⌉₊

/-- `H = 1 + ⌈log₈ T⌉` in (5). -/
noncomputable def HOf (T : ℕ) : ℕ := 1 + ⌈Real.logb 8 (T : ℝ)⌉₊

/-- `δ = T⁻³/H` in (5). -/
noncomputable def deltaOf (T : ℕ) : ℝ := (T : ℝ) ^ (-3 : ℤ) / (HOf T : ℝ)

/-- `ε⋆ = 4 √(A(K, δ)) T^{−1/3}` in (5). -/
noncomputable def epsStar (A : ℕ → ℝ → ℝ) (T : ℕ) : ℝ :=
  4 * Real.sqrt (A (Kof (nOf T)) (deltaOf T)) * (T : ℝ) ^ (-(1 : ℝ) / 3)

/-- `m = ⌊log₈(1/ε⋆)⌋` (Algorithm 1, line 6). -/
noncomputable def mOf (A : ℕ → ℝ → ℝ) (T : ℕ) : ℕ := ⌊Real.logb 8 (1 / epsStar A T)⌋₊

/-- `ε_m = 8^{−m}`, the precision after the `m` phases of Algorithm 1 (`ε₀ = 1`, `ε_{i+1} = ε_i/8`). -/
noncomputable def epsM (A : ℕ → ℝ → ℝ) (T : ℕ) : ℝ := (1 / 8 : ℝ) ^ mOf A T

/-- The loop of Algorithm 1, lines 8–13: `m` calls to `Refine` at precisions `ε, ε/8, ε/64, …`, each
call on the set and estimates returned by the previous one. -/
noncomputable def refineLoop {n : ℕ} (Refine : RefineProc n) (δ : ℝ) :
    ℕ → Finset (Act n) → (Act n → ℝ) → ℝ → QTree (Act n) (Finset (Act n) × (Act n → ℝ))
  | 0, G, Fhat, _ => .done (G, Fhat)
  | m + 1, G, Fhat, ε => qBind (Refine G Fhat ε δ) fun o => refineLoop Refine δ m o.1 o.2 (ε / 8)

/-- The set `arg max_{x ∈ G} (1 − x₁ − x₂) F̂(x)` of Algorithm 1, line 14. -/
noncomputable def argmaxSet {K : ℕ} (G : Finset (Grid K)) (Fhat : Grid K → ℝ) : Finset (Grid K) := by
  classical
  exact G.filter fun q => ∀ q' ∈ G, rhat Fhat q' ≤ rhat Fhat q

/-- **Algorithm 1, p.16.** Its output is the action to commit to: `(1, 0)` if `ε⋆ ≥ 1/8`, otherwise
`x⋆` after `m` refinement phases started from `G₀ = X_K`, `F̂₀ ≡ 0`, `ε₀ = 1`. -/
noncomputable def phasedTree (A : ℕ → ℝ → ℝ) (T : ℕ) (Refine : RefineProc (nOf T))
    (pick : Finset (Act (nOf T)) → Act (nOf T)) : QTree (Act (nOf T)) (Act (nOf T)) :=
  if 1 / 8 ≤ epsStar A T then
    .done (Fin.last _, 0)
  else
    qBind (refineLoop Refine (deltaOf T) (mOf A T) Finset.univ (fun _ => 0) 1) fun o =>
      .done (pick (argmaxSet o.1 o.2))

/-- Algorithm 1 as a policy on trade bits. -/
noncomputable def phasedPolicy (A : ℕ → ℝ → ℝ) (T : ℕ) (Refine : RefineProc (nOf T))
    (pick : Finset (Act (nOf T)) → Act (nOf T)) : List Bool → ℝ × ℝ :=
  policyOf (Kof (nOf T)) (phasedTree A T Refine pick)

end BilateralOptRegret


