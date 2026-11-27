-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_ConvergesWeaklyInD
-- name    : BauerleRiederMDP_LQ_Supplement_ConvergesWeaklyInD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:08:31.847606+00:00
-- url     : https://prove2.me/theorems/525df371-b3f7-4e69-879a-e493459efb83
-- title:
--   Weak convergence in $D[0, T]$ with the Skorohod topology to a process with continuous paths
-- statement:
--   **Weak convergence in $D[0, T]$ with the Skorohod topology to a process with continuous paths** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §3.3, p.70, PDF 84, with Definition B.1.2: the processes $X_N$ on $(\Omega , P_N)$ converge weakly to $X$ on $(\Omega ', P')$ if the laws of their paths on the space $D[0, T]$ of RCLL functions with the Skorohod $J_1$ topology converge weakly).
--
--   **Formalization Note.** Mathlib has no Skorohod space, so the definition takes the equivalent coupling form, valid because the limit has continuous paths: there are a probability space $(\Omega '', P'')$ and processes $Y_N$ (for all large $N$) and $Y$ on it, with every path of $Y_N$ RCLL on $[0, T]$ and every path of $Y$ continuous on $[0, T]$, such that $Y_N$ has the law of $X_N$ and $Y$ the law of $X$ (laws of the paths $[0, T] \to  \mathbb R $ with the product σ-algebra, which on RCLL paths is the Borel σ-algebra of $J_1$), and almost surely $\sup _{t \in  [0, T]} |Y_N(t) - Y(t)| \to  0$. Equivalence: weak convergence in the separable metrizable space $(D[0, T], J_1)$ gives a.s. $J_1$-convergent copies (Skorohod–Dudley–Wichura representation), and $J_1$-convergence to a continuous path is uniform convergence; conversely a.s. uniform convergence of RCLL copies implies a.s. $J_1$-convergence, hence weak convergence of the laws. RCLL on $[0, T]$ is right-continuity at every $t \in  [0, T)$ and a left limit at every $t \in  (0, T]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §3.3, p.70, PDF 84, with Definition B.1.2: the processes `X_N` on `(Ω, P_N)` converge weakly to `X` on `(Ω', P')` if the laws of their paths on the space `D[0, T]` of RCLL functions with the Skorohod `J_1` topology converge weakly

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace BauerleRiederMDP.LQ.Supplement

/-- **Weak convergence in `D[0, T]` with the Skorohod topology to a process with continuous paths**
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §3.3, p.70,
PDF 84, with Definition B.1.2: the processes `X_N` on `(Ω, P_N)` converge weakly to `X` on
`(Ω', P')` if the laws of their paths on the space `D[0, T]` of RCLL functions with the Skorohod
`J_1` topology converge weakly).

**Formalization Note.** Mathlib has no Skorohod space, so the definition takes the equivalent
coupling form, valid because the limit has continuous paths: there are a probability space
`(Ω'', P'')` and processes `Y_N` (for all large `N`) and `Y` on it, with every path of `Y_N` RCLL on
`[0, T]` and every path of `Y` continuous on `[0, T]`, such that `Y_N` has the law of `X_N` and `Y`
the law of `X` (laws of the paths `[0, T] → ℝ` with the product σ-algebra, which on RCLL paths is
the Borel σ-algebra of `J_1`), and almost surely `sup_{t ∈ [0, T]} |Y_N(t) − Y(t)| → 0`.
Equivalence: weak convergence in the separable metrizable space `(D[0, T], J_1)` gives a.s.
`J_1`-convergent copies (Skorohod–Dudley–Wichura representation), and `J_1`-convergence to a
continuous path is uniform convergence; conversely a.s. uniform convergence of RCLL copies implies
a.s. `J_1`-convergence, hence weak convergence of the laws. RCLL on `[0, T]` is right-continuity at
every `t ∈ [0, T)` and a left limit at every `t ∈ (0, T]`. -/
def ConvergesWeaklyInD (T : ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : ℕ → Measure Ω) (X : ℕ → Ω → ℝ → ℝ) (P' : Measure Ω') (Xlim : Ω' → ℝ → ℝ) : Prop :=
  ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'')
    (Y : ℕ → Ω'' → ℝ → ℝ) (Ylim : Ω'' → ℝ → ℝ),
    IsProbabilityMeasure P'' ∧
    (∀ N ω, (∀ t ∈ Set.Ico 0 T, ContinuousWithinAt (Y N ω) (Set.Ici t) t) ∧
      ∀ t ∈ Set.Ioc 0 T, ∃ l, Tendsto (Y N ω) (𝓝[<] t) (𝓝 l)) ∧
    (∀ ω, ContinuousOn (Ylim ω) (Set.Icc 0 T)) ∧
    (∀ᶠ N in atTop, IdentDistrib (fun ω (t : Set.Icc 0 T) => Y N ω t)
      (fun ω (t : Set.Icc 0 T) => X N ω t) P'' (P N)) ∧
    IdentDistrib (fun ω (t : Set.Icc 0 T) => Ylim ω t) (fun ω (t : Set.Icc 0 T) => Xlim ω t) P'' P' ∧
    ∀ᵐ ω ∂P'', Tendsto (fun N => ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal |Y N ω t - Ylim ω t|) atTop (𝓝 0)

end BauerleRiederMDP.LQ.Supplement


