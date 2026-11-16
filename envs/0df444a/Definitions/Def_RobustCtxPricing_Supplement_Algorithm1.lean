-- Prove2me | Definitions.Def_RobustCtxPricing_Supplement_Algorithm1
-- name    : RobustCtxPricing_Supplement_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:02:57.702215+00:00
-- url     : https://prove2.me/theorems/ef9fd7f7-822c-40da-be9a-508f31ad5c29
-- title:
--   Algorithm 1 with proximity feedback, and joint corruption of the proximity and sale bits
-- statement:
--   This module defines the setting and the algorithm of §3 of Castiglioni–Stradi, in which the seller receives a second, "proximity" bit.
--
--   1. **Proximity feedback and joint corruption.** In round $t$ the true proximity bit is $x_t=\mathbb I\{|p_t-v_t|\le\epsilon\}$ and the true sale bit is $y_t=\mathbb I\{p_t\le v_t\}$, where $v_t=\langle\theta^\star,u_t\rangle$. The seller observes $X_t,Y_t\in\{0,1\}$. The feedback is *corrupted with budget $C$* if there is one set $S\subseteq[T]$ with $|S|\le C$ such that $X_t=x_t$ and $Y_t=y_t$ for every $t\notin S$; for $t\in S$ both signals are arbitrary.
--   2. **Algorithm 1.** With input the horizon $T$ and a corruption parameter $\bar C$, set $\epsilon=T^{-3}$, start from the uniform density $\mu_1$ on $\Theta$ and $2\bar C+1$ empty evidence sets $\mathcal H_1,\dots,\mathcal H_{2\bar C+1}$. In round $t$, if every $\mathcal H_j$ satisfies the prediction test (1) for $u_t$, *commit*: post the $(\bar C+1)$-st largest of the lower endpoints $\hat v_j(u_t)-\frac1{8T}$ (Algorithm 2) and keep the state. Otherwise post an $\epsilon$-window median $m_t$ of $\mu_t$ in direction $u_t$ and read $X_t$: if $X_t=1$, append $(u_t,m_t)$ to one evidence set that does not satisfy (1) and keep the density; if $X_t=0$, keep the evidence sets and replace $\mu_t$ by Update-Density (Algorithm 3) with the sale feedback $Y_t$.
--
--   Algorithm 1 is a run relation on the published `Run` structure: a trajectory of densities, evidence sets and prices is a run when it starts in the initial state and every round follows one of the two branches. Every tie-break is admitted (any solution of (3), any non-predicting receiving set, any coefficients satisfying (1)). In Theorem 3.8 the parameter is $\bar C=C$.
--
--   **Formalization Note** The corruption constraint is evaluated on the run's own posted prices, as in the published `IsCorrupted`. The page writes only "$X_t=x_t$ for every $t\notin S$" and then "for $t\in S$, the corrupted signals $X_t,Y_t$ may be chosen arbitrarily"; that $Y_t=y_t$ off $S$ is the protocol of §2.2, kept in §3.
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §3, pp.11–12 (proximity feedback x_t, corrupted set S), Algorithm 1, p.12; Commit (Algorithm 2) p.13, (1) p.13, (2)–(3) p.14, Update-Density (Algorithm 3) p.15

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Density
import Definitions.Def_RobustCtxPricing_Algorithm4

namespace RobustCtxPricing.Supplement

/-- **Joint corruption of the sale and proximity feedback (§3).** Castiglioni–Stradi, *Decoupling
Corruption and Horizon in Robust Contextual Pricing*, arXiv:2607.11210, §3, p.12: the seller also
observes a proximity bit, whose true value is `x_t = 𝕀{|p_t − v_t| ≤ ϵ}`; "There is a set of
corrupted rounds `S ⊆ [T]` with `|S| ≤ C` such that: `X_t = x_t` for every `t ∉ S`, while for
`t ∈ S`, the corrupted signals `X_t, Y_t` may be chosen arbitrarily."

`IsCorruptedXY T C ϵ θ u p X Y` says that there is one set `S` of at most `C` of the rounds
`0, …, T−1` outside of which both the observed proximity bit `X_t` equals
`𝕀{|p_t − ⟨θ, u_t⟩| ≤ ϵ}` and the observed sale bit `Y_t` equals `𝕀{p_t ≤ ⟨θ, u_t⟩}`.

**Formalization Note.** The page states the condition off `S` for `X_t` only; that `Y_t = y_t`
off `S` as well is the protocol of §2.2, which §3 keeps ("in addition to the feedback `Y_t`"), and
the sentence "for `t ∈ S`, the corrupted signals `X_t, Y_t` may be chosen arbitrarily" makes `S`
the set of rounds where either may be corrupted. Bits are `Bool`; the constraint is evaluated on
the run's own prices `p` (as `RobustCtxPricing.IsCorrupted` does for `Y` alone). -/
def IsCorruptedXY {d : ℕ} (T C : ℕ) (ϵ : ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (p : ℕ → ℝ) (X Y : ℕ → Bool) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.range T ∧ S.card ≤ C ∧
    ∀ t < T, t ∉ S →
      X t = decide (|p t - inner ℝ θ (u t)| ≤ ϵ) ∧ Y t = decide (p t ≤ inner ℝ θ (u t))

/-- **Algorithm 1 (Robust Contextual Pricing with Proximity Feedback), as a relation on runs.**
Castiglioni–Stradi, arXiv:2607.11210, §3, Algorithm 1, p.12, with Commit (Algorithm 2, p.13), the
prediction test (1) (p.13), the interval (2) (p.14), the ϵ-window median (3) (p.14) and
Update-Density (Algorithm 3, p.15):

```
Require: Horizon T, Corruption parameter C̄
1: Set ϵ = T⁻³
2: Initialize µ₁ as the uniform density over Θ
3: Initialize 2C̄ + 1 empty evidence sets 𝓗₁, …, 𝓗_{2C̄+1} ← ∅
4: for t = 1, …, T do
5:   Observe context u_t
6:   if every 𝓗_j satisfies Equation (1) for u_t then        ▷ Commit Check
7:     Commit()
8:     Continue
9:   end if
10:  Let m_t be the ϵ-window median of µ_t in direction u_t, as in Equation (3)
11:  Post price p_t = m_t
12:  Observe sale feedback Y_t and proximity feedback X_t        ▷ Query
13:  if X_t = 1 then                                             ▷ Evidence Collection
14:    Insert (u_t, m_t) into a set 𝓗_j that does not satisfy Equation (1)
15:    Set µ_{t+1} = µ_t
16:  else                                                        ▷ Density Update
17:    Update-Density()
18:  end if
19: end for
```

`IsAlg1Run T Cb u X Y r` says that `r` (the published `Run` structure with `2·Cb + 1` evidence
sets) is a run of Algorithm 1 with horizon `T` and corruption parameter `C̄ = Cb` on the contexts
`u` and the observed feedback `X` (proximity) and `Y` (sale): the initial density is uniform, the
`2C̄ + 1` evidence sets start empty, and in every round `t < T`

* **commit** (every `𝓗_j` predicts `u_t`): for coefficients `λ^j` satisfying (1) for each `j`, the
  posted price is the `(C̄ + 1)`-st largest lower endpoint `v̂_j(u_t) − 1/(8T)` and the state is
  unchanged (Algorithm 2);
* **explore** (some `𝓗_j` does not predict `u_t`): the posted price is an ϵ-window median of the
  current density in direction `u_t`; if `X_t = 1` the sample `(u_t, p_t)` is appended to one
  evidence set that does not predict `u_t` and the density is kept; if `X_t = 0` the evidence sets
  are kept and the density is replaced by Update-Density with feedback `Y_t`.

**Formalization Note.** `ϵ = T⁻³` is the published `epsT T`. The paper fixes no tie-breaking
rule; the relation admits every choice: any solution of (3) as the median, any evidence set not
satisfying (1) as the receiving set, and any coefficients satisfying (1) in the commit. The
feedback is read only in exploration rounds. Rounds are `0, …, T−1`. In §3 (Theorem 3.8) the
parameter is `C̄ = C` ("In this section, `C̄ = C`", p.12). -/
def IsAlg1Run {d : ℕ} (T Cb : ℕ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (X Y : ℕ → Bool)
    (r : Run d (2 * Cb + 1)) : Prop :=
  r.μ 0 = uniformDensity d ∧ (∀ j, r.H 0 j = []) ∧
  ∀ t < T,
    ((∀ j, Predicts (epsT T) T (r.H t j) (u t)) ∧
      ∃ lam : ∀ j, Fin (r.H t j).length → ℝ,
        (∀ j, PredictsWith (epsT T) T (r.H t j) (u t) (lam j)) ∧
        r.p t = commitPrice T Cb (r.H t) lam ∧
        r.μ (t + 1) = r.μ t ∧ r.H (t + 1) = r.H t) ∨
    ((¬ ∀ j, Predicts (epsT T) T (r.H t j) (u t)) ∧
      IsWindowMedian (epsT T) (r.μ t) (u t) (r.p t) ∧
      ((X t = true ∧
          (∃ j, ¬ Predicts (epsT T) T (r.H t j) (u t) ∧
            r.H (t + 1) = Function.update (r.H t) j (r.H t j ++ [(u t, r.p t)])) ∧
          r.μ (t + 1) = r.μ t) ∨
        (X t = false ∧ r.H (t + 1) = r.H t ∧
          r.μ (t + 1) = updateDensity (epsT T) (r.μ t) (u t) (r.p t) (Y t))))

end RobustCtxPricing.Supplement


