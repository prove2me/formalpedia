-- Prove2me | Definitions.Def_BayesRouting_VOI_Pairwise
-- name    : BayesRouting_VOI_Pairwise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T14:47:25.96893+00:00
-- url     : https://prove2.me/theorems/be68e68b-56f8-42da-9a90-9ea0255f67cf
-- title:
--   Pairwise comparison: direction $z^{ij}$, problem (OPT-$\mathcal F^{ij}$), thresholds $\underline\lambda^i,\overline\lambda^i$ and relative value of information $V^{ij*}$
-- statement:
--   Fix two populations $i\ne j$. The **direction** $z^{ij}\in\mathbb R^{\mathcal I}$ has $1$ in position $i$, $-1$ in position $j$ and $0$ elsewhere. For a size vector $\lambda$, the total size of the remaining populations is $|\lambda^{-ij}|=\sum_{k\in\mathcal I\setminus\{i,j\}}\lambda^k$.
--
--   Problem (OPT-$\mathcal F^{ij}$) minimizes $\widehat\Phi(f)$ subject to (14a)–(14c), (IIC$_k$) $\widehat J^k(f)\le\lambda^kD$ for every $k\notin\{i,j\}$, and
--
--   $$\widehat J^i(f)+\widehat J^j(f)\le(1-|\lambda^{-ij}|)D.\qquad(\mathrm{IIC}_{ij})$$
--
--   Its set of optimal solutions is $\mathcal F^{ij,\dagger}$. The **thresholds** are
--
--   $$\underline\lambda^i=\frac1D\min_{f\in\mathcal F^{ij,\dagger}}\widehat J^i(f),\qquad \overline\lambda^i=\frac1D\max_{f\in\mathcal F^{ij,\dagger}}\big((1-|\lambda^{-ij}|)D-\widehat J^j(f)\big).$$
--
--   They split the admissible range $\lambda^i\in(0,1-|\lambda^{-ij}|)$ into the regimes $\Lambda^{ij}_1$ ($\lambda^i<\underline\lambda^i$), $\Lambda^{ij}_2$ ($\underline\lambda^i\le\lambda^i\le\overline\lambda^i$) and $\Lambda^{ij}_3$ ($\lambda^i>\overline\lambda^i$).
--
--   The **relative value of information** of population $i$ over population $j$ at a strategy profile $q$ is
--
--   $$V^{ij}(q)=C^{j}(q)-C^{i}(q);$$
--
--   at a BWE of $\Gamma(\lambda)$ it is the paper's $V^{ij*}(\lambda)=C^{j*}(\lambda)-C^{i*}(\lambda)$, the expected cost saving of a traveler of population $i$ over one of population $j$.
--
--   **Formalization Note** Everything here depends on $\lambda$ only through $\lambda^{-ij}$, so the thresholds are unchanged along $z^{ij}$. The minimum and maximum are `sInf`/`sSup` of images of $\mathcal F^{ij,\dagger}$; that set is nonempty (every $t$-independent flow with $\sum_rf_r=D$ is feasible) and compact, and $\widehat J$ is continuous, so they are attained. On an empty set Lean would return the junk value $0$; this never occurs for size vectors in the simplex. $V^{ij}$ is defined at a profile $q$ and every theorem evaluates it at an arbitrary BWE.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, pp. 156-157, §5.1 (z^{ij}, |lambda^{-ij}|, (OPT-F^{ij}), (IIC_{ij}), eqs. (23)-(24c)) and §5.2 (V^{ij*})

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows

open Finset

namespace BayesRouting.VOI

variable {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
  [∀ i, DecidableEq (T i)] {S E R : Type} [Fintype S] [Fintype E] [DecidableEq E] [Fintype R]

/-- The direction `z^{ij}` (p. 156): `1` in the `i`-th entry, `-1` in the `j`-th entry. -/
noncomputable def dir (i j : I) : I → ℝ :=
  Pi.single i 1 - Pi.single j 1

/-- `|λ^{-ij}| = ∑_{k ∈ 𝓘 ∖ {i, j}} λ^k`, the total size of the remaining populations (p. 156). -/
def restSize (lam : I → ℝ) (i j : I) : ℝ :=
  ∑ k ∈ (univ.erase i).erase j, lam k

/-- The feasible set of (OPT-ℱ^{ij}) (p. 156): (14a)–(14c), (IIC_k) for every `k ∉ {i, j}`, and
(IIC_{ij}) `Ĵ^i(f) + Ĵ^j(f) ≤ (1 - |λ^{-ij}|) D`. It depends on `λ` only through `λ^{-ij}`. -/
def pairFeasible [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ)
    (i j : I) : Set (R → ((k : I) → T k) → ℝ) :=
  flowBase G ∩
    {f | (∀ k, k ≠ i → k ≠ j → impact G k f ≤ lam k * G.D) ∧
      impact G i f + impact G j f ≤ (1 - restSize lam i j) * G.D}

/-- `ℱ^{ij,†}`, the optimal solution set of (OPT-ℱ^{ij}) (p. 156). -/
def pairOptimal [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R) (lam : I → ℝ)
    (i j : I) : Set (R → ((k : I) → T k) → ℝ) :=
  flowArgmin G (pairFeasible G lam i j)

/-- The lower threshold `λ̲^i = (1/D) min_{f ∈ ℱ^{ij,†}} Ĵ^i(f)` of (23) (p. 156). The set
`ℱ^{ij,†}` is nonempty and compact and `Ĵ^i` is continuous, so the `sInf` is the minimum. -/
noncomputable def lowThr [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R)
    (lam : I → ℝ) (i j : I) : ℝ :=
  (1 / G.D) * sInf (impact G i '' pairOptimal G lam i j)

/-- The upper threshold `λ̄^i = (1/D) max_{f ∈ ℱ^{ij,†}} ((1 - |λ^{-ij}|) D - Ĵ^j(f))` of (23)
(p. 156). The `sSup` is the maximum for the same reason as in `lowThr`. -/
noncomputable def highThr [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R)
    (lam : I → ℝ) (i j : I) : ℝ :=
  (1 / G.D) * sSup ((fun f => (1 - restSize lam i j) * G.D - impact G j f) ''
    pairOptimal G lam i j)

/-- The relative value of information `V^{ij*} = C^{j*} - C^{i*}` (p. 157), evaluated at a
strategy profile `q` (the theorems evaluate it at a BWE). -/
noncomputable def relValue [∀ i, Nonempty (T i)] [Nonempty R] (G : Game I T S E R)
    (q : (i : I) → T i → R → ℝ) (i j : I) : ℝ :=
  popCost G q j - popCost G q i

end BayesRouting.VOI


