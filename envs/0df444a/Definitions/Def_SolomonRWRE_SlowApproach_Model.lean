-- Prove2me | Definitions.Def_SolomonRWRE_SlowApproach_Model
-- name    : SolomonRWRE_SlowApproach_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:05.153207+00:00
-- url     : https://prove2.me/theorems/c9db9d81-d414-442f-9aef-8e53788df464
-- title:
--   §0 and §2 — annealed random walk with one-way mirrors and passage times
-- statement:
--   The environment consists of i.i.d. numbers $\alpha_j\in[0,1]$, indexed by $j\in\mathbb Z$. Conditional on the environment, the walk starts at zero and uses right-step probability $\alpha_j$ at site $j$. The joint law of environment and walk is specified on every measurable environment event and finite path cylinder by averaging the corresponding fixed-environment path probability.
--
--   In the one-way-mirror example, $\alpha_j=1$ with probability $1-\gamma$ and $\alpha_j=(1+\theta)^{-1}$ with probability $\gamma$. The parameters satisfy $\theta>1$, $0<\gamma<1$, and $\gamma\theta\ge1$. The first-passage time $T_j$ may equal infinity. Starting from $V_0=0$, $V_n$ is the position of the $n$th site to the right with $\alpha_j=1$. The constants are $\nu=2\theta/(\theta-1)^2$, $K=(1-\gamma)\nu/\gamma$, and $\rho=\log_{1/\gamma}\theta$.
--
--   **Formalization Note** The paper leaves $0<\gamma<1$ implicit in its logarithm and mirror-count notation. The minimum of an empty mirror set is assigned zero; this event is null under the stated i.i.d. law. Passage times use extended natural numbers, with infinity for an unvisited site.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, pp. 1–2, 5, 10–11, §0, §1, §2

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

namespace SolomonRWRE.SlowApproach

/-- Solomon, §2, pp. 10–11. The two-value i.i.d. environment with one-way mirrors. -/
def IsMirrorEnvironment {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (γ θ : ℝ) : Prop :=
  SolomonRWRE.Recurrence.IsRWRE P α X ∧ 1 < θ ∧ 0 < γ ∧ γ < 1 ∧ 1 ≤ γ * θ ∧
  P {ω | α 0 ω = 1} = ENNReal.ofReal (1 - γ) ∧
  P {ω | α 0 ω = (1 + θ)⁻¹} = ENNReal.ofReal γ

/-- Solomon, §1, p. 5. `T_0 = 0` and `T_j = min {k > 0 : X_k = j}`, `= ∞` if no such `k`. -/
noncomputable def passage {Ω : Type*} (X : ℕ → Ω → ℤ) (j : ℕ) (ω : Ω) : ℕ∞ :=
  if j = 0 then 0 else
    sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | 0 < k ∧ X k ω = (j : ℤ)})

/-- Solomon, §2, p. 11. Position of the `n`th mirror to the right of zero. The empty-set
case is assigned zero; it has probability zero in the stated i.i.d. model. -/
noncomputable def mirrorPos {Ω : Type*} (α : ℤ → Ω → ℝ) : ℕ → Ω → ℕ
  | 0, _ => 0
  | n + 1, ω => sInf {k : ℕ | mirrorPos α n ω < k ∧ α (k : ℤ) ω = 1}

/-- Solomon, §2, p. 12. The Laplace transform of the passage-time increment between mirrors. -/
noncomputable def phi {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (n : ℕ) (u : ℝ) : ℝ :=
  ∫ ω, if passage X (mirrorPos α (n + 1) ω) ω = ⊤ ∨
      passage X (mirrorPos α n ω) ω = ⊤ then (0 : ℝ)
    else Real.exp (-u * (((passage X (mirrorPos α (n + 1) ω) ω).toNat : ℝ) -
      ((passage X (mirrorPos α n ω) ω).toNat : ℝ))) ∂P

/-- Solomon, §2, pp. 13–14. The constants in (2.9) and (2.12). -/
noncomputable def nu (θ : ℝ) : ℝ := 2 * θ / (θ - 1) ^ 2
noncomputable def K (γ θ : ℝ) : ℝ := (1 - γ) / γ * nu θ
noncomputable def rho (γ θ : ℝ) : ℝ := Real.logb (1 / γ) θ

end SolomonRWRE.SlowApproach


