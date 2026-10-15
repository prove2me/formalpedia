-- Prove2me | Definitions.Def_OAI_Probability_Ising_GibbsMeasure
-- name    : OAI_Probability_Ising_GibbsMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:04:49.061895+00:00
-- url     : https://prove2.me/theorems/89449631-0a60-49d6-b41b-679469529d89
-- title:
--   Ising Gibbs measure with a coupling matrix: Hamiltonian, partition function, averages and magnetizations
-- statement:
--   Let $V$ be a finite set, $J=(J_{uv})_{u,v\in V}$ a real array of pair couplings and $h\in\mathbb{R}^V$ an external field. Configurations are $\sigma\in\{-1,+1\}^V$, where the sign map $\operatorname{sgn}$ identifies the two Boolean values with $+1$ and $-1$. The file defines:
--
--   1. **Hamiltonian.**
--
--      $$\mathcal H_{J,h}(\sigma)=\sum_{u\in V}\sum_{v\in V}J_{uv}\,\sigma_u\sigma_v+\sum_{u\in V}h_u\,\sigma_u ,$$
--
--      in which both orientations $(u,v)$ and $(v,u)$ of a pair are summed and the diagonal terms $J_{uu}\sigma_u^2=J_{uu}$ are constants.
--
--   2. **Mass** $\mu_{J,h}(\sigma)=e^{\mathcal H_{J,h}(\sigma)}$ and **partition function** $Z_{J,h}=\sum_\sigma\mu_{J,h}(\sigma)$.
--
--   3. **Average** of $f:\{-1,+1\}^V\to\mathbb{R}$: $\langle f\rangle_{J,h}=Z_{J,h}^{-1}\sum_\sigma\mu_{J,h}(\sigma)\,f(\sigma)$.
--
--   4. **Magnetization** at $v\in V$: $m_v(J,h)=\langle\sigma_v\rangle_{J,h}$.
--
--   No symmetry or sign condition is imposed on $J$ by the definitions; the ferromagnetic case $J_{uv}\ge0$ is assumed in the results that need it. The matrix presentation is convenient for removing a single site: restricting $J$ to the remaining sites and adding the induced fields gives a model of the same form, without re-enumerating edges. An edge-list graph is put into this form through its oriented coupling matrix.
--
--   **Formalization Note** These definitions live in the namespace `OAI.BufferedIsing.DSS` as `sgn`, `hamiltonian`, `mass`, `part`, `average` and `mean`, for a `Fintype` vertex type; `sgn` duplicates the base `spin`. The partition function is always positive, so the division in `average` is genuine.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/GibbsMeasure.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/GibbsMeasure.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

/-- Directed pair couplings. Both directions are counted; diagonal terms are constants.
This intermediate presentation allows exact restriction without re-enumerating edges. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

def hamiltonian (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) : ℝ :=
  (∑ u, ∑ v, J u v * sgn (σ u) * sgn (σ v)) + ∑ u, h u * sgn (σ u)

def mass (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) : ℝ :=
  Real.exp (hamiltonian J h σ)

def part (J : V → V → ℝ) (h : V → ℝ) : ℝ := ∑ σ, mass J h σ

def average (J : V → V → ℝ) (h : V → ℝ) (f : (V → Bool) → ℝ) : ℝ :=
  (∑ σ, mass J h σ * f σ) / part J h

def mean (J : V → V → ℝ) (h : V → ℝ) (v : V) : ℝ :=
  average J h (fun σ => sgn (σ v))

end

end BufferedIsing.DSS

end OAI


