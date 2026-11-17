-- Prove2me | Definitions.Def_LowTempGlauber_Supplement_Ising
-- name    : LowTempGlauber_Supplement_Ising
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:27:27.672595+00:00
-- url     : https://prove2.me/theorems/e9324700-77bc-455c-8256-1a689a225b22
-- title:
--   The ferromagnetic Ising law $\nu_G\propto e^{\beta m(\sigma)}$, its phases $\Sigma^\pm$ and $\beta_c(d)=\ln\frac d{d-2}$
-- statement:
--   Let $G=(V,E)$ be a graph on $n$ vertices and $\beta>0$. A configuration is $\sigma\in\{0,1\}^V$, and $m(\sigma)$ is the number of monochromatic edges, i.e. edges $\{u,v\}$ with $\sigma_u=\sigma_v$. The **Ising law** is
--   $$\nu_G(\sigma)\propto e^{\beta m(\sigma)}.$$
--   The **phases** are
--   $$\Sigma^+=\{\sigma:\ |\sigma^{-1}(1)|\ge n/2\},\qquad \Sigma^-=\{\sigma:\ |\sigma^{-1}(1)|<n/2\},$$
--   with phase laws $\nu^\pm_G=\nu_G(\cdot\mid\Sigma^\pm)$, and the threshold for random $d$-regular graphs is
--   $$\beta_c(d)=\ln\frac{d}{d-2}.$$
--   The chain $X^+$ starts from the all-plus configuration (every spin $1$) and $X^-$ from the all-minus configuration (every spin $0$). The sampler's output encodes $\sigma$ as the set $\sigma^{-1}(1)$; its input carries $\beta$ in real cell $0$.
--
--   These are the objects of Theorem 3.
--
--   **Formalization Note** Spins are Booleans with `true` $=1$, and $|\sigma^{-1}(1)|\ge n/2$ is written $n\le2|\sigma^{-1}(1)|$. The published `isingDist` with $\pm1$ spins carries weight $e^{2\beta m(\sigma)}$ up to a constant, so the law is defined directly.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), §1.1.3, pp.4–5, and §4, p.19

import Mathlib
import Definitions.Def_LowTempGlauber_Supplement_FinSampler

open Classical

namespace LowTempGlauber.Supplement

/-!
# The ferromagnetic Ising model with `{0,1}` spins, its phases and `β_c(d)`

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), §1.1.3, pp.4–5,
and §4, p.19.

**Formalization Note.**
* Configurations are `σ : Fin n → Bool`, `true` = spin `1`.
* `monoCount G σ = m(σ)`, the number of edges `{u, v}` of `G` with `σ_u = σ_v` (each edge once).
* `isingLaw G β σ = e^{β m(σ)} / Σ_τ e^{β m(τ)}` (p.4). (The published `MarkovMixing.isingDist` uses
  `±1` spins and weight `e^{β Σ σ_uσ_v}`, which is this law at `2β`; it is not used.)
* `IsSigmaPlus σ` is `σ ∈ Σ⁺`: `|σ⁻¹(1)| ≥ n/2`, written `n ≤ 2|σ⁻¹(1)|`; `IsSigmaMinus σ` is
  `|σ⁻¹(1)| < n/2`, written `2|σ⁻¹(1)| < n` (p.5).
* `betaCIsing d = ln(d/(d − 2))` (p.5).
* `allPlus n` is the all-`1` configuration, `allMinus n` the all-`0` one (p.19: "`X⁺_t` from all-plus").
* `spinSet σ ⊆ Fin n`, the sampler's output encoding: the vertices of spin `1`.
-/

/-- `m(σ)`: the number of monochromatic edges. -/
noncomputable def monoCount {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun e : Sym2 (Fin n) =>
    e ∈ G.edgeSet ∧ ∀ u ∈ e, ∀ v ∈ e, σ u = σ v)).card

/-- The Ising law `ν_G(σ) ∝ e^{β m(σ)}` on `{0,1}^V`, p.4. -/
noncomputable def isingLaw {n : ℕ} (G : SimpleGraph (Fin n)) (β : ℝ) (σ : Fin n → Bool) : ℝ :=
  Real.exp (β * monoCount G σ) / ∑ τ : Fin n → Bool, Real.exp (β * monoCount G τ)

/-- The number of vertices of spin `1`. -/
noncomputable def numOnes {n : ℕ} (σ : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun v => σ v = true)).card

/-- `Σ⁺ = {σ : |σ⁻¹(1)| ≥ n/2}`, p.5. -/
def IsSigmaPlus {n : ℕ} (σ : Fin n → Bool) : Prop := n ≤ 2 * numOnes σ

/-- `Σ⁻ = {σ : |σ⁻¹(1)| < n/2}`, p.5. -/
def IsSigmaMinus {n : ℕ} (σ : Fin n → Bool) : Prop := 2 * numOnes σ < n

/-- `β_c(d) = ln(d/(d − 2))`, p.5. -/
noncomputable def betaCIsing (d : ℕ) : ℝ := Real.log ((d : ℝ) / ((d : ℝ) - 2))

/-- The all-plus configuration (every spin `1`). -/
def allPlus (n : ℕ) : Fin n → Bool := fun _ => true

/-- The all-minus configuration (every spin `0`). -/
def allMinus (n : ℕ) : Fin n → Bool := fun _ => false

/-- The output encoding of a configuration: the set of vertices of spin `1`. -/
noncomputable def spinSet {n : ℕ} (σ : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => σ v = true)

/-- The Ising sampler's initial state: the graph input and real cell `0 = β`. -/
noncomputable def isingInit (n d : ℕ) (G : SimpleGraph (Fin n)) (β : ℝ) :
    SubsetConvFPRAS.State n :=
  initState n n d G (fun i => if i = 0 then β else 0)

end LowTempGlauber.Supplement


