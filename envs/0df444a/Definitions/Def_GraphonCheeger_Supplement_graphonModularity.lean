-- Prove2me | Definitions.Def_GraphonCheeger_Supplement_graphonModularity
-- name    : GraphonCheeger_Supplement_graphonModularity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:22:54.923286+00:00
-- url     : https://prove2.me/theorems/0673e90a-a71b-4426-b290-f14615a4051b
-- title:
--   Modularity of graphons: $\hat q(W,\Psi)$, $\hat q^*_\kappa(W)$, $\hat q^*(W)$ and the pure versions
-- statement:
--   Let $W$ be a graphon on $(\Omega,\mathcal F,\mu)$ with degree function $k(x)=\int W(x,y)\,d\mu(y)$ and edge density $\rho=\iint W\,d\mu\,d\mu$. For a $\kappa$-colouring $\Psi$ the **modularity score** is
--   $$
--   \hat q(W,\Psi)=\frac1\rho\iint_{\Omega^2}\Bigl(W(x,y)-\frac{k(x)k(y)}\rho\Bigr)\langle\Psi(x),\Psi(y)\rangle\,d\mu(x)\,d\mu(y),
--   $$
--   with $\langle\Psi(x),\Psi(y)\rangle=\sum_\ell\psi_\ell(x)\psi_\ell(y)$, and $\hat q(W,\Psi):=0$ when $\rho=0$. The (mixed) $\kappa$-modularity and modularity are
--   $$
--   \hat q^*_\kappa(W)=\sup_{\Psi\in\Lambda_\kappa}\hat q(W,\Psi),\qquad \hat q^*(W)=\sup_{\kappa\ge1}\hat q^*_\kappa(W),
--   $$
--   and the pure versions $\hat q^*_{\kappa,\mathrm{pure}}(W)$, $\hat q^*_{\mathrm{pure}}(W)$ take the suprema over pure colourings $\chi:\Omega\to[\kappa]$ only.
--
--   These are the graphon parameters of Theorems 5.6–5.29.
--
--   **Formalization Note** $k$ and $\rho$ are the base `degFun` and `density`. `qhat` is defined for every coloured pair; `modK κ`, `modW`, `modPureK κ`, `modPure` are the four suprema, over nonempty sets for $\kappa\ge1$ that are bounded by Proposition 5.5 ($-\tfrac12\le\hat q\le1$). Pure colourings are measurable $\chi$ with the point-mass colouring `ofColour χ`.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Definition 5.2, p.52; Definition 5.7, p.56

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens

open MeasureTheory

namespace GraphonCheeger.Supplement

/-!
# Modularity of graphons: `q̂(W, Ψ)`, `q̂*_κ(W)`, `q̂*(W)` and the pure versions

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), Definition 5.2 (p.52) and Definition 5.7
(p.56).

**Formalization Note.**
* `k = k_W` and `ρ = ρ_W` are the base `degFun` (4.1) and `density` (4.2).
* `qhat μ W Ψ` is (5.3) for a `κ`-coloured graphon `(W, Ψ)`, with `⟨Ψ(x), Ψ(y)⟩ = Σ_ℓ ψ_ℓ(x) ψ_ℓ(y)`;
  it is `0` when `ρ = 0`, as fixed on p.52.
* `modK κ μ W = q̂*_κ(W) = sup_{Ψ ∈ Λ_κ} q̂(W, Ψ)` (5.34) and `modW μ W = q̂*(W) = sup_{κ ≥ 1} q̂*_κ(W)`
  (5.35). The pure versions (5.36)–(5.37) take the supremum over measurable `χ : Ω → [κ]`, with the
  point-mass colouring `ofColour χ`. All these sets are nonempty for `κ ≥ 1` and bounded
  (`−1/2 ≤ q̂ ≤ 1`, Proposition 5.5).
-/

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The modularity score of a `κ`-coloured graphon ((5.3), p.52):
`q̂(W, Ψ) = (1/ρ) ∬ (W(x, y) − k(x) k(y)/ρ) ⟨Ψ(x), Ψ(y)⟩ dµ(x) dµ(y)`, and `q̂ := 0` when `ρ = 0`. -/
noncomputable def qhat (μ : Measure Ω) {κ : ℕ} (W : Ω → Ω → ℝ) (Ψ : Ω → Fin κ → ℝ) : ℝ :=
  if density μ W = 0 then 0 else
    (1 / density μ W) * ∫ p, (W p.1 p.2 - degFun μ W p.1 * degFun μ W p.2 / density μ W) *
      ∑ ℓ, Ψ p.1 ℓ * Ψ p.2 ℓ ∂(μ.prod μ)

/-- The (mixed) `κ`-modularity `q̂*_κ(W) = sup_{Ψ ∈ Λ_κ} q̂(W, Ψ)` ((5.34), p.56). -/
noncomputable def modK (κ : ℕ) (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ Ψ : Ω → Fin κ → ℝ, IsKColouring Ψ ∧ r = qhat μ W Ψ}

/-- The (mixed) graphon modularity `q̂*(W) = sup_{κ ≥ 1} q̂*_κ(W)` ((5.35), p.56). -/
noncomputable def modW (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ κ : ℕ, 1 ≤ κ ∧ r = modK κ μ W}

/-- The pure `κ`-modularity `q̂*_{κ,pure}(W) = sup_{χ : Ω → [κ]} q̂(W, χ)` ((5.36), p.56). -/
noncomputable def modPureK (κ : ℕ) (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ χ : Ω → Fin κ, Measurable χ ∧ r = qhat μ W (ofColour χ)}

/-- The pure graphon modularity `q̂*_pure(W) = sup_{κ ≥ 1} q̂*_{κ,pure}(W)` ((5.37), p.56). -/
noncomputable def modPure (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ κ : ℕ, 1 ≤ κ ∧ r = modPureK κ μ W}

end GraphonCheeger.Supplement


