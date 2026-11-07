-- Prove2me | Definitions.Def_BetheKS_HasProjProperty
-- name    : BetheKS_HasProjProperty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:09.06579+00:00
-- url     : https://prove2.me/theorems/39f7ef52-c08f-4f8e-b4b0-4d4ff4dc897c
-- title:
--   The projection property of the constants $c_\mu$ (Theorem 2.2)
-- statement:
--   A function $c$ has the **projection property** for the parameters $(P,\pi)$ if, for every distinct informative eigenvalue $\mu$ of $Q$, $c_\mu>0$ and, for $G_n\sim\mathrm{SBM}_n(P,\pi)$, with probability tending to one,
--   $$
--   \|\operatorname{Proj}_{E_{\mu,n}}x\|_2\ \ge\ c_\mu\|x\|_2\qquad\text{for every }x\in\operatorname{span}\{X_i:\mu_i=\mu\}.
--   $$
--   This is the property of the constants $c_\mu$ in Theorem 2.2, which Theorem 2.3 uses.
--
--   **Formalization Note** The limit is along $\mathcal N_\pi$, for every sequence of exact-size label maps and for every choice of increasing orthonormal eigenbases of $H(\pm\sqrt d,G)$ fixed for each graph before the probability is taken. The quantifier over $x$ is inside the event.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Theorem 2.2, p.5

import Mathlib
import Definitions.Def_BetheKS_sbmProb
import Definitions.Def_BetheKS_outlierSpace

set_option autoImplicit false

namespace BetheKS

variable {r : ℕ}

/-- **The projection property of the constants `c_µ`** — Dong, McKenzie, arXiv:2610.41802 (held
version, sha256 4da41e16…), Theorem 2.2, p.5: for every distinct informative eigenvalue `µ`,
`c_µ > 0` and, with probability tending to one,
`‖Proj_{E_{µ,n}} x‖₂ ≥ c_µ ‖x‖₂` for every `x ∈ span{Xᵢ : µᵢ = µ}`.

**Formalization Note.** `c` is a function of `µ` (its values off the informative eigenvalues are
irrelevant). The property is required for every sequence of exact-size label maps `σₙ`
(`n ∈ 𝒩_π`) and for every choice of increasing orthonormal eigenbases of `H(±√d, G)`, chosen for
each graph before the probability is taken; the "for every `x`" is inside the event. -/
def HasProjProperty (p : SBMParams r) (c : ℝ → ℝ) : Prop :=
  ∀ μ ∈ (informative p).toFinset, 0 < c μ ∧
    ∀ σs : ∀ n : ℕ, Fin n → Fin r, IsExactSeq p σs →
    ∀ Bp : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (Real.sqrt p.d) G),
    ∀ Bm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (-Real.sqrt p.d) G),
      Whp p σs (fun n G => ∀ x ∈ plantedSpace p (σs n) μ,
        c μ * ‖x‖ ≤ ‖(outlierSpace p (Bp n G) (Bm n G) μ).starProjection x‖)

end BetheKS


