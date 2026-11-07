-- Prove2me | Definitions.Def_PathRecording_reweight
-- name    : PathRecording_reweight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:06:28.880956+00:00
-- url     : https://prove2.me/theorems/17b2cd86-35c7-423a-8aca-d5aabed1b5e0
-- title:
--   Subspace-reweighting operators $W_t$, $W_t^+$ and the projector $\Pi_{\mathrm{diag},t}$
-- statement:
--   With the block projectors $\Pi^{\otimes2}_{\lambda,t}$ of the double Schur decomposition,
--   $$W_t=\sum_{\lambda}\sqrt{\frac{\dim V^\lambda_{\mathcal A_t}}{\dim V^\lambda_G}}\;\Pi^{\otimes2}_{\lambda,t},\qquad(5.6)$$
--   $$W_t^+=\sum_{\lambda}\sqrt{\frac{\dim V^\lambda_G}{\dim V^\lambda_{\mathcal A_t}}}\;\Pi^{\otimes2}_{\lambda,t},\qquad(5.7)$$
--   $$\Pi_{\mathrm{diag},t}=\sum_\lambda\Pi^{\otimes2}_{\lambda,t},$$
--   the sums ranging over $\lambda\in\widehat G_t$.
--
--   $W_t$ reweights each equal-label block of the path space; $W_t^+$ inverts it on $\Pi_{\mathrm{diag},t}$. Both appear in the path-recording update (5.8).
--
--   **Formalization Note** Both dimensions are positive for every label (irreducible representations are nonzero, and $\widehat G_t$ keeps only labels with $\dim V^\lambda_{\mathcal A_t}>0$), so no division by zero occurs.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Eqs. (5.6)–(5.7), pp.61–62

import Mathlib
import Definitions.Def_PathRecording_omega

set_option autoImplicit false

namespace PathRecording

/-!
# The subspace-reweighting operators `W_t`, `W_t^+` and the projector `Π_{diag,t}`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Eqs. (5.6)–(5.7), pp.61–62:

* `W_t := Σ_λ √(dim(V^λ_{𝒜_t}) / dim(V^λ_G)) Π^{⊗2}_{λ,t}` (5.6);
* `Π_{diag,t} := Σ_λ Π^{⊗2}_{λ,t}` (p.62);
* `W_t^+ := Σ_λ √(dim(V^λ_G) / dim(V^λ_{𝒜_t})) Π^{⊗2}_{λ,t}` (5.7).

**Formalization Note.** The sums range over the labels `λ ∈ Ĝ_t` of the Schur–Weyl data, the only
labels with a nonzero block. Both dimensions are positive (`dA_pos`, and `0 < dG λ` from
irreducibility), so no division by zero occurs. The real square root is cast to `ℂ`.
-/

open Matrix

variable {G : Type*} [Group G] [TopologicalSpace G] {N : ℕ} {ρ : UnitaryRep G N} {t : ℕ}

namespace SchurWeylData

variable (S : SchurWeylData ρ t)

/-- `W_t = Σ_λ √(dim V^λ_{𝒜_t} / dim V^λ_G) Π^{⊗2}_{λ,t}` (arXiv:2606.30281v2, Eq. (5.6), p.61). -/
noncomputable def reweight : Matrix (PathIdx N t) (PathIdx N t) ℂ :=
  ∑ l, ((Real.sqrt ((S.dA l : ℝ) / (S.dG l : ℝ)) : ℝ) : ℂ) • S.blockProj2 l

/-- `W_t^+ = Σ_λ √(dim V^λ_G / dim V^λ_{𝒜_t}) Π^{⊗2}_{λ,t}` (arXiv:2606.30281v2, Eq. (5.7), p.62). -/
noncomputable def reweightPlus : Matrix (PathIdx N t) (PathIdx N t) ℂ :=
  ∑ l, ((Real.sqrt ((S.dG l : ℝ) / (S.dA l : ℝ)) : ℝ) : ℂ) • S.blockProj2 l

/-- `Π_{diag,t} = Σ_λ Π^{⊗2}_{λ,t}`, the projector onto the equal-irrep subspace (p.62). -/
noncomputable def projDiag : Matrix (PathIdx N t) (PathIdx N t) ℂ :=
  ∑ l, S.blockProj2 l

end SchurWeylData

end PathRecording


