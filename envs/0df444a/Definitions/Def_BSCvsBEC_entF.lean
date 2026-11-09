-- Prove2me | Definitions.Def_BSCvsBEC_entF
-- name    : BSCvsBEC_entF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:41.053333+00:00
-- url     : https://prove2.me/theorems/b270a1c6-0cf1-4afc-9e95-0ed4e1408966
-- title:
--   Noise operator $T_\eta$ and the entropy functional $\mathrm{Ent}$ on $\mathbb F_2$
-- statement:
--   Let $\mathcal H$ be a finite-dimensional Hilbert space and $f:\mathbb F_2\to\mathrm{Pos}(\mathcal H)$ (positive semidefinite operators). The **noise operator** with correlation $\eta$ acts entrywise:
--   $$T_\eta f(b)=\frac{1+\eta}{2}\,f(b)+\frac{1-\eta}{2}\,f(b+1),$$
--   and $\mathbb E f=\tfrac12(f(0)+f(1))$. With $\phi(t)=t\log t$, the **entropy functional** is
--   $$\mathrm{Ent}(f):=\mathbb E_{b\in\mathbb F_2}\operatorname{Tr}\phi(f(b))-\operatorname{Tr}\phi(\mathbb E f).$$
--   For scalar $g:\mathbb F_2\to\mathbb R_{\ge0}$ (the case $\mathcal H=\mathbb C$) these are $T_\eta g$ and $\mathrm{Ent}(g)=\mathbb E[g\log g]-\mathbb E[g]\log\mathbb E[g]$.
--
--   $T_\eta$ is the conditional expectation through a binary symmetric channel with crossover probability $(1-\eta)/2$; Corollary 4.5(ii) bounds $\mathrm{Ent}(T_\eta f)$ by $\eta^2\,\mathrm{Ent}(f)$.
--
--   **Formalization Note** $\mathcal H=\mathbb C^\iota$ for a finite type $\iota$, $\mathbb F_2$ is `Fin 2`, and $\operatorname{Tr}\phi(M)$ uses the Hermitian functional calculus. The natural logarithm is used, as in the paper's proof ("The base of the logarithm is immaterial"); the inequalities stated with $\mathrm{Ent}$ do not depend on the base.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §4.2, p.21 (Ent, T_η entrywise); eq. (21), p.6 (T_ρ); p.10 below eq. (52) (scalar Ent)

import Mathlib

namespace BSCvsBEC

/-- The noise operator `T_η` on functions `f : F₂ → Pos(ℋ)`, applied entrywise:
`T_η f(b) = ((1 + η)/2) f(b) + ((1 − η)/2) f(b + 1)`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), eq. (21), p.6 with `q = 2`
(`T_ρ f(y) = E[f(U) | Y = y]`, `Y = BSC_p(U)`, `p = (1 − ρ)/2`), applied entrywise as in §4.2, p.21;
the proof of Proposition 4.4 writes `u = (1+η)/2`, `v = (1−η)/2`.

**Formalization Note.** `F₂ = Fin 2` (addition mod 2); `ℋ = ℂ^ι`. -/
noncomputable def noiseOp {ι : Type*} (η : ℝ) (f : Fin 2 → Matrix ι ι ℂ) : Fin 2 → Matrix ι ι ℂ :=
  fun b => ((1 + η) / 2 : ℝ) • f b + ((1 - η) / 2 : ℝ) • f (b + 1)

/-- The average `E f = (f(0) + f(1))/2` over the uniform `b ∈ F₂`. -/
noncomputable def avgF {ι : Type*} (f : Fin 2 → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℝ) • (f 0 + f 1)

/-- `Tr φ(M)` with `φ(t) = t log t`, through the Hermitian functional calculus. -/
noncomputable def trPhi {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (cfc (fun t : ℝ => t * Real.log t) M)).re

/-- The matrix entropy functional `Ent(f) := E_{b∈F₂} Tr φ(f(b)) − Tr φ(E f)`, `φ(t) = t log t`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §4.2, p.21.

**Formalization Note.** Natural logarithm (the proof of Proposition 4.4 does the same: "The base of
the logarithm is immaterial, so temporarily take `φ(t) = t ln t`"); the inequalities stated with
`Ent` are invariant under the base. -/
noncomputable def entF {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Fin 2 → Matrix ι ι ℂ) : ℝ :=
  (1 / 2) * (trPhi (f 0) + trPhi (f 1)) - trPhi (avgF f)

/-- The noise operator `T_η` on scalar functions `g : F₂ → ℝ`. -/
noncomputable def noiseR (η : ℝ) (g : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun b => (1 + η) / 2 * g b + (1 - η) / 2 * g (b + 1)

/-- The scalar entropy functional `Ent(g) = E[g log g] − E[g] log E[g]` on `g : F₂ → ℝ`
(p.10, below eq. (52); p.21 with `ℋ = ℂ`), natural logarithm. -/
noncomputable def entR (g : Fin 2 → ℝ) : ℝ :=
  (1 / 2) * (g 0 * Real.log (g 0) + g 1 * Real.log (g 1)) -
    (g 0 + g 1) / 2 * Real.log ((g 0 + g 1) / 2)

end BSCvsBEC


