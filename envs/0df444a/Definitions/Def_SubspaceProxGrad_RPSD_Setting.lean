-- Prove2me | Definitions.Def_SubspaceProxGrad_RPSD_Setting
-- name    : SubspaceProxGrad_RPSD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:24.810318+00:00
-- url     : https://prove2.me/theorems/7f487dcb-48e9-4a6b-bf4e-d65ca55fa7ed
-- title:
--   §2.1–2.3, pp. 2–5 — admissible selections, the average projection P = 𝔼[P_𝔖], λmin/λmax, the P-norm, minimizers of f + g, and the RPSD run (Algorithm 1)
-- statement:
--   This file fixes the objects of the random proximal subspace descent method (RPSD) of Grishchenko, Iutzeler and Malick.
--
--   Work in $\mathbb R^n$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|_2$. For a linear subspace $F\subseteq\mathbb R^n$ write $P_F$ for the orthogonal projection onto $F$, and $F^\perp$ for its orthogonal complement.
--
--   1. **Selections and admissibility** (Definition 2 and p. 3). A *selection* is a random subspace $\mathfrak S$ of $\mathbb R^n$, defined on a probability space $(\Omega,\mathcal A,\mathbb P)$. It is *admissible* if
--   $$\mathbb P\big[x\in\mathfrak S^\perp\big]<1\qquad\text{for all }x\in\mathbb R^n\setminus\{0\}.$$
--   2. **Average projection** (display (2), p. 3). The matrix $\mathsf P=\mathbb E[P_{\mathfrak S}]$, that is, $\mathsf P x=\int_\Omega P_{\mathfrak S(\omega)}x\,d\mathbb P(\omega)$ for every $x\in\mathbb R^n$.
--   3. **Extreme Rayleigh quotients.** For a linear map $\mathsf P$ on $\mathbb R^n$,
--   $$\lambda_{\min}(\mathsf P)=\inf_{\|x\|_2=1}\langle x,\mathsf Px\rangle,\qquad \lambda_{\max}(\mathsf P)=\sup_{\|x\|_2=1}\langle x,\mathsf Px\rangle .$$
--   For a symmetric $\mathsf P$ these are its least and greatest eigenvalues.
--   4. **The $\mathsf P$-norm** (p. 5): $\|v\|_{\mathsf P}^2=\langle v,\mathsf Pv\rangle$.
--   5. **Minimizers** of problem (1), $\min_x f(x)+g(x)$, where $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ has effective domain $C=\operatorname{dom}g$: a point $x^\star\in C$ with $f(x^\star)+g(x^\star)\le f(y)+g(y)$ for every $y\in C$.
--   6. **RPSD runs** (Algorithm 1, p. 4). Given a step size $\gamma$, linear maps $\mathsf Q$ and $\mathsf Q^{-1}$, a starting point $z^0$ and i.i.d. selections $\mathfrak S^1,\mathfrak S^2,\dots$, a run consists of sequences $(z^k)_{k\ge0}$ and $(x^k)_{k\ge1}$ with, for every $k\ge0$ and every outcome $\omega$,
--   $$x^{k+1}=\mathbf{prox}_{\gamma g}\big(\mathsf Q^{-1}z^k\big),\qquad y^{k+1}=\mathsf Q\big(x^{k+1}-\gamma\nabla f(x^{k+1})\big),\qquad z^{k+1}=P_{\mathfrak S^{k+1}}\,y^{k+1}+\big(I-P_{\mathfrak S^{k+1}}\big)z^k,$$
--   where $\mathbf{prox}_{\gamma g}(v)=\operatorname{argmin}_{y}\{g(y)+\tfrac1{2\gamma}\|y-v\|_2^2\}$ is the proximity operator (4).
--
--   These objects are shared by every statement of the mission: the convergence theorem, the three lemmas and the two displays of its proof.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and matrices are continuous linear maps. A selection is a map `S : Ω → Submodule ℝ (E n)`, and $P_F$ is Mathlib's `F.starProjection`. Definition 2 builds a selection as a random sum of members of a covering family; since every subspace is such a sum for the covering family of all subspaces, a random subspace is exactly a selection. The average projection is given pointwise by a Bochner integral; the theorems add the measurability of $\omega\mapsto P_{\mathfrak S(\omega)}x$, which makes that integral the true expectation. $\lambda_{\min}$ and $\lambda_{\max}$ are the Rayleigh infimum and supremum over the unit sphere (on $\mathbb R^0$ the sphere is empty and both are $0$). An extended-valued $g$ is the pair $(C,g)$ with $C=\operatorname{dom}g$; the prox is the published `BoydADMM.Prox.IsProx C g (1/γ) v x`. In the run, Lean's index `ξ k` draws the paper's $\mathfrak S^{k+1}$, i.e. $\mathfrak S^{k+1}=\mathrm{sel}(\xi_k)$; the run is a property of given sequences, required for every outcome, and `x 0` is unused.
-- source:
--   Grishchenko, Iutzeler & Malick, Proximal gradient methods with adaptive subspace sampling, arXiv:2004.13356v1, pp. 2–5, Definition 2, admissibility (p. 3), Lemma 1 / display (2), prox (4), (5)–(6), Algorithm 1, Assumptions 1–2

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open MeasureTheory ProbabilityTheory

namespace SubspaceProxGrad.RPSD

/-! Objects of §2.1–2.3 of Grishchenko, Iutzeler & Malick, *Proximal gradient methods with
adaptive subspace sampling*, arXiv:2004.13356v1, pp. 2–5.

`ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, so `‖·‖` is `‖·‖₂` and `inner ℝ` is `⟨·,·⟩`. Matrices are
continuous linear maps `E n →L[ℝ] E n`. A random subspace (a *selection*, Definition 2) is a map
`S : Ω → Submodule ℝ (E n)` on a probability space; `P_F` is `F.starProjection`. An
extended-valued `g : ℝⁿ → ℝ ∪ {+∞}` is the pair `(C, g)` with `C = dom g`. -/

/-- `ℝⁿ` with the Euclidean norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- p. 3: a selection `S` is *admissible* if `ℙ[x ∈ S^⊥] < 1` for every `x ∈ ℝⁿ \ {0}`. -/
def IsAdmissible {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    (S : Ω → Submodule ℝ (E n)) : Prop :=
  ∀ x : E n, x ≠ 0 → pr {ω | x ∈ (S ω)ᗮ} < 1

/-- (2), p. 3: `P = 𝔼[P_S]`, the average projection, given pointwise:
`P x = ∫ P_{S ω} x dℙ(ω)` for every `x`. -/
def IsAvgProj {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    (S : Ω → Submodule ℝ (E n)) (P : E n →L[ℝ] E n) : Prop :=
  ∀ x : E n, P x = ∫ ω, (S ω).starProjection x ∂pr

/-- `λ_min(P)`, the Rayleigh infimum `inf_{‖x‖ = 1} ⟨x, P x⟩` (the least eigenvalue of a
symmetric `P`). -/
noncomputable def lamMin {n : ℕ} (P : E n →L[ℝ] E n) : ℝ :=
  ⨅ x : Metric.sphere (0 : E n) 1, inner ℝ (x : E n) (P x)

/-- `λ_max(P)`, the Rayleigh supremum `sup_{‖x‖ = 1} ⟨x, P x⟩` (the greatest eigenvalue of a
symmetric `P`). -/
noncomputable def lamMax {n : ℕ} (P : E n →L[ℝ] E n) : ℝ :=
  ⨆ x : Metric.sphere (0 : E n) 1, inner ℝ (x : E n) (P x)

/-- `‖v‖²_P = ⟨v, P v⟩` (p. 5). -/
noncomputable def pNormSq {n : ℕ} (P : E n →L[ℝ] E n) (v : E n) : ℝ := inner ℝ v (P v)

/-- `x⋆` is a minimizer of problem (1), `min f + g`, over `dom g = C`. -/
def IsMinimizer {n : ℕ} (C : Set (E n)) (f g : E n → ℝ) (xs : E n) : Prop :=
  xs ∈ C ∧ ∀ y ∈ C, f xs + g xs ≤ f y + g y

/-- Algorithm 1 (RPSD), p. 4, run for every outcome `ω`. Lean's `ξ k` draws the paper's selection
`𝔖^{k+1} = sel (ξ k ω)`. For every `k ≥ 0`:
`x^{k+1} = prox_{γg}(Q⁻¹ z^k)` (step 2 for `k = 0`, step 6 otherwise), and
`z^{k+1} = P_{𝔖^{k+1}} y^{k+1} + (I − P_{𝔖^{k+1}}) z^k` with `y^{k+1} = Q(x^{k+1} − γ∇f(x^{k+1}))`
(steps 4–5). `z 0 = z⁰`; `x 0` is unused. -/
def IsRPSDRun {n : ℕ} {Ω Θ : Type*} (sel : Θ → Submodule ℝ (E n)) (ξ : ℕ → Ω → Θ)
    (C : Set (E n)) (f g : E n → ℝ) (γ : ℝ) (Q Qinv : E n →L[ℝ] E n) (z0 : E n)
    (z x : ℕ → Ω → E n) : Prop :=
  ∀ ω, z 0 ω = z0 ∧ ∀ k : ℕ,
    BoydADMM.Prox.IsProx C g (1 / γ) (Qinv (z k ω)) (x (k + 1) ω) ∧
    z (k + 1) ω = (sel (ξ k ω)).starProjection (Q (x (k + 1) ω - γ • gradient f (x (k + 1) ω)))
      + (z k ω - (sel (ξ k ω)).starProjection (z k ω))

end SubspaceProxGrad.RPSD


