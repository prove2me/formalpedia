-- Prove2me | Definitions.Def_DesignTest_rankOneMoment
-- name    : DesignTest_rankOneMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:21.591616+00:00
-- url     : https://prove2.me/theorems/9db9c9da-ad9c-4784-8e1f-0baed536bf89
-- title:
--   Rank-one projectors, the moment $\Phi(\nu)=\mathbb E_{x\sim\nu}[\Phi(x)]$, and the empirical mixture $\nu_{C,\lambda}=(1-\lambda)\mu+\lambda\widehat\mu_C$
-- statement:
--   Let $\mathcal X$ be a measurable space and $\mathcal H=\mathbb C^n$.
--
--   1. A matrix $P$ on $\mathbb C^n$ is a **rank-one projector** if $P=|v\rangle\langle v|$ for a unit vector $v$.
--   2. For a map $\Phi$ from $\mathcal X$ to matrices on $\mathbb C^n$ and a measure $\nu$ on $\mathcal X$, the **moment** is $\Phi(\nu)=\mathbb E_{x\sim\nu}[\Phi(x)]$ (entrywise).
--   3. For a reference measure $\mu$, a list $C=(X_1,\dots,X_M)$ of points of $\mathcal X$ and $\lambda\in[0,1]$, the **empirical mixture** is
--   $$\widehat\mu_C=\frac1M\sum_{a=1}^{M}\delta_{X_a},\qquad \nu_{C,\lambda}=(1-\lambda)\mu+\lambda\,\widehat\mu_C .$$
--
--   These are the objects of the rank–collision lemma (Lemma 3.17), from which the general sample lower bound follows.
--
--   **Formalization Note** The weights are written as `ENNReal.ofReal (1 - λ)` and `ENNReal.ofReal (λ/M)`; for $\lambda\in[0,1]$, $M\ge1$ and a probability measure $\mu$ the mixture is a probability measure.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §3.3.3, p.21; Lemma 3.17, p.21

import Mathlib

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- `P` is a rank-one (orthogonal) projector on `ℂ^n`: `P = |v⟩⟨v|` for a unit vector `v` (STOC 2027
submission (sha256 e2f0a429…), §3.3.3, p.21). -/
def IsRankOneProj {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧ P = Matrix.vecMulVec (fun i => v i) (fun j => star (v j))

/-- **The moment `Φ(ν) := E_{x∼ν}[Φ(x)]`** of a map `Φ` from a measurable space `X` to matrices on `ℂ^n`
(STOC 2027 submission (sha256 e2f0a429…), §3.3.3, p.21). Entrywise Bochner integral. -/
noncomputable def rankOneMoment {X : Type} [MeasurableSpace X] {n : ℕ}
    (Φ : X → Matrix (Fin n) (Fin n) ℂ) (ν : Measure X) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ∫ x, Φ x i j ∂ν

/-- **The empirical mixture** `ν_{C,λ} := (1 − λ)µ + λ µ̂_C`, `µ̂_C := M⁻¹ Σ_{a=1}^{M} δ_{X_a}`, of a
reference measure `µ` with the empirical measure of a list `C = (X_1, …, X_M)` (STOC 2027 submission
(sha256 e2f0a429…), Lemma 3.17, p.21; the same construction is (28), p.22).

**Formalization Note.** The weights are `ENNReal.ofReal (1 − λ)` and `ENNReal.ofReal (λ/M)`; for
`λ ∈ [0, 1]`, `M ≥ 1` and a probability measure `µ` this is a probability measure. -/
noncomputable def empiricalMixture {X : Type} [MeasurableSpace X] {M : ℕ} (μ : Measure X)
    (lam : ℝ) (c : Fin M → X) : Measure X :=
  ENNReal.ofReal (1 - lam) • μ + ENNReal.ofReal (lam / M) • ∑ a, Measure.dirac (c a)

end DesignTest


