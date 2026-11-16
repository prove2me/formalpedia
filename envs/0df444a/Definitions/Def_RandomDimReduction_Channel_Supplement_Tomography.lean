-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Supplement_Tomography
-- name    : RandomDimReduction_Channel_Supplement_Tomography
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:40:32.70743+00:00
-- url     : https://prove2.me/theorems/5d17260e-6656-4b1d-b536-ce97ede2de5a
-- title:
--   Permutation-fixed space, covariant Haar effects and their Born law
-- statement:
--   The symmetric space consists of the vectors fixed by every inverse-permutation action. Write $d[n]=\binom{d+n-1}{n}$, using the published symmetric dimension and projector. For $d>0$, the measure $du$ is the first-column pushforward of normalized Haar on $U(d)$, regarded as a measure on $\mathbb C^d$ supported on unit vectors. Its value at $d=0$ is the zero measure, outside the theorem's domain. Pure-state fidelity is the squared overlap $F(u,\psi)=|\langle u,\psi\rangle|^2$.
--
--   The specified continuous measurement has effect density and candidate outcome law
--   $$E_n(u)=d[n](|u\rangle\langle u|)^{\otimes n},\qquad d\mu_{\psi,n}(u)=d[n]F(u,\psi)^n\,du.$$
--   The latter is defined by density, without a probability normalization assumption. Its normalization, support, the effect integral, and the zero probability of the complementary effect $I-\Pi_{sym}^n$ are conclusions of Theorem 3.3.
--
--   This separates the Haar reference law from the observed Born law and leaves the measurement guarantee to be proved.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, §2.1, p.6; §3.2, pp.10–11, Theorem 3.3 and Eq. (8)

import Definitions.Def_RandomDimReduction_Channel_Tensor

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped Kronecker Matrix ComplexConjugate Matrix.Norms.Elementwise InnerProductSpace

namespace RandomDimReduction.Channel.Supplement
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Actual permutation-fixed vectors, §2.1, p.6. -/
def symmetricSpace (n d : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Word n d)) where
  carrier := {v | ∀ (p : Equiv.Perm (Fin n)) (i : Word n d), v (i ∘ p.symm) = v i}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy p i
    change x (i ∘ p.symm) + y (i ∘ p.symm) = x i + y i
    rw [hx p i, hy p i]
  smul_mem' := by
    intro c x hx p i
    change c * x (i ∘ p.symm) = c * x i
    rw [hx p i]

/-- Haar probability on the sphere, as the first-column pushforward.
For d=0 the measure is zero; every result below requires d>0. -/
def sphereHaar (d : ℕ) : Measure (EuclideanSpace ℂ (Fin d)) :=
  if hd : 0 < d then
    Measure.map (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      WithLp.toLp 2 (fun i => (U : Op (Fin d)) i ⟨0, hd⟩))
      (MixedCloning.Optimal.haar d)
  else 0

/-- Squared overlap (not root fidelity). -/
def pureFidelity {d : ℕ} (u psi : EuclideanSpace ℂ (Fin d)) : ℝ :=
  ‖inner ℂ u psi‖ ^ 2

/-- Continuous covariant effect density d[n] |u⟩⟨u|^⊗n; pp.10–11. -/
def covariantEffect {d : ℕ} (n : ℕ) (u : EuclideanSpace ℂ (Fin d)) : Op (Word n d) :=
  (MixedCloning.Optimal.symDimension d n : ℂ) • tensor n (MixedCloning.Optimal.pure u)

/-- The Born distribution, not the sampling Haar distribution.
Normalization is a theorem, not part of this definition. -/
def bornLaw {d : ℕ} (n : ℕ) (psi : EuclideanSpace ℂ (Fin d)) :
    Measure (EuclideanSpace ℂ (Fin d)) :=
  (sphereHaar d).withDensity (fun u =>
    ENNReal.ofReal ((MixedCloning.Optimal.symDimension d n : ℝ) * pureFidelity u psi ^ n))

end RandomDimReduction.Channel.Supplement


