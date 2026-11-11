-- Prove2me | Definitions.Def_IllCondRegMem_gaussMixture
-- name    : IllCondRegMem_gaussMixture
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:33.100752+00:00
-- url     : https://prove2.me/theorems/bb637732-9210-4b23-b362-872d2691849a
-- title:
--   Gaussian mixtures $\mathbb E_\omega[\mathcal N(m(\omega),S(\omega))]$, densities and $L^1$ distance
-- statement:
--   Let $(\Omega,\mathbb P)$ be a probability space, $m:\Omega\to\mathbb R^d$ a random mean and $S:\Omega\to\mathbb R^{d\times d}$ a random positive semidefinite matrix. The **Gaussian mixture**
--   $$
--   \mathbb E_{\omega}\big[\mathcal N(m(\omega),S(\omega))\big]
--   $$
--   is the law of a vector obtained by first drawing $\omega\sim\mathbb P$ and then a Gaussian vector with mean $m(\omega)$ and covariance $S(\omega)$. For a random $d\times m$ matrix $B$ and a fixed $z\in\mathbb R^m$, the mixture $\mathbb E_{\Sigma,B}[\mathcal N(Bz,\Sigma)]$ of Lemma 13 is the case $m(\omega)=B(\omega)z$, $S=\Sigma$.
--
--   For a measure $\mu$ on $\mathbb R^d$ that is absolutely continuous with respect to Lebesgue measure, its **density** $f=d\mu/dx$ is the Radon–Nikodym derivative, and $\|f-g\|_1=\int_{\mathbb R^d}|f(x)-g(x)|\,dx$ is the $L^1$ distance of two functions.
--
--   In Lemma 5 the samples $a\sim\mathcal N(0,P_E+D_0)$, $b\sim\mathcal N(0,P_E+D_1)$ with random $(E,D_0,D_1)$ are such mixtures; Lemmas 13 and 14 compare the densities of mixtures in $L^1$.
--
--   **Formalization Note** $\mathcal N(\mu,S)$ is Mathlib's `multivariateGaussian μ S`, the law of $\mu+S^{1/2}g$ with $g$ standard Gaussian; it is the Gaussian law whenever $S$ is positive semidefinite, which every theorem assumes almost surely. The mixture is the composition (`Measure.bind`) of $\mathbb P$ with this kernel. The $L^1$ distance is an extended nonnegative real ($+\infty$ if $f-g$ is not integrable).
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), §4, p.11 (PDF p.12); Lemma 5, p.8 (PDF p.9); Lemma 13, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Mixture of Gaussians** `E_ω[N(m(ω), S(ω))]`.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §4, p.11
("mixture of Gaussians"), Lemma 5 p.8 ("a ∼ N(0, P_E + D₀)" with random `E, D₀`) and Lemma 13
p.12 ("the mixture E_{Σ,B}[N(Bz, Σ)]").

Given a probability space `(Ω, P)`, a random mean `m` and a random covariance `S`,
`gaussMixture P m S` is the law of a vector drawn by first drawing `ω ∼ P` and then a Gaussian
with mean `m ω` and covariance `S ω`.

**Formalization Note.** `N(μ, S)` is Mathlib's `multivariateGaussian μ S` (the law of
`μ + S^{1/2} g` with `g` standard Gaussian), which is the Gaussian law whenever `S` is positive
semidefinite; the theorems use the mixture only when `S ω` is positive semidefinite almost
surely and `m, S` are measurable. The mixture is the bind (composition) of `P` with this kernel. -/
noncomputable def gaussMixture {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (m : Ω → Vec d) (S : Ω → Matrix (Fin d) (Fin d) ℝ) : Measure (Vec d) :=
  P.bind fun ω => multivariateGaussian (m ω) (S ω)

/-- The mixture `E_{Σ,B}[N(Bz, Σ)]` of Lemma 13 (p.12): random mean `B z` for a fixed
`z ∈ ℝ^m` and a random `d × m` matrix `B`, random covariance `Σ`. -/
noncomputable def mixtureAt {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ} (P : Measure Ω)
    (Sig : Ω → Matrix (Fin d) (Fin d) ℝ) (B : Ω → Matrix (Fin d) (Fin m) ℝ) (z : Vec m) :
    Measure (Vec d) :=
  gaussMixture P (fun ω => Matrix.toEuclideanLin (B ω) z) Sig

/-- The **density** of a measure on `ℝ^d` with respect to Lebesgue measure, as a real function
(the Radon–Nikodym derivative, converted to a real number).

**Formalization Note.** The theorems state absolute continuity `μ ≪ volume` as part of their
conclusion, so that this is a genuine density. -/
noncomputable def density {d : ℕ} (μ : Measure (Vec d)) (x : Vec d) : ℝ :=
  (μ.rnDeriv volume x).toReal

/-- The `L¹` distance `‖f − g‖₁ = ∫ |f(x) − g(x)| dx` of two real functions on `ℝ^d`, as an
extended nonnegative real (it is `∞` when `f − g` is not integrable). -/
noncomputable def l1Dist {d : ℕ} (f g : Vec d → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal |f x - g x|

end IllCondRegMem


