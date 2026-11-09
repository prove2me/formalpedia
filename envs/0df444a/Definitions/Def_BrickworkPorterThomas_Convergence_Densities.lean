-- Prove2me | Definitions.Def_BrickworkPorterThomas_Convergence_Densities
-- name    : BrickworkPorterThomas_Convergence_Densities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:12.314335+00:00
-- url     : https://prove2.me/theorems/a3d2a55f-f7b8-4e72-91a6-c51d970b09be
-- title:
--   Probability densities on $\mathbb R$: total variation, characteristic functions, moments, truncated Laplace transforms, circle maxima
-- statement:
--   A **probability density** is a measurable, nonnegative, integrable function $f:\mathbb R\to\mathbb R$ with $\int f=1$. It is **supported in $[0,1]$** if it vanishes outside $[0,1]$. Its law is $f(x)\,dx$. The objects defined for such $f,g$ are:
--
--   1. the total variation distance $d_{TV}(f,g)=\sup_A\left|\int_A f-\int_A g\right|$ over Borel sets $A$, which equals $\tfrac12\|f-g\|_{L^1}$;
--   2. the characteristic function (Eqs. (19), (38))
--
--   $$
--   \hat f(t)=\int_{\mathbb R} f(x)\,e^{itx}\,dx ;
--   $$
--
--   3. the moments $m_j=\int x^jf(x)\,dx$;
--   4. the truncated two-sided Laplace transform $H(s)=\int_{-L}^{L}(f(x)-g(x))e^{-sx}\,dx$ for complex $s$ (Eqs. (56), (155));
--   5. for a function $H$ on $\mathbb C$, $M(r)=\max_{|z|=r}|H(z)|$ (Eq. (52)).
--
--   These are the analytic objects of §§2.1 and 4 and Appendix A, in which the circuit's output law is compared with the Haar law through Fourier masses and moments.
--
--   **Formalization Note** Total variation is the reused `tvDist` applied to the laws $f(x)\,dx$, $g(x)\,dx$. $M(r)$ is the supremum of $|H|$ over the circle, which is a maximum for $H$ continuous on the circle. Fourier masses $\int|\hat f-\hat g|^2$ are taken in $[0,\infty]$ in the theorems that use them.
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §2.1, pp. 6–7, Eqs. (19)–(23); §4, pp. 9–12, Eqs. (38), (52), (54), (56); Appendix A, p. 22, Eq. (155); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist

/-!
# Probability densities on the real line, their characteristic functions and moments

Aniruddha Sen, Nick Hunter-Jones, *Local random quantum circuits converge to the Porter-Thomas
distribution in polynomial depth*, STOC 2027 submission #118 (October 2026), §2.1, pp. 6–7
(Eqs. (19)–(23)), §4, pp. 9–13 (Eqs. (38), (52), (54), (56)), Appendix A, p. 22 (Eq. (155)).
-/

noncomputable section

open MeasureTheory

namespace BrickworkPorterThomas.Convergence

/-- A probability density function on `ℝ`: measurable, nonnegative, integrable, total mass `1`. -/
def IsDensity (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ Integrable f ∧ ∫ x, f x = 1

/-- The density vanishes outside `[0, 1]` ("supported in `[0,1]`", Lemmas 4.1, 4.3, A.1). -/
def SupportedInUnit (f : ℝ → ℝ) : Prop :=
  ∀ x, x ∉ Set.Icc (0 : ℝ) 1 → f x = 0

/-- The probability law `f(x) dx` of a density. -/
def densityLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (f x)

/-- Total variation distance `d_TV(f, g) = sup_A |∫_A f − ∫_A g|` over Borel sets `A`, i.e. the
total variation distance of the laws `f(x)dx` and `g(x)dx` (for densities `= ½‖f − g‖_{L¹}`). -/
def dTV (f g : ℝ → ℝ) : ℝ :=
  FoundationsRL.DECLower.tvDist (densityLaw f) (densityLaw g)

/-- Eqs. (19), (38): the characteristic function `f̂(t) = ∫ f(x) e^{itx} dx`. -/
def charDensity (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ x, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ)

/-- The `j`-th moment `m_j = ∫ x^j f(x) dx` of a density. -/
def moment (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x, x ^ j * f x

/-- Eqs. (56), (155): the truncated two-sided Laplace transform
`H(s) = ∫_{-L}^{L} (f(x) − g(x)) e^{−sx} dx`, for complex `s`. -/
def truncLaplace (f g : ℝ → ℝ) (L : ℝ) (s : ℂ) : ℂ :=
  ∫ x in (-L)..L, ((f x - g x : ℝ) : ℂ) * Complex.exp (-(s * (x : ℂ)))

/-- Eq. (52): `M(r) = max_{|z| = r} |H(z)|`, the supremum of `|H|` over the circle of radius `r`
(a maximum whenever `H` is continuous on that circle and `r ≥ 0`). -/
def circleMax (H : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖H z‖) '' Metric.sphere (0 : ℂ) r)

end BrickworkPorterThomas.Convergence


