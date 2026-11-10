-- Prove2me | Definitions.Def_SYKFastMix_FastMixing_Coefficients
-- name    : SYKFastMix_FastMixing_Coefficients
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:07:13.685136+00:00
-- url     : https://prove2.me/theorems/712353bf-d1fd-4310-bddd-7c4f48b5e99f
-- title:
--   Exact fermionic, block, and ambient classical Taylor coefficients
-- statement:
--   Use the same SYK disorder and Hamiltonian. For every integer $m\ge0$, the fermionic coefficient is
--   $$(F_m)_{ji}=\frac{(-1)^m}{2m!}\{\gamma_i,\operatorname{ad}_H^m(\gamma_j)\}.$$
--   The coefficient $M_m=[s^m]M(\gamma(s),\gamma(-s))$ is defined by the finite convolution of the exponential coefficients in the two arguments. In particular, its second argument has the opposite time sign.
--
--   For $x\in\mathbb R^N$ let $G_w(x)=\sum_{|A|=4}w_A\prod_{i\in A}x_i$, and let $V_wf=2\nabla G_w\cdot\nabla f$. Define the classical coefficient in ambient continuous coordinates by
--   $$(\widetilde F_m(\sigma))_{ji}=\frac1{m!}\partial_{x_i}(V_w^m x_j)\big|_{x=\sigma}.$$
--   The derivative is the actual Fréchet derivative applied to a coordinate vector. These expressions define coefficients at every degree without assuming global existence of the polynomial flow. Trace moments mean $\operatorname{Tr}[(T^\dagger T)^p]$, with the trace on the full space of the matrix $T$.
--
--   These definitions separate algebraic coefficient comparison from Taylor convergence. **Formalization Note** Real classical matrices are embedded into complex matrices without changing their Euclidean norms or trace moments. The two block dimensions are $Nd$ and $Nd^2$.
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), pp.24–26, Eqs. (5.2), (5.4)–(5.8), (5.19)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Model

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory

namespace SYKFastMix.FastMixing
variable {N : ℕ}

def gammaCoefficient (Q : Model N) (w : Disorder N) (m : ℕ) (i : Fin N) : Mat (SiteHilbert N) :=
  (((-1 : ℂ)^m) / (m.factorial : ℂ)) • applySuper ((ad (hamiltonian Q w))^m) (Q.γ i)

def fermionCoefficient (Q : Model N) (w : Disorder N) (m : ℕ) : Mat (Fin N × SiteHilbert N) :=
  fun a b => ((1 / 2 : ℂ) • anticomm (Q.γ b.1) (gammaCoefficient Q w m a.1)) a.2 b.2

/-- Exact product/convolution formula for [s^m]M(γ(s),γ(-s)); no convergence hypothesis. -/
def mCoefficient (Q : Model N) (w : Disorder N) (m : ℕ) : Mat (Fin N × (SiteHilbert N × SiteHilbert N)) :=
  fun a b => ∑ r ∈ Finset.range (m + 1),
    mBlock w (gammaCoefficient Q w r) (fun i => (-1 : ℂ)^r • gammaCoefficient Q w r i)
      (gammaCoefficient Q w (m-r)) (fun i => (-1 : ℂ)^(m-r) • gammaCoefficient Q w (m-r) i)
      a.1 b.1 a.2 b.2

/-- The ambient classical variables range over all ℝ^N, not just the Ising points. -/
def classicalG (w : Disorder N) (x : Fin N → ℝ) : ℝ :=
  ∑ A : SYKEdge.KSet N 4, w A * ∏ i ∈ A.1, x i

def coordinateDerivative (f : (Fin N → ℝ) → ℝ) (i : Fin N) (x : Fin N → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

def classicalGenerator (w : Disorder N) (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  2 * ∑ i, coordinateDerivative (classicalG w) i x * coordinateDerivative f i x

def classicalIterate (w : Disorder N) (m : ℕ) (j : Fin N) : (Fin N → ℝ) → ℝ :=
  (classicalGenerator w)^[m] (fun x => x j)

def classicalCoefficient (w : Disorder N) (m : ℕ) (σ : Fin N → ℝ) : Mat (Fin N) :=
  fun j i => (coordinateDerivative (classicalIterate w m j) i σ / (m.factorial : ℝ) : ℂ)

def traceMoment {ι : Type} [Fintype ι] [DecidableEq ι] (p : ℕ) (A : Mat ι) : ℝ :=
  (Matrix.trace ((Aᴴ * A)^p)).re

end SYKFastMix.FastMixing


