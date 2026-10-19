-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
-- name    : OAI_Analysis_Littlewood_QuadraticTail
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:59:00.240092+00:00
-- url     : https://prove2.me/theorems/ccc67e21-7dd7-4f53-b04e-041a18ffb759
-- title:
--   Quadratic phases, oscillatory integrals, periodized chirps, and truncated chirp Fourier series
-- statement:
--   Throughout, $e(\theta)=e^{2\pi i\theta}$ for $\theta\in\mathbb{R}$, $\mathbb{T}=\mathbb{R}/\mathbb{Z}$, and $g:\mathbb{R}\to\mathbb{C}$ is an amplitude. The parameters $t$ (curvature), $u$ (linear frequency), $T$ (scale) and $\beta$ (slope) are real numbers.
--
--   1. **Quadratic phase.** $\varphi_{t,u}(x)=e\bigl(\tfrac{t x^2}{2}-u x\bigr)$ for $x\in\mathbb{R}$. The phase is stationary where $tx-u=0$, i.e. at $x=u/t$ when $t\ne0$.
--
--   2. **Divided amplitude.** For $k\in\mathbb{N}$, $a_{g,t,u,k}(x)=g(x)/(t x-u)^k$.
--
--   3. **Oscillatory integral.**
--   $$
--   I_k(g;t,u)=\int_{\mathbb{R}}\frac{g(x)}{(tx-u)^k}\,e\Bigl(\frac{t x^2}{2}-u x\Bigr)\,dx .
--   $$
--
--   4. **Periodized chirp.** $C_{g,t}:\mathbb{T}\to\mathbb{C}$ is the $1$-periodic function that agrees with $x\mapsto g(x)\,e(t x^2/2)$ on the interval $(-\tfrac12,\tfrac12]$.
--
--   5. **Lattice weight.** $w(m)=1/(1+|m|)^2$ for $m\in\mathbb{Z}$; it is summable over $\mathbb{Z}$.
--
--   6. **Box.** $\mathrm{Box}(T,\beta)=\{m\in\mathbb{Z}:\ |m|\le\lfloor T|\beta|/2\rfloor\}$, the integer interval from $-\lfloor T|\beta|/2\rfloor$ to $\lfloor T|\beta|/2\rfloor$.
--
--   7. **Row truncation.** For $z\in\mathbb{T}$,
--   $$
--   R_{g,T,\beta}(z)=\sum_{m\in\mathrm{Box}(T,\beta)}\Bigl(\int_{\mathbb{R}}g(x)\,e\Bigl(\frac{T\beta x^2}{2}-m x\Bigr)dx\Bigr)\,e(m z).
--   $$
--
--   If $g$ is supported in $[-\alpha,\alpha]$ with $\alpha<\tfrac12$, the $m$-th Fourier coefficient of $C_{g,t}$ equals $\int g(x)\,e(t x^2/2-m x)\,dx$, so $R_{g,T,\beta}$ is the partial Fourier series of the chirp $C_{g,T\beta}$ over the frequencies $|m|\le T|\beta|/2$, namely those whose stationary point $m/(T\beta)$ lies in $[-\tfrac12,\tfrac12]$. Repeated integration by parts in $I_k$ shows that, for smooth compactly supported $g$ and $\beta\ne0$, the coefficients outside the box decay faster than any power of $T$, with the summable profile $w(m)$; consequently $R_{g,T,\beta}$ approximates $C_{g,T\beta}$ uniformly on $\mathbb{T}$ with error $O(1/T)$ for $T\ge1$, and, when $|g|\le1$, the retained squared Fourier mass is at least $\int|g|^2-O(1/T)$. These are the one-dimensional inputs of the Fourier-spreading construction.
--
--   **Formalization Note** `phase t u x` is `Complex.exp (Complex.I * (2π(t x²/2 − u x) : ℝ))`. `amp g t u k x` uses complex division, so at a point with $tx=u$ and $k\ge1$ it equals $0$ by the convention $a/0=0$ (for $k=0$ it is $g(x)$); `osc g t u k` is the integral of `amp g t u k * phase t u`. `circleChirp` is built with `AddCircle.liftIoc 1 (-1/2)`, `fourier m z` is $e(mz)$, and `box T β` is `Finset.Icc (-⌊T|β|/2⌋) ⌊T|β|/2⌋`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

def phase (t u x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2*Real.pi*(t*x^2/2-u*x) : ℝ))

def amp (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  g x / ((t*x-u : ℝ) : ℂ)^k

def osc (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) : ℂ :=
  ∫ x : ℝ, amp g t u k x * phase t u x

def circleChirp (g : ℝ → ℂ) (t : ℝ) : UnitAddCircle → ℂ :=
  AddCircle.liftIoc 1 (-1/2) (fun x ↦ g x*phase t 0 x)

def latticeWeight (w : ℤ) : ℝ := 1/(1+|(w:ℝ)|)^2

noncomputable def box (T β : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋

def rowTrunc (g : ℝ → ℂ) (T β : ℝ) (z : UnitAddCircle) : ℂ :=
  ∑ w ∈ box T β, (∫ x : ℝ, g x*phase (T*β) w x)*fourier w z

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI


