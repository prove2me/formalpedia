-- Prove2me | Definitions.Def_SoSPlantedCSP_Reduction_SoS
-- name    : SoSPlantedCSP_Reduction_SoS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:19.372765+00:00
-- url     : https://prove2.me/theorems/bcaf1d71-8145-4189-b4be-076a6c0f02ad
-- title:
--   Pseudo-expectations over the hypercube, $\mathrm{SoS}_d$, and the refutation hypothesis
-- statement:
--   Let $\mathbb R[x_1,\dots,x_n]_{\le t}$ be the real polynomials of degree at most $t$.
--
--   **Definition 2.2.** A degree-$d$ **pseudo-expectation** over $\{-1,1\}^n$ is a linear functional $\tilde{\mathbb E}$ on polynomials with
--
--   1. (Normalization) $\tilde{\mathbb E}[1]=1$;
--   2. (Booleanity) $\tilde{\mathbb E}[f\,x_i^2]=\tilde{\mathbb E}[f]$ for all $i\in[n]$ and all $f\in\mathbb R[x]_{\le d-2}$;
--   3. (Positivity) $\tilde{\mathbb E}[f^2]\ge0$ for all $f\in\mathbb R[x]_{\le d/2}$.
--
--   $\mathrm{SoS}_d$ is the set of all degree-$d$ pseudo-expectations. Every point evaluation $f\mapsto f(x)$ with $x\in\{-1,1\}^n$ belongs to $\mathrm{SoS}_d$.
--
--   **Refutation hypothesis.** For a hypergraph $\mathcal H$ with $m$ hyperedges, a degree parameter $\ell$ and a threshold $\delta$, degree-$2\ell$ sum-of-squares refutes $\mathrm{XOR}(\mathcal H,1^n,0)$ at level $\delta$ if
--   $$\Pr_{\Phi\sim\mathrm{XOR}(\mathcal H,1^n,0)}\Big[\max_{\tilde{\mathbb E}\in\mathrm{SoS}_{2\ell}}\tilde{\mathbb E}[\Phi(x)]\le\frac12+\delta\Big]\ge1-\frac1{mn}.$$
--   Under $\mathrm{XOR}(\mathcal H,1^n,0)$ the right-hand sides are independent uniform signs. Theorem 3.1 uses $\delta=\gamma\hat\varepsilon/(720\log(mn))$ and Lemma 3.5 uses $\delta=\hat\varepsilon\gamma/18$.
--
--   **Formalization Note** $\tilde{\mathbb E}$ is a linear functional on the whole polynomial ring whose conditions involve only polynomials of degree $\le d$; every functional on the degree-$\le d$ part extends to the whole ring and its values on degree-$\le d$ polynomials do not depend on the extension, so the statements "$\tilde{\mathbb E}[\Phi]\le c$ for all $\tilde{\mathbb E}\in\mathrm{SoS}_d$" coincide. The maximum is stated as "for every $\tilde{\mathbb E}$". The paper requires $d\ge2$; the definition is written for every $d$ and used only with $d=2\ell\ge2$. Degrees $d-2$ and $d/2$ are natural-number subtraction and division, exact for $d=2\ell\ge2$.
-- source:
--   Arpon Basu, Andrew D. Lin, Peter Manohar, STOC 2027 submission #544 (October 2026), Definition 2.2, p. 9 (PDF p. 11); refutation hypotheses of Theorem 3.1, p. 10 (PDF p. 12), and Lemma 3.5, p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_SoSPlantedCSP_Reduction_KXOR

namespace SoSPlantedCSP.Reduction

/-!
# Pseudo-expectations over the hypercube and the refutation hypothesis

Basu–Lin–Manohar, STOC 2027 submission #544 (October 2026): Definition 2.2 (pseudo-expectations
over the hypercube), printed p. 9 (PDF p. 11); the refutation hypothesis of Theorem 3.1
(printed p. 10, PDF p. 12) and of Lemma 3.5 (printed p. 11, PDF p. 13).

**Formalization Note** The paper's pseudo-expectation is a linear functional on the polynomials
of degree `≤ d`. Here it is a linear functional on all of `ℝ[x_1, …, x_n]` whose three
conditions only involve polynomials of degree `≤ d`; every functional on the degree-`≤ d` part
extends linearly to the whole ring, and the value on a polynomial of degree `≤ d` depends only on
the restriction, so "for every `Ẽ ∈ SoS_d`, `Ẽ[Φ] ≤ c`" (for `Φ` of degree `≤ d`) means the same in
both formulations. The definition is stated for every `d`; the paper requires `d ≥ 2`, and the
mission only uses `d = 2ℓ` with `ℓ ≥ 1`. The maximum `max_{Ẽ ∈ SoS_d} Ẽ[Φ] ≤ c` is stated as
`∀ Ẽ ∈ SoS_d, Ẽ[Φ] ≤ c`.
-/

/-- Definition 2.2: `E` is a degree-`d` pseudo-expectation over `{−1, 1}^n`:
(1) normalization `Ẽ[1] = 1`; (2) booleanity `Ẽ[f x_i²] = Ẽ[f]` for every `i` and every `f` of
degree `≤ d − 2`; (3) positivity `Ẽ[f²] ≥ 0` for every `f` of degree `≤ d/2`. -/
structure IsPseudoExp (n d : ℕ) (E : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) : Prop where
  /-- Normalization. -/
  normalized : E 1 = 1
  /-- Booleanity. -/
  boolean : ∀ (i : Fin n) (f : MvPolynomial (Fin n) ℝ), f.totalDegree ≤ d - 2 →
    E (f * MvPolynomial.X i ^ 2) = E f
  /-- Positivity. -/
  positive : ∀ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ d / 2 → 0 ≤ E (f ^ 2)

/-- `SoS_d`: the set of degree-`d` pseudo-expectations over `{−1, 1}^n`. -/
def SoS (n d : ℕ) : Set (MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) :=
  {E | IsPseudoExp n d E}

/-- The refutation hypothesis with threshold `δ`: with probability at least `1 − 1/(mn)` over
`Φ ∼ XOR(ℋ, 1ⁿ, 0)` (uniformly random right-hand sides), every degree-`2ℓ` pseudo-expectation
satisfies `Ẽ[Φ(x)] ≤ 1/2 + δ`. Theorem 3.1 uses `δ = γ ε̂ / (720 log(mn))`, Lemma 3.5 uses
`δ = ε̂ γ / 18`. -/
def RefutationHyp {n m : ℕ} (H : Fin m → Finset (Fin n)) (ℓ : ℕ) (δ : ℝ) : Prop :=
  1 - 1 / ((m : ℝ) * n) ≤
    prob (xorMass H (fun _ => 1) 0)
      (fun b => ∀ E ∈ SoS n (2 * ℓ), E (instancePoly H b) ≤ 1 / 2 + δ)

end SoSPlantedCSP.Reduction


