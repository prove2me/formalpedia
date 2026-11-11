-- Prove2me | Definitions.Def_OrderedSearchExact_Exact_Analysis
-- name    : OrderedSearchExact_Exact_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:04.742713+00:00
-- url     : https://prove2.me/theorems/a337de59-af10-4112-9697-d9792c895155
-- title:
--   Determinants, continuum certificates and quartic endpoint integrals
-- statement:
--   For positive finite rates, $U_\lambda(\theta)=\sinh(\lambda/n)/(\cosh(\lambda/n)-\cos\theta)$ and $V_\lambda(\theta)=-\sin\theta/(\cosh(\lambda/n)-\cos\theta)$. The two diagonal terms and cross term are the expectations in (21); the determinant condition squares the expected difference of the $V$ terms.
--
--   For a density $h$, put
--
--   $$a_h(x)=\int_{\mathbb R}\frac{h(y)}{2\cosh(x-y)}\,dy,\quad b_h(x)=\int_{\mathbb R}\frac{h(y)}{1+e^{2(y-x)}}\,dy.$$
--
--   The continuum certificate is (28), at every real $x$. The quartic density is $h_W(y)=\cos^4(\pi y/(2W))\mathbf1[|y|<W]/(3W/4)$ for $W>0$. Write $\ell(u)=(1+\tanh u)/2$ and $L_d(u)=\ell(u)-\ell(u-d)$. The endpoint quantities are $A_r(x)=\int_0^\infty s^r/\cosh(x+s)\,ds$ and $D_{4,d}(x)=\int_0^\infty s^4L_d(x+s)\,ds$. The endpoint ratio is $D_{4,d}/\sqrt{A_4(x)A_4(x-d)}$.
--
--   The decay-constant predicate spells out the sufficient numerical criterion from the proof of Lemma 4.12, uniformly for $n\ge2$: $D>0$ and $4/((e^D-1)(1-e^{-4D}))<1$. The formulas use full Lebesgue integrals, not truncations.
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), (20)–(22), (27)–(33); Lemma 4.12 proof, p.15–19, 22 (PDF p.15–19, 22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Packets

open MeasureTheory

namespace OrderedSearchExact.Exact

noncomputable def U (n : ℕ) (lam θ : ℝ) : ℝ :=
  Real.sinh (lam / n) / (Real.cosh (lam / n) - Real.cos θ)

noncomputable def V (n : ℕ) (lam θ : ℝ) : ℝ :=
  -Real.sin θ / (Real.cosh (lam / n) - Real.cos θ)

noncomputable def diagS (n : ℕ) (h : ℝ → ℝ) (β θ : ℝ) : ℝ :=
  expectation h (fun y => Real.tanh (β * Real.exp y / 2) * U n (β * Real.exp y) θ)

noncomputable def diagA (n : ℕ) (h : ℝ → ℝ) (α θ : ℝ) : ℝ :=
  expectation h (fun y => (Real.tanh (α * Real.exp y / 2))⁻¹ * U n (α * Real.exp y) θ)

noncomputable def crossTerm (n : ℕ) (h : ℝ → ℝ) (α β θ : ℝ) : ℝ :=
  expectation h (fun y => V n (α * Real.exp y) θ - V n (β * Real.exp y) θ)

def DeterminantCondition (n : ℕ) (h : ℝ → ℝ) (α β : ℝ) : Prop :=
  ∀ θ, crossTerm n h α β θ ^ 2 ≤ 4 * diagS n h β θ * diagA n h α θ

noncomputable def convA (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, h y / (2 * Real.cosh (x - y))

noncomputable def convB (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, h y / (1 + Real.exp (2 * (y - x)))

def Certificate (h : ℝ → ℝ) (d ρ : ℝ) : Prop :=
  ∀ x, convB h x - convB h (x - d) ≤ 2 * ρ * Real.sqrt (convA h x * convA h (x - d))

noncomputable def quarticDensity (W y : ℝ) : ℝ :=
  if |y| < W then Real.cos (Real.pi * y / (2 * W)) ^ 4 / (3 * W / 4) else 0

noncomputable def logistic (u : ℝ) : ℝ := (1 + Real.tanh u) / 2

noncomputable def logisticDifference (d u : ℝ) : ℝ := logistic u - logistic (u - d)

noncomputable def endpointA (r x : ℝ) : ℝ :=
  ∫ v in Set.Ici (0 : ℝ), v ^ r / Real.cosh (x + v)

noncomputable def endpointD (d x : ℝ) : ℝ :=
  ∫ v in Set.Ici (0 : ℝ), v ^ 4 * logisticDifference d (x + v)

noncomputable def endpointRatio (d x : ℝ) : ℝ :=
  endpointD d x / Real.sqrt (endpointA 4 x * endpointA 4 (x - d))

/-- The numerical decay criterion in the proof of Lemma 4.12, uniformly for n≥2.
It is met by D=2. -/
def DecayConstant (D : ℝ) : Prop :=
  0 < D ∧ 4 / ((Real.exp D - 1) * (1 - Real.exp (-4 * D))) < 1

end OrderedSearchExact.Exact


