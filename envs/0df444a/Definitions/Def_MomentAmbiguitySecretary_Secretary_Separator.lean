-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator
-- name    : MomentAmbiguitySecretary_Secretary_Separator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:17.338836+00:00
-- url     : https://prove2.me/theorems/8f742ef5-6e17-4dc6-b4f9-776d8cb03722
-- title:
--   Geometric entire product, occupancy coefficients and atomic residue measures
-- statement:
--   For integers $B,N\ge2$, define
--
--   $$G_{N,M}(z)=\prod_{a=0}^M\sum_{u=0}^{N-1}(zB^{-a})^u,\quad G_N(z)=\prod_{a\ge0}\sum_{u=0}^{N-1}(zB^{-a})^u.$$
--
--   Finite and limiting Taylor coefficients are computed at zero. Finite occupancy sums use digits $0\le c_a<N$ of total degree $j$; infinite occupancies are finitely supported sequences of that same total degree. Put
--
--   $$W_h(t)=\sum_{j\equiv h\pmod N}w_j B^{tj},\quad W=W_0(0),\quad \mu_h=\sum_{j\equiv h\pmod N}\frac{w_j}{W}\delta_{B^j}.$$
--
--   The raw atomic measures are constructed from these formulas; their probability, moment and support properties are theorem conclusions. For $j=L(N-1)+b$, $0\le b<N-1$, define $e(j)=(N-1)L(L-1)/2+Lb$. The signed quantity $j-e(j)$ is evaluated in the integers. The minimum designated-atom mass ranges over all $h<N$.
--
--   This shared definition layer does not assume convergence, normalization, equal moments or coefficient bounds. Formula declarations were adapted from the authors' repository at commit c90f06745a1b6a248e7147eaf4ec2403700b713f; the cited pinned PDF supplies the mathematical specifications.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, §3.2 and §8.2, PDF/printed p.8,29–34, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Laws

open scoped NNReal

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace MomentAmbiguitySecretary.Secretary

noncomputable section

/-- Formula definitions adapted from the authors' NWayCoefficients module, commit
c90f06745a1b6a248e7147eaf4ec2403700b713f. The source remains the pinned preprint. -/
def factor (B N m : ℕ) (z : ℂ) : ℂ :=
  ∑ u : Fin N, (z * (B : ℂ)⁻¹ ^ m) ^ (u : ℕ)

def finiteProduct (B N M : ℕ) (z : ℂ) : ℂ :=
  ∏ m : Fin (M + 1), factor B N m z

def entireProduct (B N : ℕ) (z : ℂ) : ℂ := ∏' m : ℕ, factor B N m z

def finiteTaylor (B N M j : ℕ) : ℂ :=
  (j.factorial : ℂ)⁻¹ * iteratedDeriv j (finiteProduct B N M) 0

def coefficient (B N j : ℕ) : ℝ :=
  ((j.factorial : ℂ)⁻¹ * iteratedDeriv j (entireProduct B N) 0).re

abbrev FiniteDigits (N M : ℕ) := Fin (M + 1) → Fin N

def digitTotal {N M : ℕ} (c : FiniteDigits N M) : ℕ := ∑ m, (c m : ℕ)
def digitExponent {N M : ℕ} (c : FiniteDigits N M) : ℕ :=
  ∑ m : Fin (M + 1), (m : ℕ) * (c m : ℕ)

def finiteOccupancySum (B N M j : ℕ) : ℝ :=
  ∑ c : FiniteDigits N M,
    if digitTotal c = j then ((B : ℝ)⁻¹) ^ digitExponent c else 0

/-- Finite support is part of the type; no default-valued natural infinite sum is used. -/
abbrev Occupancy (N j : ℕ) :=
  {c : ℕ →₀ ℕ // (∀ m, c m < N) ∧ c.sum (fun _ u => u) = j}

def occupancyExponent {N j : ℕ} (c : Occupancy N j) : ℕ :=
  c.val.sum (fun m u => m * u)

def residueTerm (B N h t j : ℕ) : ℝ :=
  if j % N = h then coefficient B N j * (B : ℝ) ^ (t * j) else 0

def residueSum (B N h t : ℕ) : ℝ := ∑' j : ℕ, residueTerm B N h t j
def normalizer (B N : ℕ) : ℝ := residueSum B N 0 0

def exponent (N j : ℕ) : ℕ :=
  let L := j / (N - 1)
  let b := j % (N - 1)
  (N - 1) * L * (L - 1) / 2 + L * b

def residueSupport (B N h : ℕ) : Set ℝ≥0 :=
  {x | ∃ j : ℕ, j % N = h ∧ x = (B : ℝ≥0) ^ j}

/-- The raw countable atomic measure. Probability and all-moment properties are conclusions. -/
def residueMeasure (B N h : ℕ) : Measure ℝ≥0 :=
  Measure.sum fun j : ℕ =>
    ENNReal.ofReal (if j % N = h then coefficient B N j / normalizer B N else 0) •
      Measure.dirac ((B : ℝ≥0) ^ j)

def coefficientProfile (B N : ℕ) : Prop :=
  ∀ j : ℕ,
    (B : ℝ) ^ (-(exponent N j : ℤ)) ≤ coefficient B N j ∧
    coefficient B N j ≤ (2 : ℝ) ^ j * (B : ℝ) ^ (-(exponent N j : ℤ)) ∧
    (j : ℤ) - (exponent N j : ℤ) ≤ (N : ℤ) - 1 ∧
    ((j : ℤ) - (exponent N j : ℤ) = (N : ℤ) - 1 ↔ N - 1 ≤ j ∧ j ≤ 2 * N - 2)

def minimumFirstAtom (B N : ℕ) : ℝ :=
  if hN : 0 < N then
    letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    Finset.univ.inf' Finset.univ_nonempty
      (fun h : Fin N => (residueMeasure B N h.val {((B : ℝ≥0) ^ h.val)}).toReal)
  else 0

end
end MomentAmbiguitySecretary.Secretary


