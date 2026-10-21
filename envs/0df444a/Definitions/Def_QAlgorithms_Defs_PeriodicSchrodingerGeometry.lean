-- Prove2me | Definitions.Def_QAlgorithms_Defs_PeriodicSchrodingerGeometry
-- name    : QAlgorithms_Defs_PeriodicSchrodingerGeometry
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:20:23.663246+00:00
-- url     : https://prove2.me/theorems/37d18971-eb1a-4e79-87b5-d6f6cd2286f1
-- title:
--   prove2quantum library: Defs.PeriodicSchrodingerGeometry
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.PeriodicSchrodingerGeometry`), reused by its paper formalizations.
--
--   - `Position`: Implementation helper; source: arxiv-2503.24332v2 PDF p.12.
--   - `simulationBox`: S=[-1/2,1/2]^d in real Euclidean coordinates, d>=1; measure is restricted Lebesgue volume, total mass one. Periodic face identification specified separately. Source: arxiv-2503.24332v2 PDF p.12; arxiv-2503.24332v2 PDF p.13.
--   - `Hilbert`: Abbreviation of complex MeasureTheory.Lp at exponent 2 for Lebesgue volume restricted to S. Continuous representatives retained separately for evaluation. No atomic position ket substitute. Source: arxiv-2503.24332v2 PDF p.12; arxiv-2503.24332v2 PDF p.13.
--   - `restrictedPotential`: Construct g(x)=f(2Rx), R>0 and [−R,R]^d⊆X; optional x₀ translation before choosing x₀=0. Never an unrelated free g. Source: arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.16.
--   - `IsPNormLipschitzOn`: Real p≥1; ‖v‖_p=(∑|v_i|^p)^(1/p); ∀x,y∈X, |f(x)−f(y)|≤G‖x−y‖_p. Match the counting-measure p-norm, not the default function sup norm. Source: arxiv-2503.24332v2 PDF p.11; arxiv-2503.24332v2 PDF p.12.
--   - `HasPeriodicFaces`: Matching values on opposite faces of the source box. The periodic representative on all of R^d is specified separately by IsPeriodicExtension. Source: arxiv-2503.24332v2 PDF pp.14,17.
--   - `IsPeriodicExtension`: A periodic representative on all of R^d; distinct from the matching-face condition on the source box. Source: arxiv-2503.24332v2 PDF pp.14,17 (footnote 4).
--   - `partialDerivative`: Implementation helper; source: arxiv-2503.24332v2 PDF p.12.
--   - `listPartial`: Implementation helper; source: arxiv-2503.24332v2 PDF p.12.
--   - `PartialsExistAt`: Existence of the iterated coordinate derivatives used by a given mixed partial. This uses one-dimensional derivatives along coordinate lines, not a stronger C^k assumption. Source: arxiv-2503.24332v2 PDF p.17, footnote 4.
--   - `multiPartial`: Implementation helper; source: arxiv-2503.24332v2 PDF p.12.
--   - `HasSourceSolutionRegularity`: Opposite-face equality and periodic extension on R^d; true solution is C¹ in x at each t and each existing mixed partial is continuous in t, exactly footnote4. Potential PBC and solution regularity are distinct. Source: arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.17; arxiv-2503.24332v2 PDF p.28.
--   - `IsWeakSobolev`: H^k comprises wavefunctions whose weak partial derivatives up to order k lie in L². Define distributional/periodic weak derivatives, not pointwise derivative defaults. Initial membership H² and H_N is retained. Source: arxiv-2503.24332v2 PDF p.12; arxiv-2503.24332v2 PDF p.13; arxiv-2503.24332v2 PDF p.55; arxiv-2503.24332v2 PDF p.56.
--   - `sobolevSeminorm`: Eq.(2): |φ|_{H^k}²=∑_{|α|=k}∫_S|∂^αφ|², one copy of each multi-index, no multinomial weights. Full source norm squared adds ‖φ‖². On H_N define directly from finite Fourier coefficients and the exact multi-index weight; source mismatch with Laplacian norm requires independent audit. Source: arxiv-2503.24332v2 PDF p.13; arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.59; arxiv-2503.24332v2 PDF p.60; arxiv-2503.24332v2 PDF p.68.
--   - `sobolevNorm`: Source full norm sqrt(norm(phi)_L2^2+sobolevSeminorm(k,phi)^2), with weak derivatives in the stated domain. Homogeneous sum counts each multi-index once. Source: arxiv-2503.24332v2 PDF p.13; arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.59; arxiv-2503.24332v2 PDF p.60; arxiv-2503.24332v2 PDF p.68.
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.PeriodicSchrodingerGeometry

import Mathlib

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open MeasureTheory
namespace QAlgorithms.PeriodicSchrodinger

/-- Implementation helper; source: arxiv-2503.24332v2 PDF p.12. -/
abbrev Position (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- S=[-1/2,1/2]^d in real Euclidean coordinates, d>=1; measure is restricted Lebesgue volume, total mass one. Periodic face identification specified separately. Source: arxiv-2503.24332v2 PDF p.12; arxiv-2503.24332v2 PDF p.13. -/
def simulationBox (d : ℕ) : Set (Position d) := {x | ∀ j, x j ∈ Set.Icc (-1/2 : ℝ) (1/2)}

/-- Abbreviation of complex MeasureTheory.Lp at exponent 2 for Lebesgue volume restricted to S. Continuous representatives retained separately for evaluation. No atomic position ket substitute. Source: arxiv-2503.24332v2 PDF p.12; arxiv-2503.24332v2 PDF p.13. -/
abbrev Hilbert (d : ℕ) := MeasureTheory.Lp ℂ 2 ((volume : Measure (Position d)).restrict (simulationBox d))

/-- Construct g(x)=f(2Rx), R>0 and [−R,R]^d⊆X; optional x₀ translation before choosing x₀=0. Never an unrelated free g. Source: arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.16. -/
def restrictedPotential {d : ℕ} (X : Set (Position d)) (f : Position d → ℝ)
    (R : ℝ) (_hR : 0 < R) (x0 : Position d)
    (_contained : ∀ x ∈ simulationBox d, (2*R) • x+x0 ∈ X) : Position d → ℝ :=
  fun x => f ((2*R) • x+x0)

/-- Real p≥1; ‖v‖_p=(∑|v_i|^p)^(1/p); ∀x,y∈X, |f(x)−f(y)|≤G‖x−y‖_p. Match the counting-measure p-norm, not the default function sup norm. Source: arxiv-2503.24332v2 PDF p.11; arxiv-2503.24332v2 PDF p.12. -/
def IsPNormLipschitzOn {d : ℕ} (X : Set (Position d)) (f : Position d → ℝ) (p G : ℝ) : Prop :=
  1 ≤ p ∧ 0 ≤ G ∧ ∀ x ∈ X, ∀ y ∈ X,
    |f x-f y| ≤ G*(∑ j, |x j-y j|^p)^(1/p)

/-- Matching values on opposite faces of the source box. The periodic representative on
all of R^d is specified separately by IsPeriodicExtension. Source: arxiv-2503.24332v2 PDF pp.14,17. -/
def HasPeriodicFaces {d : ℕ} {V : Type*} (f : Position d → V) : Prop :=
  ∀ j x, x ∈ simulationBox d → x j = -1/2 → f (x+EuclideanSpace.single j 1) = f x

/-- A periodic representative on all of R^d; distinct from the matching-face condition
on the source box. Source: arxiv-2503.24332v2 PDF pp.14,17 (footnote 4). -/
def IsPeriodicExtension {d : ℕ} {V : Type*} (f : Position d → V) : Prop :=
  ∀ j x, f (x+EuclideanSpace.single j 1) = f x

/-- Implementation helper; source: arxiv-2503.24332v2 PDF p.12. -/
def partialDerivative {d : ℕ} (j : Fin d) (f : Position d → ℂ) (x : Position d) : ℂ :=
  deriv (fun t : ℝ => f (x+t • EuclideanSpace.single j 1)) 0

/-- Implementation helper; source: arxiv-2503.24332v2 PDF p.12. -/
def listPartial {d : ℕ} : List (Fin d) → (Position d → ℂ) → Position d → ℂ
  | [], f => f
  | j::rest, f => partialDerivative j (listPartial rest f)

/-- Existence of the iterated coordinate derivatives used by a given mixed partial.
This uses one-dimensional derivatives along coordinate lines, not a stronger C^k assumption.
Source: arxiv-2503.24332v2 PDF p.17, footnote 4. -/
def PartialsExistAt {d : ℕ} : List (Fin d) → (Position d → ℂ) → Position d → Prop
  | [], _, _ => True
  | j::rest, f, x => PartialsExistAt rest f x ∧
      DifferentiableAt ℝ (fun t : ℝ => listPartial rest f (x+t • EuclideanSpace.single j 1)) 0

/-- Implementation helper; source: arxiv-2503.24332v2 PDF p.12. -/
def multiPartial {d : ℕ} (alpha : Fin d → ℕ) (f : Position d → ℂ) : Position d → ℂ :=
  listPartial ((List.finRange d).flatMap fun j => List.replicate (alpha j) j) f

/-- Opposite-face equality and periodic extension on R^d; true solution is C¹ in x at each t and each existing mixed partial is continuous in t, exactly footnote4. Potential PBC and solution regularity are distinct. Source: arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.17; arxiv-2503.24332v2 PDF p.28. -/
def HasSourceSolutionRegularity {d : ℕ} (T : ℝ) (phi : ℝ → Position d → ℂ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ 1 (phi t) ∧ IsPeriodicExtension (phi t)) ∧
    ∀ axes : List (Fin d), ∀ x ∈ simulationBox d,
      (∀ t ∈ Set.Icc (0 : ℝ) T, PartialsExistAt axes (phi t) x) →
      ContinuousOn (fun t => listPartial axes (phi t) x) (Set.Icc 0 T)

/-- H^k comprises wavefunctions whose weak partial derivatives up to order k lie in L². Define distributional/periodic weak derivatives, not pointwise derivative defaults. Initial membership H² and H_N is retained. Source: arxiv-2503.24332v2 PDF p.12; arxiv-2503.24332v2 PDF p.13; arxiv-2503.24332v2 PDF p.55; arxiv-2503.24332v2 PDF p.56. -/
def IsWeakSobolev {d : ℕ} (k : ℕ) (phi : Hilbert d) : Prop :=
  ∃ derivatives : (Fin d → ℕ) → Hilbert d,
    derivatives 0 = phi ∧ ∀ alpha, (∑ j, alpha j) ≤ k →
      ∀ test : Position d → ℂ, ContDiff ℝ ⊤ test → IsPeriodicExtension test →
        (∫ x, (derivatives alpha) x*test x ∂(volume.restrict (simulationBox d))) =
          (-1 : ℂ)^(∑ j, alpha j) *
            (∫ x, phi x*multiPartial alpha test x ∂(volume.restrict (simulationBox d)))

/-- Eq.(2): |φ|_{H^k}²=∑_{|α|=k}∫_S|∂^αφ|², one copy of each multi-index, no multinomial weights. Full source norm squared adds ‖φ‖². On H_N define directly from finite Fourier coefficients and the exact multi-index weight; source mismatch with Laplacian norm requires independent audit. Source: arxiv-2503.24332v2 PDF p.13; arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.59; arxiv-2503.24332v2 PDF p.60; arxiv-2503.24332v2 PDF p.68. -/
def sobolevSeminorm {d : ℕ} (k : ℕ) (phi : Hilbert d) (h : IsWeakSobolev k phi) : ℝ :=
  Real.sqrt (∑ alpha ∈ (Fintype.piFinset fun _ : Fin d => Finset.range (k+1)).filter
    (fun alpha => ∑ j, alpha j = k), ‖h.choose alpha‖^2)

/-- Source full norm sqrt(norm(phi)_L2^2+sobolevSeminorm(k,phi)^2), with weak derivatives in the stated domain. Homogeneous sum counts each multi-index once. Source: arxiv-2503.24332v2 PDF p.13; arxiv-2503.24332v2 PDF p.14; arxiv-2503.24332v2 PDF p.59; arxiv-2503.24332v2 PDF p.60; arxiv-2503.24332v2 PDF p.68. -/
def sobolevNorm {d : ℕ} (k : ℕ) (phi : Hilbert d) (h : IsWeakSobolev k phi) : ℝ :=
  Real.sqrt (‖phi‖^2+sobolevSeminorm k phi h^2)

example (d : ℕ) : (0 : Position d) ∈ simulationBox d := by
  intro j
  norm_num

example {d : ℕ} (f : Position d → ℂ) : multiPartial 0 f = f := by
  unfold multiPartial
  have h : (List.finRange d).flatMap (fun j => List.replicate ((0 : Fin d → ℕ) j) j) = [] := by
    induction (List.finRange d) with
    | nil => rfl
    | cons j rest ih => simpa using ih
  rw [h]
  rfl

end QAlgorithms.PeriodicSchrodinger


