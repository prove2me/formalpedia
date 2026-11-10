-- Prove2me | Definitions.Def_APSCounting893_Main_RandomReduction
-- name    : APSCounting893_Main_RandomReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:35.365731+00:00
-- url     : https://prove2.me/theorems/d5364bae-a533-4fb7-abab-f8e64d739199
-- title:
--   Independent affine-section and output-projection sampling
-- statement:
--   Every affine coefficient, including its constant term, and every output-projection coefficient is sampled independently and uniformly from a finite set $B\subset\mathbb Q$. A rational affine parametrization of the sampled section is selected by its actual image and injectivity conditions. Failure to define an $r$-plane is counted as failure. Output projection is applied only when $m>r+1$.
--
--   The success event requires the resulting map $\widetilde F:\mathbb C^r\to\mathbb C^{r+1}$ to have image dimension $r$ and to satisfy
--
--   $$\operatorname{APS}(F)\iff\operatorname{APS}(\widetilde F).$$
--
--   Probability is the cardinality ratio in the finite product sample space, not a hypothesis promising good coefficients. The input degree is exactly $d=\max(1,\deg f_1,\ldots,\deg f_m)$. This separates sampled parameters from the unrestricted geometric input domain.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §3.3, Proposition 3.14, p. 14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Geometry

set_option autoImplicit false

namespace APSCounting893.Main

abbrev ReductionLabels (n m r : ℕ) :=
  (Fin (n - r) × Fin (n + 1)) ⊕ (Fin (r + 1) × Fin m)

noncomputable def affineSection {n m r : ℕ} (s : ReductionLabels n m r → ℚ) :
    Set (Affine ℂ n) :=
  {x | ∀ i : Fin (n - r),
    ∑ j : Fin n, (s (.inl (i, j.castSucc)) : ℂ) * x j =
      (s (.inl (i, Fin.last n)) : ℂ)}

abbrev SectionParameter (n r : ℕ) := Matrix (Fin n) (Fin r) ℚ × Affine ℚ n

noncomputable def parameterMap {n r : ℕ} (p : SectionParameter n r) : PolynomialMap ℂ r n :=
  fun i => MvPolynomial.C (p.2 i : ℂ) +
    ∑ j : Fin r, MvPolynomial.C (p.1 i j : ℂ) * MvPolynomial.X j

noncomputable def ParametrizesSection {n m r : ℕ} (s : ReductionLabels n m r → ℚ)
    (p : SectionParameter n r) : Prop :=
  Function.Injective (evaluate (parameterMap p)) ∧
    Set.range (evaluate (parameterMap p)) = affineSection s

/-- Any rational affine parametrization of the sampled plane. If none exists, the choice is
unsuccessful; no success property is stipulated for that case. -/
noncomputable def selectedSectionParameter {n m r : ℕ}
    (s : ReductionLabels n m r → ℚ) : SectionParameter n r :=
  Classical.epsilon (ParametrizesSection s)

noncomputable def reducedPolynomialMap {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (s : ReductionLabels n m r → ℚ) : PolynomialMap ℂ r (r + 1) :=
  let p := parameterMap (selectedSectionParameter s)
  let restricted := fun j => MvPolynomial.eval₂Hom MvPolynomial.C p (F j)
  if h : m = r + 1 then
    fun j => restricted (Fin.cast h.symm j)
  else
    fun i => ∑ j : Fin m, MvPolynomial.C (s (.inr (i, j)) : ℂ) * restricted j

noncomputable def ReductionSucceeds {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (s : ReductionLabels n m r → ℚ) : Prop :=
  ParametrizesSection s (selectedSectionParameter s) ∧
    RSCapacity.algDim (imageClosure (reducedPolynomialMap F s)) = ((r : ℕ∞) : WithBot ℕ∞) ∧
    (hasAPS F ↔ hasAPS (reducedPolynomialMap F s))

/-- Independent uniform coefficients in the finite, nonempty set B, including affine constants. -/
noncomputable def reductionSuccessProbability {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (B : Finset ℚ) : ℝ :=
  (Set.ncard {s : ReductionLabels n m r → {q // q ∈ B} |
      ReductionSucceeds F (fun j => (s j).val)} : ℝ) /
    (Fintype.card (ReductionLabels n m r → {q // q ∈ B}) : ℝ)

noncomputable def inputDegree {n m : ℕ} (F : PolynomialMap ℂ n m) : ℕ :=
  max 1 (Finset.univ.sup (fun i => (F i).totalDegree))

end APSCounting893.Main


