-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_RandomCayley
-- name    : FiniteGroupTesting_LinearQuery_RandomCayley
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:51.062705+00:00
-- url     : https://prove2.me/theorems/9c7e3b26-3fc1-4994-8f16-373d43122ea8
-- title:
--   Symmetric random Cayley walks and simultaneous short words
-- statement:
--   For a finite group $H$ and sampled tuple $(a_1,\ldots,a_k)$, retain each sample and its inverse with multiplicity and use right multiplication. Acting on real functions,
--
--   $$(Pf)(x)=\frac1{2k}\sum_i\bigl(f(xa_i)+f(xa_i^{-1})\bigr).$$
--
--   Expansion is the inequality $\|(P-J/n)f\|_2\le\lambda\|f\|_2$ for every real vector, with $J/n$ defined by averaging over all group elements. This includes absolute negative eigenvalues. At zero samples the identity kernel supplies the singleton boundary case. The short-word event provides, simultaneously for every group element, a product of sampled elements and inverses within the real length bound. The later spectral accuracy is fixed once as $1/3000$.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 13–14, 44–45, §2.3 and Appendix A

import Definitions.Def_FiniteGroupTesting_LinearQuery_TableModel

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

/-- Symmetric multiset walk. Repetitions are retained. For zero samples the identity kernel
completes the singleton case; all non-singleton theorem instances have a positive sample count. -/
noncomputable def rightCayley {H : Type*} [Group H] {k : ℕ} (a : Fin k → H)
    (f : H → ℝ) (x : H) : ℝ :=
  if k = 0 then f x else (∑ i : Fin k, (f (x * a i) + f (x * (a i)⁻¹))) / (2 * k : ℝ)

noncomputable def euclideanNorm {H : Type*} [Fintype H] (f : H → ℝ) : ℝ :=
  Real.sqrt (∑ x : H, f x ^ 2)

/-- Exactly ||P-J/n||_{2->2} <= lambda, expressed on every real vector, hence including
absolute negative as well as positive nontrivial eigenvalues, without an empty supremum. -/
def CayleyExpansion {H : Type*} [Group H] [Fintype H] {k : ℕ}
    (a : Fin k → H) (lam : ℝ) : Prop :=
  ∀ f : H → ℝ,
    euclideanNorm (fun x => rightCayley a f x - (∑ y : H, f y) / Fintype.card H) ≤
      lam * euclideanNorm f

def ShortWords {H : Type*} [Group H] {k : ℕ} (a : Fin k → H) (lengthBound : ℝ) : Prop :=
  ∀ x : H, ∃ word : List H,
    (word.length : ℝ) ≤ lengthBound ∧ word.prod = x ∧
      ∀ s ∈ word, ∃ i : Fin k, s = a i ∨ s = (a i)⁻¹

/-- The submission fixes this accuracy before later spectral invocations. -/
noncomputable def spectralAccuracy : ℝ := 1 / 3000

end FiniteGroupTesting.LinearQuery


