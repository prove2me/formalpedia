-- Prove2me | Definitions.Def_AgnGaussTomo_IsSeededProjective
-- name    : AgnGaussTomo_IsSeededProjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:10.945386+00:00
-- url     : https://prove2.me/theorems/ea0be07b-5922-4e11-b131-06405d20d33e
-- title:
--   Single-copy projective measurements with a random seed
-- statement:
--   A POVM with outcomes $(s,k)$ in finite sets is **seeded projective** if there are probabilities $p_s$ and, for each seed $s$, orthogonal projections $Q_{s,k}$ with $\sum_kQ_{s,k}=I$, such that the effect of outcome $(s,k)$ is $p_s\,Q_{s,k}$: a seed $s$ is drawn with probability $p_s$ and recorded, and then the projective measurement $\{Q_{s,k}\}_k$ is performed. A scheme **uses single-copy projective measurements** if every round is seeded projective.
--
--   This is the measurement model of the direct gradient estimator (Lemma 3.16), which on each copy draws a random phase $s\in\{\pm1,\pm i\}$ and measures in a corresponding orthonormal basis of the two-photon subspace.
--
--   **Formalization Note** The seed is part of the outcome; a mixture of projective measurements with the seed forgotten is a general POVM. Projections are Hermitian and idempotent Fock-basis arrays.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.16, printed p. 24 (PDF p. 27) and its proof, p. 25 (PDF p. 28)

import Mathlib
import Definitions.Def_BosonicLearn_AdaptiveScheme

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **A single-copy projective measurement with a classical random seed.** Arulandu, Chen, Chen, Li,
Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026),
Lemma 3.16, printed p. 24 (PDF p. 27): "using … single-copy projective measurements"; its proof
(p. 25): "suppose on each copy we independently draw a random s and then measure
{|v_{sk}⟩⟨v_{sk}|}_{k=0}^{d−1} ∪ {I − Π}".

A POVM with outcomes `(s, k) ∈ Fin a × Fin b` is seeded projective if there are probabilities
`p_s` and, for each seed `s`, a projection-valued measure `{Q_{s,k}}_k` (orthogonal projections
summing to `I`) such that the effect of the outcome `(s, k)` is `p_s Q_{s,k}`: a seed `s` is drawn
with probability `p_s`, recorded, and then the projective measurement `{Q_{s,k}}_k` is performed.

**Formalization Note.** The seed is part of the outcome; a mixture of projective measurements
whose seed is forgotten would be a general POVM, so recording it is what makes "projective"
meaningful. Projections are Fock-basis arrays that are Hermitian (`Q_ij = conj Q_ji`) and
idempotent (`Σ_l Q_il Q_lj = Q_ij`, a series over the Fock basis). -/
def IsSeededProjective {n a b : ℕ}
    (M : BosonicLearn.FockPOVM (Occupation (Fin n)) (Fin a × Fin b)) : Prop :=
  ∃ (p : Fin a → ℝ) (Q : Fin a → Fin b → Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ),
    (∀ s, 0 ≤ p s) ∧ ∑ s, p s = 1 ∧
    (∀ s k i j, Q s k i j = star (Q s k j i)) ∧
    (∀ s k i j, ∑' l, Q s k i l * Q s k l j = Q s k i j) ∧
    (∀ s, ∑ k, Q s k = 1) ∧
    ∀ s k, M.effect {(s, k)} = (p s : ℂ) • Q s k

/-- **A scheme of single-copy projective measurements** (Lemma 3.16): every round's POVM is
seeded projective. -/
def IsProjectiveScheme {n N a b : ℕ} (S : BosonicLearn.AdaptiveScheme n N (Fin a × Fin b)) :
    Prop :=
  ∀ (t : Fin N) (x : Fin t → Fin a × Fin b), IsSeededProjective (S.povm t x)

end AgnGaussTomo


