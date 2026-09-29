-- Prove2me | Definitions.Def_LanglandsTunnell_LambdaSquared
-- name    : LanglandsTunnell_LambdaSquared
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f5728026-7303-56ba-91d0-f33b9cd87465
-- title:
--   Squared local constants from a number field's discriminant
-- statement:
--   Fix a number field $K$. The module first defines, for rationals $a, b$ and a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, the predicate `IsAnisotropicAt a b p`: there is no triple $(z, x, y)$ in the $p$-adic completion of $\mathbb{Q}$ at $p$ which is not the all-zero triple and satisfies $z^2 - a x^2 - b y^2 = 0$, the coefficients being taken via the structure map $\mathbb{Q} \to \mathbb{Q}_p$. Thus it asserts anisotropy of the ternary form $\langle 1, -a, -b\rangle$ over the completion, phrased directly on the equation; the non-triviality condition is the negation of the conjunction $z = 0 \wedge x = 0 \wedge y = 0$. Next, `discQ K` is the discriminant $\mathrm{discr}_{\mathbb{Q}}$ of the particular $\mathbb{Q}$-basis `Module.finBasis ℚ K` of $K$, and `discQ_ne_zero` records that it is non-zero. The squared local constant `lamSq K p` is the complex number $-1$ when $\langle 1, -\mathrm{discQ}\,K, 1\rangle$ is anisotropic at $p$, i.e. when `IsAnisotropicAt (discQ K) (-1) p` holds, and $1$ otherwise; its archimedean companion `lamSqArch K` is $-1$ when $\mathrm{discQ}\,K < 0$ and $1$ otherwise. Both take values in $\{1, -1\}$, as `lamSq_eq_one_or_eq_neg_one` and `lamSqArch_eq_one_or_eq_neg_one` state.
--
--   The independence of these choices from the chosen basis is established in two steps: `isAnisotropicAt_mul_sq_left_iff` shows that for $c \neq 0$ the predicate for $(c^2 a, b)$ is equivalent to that for $(a, b)$, and `exists_discr_eq_sq_mul_discQ` produces, for any basis $b$ of $K$ over $\mathbb{Q}$ indexed by a finite type, a non-zero rational $c$ (the determinant of the change-of-basis matrix) with $\mathrm{discr}_{\mathbb{Q}}(b) = c^2 \cdot \mathrm{discQ}\,K$. Consequently `isAnisotropicAt_discr_iff` and `discr_neg_iff` give that the anisotropy condition and the sign condition may be tested with any basis. Finally, under an algebra structure $\mathcal{O}_{\mathbb{Q}} \to \mathcal{O}_K$ with $\mathcal{O}_K$ integral over it, `lamSqFin K w` attaches to a height-one prime $w$ of $\mathcal{O}_K$ the value $1$ when both the ramification index `Ideal.ramificationIdx'` and the inertia degree `inertiaDeg'` of $w$ over the prime $w \cap \mathcal{O}_{\mathbb{Q}}$ beneath it equal $1$, and otherwise the value `lamSq K` at that prime below.
--
--   **Relation to Mathlib.** The discriminant of a basis (`Algebra.discr`), adic completions at height-one primes, and `Ideal.ramificationIdx'`/`inertiaDeg'` are Mathlib's; the anisotropy predicate and the constants built from it are the project's own, the predicate being stated directly as the absence of a non-trivial solution of the equation rather than through Mathlib's quadratic-form machinery.
--
--   **Where it is used.** The values $\pm 1$ defined here are the local data, indexed by the finite places of $\mathbb{Q}$ or of $K$ and by the real place, that enter the cubic-induction step towards the Langlands–Tunnell theorem, which supplies the modularity of the mod $3$ representation used in the Frey curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_LambdaSquared.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Discriminant
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell.CubicInduction

def IsAnisotropicAt (a b : ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ¬ ∃ z x y : p.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
    z ^ 2 - algebraMap ℚ (p.adicCompletion ℚ) a * x ^ 2
      - algebraMap ℚ (p.adicCompletion ℚ) b * y ^ 2 = 0

variable (K : Type) [Field K] [NumberField K]

noncomputable def discQ : ℚ := Algebra.discr ℚ (Module.finBasis ℚ K)

theorem discQ_ne_zero : discQ K ≠ 0 := Algebra.discr_not_zero_of_basis ℚ (Module.finBasis ℚ K)

open scoped Classical in

noncomputable def lamSq (p : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  if IsAnisotropicAt (discQ K) (-1) p then -1 else 1

noncomputable def lamSqArch : ℂ := if discQ K < 0 then -1 else 1

theorem lamSq_eq_one_or_eq_neg_one (p : HeightOneSpectrum (𝓞 ℚ)) :
    lamSq K p = 1 ∨ lamSq K p = -1 := by
  unfold lamSq
  split_ifs <;> simp

theorem lamSqArch_eq_one_or_eq_neg_one : lamSqArch K = 1 ∨ lamSqArch K = -1 := by
  unfold lamSqArch
  split_ifs <;> simp

section Rescaling

theorem isAnisotropicAt_mul_sq_left_iff {a b c : ℚ} (hc : c ≠ 0) (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsAnisotropicAt (c ^ 2 * a) b p ↔ IsAnisotropicAt a b p := by
  unfold IsAnisotropicAt
  have hc' : algebraMap ℚ (p.adicCompletion ℚ) c ≠ 0 :=
    (map_ne_zero (algebraMap ℚ (p.adicCompletion ℚ))).mpr hc
  constructor
  · intro h ⟨z, x, y, hne, hzxy⟩
    refine h ⟨z, x / algebraMap ℚ (p.adicCompletion ℚ) c, y, ?_, ?_⟩
    · rintro ⟨hz, hx, hy⟩
      exact hne ⟨hz, (div_eq_zero_iff.mp hx).resolve_right hc', hy⟩
    · rw [map_mul, map_pow, div_pow, ← hzxy]
      field_simp
  · intro h ⟨z, x, y, hne, hzxy⟩
    refine h ⟨z, algebraMap ℚ (p.adicCompletion ℚ) c * x, y, ?_, ?_⟩
    · rintro ⟨hz, hx, hy⟩
      exact hne ⟨hz, (mul_eq_zero.mp hx).resolve_left hc', hy⟩
    · rw [map_mul, map_pow] at hzxy
      rw [← hzxy, mul_pow]
      ring

end Rescaling

section BasisIndependence

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_discr_eq_sq_mul_discQ (b : Module.Basis ι ℚ K) :
    ∃ c : ℚ, c ≠ 0 ∧ Algebra.discr ℚ ⇑b = c ^ 2 * discQ K := by
  have hcard : Fintype.card (Fin (Module.finrank ℚ K)) = Fintype.card ι := by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis b]
  let e : Module.Basis ι ℚ K := (Module.finBasis ℚ K).reindex (Fintype.equivOfCardEq hcard)
  have he : Algebra.discr ℚ ⇑e = discQ K := by
    rw [discQ, Module.Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ (Module.finBasis ℚ K) (Fintype.equivOfCardEq hcard)
  have hb : (⇑b : ι → K) = Matrix.vecMul ⇑e ((e.toMatrix ⇑b).map ⇑(algebraMap ℚ K)) := by
    funext j
    rw [← e.sum_toMatrix_smul_self ⇑b j]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hd : Algebra.discr ℚ ⇑b = (e.toMatrix ⇑b).det ^ 2 * discQ K := by
    conv_lhs => rw [hb]
    rw [Algebra.discr_of_matrix_vecMul, he]
  exact ⟨(e.toMatrix ⇑b).det, (e.isUnit_det b).ne_zero, hd⟩

theorem isAnisotropicAt_discr_iff (b : Module.Basis ι ℚ K) (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsAnisotropicAt (Algebra.discr ℚ ⇑b) (-1) p ↔ IsAnisotropicAt (discQ K) (-1) p := by
  obtain ⟨c, hc, hcb⟩ := exists_discr_eq_sq_mul_discQ K b
  rw [hcb]
  exact isAnisotropicAt_mul_sq_left_iff hc p

theorem discr_neg_iff (b : Module.Basis ι ℚ K) : Algebra.discr ℚ ⇑b < 0 ↔ discQ K < 0 := by
  obtain ⟨c, hc, hcb⟩ := exists_discr_eq_sq_mul_discQ K b
  have hc2 : 0 < c ^ 2 := by positivity
  rw [hcb, mul_neg_iff]
  simp [hc2, not_lt.mpr hc2.le]

end BasisIndependence

section PlacesOfK

variable [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

noncomputable def lamSqFin (w : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal = 1 ∧
      (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = 1 then 1
  else lamSq K (w.under (𝓞 ℚ))

end PlacesOfK

end LanglandsTunnell.CubicInduction


