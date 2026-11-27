-- Prove2me | solution 1 for AbelianCayleyHDX.tower_polynomial_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:34:06.710528+00:00
-- url     : https://prove2.me/submissions/4b970cf0-f1b4-495e-86fe-aeebf74a0ec3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AbelianCayleyHDX_tower_generic_data
import Theorems.Thm_AbelianCayleyHDX_maximal_minors_linearIndependent_of_oneGeneric
open Filter RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.RG

open MvPolynomial

/-- Linear independence descends from a field extension: if the images of polynomials over `F`
are independent over `K`, the polynomials are independent over `F`. -/
lemma linearIndependent_of_map {F K ι σ : Type*} [Field F] [Field K] [Algebra F K] [Fintype ι]
    (P : ι → MvPolynomial σ F)
    (h : LinearIndependent K (fun i => MvPolynomial.map (algebraMap F K) (P i))) :
    LinearIndependent F P := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have := h (fun i => algebraMap F K (g i)) (by
    have := congrArg (MvPolynomial.map (algebraMap F K)) hg
    simp only [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C])
  exact (FaithfulSMul.algebraMap_injective F K) (by simpa using this i)

end AbelianCayleyHDX.RG

open AbelianCayleyHDX AbelianCayleyHDX.RG MvPolynomial in
theorem solution (h : ℕ) (hq : 8 ≤ 2 ^ h) (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (hF : Fintype.card F = (2 ^ h) ^ 2) (g₀ : ℕ) :
    ∃ g : ℕ → ℕ, Tendsto g atTop atTop ∧ (∀ j, g₀ ≤ g j) ∧
    ∃ (e : ∀ j, Fin ((2 ^ h - 2) * g j) → (Fin (2 * g j + 1) → F))
      (L : ∀ j, Fin (g j / 4) → Fin (3 * (g j / 4)) → Module.Dual F (Fin (2 * g j + 1) → F)),
      (∀ j,
        Submodule.span F (Set.range (e j)) = ⊤ ∧
        (∀ a, e j a ≠ 0) ∧
        (∀ a b, a ≠ b → ∀ c : F, e j a ≠ c • e j b) ∧
        (∀ c : Module.Dual F (Fin (2 * g j + 1) → F), c ≠ 0 →
          (Finset.univ.filter fun a => c (e j a) = 0).card ≤ 3 * g j) ∧
        (∀ a, ∃ (u : Fin (g j / 4) → F) (z : Fin (3 * (g j / 4)) → F),
          ∀ i l, L j i l (e j a) = u i * z l) ∧
        LinearIndependent F (fun J : {J : Finset (Fin (3 * (g j / 4))) // J.card = g j / 4} =>
          (Matrix.of fun i l => ∑ r : Fin (2 * g j + 1),
            MvPolynomial.C (L j i (J.1.orderEmbOfFin J.2 l) (Pi.single r 1)) *
              MvPolynomial.X r).det)) ∧
      ∀ enc : F ≃ Fin (Fintype.card F), ∃ M : Turing.TM2ComputableAux Bool Bool,
        ∃ p : Polynomial ℕ, ∀ j,
          HMBinPacking.OutputsWithin M (encNat j)
            (encNat (2 * g j + 1) ++ encList (encFVec enc) (List.ofFn (e j)))
            (p.eval (2 * g j + 1)) := by
  obtain ⟨g, hg, hgge, e, L, hprop, hmach⟩ := tower_generic_data h hq F hF g₀
  refine ⟨g, hg, hgge, e, L, fun j => ?_, hmach⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hprop j
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  apply linearIndependent_of_map (K := AlgebraicClosure F)
  have key := maximal_minors_linearIndependent_of_oneGeneric (AlgebraicClosure F)
    (Nat.le_mul_of_pos_left _ (by norm_num))
    (fun i l r => algebraMap F (AlgebraicClosure F) (L j i l (Pi.single r 1))) h6
  convert key using 2 with J
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  refine Matrix.ext fun i l => ?_
  simp only [Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, map_C, map_X]
