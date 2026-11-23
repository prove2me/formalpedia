-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:38.918285+00:00
-- url     : https://prove2.me/theorems/ed9d1f5b-a042-4472-800d-141427596e29
-- title:
--   Mmat Mul Vec
-- statement:
--   Definitions and structural lemmas for Mmat Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MmatMulVec.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
noncomputable def Mmat (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a j => (if a = j then 1 else 0) +
    X.κ0 * ∑ i, ∑ k, β i k * u i a * ∑ l, X.Gm j l * cc (u k l)
theorem Mmat_zero (u : Fin 2 → Fin r → E) : X.Mmat u 0 = 1 := by
  ext a j
  simp [Data.Mmat, Matrix.one_apply]
lemma Mmat_mulVec_eq_add_sum (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (v : Fin r → E) :
    X.Mmat u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Data.Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
lemma herm_add_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
lemma herm_smul_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (c : E) (x z : Fin r → E) :
    herm G (c • x) z = c * herm G x z := by
  simp only [herm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
theorem Mmat_mul (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β β' : Matrix (Fin 2) (Fin 2) E) : X.Mmat u β * X.Mmat u β' = X.Mmat u (β + β') := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Mmat_mulVec_eq_add_sum, herm_add_left_fundamental_domains,
    herm_smul_left_fundamental_domains, Fin.sum_univ_two, hu, mul_zero, add_zero, Matrix.add_apply]
  first
    | module
    | (simp only [add_mul, mul_add, add_smul]; abel)
noncomputable def gam (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin 2) (Fin 2) E) : GL (Fin r) E :=
  ⟨X.Mmat u β, X.Mmat u (-β), by rw [X.Mmat_mul u hu, add_neg_cancel, Mmat_zero],
    by rw [X.Mmat_mul u hu, neg_add_cancel, Mmat_zero]⟩
end Data
end ReciprocityTheory.ChartRestriction.G.FD


