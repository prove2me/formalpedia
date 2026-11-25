-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:47.078236+00:00
-- url     : https://prove2.me/theorems/9d1e1f90-c209-47bc-9b99-f841703afb98
-- title:
--   Row Tie PDesc Jet
-- statement:
--   Definitions and structural lemmas for Row Tie PDesc Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Jet
variable {k : Type} [CommRing k] {n d : ℕ}
def HiOrd (K : ℕ) (g : PS k n d) : Prop :=
  ∀ μ : Fin n × Fin d →₀ ℕ, μ.degree < K → coeff μ g = 0
theorem HiOrd.mul_left {K : ℕ} {g : PS k n d} (h : HiOrd K g) (a : PS k n d) : HiOrd K (a * g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have h2 : Finsupp.degree pq.2 < K :=
    lt_of_le_of_lt (by rw [← hpq', map_add]; exact Nat.le_add_left _ _) hμ
  rw [h _ h2, mul_zero]
theorem HiOrd.sum {K : ℕ} {α : Type} (s : Finset α) (g : α → PS k n d) (h : ∀ i ∈ s, HiOrd K (g i)) :
    HiOrd K (∑ i ∈ s, g i) := by
  intro μ hμ
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi μ hμ
theorem HiOrd.deriv {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (i : Fin n × Fin d) :
    HiOrd K (MvPowerSeries.pderiv k i g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]
theorem HiOrd.dofN {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (F : Fin d → PS k 2 d) (b : Fin n)
    (u : Fin d → k) : HiOrd K (DofN F b u g) := by
  unfold DofN
  exact HiOrd.sum _ _ fun j _ => (h.deriv _).mul_left _
theorem HiOrd.iter (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) :
    ∀ (j K : ℕ) (g : PS k n d), HiOrd (K + j) g → HiOrd K ((DofN F b u)^[j] g)
  | 0, K, g, h => h
  | j + 1, K, g, h => by
    rw [Function.iterate_succ_apply]
    exact HiOrd.iter F b u j K _ (HiOrd.dofN (K := K + j) (by rw [add_assoc]; exact h) F b u)
theorem HiOrd.foldr (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (K : ℕ) (g : PS k n d), HiOrd (K + (L.map m).sum) g →
      HiOrd K (L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g)
  | [], K, g, h => by simpa using h
  | l :: L, K, g, h => by
    rw [List.foldr_cons]
    refine HiOrd.iter F (cp l) (u l) (m l) K _ (HiOrd.foldr F cp u m L (K + m l) g ?_)
    rw [List.map_cons, List.sum_cons] at h
    rw [add_assoc]
    exact h
theorem dofN_add (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f g : PS k n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]
theorem dofN_smul (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (c : k) (f : PS k n d) :
    DofN F b u (c • f) = c • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, Finset.smul_sum, mul_smul_comm]
theorem iter_add (A : PS k n d → PS k n d) (hA : ∀ f g, A (f + g) = A f + A g) :
    ∀ (j : ℕ) (f g : PS k n d), A^[j] (f + g) = A^[j] f + A^[j] g
  | 0, f, g => rfl
  | j + 1, f, g => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, hA,
      iter_add A hA j]
theorem iter_smul (A : PS k n d → PS k n d) (hA : ∀ (c : k) f, A (c • f) = c • A f) :
    ∀ (j : ℕ) (c : k) (f : PS k n d), A^[j] (c • f) = c • A^[j] f
  | 0, c, f => rfl
  | j + 1, c, f => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hA, iter_smul A hA j]
theorem foldr_add (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (f g : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (f + g) =
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f + L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g
  | [], f, g => rfl
  | l :: L, f, g => by
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, foldr_add F cp u m L f g,
      iter_add _ (dofN_add F (cp l) (u l))]
theorem foldr_smul (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (c : k) (f : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (c • f) =
        c • L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f
  | [], c, f => rfl
  | l :: L, c, f => by
    rw [List.foldr_cons, List.foldr_cons, foldr_smul F cp u m L c f,
      iter_smul _ (dofN_smul F (cp l) (u l))]
theorem dpolyN_add (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f g : PS k n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, DmonN, foldr_add, mul_add, Finset.sum_add_distrib]
theorem dpolyN_smul (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (c : k) (f : PS k n d) :
    DpolyN F cp u P (c • f) = c • DpolyN F cp u P f := by
  simp only [DpolyN, DmonN, foldr_smul, mul_smul_comm, Finset.smul_sum]
def nabL (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) : PS k n d →ₗ[k] k where
  toFun f := constantCoeff (DpolyN F cp u P (f * G))
  map_add' f g := by
    rw [add_mul, dpolyN_add, map_add]
  map_smul' c f := by
    rw [smul_mul_assoc, dpolyN_smul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      map_smul]
    rfl
def cst (D : ℕ) : Fin n × Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => D
end Jet
end Formalism.L2.FormalSeriesBounds.DescP


