-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:29.574506+00:00
-- url     : https://prove2.me/theorems/97e58022-ed1a-452c-8396-03cf3de39768
-- title:
--   Algebra Map Mem Max
-- statement:
--   Definitions and structural lemmas for Algebra Map Mem Max, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
namespace GlobalTheory.GenSep
section Subst
variable {Ω : Type} [Field Ω] {D N : ℕ}
abbrev Free (D N : ℕ) (j0 : Fin N) : Type := {p : Fin (D + 1) × Fin N // p.1 = 0 ∨ p.2 ≠ j0}
open Classical in

def subst (x : Fin N → Ω) (j0 : Fin N) (p : Fin (D + 1) × Fin N) : MvPolynomial (Free D N j0) Ω :=
  if h : p.1 = 0 ∨ p.2 ≠ j0 then X ⟨p, h⟩
  else -∑ k : {k : Fin N // k ≠ j0}, C (x k / x j0) * X ⟨(p.1, k), Or.inr k.2⟩
end Subst
section Gauss
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
end Gauss
section Pair
variable {Ω F F' : Type} [Field Ω] [Field F] [Field F'] (w : AddValuation F (WithTop ℤ))
  (w' : AddValuation F' (WithTop ℤ)) (ι : Ω →+* F) (ι' : Ω →+* F')
def Att (z : F × F') : Prop := ∃ a : Ω, w z.1 = w (ι a) ∧ w' z.2 = w' (ι' a)
theorem le_mul_of {a b : ℤ} {x y : F} (hx : (a : WithTop ℤ) ≤ w x) (hy : (b : WithTop ℤ) ≤ w y) {c : ℤ}
    (hc : c ≤ a + b) : (c : WithTop ℤ) ≤ w (x * y) := by
  rw [AddValuation.map_mul]
  exact (by exact_mod_cast hc : (c : WithTop ℤ) ≤ (a : WithTop ℤ) + b).trans (add_le_add hx hy)
theorem exists_lower (x : F) : ∃ m : ℕ, ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ w x := by
  induction h : w x using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe a => exact ⟨a.natAbs, by exact_mod_cast (by omega : -(a.natAbs : ℤ) ≤ a)⟩
theorem approx_mul {r s a b : F} {m : ℕ} {n : ℤ} (hr : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ w r)
    (hs : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ w s) (ha : (((n.natAbs + m : ℕ) : ℤ) : WithTop ℤ) ≤ w (r - a))
    (hb : (((n.natAbs + m : ℕ) : ℤ) : WithTop ℤ) ≤ w (s - b)) : (n : WithTop ℤ) ≤ w (r * s - a * b) := by
  have e : r * s - a * b = r * (s - b) + (r - a) * s - (r - a) * (s - b) := by ring
  rw [e]
  refine w.map_le_sub (w.map_le_add ?_ ?_) ?_
  · exact le_mul_of w hr hb (by omega)
  · exact le_mul_of w ha hs (by omega)
  · exact le_mul_of w ha hb (by omega)
def lim (A : Subring (F × F')) : Subring (F × F') where
  carrier := {z | ∀ n : ℤ, ∃ a ∈ A, (n : WithTop ℤ) ≤ w (z.1 - a.1) ∧ (n : WithTop ℤ) ≤ w' (z.2 - a.2)}
  one_mem' n := ⟨1, A.one_mem, by simp, by simp⟩
  zero_mem' n := ⟨0, A.zero_mem, by simp, by simp⟩
  add_mem' := by
    intro y z hy hz n
    obtain ⟨a, ha, h1, h2⟩ := hy n
    obtain ⟨b, hb, h3, h4⟩ := hz n
    refine ⟨a + b, A.add_mem ha hb, ?_, ?_⟩
    · rw [Prod.fst_add, Prod.fst_add, add_sub_add_comm]; exact w.map_le_add h1 h3
    · rw [Prod.snd_add, Prod.snd_add, add_sub_add_comm]; exact w'.map_le_add h2 h4
  neg_mem' := by
    intro y hy n
    obtain ⟨a, ha, h1, h2⟩ := hy n
    refine ⟨-a, A.neg_mem ha, ?_, ?_⟩
    · rw [Prod.fst_neg, Prod.fst_neg, neg_sub_neg, AddValuation.map_sub_swap]; exact h1
    · rw [Prod.snd_neg, Prod.snd_neg, neg_sub_neg, AddValuation.map_sub_swap]; exact h2
  mul_mem' := by
    intro y z hy hz n
    obtain ⟨m1, hm1⟩ := exists_lower w y.1
    obtain ⟨m2, hm2⟩ := exists_lower w z.1
    obtain ⟨m3, hm3⟩ := exists_lower w' y.2
    obtain ⟨m4, hm4⟩ := exists_lower w' z.2
    have hle : ∀ k : ℕ, k ≤ m1 + m2 + m3 + m4 →
        ((-((m1 + m2 + m3 + m4 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ ((-(k : ℤ) : ℤ) : WithTop ℤ) := fun k hk =>
      WithTop.coe_le_coe.2 (by omega)
    obtain ⟨a, ha, h1, h2⟩ := hy ((n.natAbs + (m1 + m2 + m3 + m4) : ℕ) : ℤ)
    obtain ⟨b, hb, h3, h4⟩ := hz ((n.natAbs + (m1 + m2 + m3 + m4) : ℕ) : ℤ)
    exact ⟨a * b, A.mul_mem ha hb,
      approx_mul w ((hle _ (by omega)).trans hm1) ((hle _ (by omega)).trans hm2) h1 h3,
      approx_mul w' ((hle _ (by omega)).trans hm3) ((hle _ (by omega)).trans hm4) h2 h4⟩
def frc (A : Subring (F × F')) : Subring (F × F') where
  carrier := {z | ∃ d ∈ A, d.1 ≠ 0 ∧ d.2 ≠ 0 ∧ d * z ∈ A}
  one_mem' := ⟨1, A.one_mem, one_ne_zero, one_ne_zero, by simpa using A.one_mem⟩
  zero_mem' := ⟨1, A.one_mem, one_ne_zero, one_ne_zero, by simpa using A.zero_mem⟩
  add_mem' := by
    rintro y z ⟨d, hd, d1, d2, hy⟩ ⟨e, he, e1, e2, hz⟩
    refine ⟨d * e, A.mul_mem hd he, mul_ne_zero d1 e1, mul_ne_zero d2 e2, ?_⟩
    have : d * e * (y + z) = e * (d * y) + d * (e * z) := by ring
    rw [this]
    exact A.add_mem (A.mul_mem he hy) (A.mul_mem hd hz)
  neg_mem' := by
    rintro y ⟨d, hd, d1, d2, hy⟩
    exact ⟨d, hd, d1, d2, by rw [mul_neg]; exact A.neg_mem hy⟩
  mul_mem' := by
    rintro y z ⟨d, hd, d1, d2, hy⟩ ⟨e, he, e1, e2, hz⟩
    refine ⟨d * e, A.mul_mem hd he, mul_ne_zero d1 e1, mul_ne_zero d2 e2, ?_⟩
    rw [mul_mul_mul_comm]
    exact A.mul_mem hy hz
end Pair
section Both
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {Ω : Type} [Field Ω] [Algebra K Ω]
  {D N : ℕ}
variable {K' : Type} [Field K'] (φ : MvPolynomial (Fin (D + 1) × Fin N) (la.adicCompletionIntegers K) →+* K')
  (κ : la.adicCompletion K →+* K') (x : Fin N → Ω)
def OverGauss {F : Type} [Field F] (w : AddValuation F (WithTop ℤ)) (ι : Ω →+* F) (e : K' →+* F) : Prop :=
  (∀ P, 0 ≤ w (e (φ P))) ∧ (∀ P, 0 < w (e (φ P)) ↔ ∀ α, P.coeff α ∈ maximalIdeal (la.adicCompletionIntegers K)) ∧
  (∀ a : K, ι (algebraMap K Ω a) = e (κ (algebraMap K (la.adicCompletion K) a))) ∧
  ∀ i : Fin D, ∑ k, e (φ (X (i.succ, k))) * ι (x k) = 0
variable {la φ κ x}
end Both
end GlobalTheory.GenSep


