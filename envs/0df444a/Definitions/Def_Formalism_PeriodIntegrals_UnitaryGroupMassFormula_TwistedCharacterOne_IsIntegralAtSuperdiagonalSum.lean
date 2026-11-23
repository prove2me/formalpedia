-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:20.739952+00:00
-- url     : https://prove2.me/theorems/c2ee1ffd-2b5d-4be5-a758-ba5b4246cb0c
-- title:
--   Is Integral At Superdiagonal Sum
-- statement:
--   Definitions and structural lemmas for Is Integral At Superdiagonal Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
lemma mk_ne {s : 𝓞 E} (hs : s ∉ P.asIdeal) : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
  rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
lemma nm_mul {s s' : 𝓞 E} (hs : s ∉ P.asIdeal) (hs' : s' ∉ P.asIdeal) : s * s' ∉ P.asIdeal :=
  fun h => (P.isPrime.mem_or_mem h).elim hs hs'
lemma one_nm : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
lemma reduction_spec {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  have : P.asIdeal.IsMaximal := P.isMaximal
  let _ := Ideal.Quotient.field P.asIdeal
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ (mk_ne P hs), mul_one]⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc⟩ := hex.choose_spec
  have hx : s * r' = s' * r := by
    apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_mul, ← h, ← h']
    ring
  apply mul_left_cancel₀ (mk_ne P hs')
  calc Ideal.Quotient.mk P.asIdeal s' * (Ideal.Quotient.mk P.asIdeal s * hex.choose)
      = Ideal.Quotient.mk P.asIdeal s * (Ideal.Quotient.mk P.asIdeal s' * hex.choose) := by ring
    _ = Ideal.Quotient.mk P.asIdeal (s * r') := by rw [hc, map_mul]
    _ = Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r := by rw [hx, map_mul]
lemma redP_eq {a : E} {r s : 𝓞 E} {x : 𝓞 E ⧸ P.asIdeal} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r)
    (hx : Ideal.Quotient.mk P.asIdeal s * x = Ideal.Quotient.mk P.asIdeal r) : redP P a = x := by
  have : P.asIdeal.IsPrime := P.isPrime
  exact mul_left_cancel₀ (mk_ne P hs) ((reduction_spec P hs h).trans hx.symm)
def intS : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨r, s, hs, h⟩ := ha
    obtain ⟨r', s', hs', h'⟩ := hb
    refine ⟨r * r', s * s', nm_mul P hs hs', ?_⟩
    rw [map_mul, map_mul, ← h, ← h']
    ring
  one_mem' := ⟨1, 1, one_nm P, by simp⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨r, s, hs, h⟩ := ha
    obtain ⟨r', s', hs', h'⟩ := hb
    refine ⟨s' * r + s * r', s * s', nm_mul P hs hs', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
    ring
  zero_mem' := ⟨0, 1, one_nm P, by simp⟩
  neg_mem' := by
    intro a ha
    obtain ⟨r, s, hs, h⟩ := ha
    exact ⟨-r, s, hs, by rw [map_neg, ← h]; ring⟩
def redH : intS P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := redP_eq P (r := 1) (s := 1) (one_nm P) (by simp) (by simp)
  map_mul' a b := by
    obtain ⟨r, s, hs, h⟩ := a.2
    obtain ⟨r', s', hs', h'⟩ := b.2
    show redP P (a.1 * b.1) = redP P a.1 * redP P b.1
    refine redP_eq P (r := r * r') (s := s * s') (nm_mul P hs hs') ?_ ?_
    · rw [map_mul, map_mul, ← h, ← h']
      ring
    · rw [map_mul, map_mul, ← reduction_spec P hs h, ← reduction_spec P hs' h']
      ring
  map_zero' := redP_eq P (r := 0) (s := 1) (one_nm P) (by simp) (by simp)
  map_add' a b := by
    obtain ⟨r, s, hs, h⟩ := a.2
    obtain ⟨r', s', hs', h'⟩ := b.2
    show redP P (a.1 + b.1) = redP P a.1 + redP P b.1
    refine redP_eq P (r := s' * r + s * r') (s := s * s') (nm_mul P hs hs') ?_ ?_
    · rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
      ring
    · rw [map_add, map_mul, map_mul, map_mul, ← reduction_spec P hs h, ← reduction_spec P hs' h']
      ring
variable {n : ℕ}
variable {kj N c : ℕ}
def Ment (kj N c : ℕ) (f : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Matrix (Fin (N - kj)) (Fin (N - kj)) E :=
  Matrix.of fun s t => Loc.atN (f (Loc.eN E (N + c) (kj + t.1))) (kj + s.1)
def Mb (kj N c : ℕ) (f : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) :
    Matrix (Fin (N - kj)) (Fin (N - kj)) (𝓞 E ⧸ P.asIdeal) :=
  (Ment kj N c f).map (redP P)
def dI (kj N c : ℕ) (t : Fin (N - kj)) : Fin (N + c) := ⟨kj + t.1, by have := t.2; omega⟩
variable {K : Type} [Field K]
end PI.TwChrOne.Pf


