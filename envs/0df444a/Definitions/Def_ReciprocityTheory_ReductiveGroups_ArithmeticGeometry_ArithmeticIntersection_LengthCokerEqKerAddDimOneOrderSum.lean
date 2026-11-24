-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:41.239259+00:00
-- url     : https://prove2.me/theorems/f9fe5403-f3ab-43cc-8d07-5ef855a23776
-- title:
--   Length Coker Eq Ker Add Dim One Order Sum
-- statement:
--   Definitions and structural lemmas for Length Coker Eq Ker Add Dim One Order Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
section Noeth
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
end Noeth
section Loc
variable {A : Type u} [CommRing A]
noncomputable def locLen (N : Type v) [AddCommGroup N] [Module A N] (p : PrimeSpectrum A) : ℕ∞ :=
  length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N)
end Loc
section Local
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
theorem withBot_eq_one {d : WithBot ℕ∞} (h1 : d ≤ 1) (h0 : ¬ d ≤ 0) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe e =>
    have h1' : e ≤ 1 := by exact_mod_cast h1
    have h0' : ¬ e ≤ 0 := fun h => h0 (by exact_mod_cast h)
    induction e using ENat.recTopCoe with
    | top => exact absurd h1' (by simp)
    | coe n =>
      have a1 : n ≤ 1 := by exact_mod_cast h1'
      have a0 : ¬ n ≤ 0 := fun h => h0' (by exact_mod_cast h)
      have hn : n = 1 := by omega
      subst hn
      first | rfl | norm_cast | simp
theorem dim_quot_eq_one_iff (hdim : ringKrullDim A = 1) (q : Ideal A) [q.IsPrime] :
    ringKrullDim (A ⧸ q) = 1 ↔ ¬ q.IsMaximal := by
  constructor
  · intro h hq
    haveI := hq
    letI := Ideal.Quotient.field q
    have h0 : ringKrullDim (A ⧸ q) = 0 := ringKrullDim_eq_zero_of_field (A ⧸ q)
    rw [h0] at h
    first | exact zero_ne_one h | simp at h | exact absurd h (by decide)
  · intro hq
    apply withBot_eq_one
    · calc ringKrullDim (A ⧸ q) ≤ ringKrullDim A :=
            ringKrullDim_le_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
        _ = 1 := hdim
    · intro hle
      have hbot : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk q) ≠ ⊥ := by
        intro h
        rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h
        apply hq
        have hqm : q = IsLocalRing.maximalIdeal A :=
          le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h
        rw [hqm]
        exact IsLocalRing.maximalIdeal.isMaximal A
      have hprime : ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk q)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
          (by rw [Ideal.mk_ker]; exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
      let P0 : PrimeSpectrum (A ⧸ q) := ⟨⊥, Ideal.bot_prime⟩
      let P1 : PrimeSpectrum (A ⧸ q) := ⟨_, hprime⟩
      have hlt : P0 < P1 := lt_of_le_of_ne (show P0 ≤ P1 from bot_le)
        (fun h => hbot (congrArg PrimeSpectrum.asIdeal h).symm)
      let s : LTSeries (PrimeSpectrum (A ⧸ q)) :=
        { length := 1
          toFun := ![P0, P1]
          step := fun i => by
            fin_cases i
            first | exact hlt | simpa using hlt }
      have hs : (s.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum (A ⧸ q)) := by
        first
          | exact Order.LTSeries.length_le_krullDim s
          | exact LTSeries.length_le_krullDim s
          | exact Order.length_le_krullDim s
      have hk : (s.length : WithBot ℕ∞) ≤ 0 := hs.trans hle
      have hlen : s.length = 1 := rfl
      rw [hlen] at hk
      have h1 : (1 : ℕ) ≤ 0 := by exact_mod_cast hk
      omega
theorem eq_of_not_max_of_le (hdim : ringKrullDim A = 1) {p q : Ideal A} [p.IsPrime] [q.IsPrime]
    (hp : ¬ p.IsMaximal) (hqp : q ≤ p) : p = q := by
  by_contra hne
  let P : PrimeSpectrum A := ⟨p, inferInstance⟩
  let Q : PrimeSpectrum A := ⟨q, inferInstance⟩
  let M : PrimeSpectrum A := IsLocalRing.closedPoint A
  have hQP : Q < P := lt_of_le_of_ne (show Q ≤ P from hqp)
    (fun h => hne (congrArg PrimeSpectrum.asIdeal h).symm)
  have hPM : P < M := lt_of_le_of_ne
    (show P ≤ M from IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
    (fun h => hp (by
      have h' : p = IsLocalRing.maximalIdeal A := congrArg PrimeSpectrum.asIdeal h
      rw [h']
      exact IsLocalRing.maximalIdeal.isMaximal A))
  let s : LTSeries (PrimeSpectrum A) :=
    { length := 2
      toFun := ![Q, P, M]
      step := fun i => by
        fin_cases i
        · first | exact hQP | simpa using hQP
        · first | exact hPM | simpa using hPM }
  have hs : (s.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum A) := by
    first
      | exact Order.LTSeries.length_le_krullDim s
      | exact LTSeries.length_le_krullDim s
      | exact Order.length_le_krullDim s
  have hlen : s.length = 2 := by
    first | rfl | simp [s, RelSeries.snoc_length, RelSeries.singleton_length]
  have hk : Order.krullDim (PrimeSpectrum A) = 1 := hdim
  rw [hlen, hk] at hs
  have h2 : (2 : ℕ) ≤ 1 := by exact_mod_cast hs
  omega
theorem finite_dimOne (hdim : ringKrullDim A = 1) :
    {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1}.Finite := by
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  refine (Set.Finite.preimage (fun a _ b _ h => PrimeSpectrum.ext h) hfin).subset ?_
  intro p hp
  have hp' : ¬ p.asIdeal.IsMaximal := (dim_quot_eq_one_iff hdim p.asIdeal).1 hp
  show p.asIdeal ∈ minimalPrimes A
  simp only [minimalPrimes, Ideal.minimalPrimes, Set.mem_setOf_eq]
  refine ⟨⟨p.isPrime, bot_le⟩, fun q hq hqp => ?_⟩
  haveI := hq.1
  exact (eq_of_not_max_of_le hdim hp' hqp).le
end Local
section Main
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
end Main
section Final
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
noncomputable def dimOneSum (N : Type v) [AddCommGroup N] [Module A N] (x : A) : ℕ∞ :=
  ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1), locLen N p * ordMod p x
end Final
end ReciprocityTheory.ChartRestriction.G.AI


