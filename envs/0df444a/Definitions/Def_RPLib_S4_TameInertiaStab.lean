-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaStab
-- name    : RPLib_S4_TameInertiaStab
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:46:00.136701+00:00
-- url     : https://prove2.me/theorems/b42d9b48-b25f-4259-8b5d-97d8ab2e40b3
-- title:
--   The decomposition group fixes the small root, and normalises inertia
-- statement:
--   The argument that inertia elements fix the unique small root of a split trinomial $X^{p+1} - F X + 1$ only uses that $\sigma$ stabilises the prime ($\sigma b \in P \iff b \in P$), so it holds for the whole decomposition group, including at finite levels of the pro-chart. The file also proves that inertia elements stabilise their prime and that the inertia group is normalised by the stabiliser: $$\varphi Q = Q,\ \sigma \in I(Q) \implies \varphi^{-1} \sigma \varphi \in I(Q).$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter I, Section 7

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaFix

/-!
# Tame inertia, part Stab: the decomposition group fixes the small root (S4-PD item (2), T10a)

`Fix` shows that inertia elements fix the unique small root of the split trinomial `X^(p+1) - F X + 1`. The same proof
only uses that `σ` stabilises the prime (`σ • b ∈ P ↔ b ∈ P`), so it holds for the whole decomposition group:
`valuation_smul_lt_one_stab`, `fix_small_root_stab`, and at a finite level of the pro-chart `fix_of_stab_small`.
Also: inertia elements stabilise their prime (`stab_of_mem_inertia`), and the inertia group is normalised by the
stabiliser (`inertia_conj`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

section Gen

variable {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
  {G : Type*} [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : B), σ • algebraMap B L s = algebraMap B L (σ • s))

include hc in
/-- Elements stabilising `P` preserve `v_P(w) < 1`. -/
theorem valuation_smul_lt_one_stab (P : HeightOneSpectrum B) {σ : G}
    (hσ : ∀ b : B, σ • b ∈ P.asIdeal ↔ b ∈ P.asIdeal) {w : L}
    (hw : P.valuation L w < 1) : P.valuation L (σ • w) < 1 := by
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer w hw.le
  have hd1 : P.valuation L (algebraMap B L d) = 1 := (P.valuation_eq_one_iff_notMem (K := L)).2 d.2
  have hn : n ∈ P.asIdeal := by
    refine (P.valuation_lt_one_iff_mem (K := L) n).1 ?_
    show P.valuation L (algebraMap B L n) < 1
    rw [← hnd, map_mul, hd1, mul_one]
    exact hw
  have hσn : σ • n ∈ P.asIdeal := (hσ n).2 hn
  have hσd : σ • (d : B) ∉ P.asIdeal := fun h => d.2 ((hσ _).1 h)
  have hmul : σ • w * algebraMap B L (σ • (d : B)) = algebraMap B L (σ • n) := by
    rw [← hc, ← hc, ← smul_mul', hnd]
  have h1 : P.valuation L (algebraMap B L (σ • (d : B))) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := L)).2 hσd
  have h2 : P.valuation L (algebraMap B L (σ • n)) < 1 := (P.valuation_lt_one_iff_mem (K := L) _).2 hσn
  rw [← hmul, map_mul, h1, mul_one] at h2
  exact h2

include hc in
/-- **T10a (level form).** An element stabilising `P` and fixing `F` fixes the unique small root of the split
trinomial. -/
theorem fix_small_root_stab (P : HeightOneSpectrum B) {p : ℕ} (hp : 0 < p) {F : L} (hF : 1 < P.valuation L F)
    (hs : (trin p F).Splits) {σ : G} (hσ : ∀ b : B, σ • b ∈ P.asIdeal ↔ b ∈ P.asIdeal) (hσF : σ • F = F) {w : L}
    (hw : (trin p F).IsRoot w) (hwv : P.valuation L w < 1) : σ • w = w := by
  obtain ⟨w₀, -, huniq⟩ := trin_existsUnique_small (P.valuation L) hp hF hs
  have hr : (trin p F).IsRoot (σ • w) := by
    have h := congrArg (fun t => σ • t) ((trin_isRoot_iff p F w).1 hw)
    simp only [smul_add, smul_sub, smul_mul', smul_pow', smul_one, smul_zero, hσF] at h
    exact (trin_isRoot_iff p F _).2 h
  exact (huniq (σ • w) ⟨hr, valuation_smul_lt_one_stab hc P hσ hwv⟩).trans (huniq w ⟨hw, hwv⟩).symm

end Gen

section Level

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- Inertia elements stabilise their prime. -/
theorem stab_of_mem_inertia {Q : Ideal (proChart A K R0)} {σ : Pi1 A K} (hσ : σ ∈ Q.inertia (Pi1 A K))
    (b : proChart A K R0) : σ • b ∈ Q ↔ b ∈ Q := by
  have h := AddSubgroup.mem_inertia.1 hσ b
  constructor
  · intro hb
    have h' := Q.sub_mem hb h
    rwa [sub_sub_cancel] at h'
  · intro hb
    have h' := Q.add_mem h hb
    rwa [sub_add_cancel] at h'

/-- The inertia group is normalised by the stabiliser of the prime. -/
theorem inertia_conj {Q : Ideal (proChart A K R0)} {φ : Pi1 A K}
    (hφ : ∀ b : proChart A K R0, φ • b ∈ Q ↔ b ∈ Q) {σ : Pi1 A K} (hσ : σ ∈ Q.inertia (Pi1 A K)) :
    φ⁻¹ * σ * φ ∈ Q.inertia (Pi1 A K) := by
  refine AddSubgroup.mem_inertia.2 fun b => ?_
  have h := AddSubgroup.mem_inertia.1 hσ (φ • b)
  have e : (φ⁻¹ * σ * φ) • b - b = φ⁻¹ • (σ • φ • b - φ • b) := by
    rw [smul_sub, mul_smul, mul_smul, inv_smul_smul]
  rw [e]
  refine (hφ _).1 ?_
  rwa [smul_inv_smul]

/-- Restriction to a finite level preserves stabilising the prime. -/
theorem restrict_stab {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {Q : Ideal (proChart A K R0)} {g : Pi1 A K} (hg : ∀ b : proChart A K R0, g • b ∈ Q ↔ b ∈ Q)
    {τ : L ≃ₐ[K] L} (hτ : ∀ y : L, ((τ y : L) : AlgebraicClosure K) =
      ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K))
    (y : integralClosure R0 L) :
    τ • y ∈ Q.comap (inclU R0 hLU) ↔ y ∈ Q.comap (inclU R0 hLU) := by
  have e : inclU R0 hLU (τ • y) = g • inclU R0 hLU y := by
    apply Subtype.ext; apply Subtype.ext
    show ((τ (y : L) : L) : AlgebraicClosure K) =
      ((g ((inclU R0 hLU y : proChart A K R0) : maxUnram A K) : maxUnram A K) : AlgebraicClosure K)
    rw [hτ]
    rfl
  rw [Ideal.mem_comap, Ideal.mem_comap, e, hg]

/-- **T10a.** Elements of `Pi1` stabilising `Q` fix the small root of the trinomial at a finite Galois level. -/
theorem fix_of_stab_small {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] [IsGalois K L]
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    {Q : Ideal (proChart A K R0)} (P : HeightOneSpectrum (integralClosure R0 L))
    (hP : P.asIdeal = Q.comap (inclU R0 hLU)) {p : ℕ} (hp : 0 < p) {a : K}
    (hF : 1 < P.valuation L (algebraMap K L a)) (hs : (trin p (algebraMap K L a)).Splits) {w : L}
    (hw : (trin p (algebraMap K L a)).IsRoot w) (hwv : P.valuation L w < 1) {σ : Pi1 A K}
    (hσ : ∀ b : proChart A K R0, σ • b ∈ Q ↔ b ∈ Q) :
    σ (IntermediateField.inclusion hLU w) = IntermediateField.inclusion hLU w := by
  obtain ⟨τ, hτ⟩ := exists_restrict hLU σ
  have hτP : ∀ b : integralClosure R0 L, τ • b ∈ P.asIdeal ↔ b ∈ P.asIdeal := by
    rw [hP]
    exact restrict_stab hLU hσ hτ
  have hfix : τ • w = w := fix_small_root_stab (fun _ _ => rfl) P hp hF hs hτP (τ.commutes a) hw hwv
  apply Subtype.ext
  rw [← hτ w]
  exact congrArg Subtype.val hfix

end Level

end

end TameInertia
end RamanujanPetersson


