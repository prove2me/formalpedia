-- Prove2me | Definitions.Def_RPLib_S4_CDPack16
-- name    : RPLib_S4_CDPack16
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T10:56:12.277022+00:00
-- url     : https://prove2.me/theorems/34380276-9750-4bb1-863b-f63c3b27ca6b
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 16 of 71
-- statement:
--   Part 16 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_ResStab`: S4-PD E4S arithmetic ResA, part 1: stabilisers in `π₁^geo` and Kummer characters under conjugation
--   * `Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
--   * `Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack15b
import Definitions.Def_RPLib_S3_SBTransport

/-!
# Curve-duality library package, part 16 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_ResStab`: S4-PD E4S arithmetic ResA, part 1: stabilisers in `π₁^geo` and Kummer characters under conjugation
* `Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
* `Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_ResStab =====
section

/-!
# S4-PD E4S arithmetic ResA, part 1: stabilisers in `π₁^geo` and Kummer characters under conjugation

* `stab_mem_inertia`: an element of `π₁^geo` stabilising a boundary prime `Q` of the pro-chart lies in its inertia group
  (every residue class mod `Q` is represented by a constant, and `π₁^geo` fixes the constants).
* `kchar_conj`: `kchar α (γ τ γ⁻¹) = kchar β τ` when `α = γ β` and `γ` fixes `ζ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a
open scoped Pointwise

section Stab

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {p : ℕ} [Fact p.Prime] [CharP K p]

/-- **Decomposition = inertia in `π₁^geo`**: `σ ∈ π₁^geo` with `σ Q = Q` lies in `I(Q)`. -/
theorem stab_mem_inertia {e : ℕ} (he : 0 < e)
    (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
    {Q : Ideal (proChart A K R0)} [Q.IsPrime] [Finite (R0 ⧸ Q.under R0)]
    (hcard : ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d) {σ : Pi1 A K} (hσ : σ ∈ pi1geo A K (p ^ e))
    (hQ : σ • Q = Q) : σ ∈ Q.inertia (Pi1 A K) := by
  refine AddSubgroup.mem_inertia.2 fun x => ?_
  obtain ⟨c, hc, hxc⟩ := exists_const_sub_mem he hζ hcard x
  have hσc : σ • c = c := Subtype.ext ((mem_pi1geo A K _ σ).1 hσ _ (mem_constSub.1 hc))
  have h1 : σ • (x - c) ∈ Q := by
    rw [← hQ]
    exact Ideal.smul_mem_pointwise_smul σ _ Q hxc
  have h2 : σ • x - x = σ • (x - c) - (x - c) := by
    rw [smul_sub, hσc]
    abel
  rw [h2]
  exact Q.sub_mem h1 hxc

end Stab

section Conj

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E}

/-- **Kummer characters under conjugation**: if `α = γ β`, `γ ζ = ζ` and `(τ β / β) ^ N = 1`, then
`kchar α (γ τ γ⁻¹) = kchar β τ`. -/
theorem kchar_conj (hζ : IsPrimitiveRoot ζ N) {J J' : Subgroup (E ≃ₐ[K] E)} {γ : E ≃ₐ[K] E} (hγ : γ ζ = ζ)
    {α β : Eˣ} (hβ : (α : E) = γ (β : E)) (τ : J) (hτ' : γ * (τ : E ≃ₐ[K] E) * γ⁻¹ ∈ J')
    (hpow : ((τ : E ≃ₐ[K] E) (β : E) / β) ^ N = 1) :
    kchar hζ (Γ := J') α ⟨γ * (τ : E ≃ₐ[K] E) * γ⁻¹, hτ'⟩ = kchar hζ (Γ := J) β τ := by
  have h1 : (γ * (τ : E ≃ₐ[K] E) * γ⁻¹) (α : E) / α = γ ((τ : E ≃ₐ[K] E) (β : E) / β) := by
    rw [map_div₀, hβ]
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have h2 : γ ((τ : E ≃ₐ[K] E) (β : E) / β) = (τ : E ≃ₐ[K] E) (β : E) / β := by
    rw [← epow_dlog hζ hpow]
    exact map_epow hγ _
  show dlog hζ _ = dlog hζ _
  rw [h1, h2]

end Conj

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_ResTr =====
section

/-!
# S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation

* `inclU_restrict`, `exists_valuation_transport` (L3): if `τ` is the restriction of `g` to a normal level `L`, the
  place of `L` under `g • Q` is the transport of the place under `Q`, and `v_{gQ}(τ b) = v_Q(b)`.
* `norm_conj` (L4, one level): a generator normalised at `(L, Q)` conjugates by `x` (fixing `ζ_N`) to a generator
  normalised at `(L, x • Q)`.
* `NormAll`, `normAll_conj` (L4, S3 chart): the same at all constant levels `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k`.
* `chi_eq_of_norm` (L5): two generators normalised at the same prime have the same value under every locally
  constant hom `Γ_H → ℤ/N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Transport

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- The restriction `τ` of `g` to `L` commutes with `inclU`. -/
theorem inclU_restrict {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    {g : Pi1 A K} {τ : L ≃ₐ[K] L}
    (hτ : ∀ y : L, ((τ y : L) : AlgebraicClosure K) =
      ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K))
    (y : integralClosure R0 L) :
    inclU R0 hLU ((τ.restrictScalars R0).mapIntegralClosure y) = g • inclU R0 hLU y := by
  apply Subtype.ext
  apply Subtype.ext
  show ((τ (y : L) : L) : AlgebraicClosure K) =
    ((g ((inclU R0 hLU y : proChart A K R0) : maxUnram A K) : maxUnram A K) : AlgebraicClosure K)
  rw [hτ]
  rfl

/-- **(L3) Valuation transport**: the place under `g • Q` is the `τ`-transport of the place under `Q`. -/
theorem exists_valuation_transport {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    {g : Pi1 A K} {τ : L ≃ₐ[K] L}
    (hτ : ∀ y : L, ((τ y : L) : AlgebraicClosure K) =
      ((g (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K))
    {Q : Ideal (proChart A K R0)} (v' : HeightOneSpectrum (integralClosure R0 L))
    (hv' : v'.asIdeal = (g • Q).comap (inclU R0 hLU)) :
    ∃ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) ∧
      ∀ b : L, v'.valuation L (τ b) = v.valuation L b := by
  let e : integralClosure R0 L ≃+* integralClosure R0 L :=
    ((τ.restrictScalars R0).mapIntegralClosure).toRingEquiv
  have he : ∀ y, inclU R0 hLU (e y) = g • inclU R0 hLU y := inclU_restrict hLU hτ
  have hvv : HeightOneSpectrum.equivOfRingEquiv e (HeightOneSpectrum.equivOfRingEquiv e.symm v') = v' := by
    apply HeightOneSpectrum.ext
    ext y
    show e.symm.symm (e.symm y) ∈ v'.asIdeal ↔ y ∈ v'.asIdeal
    rw [RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
  refine ⟨HeightOneSpectrum.equivOfRingEquiv e.symm v', ?_, fun b => ?_⟩
  · ext y
    show e.symm.symm y ∈ v'.asIdeal ↔ inclU R0 hLU y ∈ Q
    rw [RingEquiv.symm_symm, hv', Ideal.mem_comap, he, Ideal.smul_mem_pointwise_smul_iff]
  · have h := ZetaSB.valuation_equiv e (τ : L →+* L) (fun r => rfl)
      (HeightOneSpectrum.equivOfRingEquiv e.symm v') b
    rw [hvv] at h
    exact h

end Transport

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- **(L4) at one level**: if `τ ∈ J` (fixing `L`) is normalised at `(L, Q)` and `x` fixes `ζ_N`, then
`x τ x⁻¹ ∈ J'` is normalised at `(L, x • Q)`. -/
theorem norm_conj {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    [hD : IsDedekindDomain (integralClosure R0 L)] [hF : IsFractionRing (integralClosure R0 L) L]
    {N : ℕ} [NeZero N] {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N)
    {J J' : Subgroup (Pi1 A K)} (τ : J) {x : Pi1 A K} (hx : x ζN = ζN)
    (hτ' : x * (τ : Pi1 A K) * x⁻¹ ∈ J')
    (hτL : ∀ y : L, (τ : Pi1 A K) (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y)
    (Q : Ideal (proChart A K R0))
    (hn : ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
      ∀ (α : (maxUnram A K)ˣ) (b : L), (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation L b) : ℤ) : ZMod N))
    (v' : HeightOneSpectrum (integralClosure R0 L)) (hv' : v'.asIdeal = (x • Q).comap (inclU R0 hLU))
    (α : (maxUnram A K)ˣ) (b : L) (hαb : (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b) :
    kchar hζN (Γ := J') α ⟨x * (τ : Pi1 A K) * x⁻¹, hτ'⟩ =
      ((WithZero.log (v'.valuation L b) : ℤ) : ZMod N) := by
  obtain ⟨σL, hσL⟩ := exists_restrict hLU x
  obtain ⟨v, hv, hval⟩ := exists_valuation_transport hLU hσL v' hv'
  have hxi : ∀ y : L, x (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (σL y) :=
    fun y => Subtype.ext (hσL y).symm
  let β : (maxUnram A K)ˣ := Units.map (x⁻¹ : Pi1 A K).toRingEquiv.toMonoidHom α
  have hβ' : (β : maxUnram A K) = (x⁻¹ : Pi1 A K) α := rfl
  have hβ : (α : maxUnram A K) = x (β : maxUnram A K) := by
    rw [hβ', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hb' : (β : maxUnram A K) ^ N = IntermediateField.inclusion hLU (σL.symm b) := by
    have h := hxi (σL.symm b)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [hβ', ← map_pow, hαb, ← h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hpow : ((τ : Pi1 A K) (β : maxUnram A K) / β) ^ N = 1 := by
    rw [div_pow, ← map_pow, hb', hτL, div_self]
    rw [← hb']
    exact pow_ne_zero _ β.ne_zero
  rw [kchar_conj hζN hx hβ τ hτ' hpow, hn v hv β (σL.symm b) hb', ← hval, AlgEquiv.apply_symm_apply]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
/-- `τ ∈ J` is normalised at `Q` at every constant level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k` (the `hnorm` shape of
`exists_norm_tau_sum`, for one prime). -/
abbrev NormAll (p e : ℕ) {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (M : IntermediateField F (AlgebraicClosure F))
    (Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) (J : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (τ : J) (k₀ : ℕ) : Prop :=
  ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
      ↥(M ⊔ constLevel F p (e * k))]
    (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
    v.asIdeal = Q.comap (inclU (Places.Rinf Fq F) hLU) →
    ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
      (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
      kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **(L4)** Conjugating a normalised geometric generator by `x` (fixing `ζ_N`) gives a normalised generator at
`x • Q`. -/
theorem normAll_conj {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {J J' : Subgroup (Pi1 (Places.Rfin Fq F) F)} (τ : J)
    (hτg : (τ : Pi1 (Places.Rfin Fq F) F) ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))
    (hτM : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {x : Pi1 (Places.Rfin Fq F) F} (hx : x ζN = ζN) (hτ' : x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹ ∈ J')
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))} {k₀ : ℕ}
    (hn : NormAll p e hζN M Q J τ k₀) :
    NormAll p e hζN M (x • Q) J' ⟨x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹, hτ'⟩ k₀ := by
  intro k hk hdvd hLU hD hF v' hv' α b hαb
  have hLM : M ⊔ constLevel F p (e * k) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hk))
  have : IsGalois F ↥(M ⊔ constLevel F p (e * k)) := hLM.2.1
  have hCU : constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hLU
  have hτC : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hk) ((IntermediateField.mem_restrict hCU _).1 hy) _
      (by rw [← hq]; exact hτg)
  have hτL' := mem_fix_sup hMU hCU hτM hτC
  have hτL : ∀ y : ↥(M ⊔ constLevel F p (e * k)), (τ : Pi1 (Places.Rfin Fq F) F)
      (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y := fun y =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτL' _ ((IntermediateField.mem_restrict _ _).2 y.2)
  exact norm_conj (hD := hD) (hF := hF) hLU hζN τ hx hτ' hτL Q (fun v hv => @hn k hk hdvd hLU hD hF v hv)
    v' hv' α b hαb

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **(L5)** Two generators normalised at the same boundary prime have the same value under every locally constant
hom `χ : Γ_H → ℤ/N`. -/
theorem chi_eq_of_norm {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hζΓ : ∀ σ ∈ Γ, σ ζN = ζN)
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    (J : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : J ≤ Γ) (τ τ' : J) {k₀ k₀' : ℕ} (hk₀ : 0 < k₀)
    (hk₀' : 0 < k₀') (hn : NormAll p e hζN M Q J τ k₀) (hn' : NormAll p e hζN M Q J τ' k₀')
    (χ : Γ → ZMod N) (hχc : IsLocallyConstant χ) (hχ : ∀ σ σ', χ (σ * σ') = χ σ + χ σ') :
    χ ⟨τ, hJΓ τ.2⟩ = χ ⟨τ', hJΓ τ'.2⟩ := by
  obtain ⟨α, hαr, hαχ⟩ := exists_kchar_eq hζN hζΓ χ hχc hχ
  have hfixx : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup →
      σ ((α : maxUnram (Places.Rfin Fq F) F) ^ N) = (α : maxUnram (Places.Rfin Fq F) F) ^ N := by
    intro σ hσg hσM
    exact (mem_rad _ _ α).1 hαr σ ((hΓ σ).2 ⟨by rw [hq]; exact hσg, hσM⟩)
  obtain ⟨k1, hk1, hx1⟩ := exists_sup_constLevel_of_fixed he hMU hfixx
  obtain ⟨m, hm_def⟩ : ∃ m, m = k₀ * k₀' * k1 := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos (Nat.mul_pos hk₀ hk₀') hk1
  have hdvd0 : k₀ ∣ m := ⟨k₀' * k1, by rw [hm_def]; ring⟩
  have hdvd0' : k₀' ∣ m := ⟨k₀ * k1, by rw [hm_def]; ring⟩
  have hdvd1 : k1 ∣ m := ⟨k₀ * k₀', by rw [hm_def]; ring⟩
  have hLM : M ⊔ constLevel F p (e * m) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hm))
  have hLU : M ⊔ constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hLM
  have hFDL : FiniteDimensional F ↥(M ⊔ constLevel F p (e * m)) := hLM.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * m)) := hLM.2.1
  have hDedI : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracI : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  have hxL : (((α : maxUnram (Places.Rfin Fq F) F) ^ N : maxUnram (Places.Rfin Fq F) F) :
      AlgebraicClosure F) ∈ M ⊔ constLevel F p (e * m) :=
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hm) (Nat.mul_dvd_mul_left e hdvd1)) M hx1
  let b : ↥(M ⊔ constLevel F p (e * m)) := ⟨_, hxL⟩
  let v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    ⟨Q.comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := hQ.1), comap_inclU_ne_bot hLU hQ⟩
  have h1 := @hn m hm hdvd0 hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  have h2 := @hn' m hm hdvd0' hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  rw [← hαχ, ← hαχ]
  show kchar hζN (Γ := J) α τ = kchar hζN (Γ := J) α τ'
  rw [h1, h2]

end S3

end

end Residue
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_TwNorm =====
section

/-!
# S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation

The twisted forms of `kchar_conj`, `norm_conj`, `normAll_conj` and `chi_eq_of_norm` (`Def_RP_Cone_ResTr`): if `x`
acts on `ζ_N` by `x ζ_N = ζ_N ^ w` (e.g. a Frobenius lift, `w = q`), then conjugating a normalised generator by `x`
gives a generator `w`-normalised at `x • Q` (`NormAllTw`), and a `w`-normalised generator has `w` times the
`χ`-value of a normalised one at the same prime (`chi_eq_of_normTw`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section ConjTw

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E}

/-- **Kummer characters under twisted conjugation**: if `α = γ β`, `γ ζ = ζ ^ w` and `(τ β / β) ^ N = 1`, then
`kchar α (γ τ γ⁻¹) = w * kchar β τ`. -/
theorem kchar_conj_tw (hζ : IsPrimitiveRoot ζ N) {J J' : Subgroup (E ≃ₐ[K] E)} {γ : E ≃ₐ[K] E} {w : ZMod N}
    (hγ : γ ζ = epow ζ w) {α β : Eˣ} (hβ : (α : E) = γ (β : E)) (τ : J)
    (hτ' : γ * (τ : E ≃ₐ[K] E) * γ⁻¹ ∈ J') (hpow : ((τ : E ≃ₐ[K] E) (β : E) / β) ^ N = 1) :
    kchar hζ (Γ := J') α ⟨γ * (τ : E ≃ₐ[K] E) * γ⁻¹, hτ'⟩ = w * kchar hζ (Γ := J) β τ := by
  have h1 : (γ * (τ : E ≃ₐ[K] E) * γ⁻¹) (α : E) / α = γ ((τ : E ≃ₐ[K] E) (β : E) / β) := by
    rw [map_div₀, hβ]
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have e1 : (τ : E ≃ₐ[K] E) (β : E) / β = ζ ^ (dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)).val :=
    (epow_dlog hζ hpow).symm
  have h2 : γ ((τ : E ≃ₐ[K] E) (β : E) / β) = epow ζ (w * dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)) := by
    calc γ ((τ : E ≃ₐ[K] E) (β : E) / β)
        = γ (ζ ^ (dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)).val) := congrArg (fun z => γ z) e1
      _ = (γ ζ) ^ (dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)).val := map_pow _ _ _
      _ = epow ζ (w * dlog hζ ((τ : E ≃ₐ[K] E) (β : E) / β)) := by rw [hγ, epow_pow hζ]
  show dlog hζ _ = w * dlog hζ _
  rw [h1, h2, dlog_epow]

end ConjTw

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

/-- **Twisted (L4) at one level**: if `τ ∈ J` (fixing `L`) is normalised at `(L, Q)` and `x ζ_N = ζ_N ^ w`, then
`x τ x⁻¹ ∈ J'` is `w`-normalised at `(L, x • Q)`. -/
theorem norm_conj_tw {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K) [Normal K L]
    [hD : IsDedekindDomain (integralClosure R0 L)] [hF : IsFractionRing (integralClosure R0 L) L]
    {N : ℕ} [NeZero N] {ζN : maxUnram A K} (hζN : IsPrimitiveRoot ζN N)
    {J J' : Subgroup (Pi1 A K)} (τ : J) {x : Pi1 A K} {w : ZMod N} (hx : x ζN = epow ζN w)
    (hτ' : x * (τ : Pi1 A K) * x⁻¹ ∈ J')
    (hτL : ∀ y : L, (τ : Pi1 A K) (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y)
    (Q : Ideal (proChart A K R0))
    (hn : ∀ v : HeightOneSpectrum (integralClosure R0 L), v.asIdeal = Q.comap (inclU R0 hLU) →
      ∀ (α : (maxUnram A K)ˣ) (b : L), (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b →
        kchar hζN (Γ := J) α τ = ((WithZero.log (v.valuation L b) : ℤ) : ZMod N))
    (v' : HeightOneSpectrum (integralClosure R0 L)) (hv' : v'.asIdeal = (x • Q).comap (inclU R0 hLU))
    (α : (maxUnram A K)ˣ) (b : L) (hαb : (α : maxUnram A K) ^ N = IntermediateField.inclusion hLU b) :
    kchar hζN (Γ := J') α ⟨x * (τ : Pi1 A K) * x⁻¹, hτ'⟩ =
      w * ((WithZero.log (v'.valuation L b) : ℤ) : ZMod N) := by
  obtain ⟨σL, hσL⟩ := exists_restrict hLU x
  obtain ⟨v, hv, hval⟩ := exists_valuation_transport hLU hσL v' hv'
  have hxi : ∀ y : L, x (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (σL y) :=
    fun y => Subtype.ext (hσL y).symm
  let β : (maxUnram A K)ˣ := Units.map (x⁻¹ : Pi1 A K).toRingEquiv.toMonoidHom α
  have hβ' : (β : maxUnram A K) = (x⁻¹ : Pi1 A K) α := rfl
  have hβ : (α : maxUnram A K) = x (β : maxUnram A K) := by
    rw [hβ', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hb' : (β : maxUnram A K) ^ N = IntermediateField.inclusion hLU (σL.symm b) := by
    have h := hxi (σL.symm b)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [hβ', ← map_pow, hαb, ← h, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hpow : ((τ : Pi1 A K) (β : maxUnram A K) / β) ^ N = 1 := by
    rw [div_pow, ← map_pow, hb', hτL, div_self]
    rw [← hb']
    exact pow_ne_zero _ β.ne_zero
  rw [kchar_conj_tw hζN hx hβ τ hτ' hpow, hn v hv β (σL.symm b) hb', ← hval, AlgEquiv.apply_symm_apply]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `τ ∈ J` is `w`-normalised at `Q` at every constant level `M ⊔ K(𝔽_{p^(e k)})` with `k₀ ∣ k`. -/
abbrev NormAllTw (p e : ℕ) {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (M : IntermediateField F (AlgebraicClosure F))
    (Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) (J : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (τ : J) (k₀ : ℕ) (w : ZMod N) : Prop :=
  ∀ k, 0 < k → k₀ ∣ k → ∀ (hLU : M ⊔ constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F)
    [IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))]
    [IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))
      ↥(M ⊔ constLevel F p (e * k))]
    (v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * k)))),
    v.asIdeal = Q.comap (inclU (Places.Rinf Fq F) hLU) →
    ∀ (α : (maxUnram (Places.Rfin Fq F) F)ˣ) (b : ↥(M ⊔ constLevel F p (e * k))),
      (α : maxUnram (Places.Rfin Fq F) F) ^ N = IntermediateField.inclusion hLU b →
      kchar hζN (Γ := J) α τ = w * ((WithZero.log (v.valuation ↥(M ⊔ constLevel F p (e * k)) b) : ℤ) : ZMod N)

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Twisted (L4)**: conjugating a normalised geometric generator by `x` with `x ζ_N = ζ_N ^ w` gives a
`w`-normalised generator at `x • Q`. -/
theorem normAll_conj_tw {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {J J' : Subgroup (Pi1 (Places.Rfin Fq F) F)} (τ : J)
    (hτg : (τ : Pi1 (Places.Rfin Fq F) F) ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq))
    (hτM : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {x : Pi1 (Places.Rfin Fq F) F} {w : ZMod N} (hx : x ζN = epow ζN w)
    (hτ' : x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹ ∈ J')
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))} {k₀ : ℕ}
    (hn : NormAll p e hζN M Q J τ k₀) :
    NormAllTw p e hζN M (x • Q) J' ⟨x * (τ : Pi1 (Places.Rfin Fq F) F) * x⁻¹, hτ'⟩ k₀ w := by
  intro k hk hdvd hLU hD hF v' hv' α b hαb
  have hLM : M ⊔ constLevel F p (e * k) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hk))
  have : IsGalois F ↥(M ⊔ constLevel F p (e * k)) := hLM.2.1
  have hCU : constLevel F p (e * k) ≤ maxUnram (Places.Rfin Fq F) F := le_sup_right.trans hLU
  have hτC : (τ : Pi1 (Places.Rfin Fq F) F) ∈ (IntermediateField.restrict hCU).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact fixed_of_mem_constLevel he (Nat.mul_pos he hk) ((IntermediateField.mem_restrict hCU _).1 hy) _
      (by rw [← hq]; exact hτg)
  have hτL' := mem_fix_sup hMU hCU hτM hτC
  have hτL : ∀ y : ↥(M ⊔ constLevel F p (e * k)), (τ : Pi1 (Places.Rfin Fq F) F)
      (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y := fun y =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτL' _ ((IntermediateField.mem_restrict _ _).2 y.2)
  exact norm_conj_tw (hD := hD) (hF := hF) hLU hζN τ hx hτ' hτL Q (fun v hv => @hn k hk hdvd hLU hD hF v hv)
    v' hv' α b hαb

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Twisted (L5)**: a `w`-normalised generator has `w` times the `χ`-value of a normalised generator at the same
boundary prime, for every locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem chi_eq_of_normTw {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hζΓ : ∀ σ ∈ Γ, σ ζN = ζN)
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    (J : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : J ≤ Γ) (τ τ' : J) {k₀ k₀' : ℕ} (hk₀ : 0 < k₀)
    (hk₀' : 0 < k₀') {w : ZMod N} (hn : NormAllTw p e hζN M Q J τ k₀ w) (hn' : NormAll p e hζN M Q J τ' k₀')
    (χ : Γ → ZMod N) (hχc : IsLocallyConstant χ) (hχ : ∀ σ σ', χ (σ * σ') = χ σ + χ σ') :
    χ ⟨τ, hJΓ τ.2⟩ = w * χ ⟨τ', hJΓ τ'.2⟩ := by
  obtain ⟨α, hαr, hαχ⟩ := exists_kchar_eq hζN hζΓ χ hχc hχ
  have hfixx : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup →
      σ ((α : maxUnram (Places.Rfin Fq F) F) ^ N) = (α : maxUnram (Places.Rfin Fq F) F) ^ N := by
    intro σ hσg hσM
    exact (mem_rad _ _ α).1 hαr σ ((hΓ σ).2 ⟨by rw [hq]; exact hσg, hσM⟩)
  obtain ⟨k1, hk1, hx1⟩ := exists_sup_constLevel_of_fixed he hMU hfixx
  obtain ⟨m, hm_def⟩ : ∃ m, m = k₀ * k₀' * k1 := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos (Nat.mul_pos hk₀ hk₀') hk1
  have hdvd0 : k₀ ∣ m := ⟨k₀' * k1, by rw [hm_def]; ring⟩
  have hdvd0' : k₀' ∣ m := ⟨k₀ * k1, by rw [hm_def]; ring⟩
  have hdvd1 : k1 ∣ m := ⟨k₀ * k₀', by rw [hm_def]; ring⟩
  have hLM : M ⊔ constLevel F p (e * m) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hm))
  have hLU : M ⊔ constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hLM
  have hFDL : FiniteDimensional F ↥(M ⊔ constLevel F p (e * m)) := hLM.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * m)) := hLM.2.1
  have hDedI : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracI : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  have hxL : (((α : maxUnram (Places.Rfin Fq F) F) ^ N : maxUnram (Places.Rfin Fq F) F) :
      AlgebraicClosure F) ∈ M ⊔ constLevel F p (e * m) :=
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hm) (Nat.mul_dvd_mul_left e hdvd1)) M hx1
  let b : ↥(M ⊔ constLevel F p (e * m)) := ⟨_, hxL⟩
  let v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    ⟨Q.comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := hQ.1), comap_inclU_ne_bot hLU hQ⟩
  have h1 := @hn m hm hdvd0 hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  have h2 := @hn' m hm hdvd0' hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  rw [← hαχ, ← hαχ]
  show kchar hζN (Γ := J) α τ = w * kchar hζN (Γ := J) α τ'
  rw [h1, h2]

end S3

end

end Residue
end RamanujanPetersson

end


