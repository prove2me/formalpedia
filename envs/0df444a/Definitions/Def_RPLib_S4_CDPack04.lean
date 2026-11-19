-- Prove2me | Definitions.Def_RPLib_S4_CDPack04
-- name    : RPLib_S4_CDPack04
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:23:24.133579+00:00
-- url     : https://prove2.me/theorems/c4a59167-bccb-4361-9bdc-066bf38ce91b
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 4 of 71
-- statement:
--   Part 4 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_HattoriStallings_Twisted`: Hattori–Stallings traces, part B1: trace relations, the twisted-trace formula, base change
--   * `Def_RP_HattoriStallings_Complex`: Hattori–Stallings traces, part B2: bounded complexes (Lefschetz numbers)
--   * `Def_RP_PerfectCx_Tri`: S4-PD (5), E3: three-term complexes as `ℕ`-indexed families
--   * `Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
--   * `Def_RP_PerfectCx_CxNat`: S4-PD (5), E3: the identification `P ⊗_{Λ[Gf]} M ≅ K(M)` is natural in `M`
--   * `Def_RP_HattoriStallings_CT`: Hattori–Stallings traces, part C: cohomologically trivial modules are projective
--   * `Def_RP_PerfectCx_Proj`: S4-PD (5), E2(b): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ[Gf]`-projective
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack03

/-!
# Curve-duality library package, part 4 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_HattoriStallings_Twisted`: Hattori–Stallings traces, part B1: trace relations, the twisted-trace formula, base change
* `Def_RP_HattoriStallings_Complex`: Hattori–Stallings traces, part B2: bounded complexes (Lefschetz numbers)
* `Def_RP_PerfectCx_Tri`: S4-PD (5), E3: three-term complexes as `ℕ`-indexed families
* `Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
* `Def_RP_PerfectCx_CxNat`: S4-PD (5), E3: the identification `P ⊗_{Λ[Gf]} M ≅ K(M)` is natural in `M`
* `Def_RP_HattoriStallings_CT`: Hattori–Stallings traces, part C: cohomologically trivial modules are projective
* `Def_RP_PerfectCx_Proj`: S4-PD (5), E2(b): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ[Gf]`-projective
-/

set_option autoImplicit false

-- ===== S4.Def_RP_HattoriStallings_Twisted =====
section

/-!
# Hattori–Stallings traces, part B1: trace relations, the twisted-trace formula, base change

* `trace_inv_comp_eq_sum`, `trace_inv_comp_eq_card_mul_hs`:
  `Tr_R (ρ γ⁻¹ ∘ φ) = ∑_h hsFun (h⁻¹ γ h) = |Z(γ)| · hs φ [γ]` (`trace_eq_card_mul_hs_one` for `γ = 1`).
* `trace_coinvMap_tprod` (SGA 4½ *Rapport*, twisted trace formula): on the coinvariants
  `(P ⊗ M)_G = P ⊗_{R[G]} M`, `Tr (φ ⊗ ψ) = ∑_g hsFun E φ g · Tr (τ g⁻¹ ∘ ψ) = ∑_c hs φ c · χ_ψ c`.
* `hs_baseChange`: `hs` commutes with base change `R → A` (e.g. reduction `ZMod (ℓ^n) → ZMod (ℓ^m)`).
* `hs_conj`: invariance under equivariant isomorphisms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap TensorProduct

section TraceRel

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}
variable [Module.Free R P] [Module.Finite R P]

lemma rep_conj_inv (h γ : G) :
    ρ (h⁻¹ * γ * h)⁻¹ = ρ h⁻¹ ∘ₗ ρ γ⁻¹ ∘ₗ ρ h := by
  rw [show (h⁻¹ * γ * h)⁻¹ = h⁻¹ * γ⁻¹ * h by group, map_mul, map_mul]
  rfl

/-- `Tr_R (ρ γ⁻¹ ∘ φ) = ∑_h hsFun E φ (h⁻¹ γ h)`. -/
theorem trace_inv_comp_eq_sum {E : P →ₗ[R] P} (hE : IsHigman ρ E) {φ : P →ₗ[R] P}
    (hφ : IsEquivariant ρ ρ φ) (γ : G) :
    trace R P (ρ γ⁻¹ ∘ₗ φ) = ∑ h : G, hsFun ρ E φ (h⁻¹ * γ * h) := by
  have hsplit : ρ γ⁻¹ ∘ₗ φ = ∑ h : G, (ρ γ⁻¹ ∘ₗ ρ h ∘ₗ φ ∘ₗ E) ∘ₗ ρ h⁻¹ := by
    refine LinearMap.ext fun v => ?_
    simp only [comp_apply, LinearMap.sum_apply]
    conv_lhs => rw [← hE.apply v]
    simp [map_sum, hφ.apply]
  rw [hsplit, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [trace_comp_comm', hsFun, rep_conj_inv]
  rfl

open Classical in
lemma card_conj_fiber (γ g : G) (hg : IsConj γ g) :
    (Finset.univ.filter fun h : G => h⁻¹ * γ * h = g).card =
      (Finset.univ.filter fun z : G => z⁻¹ * γ * z = γ).card := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hg
  refine Finset.card_nbij' (fun h => h * c) (fun z => z * c⁻¹) ?_ ?_ ?_ ?_
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    calc (h * c)⁻¹ * γ * (h * c) = c⁻¹ * (h⁻¹ * γ * h) * c := by group
      _ = γ := by rw [hh, ← hc]; group
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    calc (z * c⁻¹)⁻¹ * γ * (z * c⁻¹) = c * (z⁻¹ * γ * z) * c⁻¹ := by group
      _ = g := by rw [hz, hc]
  · intro h _; simp
  · intro z _; simp

open Classical in
lemma card_conj_fiber_eq_zero (γ g : G) (hg : ¬ IsConj γ g) :
    (Finset.univ.filter fun h : G => h⁻¹ * γ * h = g).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro h _ hh
  exact hg (isConj_iff.2 ⟨h⁻¹, by rw [inv_inv, hh]⟩)

/-- Fibre counting: `∑_h f (h⁻¹ γ h) = |Z(γ)| · ∑_{g ∈ [γ]} f g`. -/
lemma sum_conj_eq_card_mul_classSum (f : G → R) (γ : G) :
    ∑ h : G, f (h⁻¹ * γ * h) =
      (Nat.card {z : G // z⁻¹ * γ * z = γ} : R) * classSum f (ConjClasses.mk γ) := by
  classical
  have hZ : Nat.card {z : G // z⁻¹ * γ * z = γ} =
      (Finset.univ.filter fun z : G => z⁻¹ * γ * z = γ).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hZ, classSum_apply, Finset.mul_sum]
  have e1 : ∀ h : G, f (h⁻¹ * γ * h) = ∑ g : G, if h⁻¹ * γ * h = g then f g else 0 := fun h => by
    rw [Finset.sum_ite_eq]; simp
  simp_rw [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  by_cases hg : IsConj γ g
  · have hmk : ConjClasses.mk g = ConjClasses.mk γ :=
      (ConjClasses.mk_eq_mk_iff_isConj.2 hg).symm
    rw [if_pos hmk, card_conj_fiber γ g hg]
  · have hmk : ¬ ConjClasses.mk g = ConjClasses.mk γ := fun h =>
      hg (ConjClasses.mk_eq_mk_iff_isConj.1 h.symm)
    rw [if_neg hmk, card_conj_fiber_eq_zero γ g hg]
    simp

/-- `Tr_R (ρ γ⁻¹ ∘ φ) = |Z(γ)| · hs φ [γ]`. -/
theorem trace_inv_comp_eq_card_mul_hs (hρ : IsProj ρ) {φ : P →ₗ[R] P}
    (hφ : IsEquivariant ρ ρ φ) (γ : G) :
    trace R P (ρ γ⁻¹ ∘ₗ φ) =
      (Nat.card {z : G // z⁻¹ * γ * z = γ} : R) * hs ρ φ (ConjClasses.mk γ) := by
  obtain ⟨E, hE⟩ := hρ
  rw [trace_inv_comp_eq_sum hE hφ, hs_eq hE hφ, sum_conj_eq_card_mul_classSum]

/-- `Tr_R φ = |G| · hs φ [1]`. -/
theorem trace_eq_card_mul_hs_one (hρ : IsProj ρ) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ) :
    trace R P φ = (Fintype.card G : R) * hs ρ φ (ConjClasses.mk 1) := by
  have := trace_inv_comp_eq_card_mul_hs hρ hφ 1
  simp only [inv_one, map_one, Module.End.one_eq_id, LinearMap.id_comp] at this
  rw [this]
  congr 2
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun z : G => show z⁻¹ * 1 * z = 1 by group)),
    Nat.card_eq_fintype_card]

end TraceRel

section Coinv

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The endomorphism of the coinvariants induced by an equivariant endomorphism. -/
noncomputable def coinvMap (θ : Representation R G V) (F : V →ₗ[R] V) (hF : IsEquivariant θ θ F) :
    Representation.Coinvariants θ →ₗ[R] Representation.Coinvariants θ :=
  Representation.Coinvariants.lift θ (Representation.Coinvariants.mk θ ∘ₗ F) fun g =>
    LinearMap.ext fun x => by
      simp [hF.apply, Representation.Coinvariants.mk_self_apply]

lemma coinvMap_mk (θ : Representation R G V) (F : V →ₗ[R] V) (hF : IsEquivariant θ θ F) (x : V) :
    coinvMap θ F hF (Representation.Coinvariants.mk θ x) = Representation.Coinvariants.mk θ (F x) :=
  rfl

end Coinv

section Twisted

lemma sum_comp' {R : Type*} [CommRing R] {A B C : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] {ι : Type*} (s : Finset ι)
    (f : ι → B →ₗ[R] C) (g : A →ₗ[R] B) : (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g :=
  LinearMap.ext fun x => by simp [LinearMap.sum_apply]

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}
variable {M : Type*} [AddCommGroup M] [Module R M] {τ : Representation R G M}

lemma isEquivariant_tensorMap {φ : P →ₗ[R] P} {ψ : M →ₗ[R] M} (hφ : IsEquivariant ρ ρ φ)
    (hψ : IsEquivariant τ τ ψ) :
    IsEquivariant (Representation.tprod ρ τ) (Representation.tprod ρ τ) (TensorProduct.map φ ψ) :=
  fun g => by
    rw [Representation.tprod_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp, hφ g, hψ g]

/-- The right-invariant map `(E ⊗ 1) ∘ ∑_h θ h` that induces a section of the coinvariants. -/
noncomputable def twSec (ρ : Representation R G P) (τ : Representation R G M) (E : P →ₗ[R] P) :
    P ⊗[R] M →ₗ[R] P ⊗[R] M :=
  ∑ h : G, TensorProduct.map E LinearMap.id ∘ₗ Representation.tprod ρ τ h

lemma twSec_comp (E : P →ₗ[R] P) (g : G) :
    twSec ρ τ E ∘ₗ Representation.tprod ρ τ g = twSec ρ τ E := by
  refine LinearMap.ext fun x => ?_
  simp only [twSec, comp_apply, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => ?_)
  rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply]

lemma sum_tw_eq_id {E : P →ₗ[R] P} (hE : IsHigman ρ E) :
    ∑ h : G, Representation.tprod ρ τ h⁻¹ ∘ₗ TensorProduct.map E LinearMap.id ∘ₗ
      Representation.tprod ρ τ h = LinearMap.id := by
  refine TensorProduct.ext' fun p m => ?_
  simp only [LinearMap.sum_apply, comp_apply, Representation.tprod_apply, map_tmul, id_apply,
    rep_inv_apply_apply]
  rw [← TensorProduct.sum_tmul, hE.apply_inv]

lemma mk_twSec {E : P →ₗ[R] P} (hE : IsHigman ρ E) (x : P ⊗[R] M) :
    Representation.Coinvariants.mk (Representation.tprod ρ τ) (twSec ρ τ E x) =
      Representation.Coinvariants.mk (Representation.tprod ρ τ) x := by
  have key := LinearMap.congr_fun (sum_tw_eq_id (τ := τ) hE) x
  rw [LinearMap.id_apply] at key
  conv_rhs => rw [← key]
  simp only [twSec, LinearMap.sum_apply, comp_apply, id_apply, map_sum,
    Representation.Coinvariants.mk_self_apply]

/-- The section `s : (P ⊗ M)_G → P ⊗ M` of the quotient map, for a Higman datum `E`. -/
noncomputable def coinvSec (ρ : Representation R G P) (τ : Representation R G M) (E : P →ₗ[R] P) :
    Representation.Coinvariants (Representation.tprod ρ τ) →ₗ[R] P ⊗[R] M :=
  Representation.Coinvariants.lift _ (twSec ρ τ E) (twSec_comp E)

lemma mk_comp_coinvSec {E : P →ₗ[R] P} (hE : IsHigman ρ E) :
    Representation.Coinvariants.mk (Representation.tprod ρ τ) ∘ₗ coinvSec ρ τ E = LinearMap.id := by
  refine Representation.Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
  simp only [comp_apply, coinvSec, Representation.Coinvariants.lift_mk, id_apply]
  exact mk_twSec hE x

variable [Module.Free R P] [Module.Finite R P] [Module.Free R M] [Module.Finite R M]

/-- **Twisted trace formula** (SGA 4½, *Rapport*), density form: on `(P ⊗ M)_G = P ⊗_{R[G]} M`,
`Tr (φ ⊗ ψ) = ∑_g hsFun E φ g · Tr_R (τ g⁻¹ ∘ ψ)`. -/
theorem trace_coinvMap_tprod
    [Module.Free R (Representation.Coinvariants (Representation.tprod ρ τ))]
    [Module.Finite R (Representation.Coinvariants (Representation.tprod ρ τ))]
    {E : P →ₗ[R] P} (hE : IsHigman ρ E) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ)
    {ψ : M →ₗ[R] M} (hψ : IsEquivariant τ τ ψ) :
    trace R _ (coinvMap (Representation.tprod ρ τ) (TensorProduct.map φ ψ)
        (isEquivariant_tensorMap hφ hψ)) =
      ∑ g : G, hsFun ρ E φ g * trace R M (τ g⁻¹ ∘ₗ ψ) := by
  set q := Representation.Coinvariants.mk (Representation.tprod ρ τ)
  set s := coinvSec ρ τ E
  set FC := coinvMap (Representation.tprod ρ τ) (TensorProduct.map φ ψ)
    (isEquivariant_tensorMap hφ hψ)
  have hqs : q ∘ₗ s = LinearMap.id := mk_comp_coinvSec hE
  have hFq : FC ∘ₗ q = q ∘ₗ TensorProduct.map φ ψ := rfl
  have hsq : s ∘ₗ q = twSec ρ τ E := rfl
  have e1 : trace R _ FC = trace R _ (twSec ρ τ E ∘ₗ TensorProduct.map φ ψ) := by
    calc trace R _ FC = trace R _ (FC ∘ₗ (q ∘ₗ s)) := by rw [hqs, LinearMap.comp_id]
      _ = trace R _ ((q ∘ₗ TensorProduct.map φ ψ) ∘ₗ s) := by
          rw [← LinearMap.comp_assoc, hFq]
      _ = trace R _ (s ∘ₗ (q ∘ₗ TensorProduct.map φ ψ)) := trace_comp_comm' _ _
      _ = trace R _ (twSec ρ τ E ∘ₗ TensorProduct.map φ ψ) := by
          rw [← LinearMap.comp_assoc, hsq]
  rw [e1, twSec, sum_comp', map_sum]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ (fun h => ?_)
  rw [Representation.tprod_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    trace_tensorProduct', Equiv.inv_apply, hsFun, inv_inv, LinearMap.id_comp]
  congr 1
  rw [LinearMap.comp_assoc, trace_comp_comm' (ρ h ∘ₗ φ) E, LinearMap.comp_assoc]

omit [Module.Free R P] [Module.Finite R P] in
lemma trace_inv_comp_conj {ψ : M →ₗ[R] M} (hψ : IsEquivariant τ τ ψ) (k g : G) :
    trace R M (τ (k * g * k⁻¹)⁻¹ ∘ₗ ψ) = trace R M (τ g⁻¹ ∘ₗ ψ) := by
  have e : τ (k * g * k⁻¹)⁻¹ ∘ₗ ψ = τ k ∘ₗ ((τ g⁻¹ ∘ₗ ψ) ∘ₗ τ k⁻¹) := by
    rw [show (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ by group, map_mul, map_mul]
    refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, comp_apply]
    rw [hψ.apply]
  rw [e, trace_comp_comm' ((τ g⁻¹ ∘ₗ ψ) ∘ₗ τ k⁻¹) (τ k)]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp only [comp_apply, rep_inv_apply_apply]

open Classical in
/-- The class function `[g] ↦ Tr_R (τ g⁻¹ ∘ ψ)`. -/
noncomputable def twChar (τ : Representation R G M) (ψ : M →ₗ[R] M) : ConjClasses G → R :=
  fun c => trace R M (τ (ConjClasses.mk_surjective c).choose⁻¹ ∘ₗ ψ)

omit [Module.Free R P] [Module.Finite R P] in
lemma twChar_mk {ψ : M →ₗ[R] M} (hψ : IsEquivariant τ τ ψ) (g : G) :
    twChar τ ψ (ConjClasses.mk g) = trace R M (τ g⁻¹ ∘ₗ ψ) := by
  have hc := (ConjClasses.mk_surjective (ConjClasses.mk g)).choose_spec
  obtain ⟨k, hk⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hc)
  show trace R M (τ (ConjClasses.mk_surjective (ConjClasses.mk g)).choose⁻¹ ∘ₗ ψ) = _
  rw [← trace_inv_comp_conj hψ k, hk]

/-- **Twisted trace formula**, class form: `Tr (φ ⊗ ψ | P ⊗_{R[G]} M) = ∑_c hs φ c · Tr (c⁻¹ ∘ ψ)`. -/
theorem trace_coinvMap_tprod_eq_sum_hs [Fintype (ConjClasses G)]
    [Module.Free R (Representation.Coinvariants (Representation.tprod ρ τ))]
    [Module.Finite R (Representation.Coinvariants (Representation.tprod ρ τ))]
    (hρ : IsProj ρ) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ)
    {ψ : M →ₗ[R] M} (hψ : IsEquivariant τ τ ψ) :
    trace R _ (coinvMap (Representation.tprod ρ τ) (TensorProduct.map φ ψ)
        (isEquivariant_tensorMap hφ hψ)) =
      ∑ c : ConjClasses G, hs ρ φ c * twChar τ ψ c := by
  obtain ⟨E, hE⟩ := hρ
  rw [trace_coinvMap_tprod hE hφ hψ, hs_eq hE hφ]
  exact sum_mul_eq_sum_classSum _ _ _ (fun g => twChar_mk hψ g)

omit [Module.Free R M] [Module.Finite R M] in
/-- Over a local ring the coinvariants `P ⊗_{R[G]} M` of a projective `P` and a free finite `M` are
free and finite (they are a retract of `P ⊗ M`). -/
theorem coinv_free_finite [IsLocalRing R] [Module.Free R M] [Module.Finite R M]
    {E : P →ₗ[R] P} (hE : IsHigman ρ E) :
    Module.Free R (Representation.Coinvariants (Representation.tprod ρ τ)) ∧
      Module.Finite R (Representation.Coinvariants (Representation.tprod ρ τ)) :=
  free_finite_of_retract (P := P ⊗[R] M) (mk_comp_coinvSec hE)

end Twisted

section BaseChange

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}
variable (A : Type*) [CommRing A] [Algebra R A]

/-- Base change of a representation along `R → A`. -/
noncomputable def repBaseChange (ρ : Representation R G P) : Representation A G (A ⊗[R] P) :=
  (Module.End.baseChangeHom R A P).toMonoidHom.comp ρ

@[simp] lemma repBaseChange_apply (g : G) : repBaseChange A ρ g = (ρ g).baseChange A := rfl

variable {A}

lemma IsEquivariant.baseChange {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ) :
    IsEquivariant (repBaseChange A ρ) (repBaseChange A ρ) (φ.baseChange A) := fun g => by
  rw [repBaseChange_apply, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hφ g]

lemma IsHigman.baseChange {E : P →ₗ[R] P} (hE : IsHigman ρ E) :
    IsHigman (repBaseChange A ρ) (E.baseChange A) := by
  have h1 : ∑ h : G, (ρ h ∘ₗ E ∘ₗ ρ h⁻¹).baseChange A =
      (∑ h : G, ρ h ∘ₗ E ∘ₗ ρ h⁻¹).baseChange A :=
    (map_sum (LinearMap.baseChangeHom R A P P) _ _).symm
  have hE' : ∑ h : G, ρ h ∘ₗ E ∘ₗ ρ h⁻¹ = LinearMap.id := hE
  rw [hE', LinearMap.baseChange_id] at h1
  show ∑ h : G, repBaseChange A ρ h ∘ₗ E.baseChange A ∘ₗ repBaseChange A ρ h⁻¹ = LinearMap.id
  rw [← h1]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [repBaseChange_apply, repBaseChange_apply, LinearMap.baseChange_comp,
    LinearMap.baseChange_comp]

lemma IsProj.baseChange (hρ : IsProj ρ) : IsProj (repBaseChange A ρ) :=
  let ⟨_, hE⟩ := hρ
  ⟨_, hE.baseChange⟩

variable [Module.Free R P] [Module.Finite R P]

lemma hsFun_baseChange (E φ : P →ₗ[R] P) (g : G) :
    hsFun (repBaseChange A ρ) (E.baseChange A) (φ.baseChange A) g =
      algebraMap R A (hsFun ρ E φ g) := by
  rw [hsFun, hsFun, repBaseChange_apply, ← LinearMap.baseChange_comp,
    ← LinearMap.baseChange_comp, LinearMap.trace_baseChange]

lemma classSum_algebraMap (f : G → R) (c : ConjClasses G) :
    classSum (fun g => algebraMap R A (f g)) c = algebraMap R A (classSum f c) := by
  classical
  rw [classSum_apply, classSum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

/-- **Compatibility with base change** (e.g. reduction `ZMod (ℓ^n) → ZMod (ℓ^m)`). -/
theorem hs_baseChange (hρ : IsProj ρ) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ)
    (c : ConjClasses G) :
    hs (repBaseChange A ρ) (φ.baseChange A) c = algebraMap R A (hs ρ φ c) := by
  obtain ⟨E, hE⟩ := hρ
  have hf : hsFun (repBaseChange A ρ) (E.baseChange A) (φ.baseChange A) =
      fun g => algebraMap R A (hsFun ρ E φ g) := funext fun g => hsFun_baseChange E φ g
  rw [hs_eq hE.baseChange hφ.baseChange, hs_eq hE hφ, ← classSum_algebraMap, hf]

end BaseChange

section Conj

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {ρ : Representation R G P} {σ : Representation R G Q}
variable [Module.Free R P] [Module.Finite R P] [Module.Free R Q] [Module.Finite R Q]

/-- `hs` is invariant under equivariant isomorphisms. -/
theorem hs_conj (hρ : IsProj ρ) (e : P ≃ₗ[R] Q) (he : IsEquivariant ρ σ e.toLinearMap)
    {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ) :
    hs σ (e.toLinearMap ∘ₗ φ ∘ₗ e.symm.toLinearMap) = hs ρ φ := by
  have he' : IsEquivariant σ ρ e.symm.toLinearMap := isEquivariant_iff.2 fun g x => by
    apply e.injective
    rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ← LinearEquiv.coe_coe, he.apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  have hσ : IsProj σ := hρ.retract he' he (LinearMap.ext fun x => by simp)
  have := hs_comp_comm hσ hρ e.symm.toLinearMap (e.toLinearMap ∘ₗ φ) he' (he.comp hφ)
  rw [← LinearMap.comp_assoc, this]
  congr 1
  exact LinearMap.ext fun x => by simp

end Conj

end RamanujanPetersson.HattoriStallings

end

-- ===== S4.Def_RP_HattoriStallings_Complex =====
section

/-!
# Hattori–Stallings traces, part B2: bounded complexes (Lefschetz numbers)

A bounded complex of projective `R[G]`-modules is a family `ρ i : Representation R G (P i)`
(`i ∈ ℕ`, only `i ≤ N` matters) with equivariant differentials `d i : P i → P (i+1)`.
The Lefschetz number of an endomorphism `φ` is the alternating sum of Hattori–Stallings traces
`lefschetz ρ N φ = ∑_{i ≤ N} (-1)^i hs (φ i)`.

* `lefschetz_sub_eq`, `lefschetz_homotopy`: homotopic maps have the same Lefschetz number.
* `lefschetz_eq_zero_of_contractible`: contractible complexes have Lefschetz number `0`.
* `lefschetz_ses`: additivity on termwise short exact sequences of complexes.
* `lefschetz_coinv`: the twisted trace formula for complexes (SGA 4½ *Rapport*).
* `lefschetz_baseChange`: compatibility with base change (reduction mod `ℓ^m`).
* `lefschetz_trace_inv_comp`, `lefschetz_trace`: `∑ (-1)^i Tr (γ⁻¹ ∘ φ i) = |Z(γ)| · L(φ)[γ]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap TensorProduct

section Complex

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : ℕ → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
variable [∀ i, Module.Free R (P i)] [∀ i, Module.Finite R (P i)]

/-- The Lefschetz number (alternating Hattori–Stallings trace) of an endomorphism `φ` of the
complex `P 0 → ⋯ → P N`. -/
noncomputable def lefschetz (ρ : ∀ i, Representation R G (P i)) (N : ℕ) (φ : ∀ i, P i →ₗ[R] P i) :
    ConjClasses G → R :=
  ∑ i ∈ Finset.range (N + 1), ((-1 : R) ^ i) • hs (ρ i) (φ i)

variable {ρ : ∀ i, Representation R G (P i)}

lemma lefschetz_succ (N : ℕ) (φ : ∀ i, P i →ₗ[R] P i) :
    lefschetz ρ (N + 1) φ = lefschetz ρ N φ + ((-1 : R) ^ (N + 1)) • hs (ρ (N + 1)) (φ (N + 1)) :=
  Finset.sum_range_succ _ _

lemma lefschetz_zero (φ : ∀ i, P i →ₗ[R] P i) : lefschetz ρ 0 φ = hs (ρ 0) (φ 0) := by
  simp [lefschetz]

/-- Telescoping identity behind homotopy invariance: if `φ - φ' = d h + h d`, then
`L_n(φ) - L_n(φ') = (-1)^n hs (h n ∘ d n)`. -/
theorem lefschetz_sub_eq (hρ : ∀ i, IsProj (ρ i))
    {φ φ' : ∀ i, P i →ₗ[R] P i} (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i))
    (hφ' : ∀ i, IsEquivariant (ρ i) (ρ i) (φ' i))
    {d : ∀ i, P i →ₗ[R] P (i + 1)} {h : ∀ i, P (i + 1) →ₗ[R] P i}
    (hd : ∀ i, IsEquivariant (ρ i) (ρ (i + 1)) (d i))
    (hh : ∀ i, IsEquivariant (ρ (i + 1)) (ρ i) (h i))
    (h0 : φ 0 - φ' 0 = h 0 ∘ₗ d 0)
    (hsucc : ∀ i, φ (i + 1) - φ' (i + 1) = d i ∘ₗ h i + h (i + 1) ∘ₗ d (i + 1)) (n : ℕ) :
    lefschetz ρ n φ - lefschetz ρ n φ' = ((-1 : R) ^ n) • hs (ρ n) (h n ∘ₗ d n) := by
  induction n with
  | zero =>
    rw [lefschetz_zero, lefschetz_zero, pow_zero, one_smul, ← hs_sub (hρ 0) (hφ 0) (hφ' 0), h0]
  | succ n ih =>
    rw [lefschetz_succ, lefschetz_succ, add_sub_add_comm, ih, ← smul_sub,
      ← hs_sub (hρ (n + 1)) (hφ (n + 1)) (hφ' (n + 1)), hsucc n,
      hs_add (hρ (n + 1)) ((hd n).comp (hh n)) ((hh (n + 1)).comp (hd (n + 1))),
      ← hs_comp_comm (hρ n) (hρ (n + 1)) (d n) (h n) (hd n) (hh n), pow_succ, smul_add]
    simp only [mul_neg, mul_one, neg_smul]
    abel

/-- **Homotopy invariance** of the Lefschetz number on the bounded complex `P 0 → ⋯ → P N`
(`d N = 0`). -/
theorem lefschetz_homotopy (hρ : ∀ i, IsProj (ρ i))
    {φ φ' : ∀ i, P i →ₗ[R] P i} (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i))
    (hφ' : ∀ i, IsEquivariant (ρ i) (ρ i) (φ' i))
    {d : ∀ i, P i →ₗ[R] P (i + 1)} {h : ∀ i, P (i + 1) →ₗ[R] P i}
    (hd : ∀ i, IsEquivariant (ρ i) (ρ (i + 1)) (d i))
    (hh : ∀ i, IsEquivariant (ρ (i + 1)) (ρ i) (h i))
    (h0 : φ 0 - φ' 0 = h 0 ∘ₗ d 0)
    (hsucc : ∀ i, φ (i + 1) - φ' (i + 1) = d i ∘ₗ h i + h (i + 1) ∘ₗ d (i + 1))
    (N : ℕ) (hN : d N = 0) :
    lefschetz ρ N φ = lefschetz ρ N φ' := by
  have key := lefschetz_sub_eq hρ hφ hφ' hd hh h0 hsucc N
  rw [hN, LinearMap.comp_zero, hs_zero (hρ N), smul_zero] at key
  exact sub_eq_zero.1 key

/-- **Contractible complexes** have Lefschetz number `0`: if `s` is a contracting homotopy
(`s d = id` in degree `0`, `d s + s d = id` above) and `φ` is a chain map, then `L(φ) = 0`. -/
theorem lefschetz_eq_zero_of_contractible (hρ : ∀ i, IsProj (ρ i))
    {φ : ∀ i, P i →ₗ[R] P i} (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i))
    {d : ∀ i, P i →ₗ[R] P (i + 1)} {s : ∀ i, P (i + 1) →ₗ[R] P i}
    (hd : ∀ i, IsEquivariant (ρ i) (ρ (i + 1)) (d i))
    (hsE : ∀ i, IsEquivariant (ρ (i + 1)) (ρ i) (s i))
    (hchain : ∀ i, φ (i + 1) ∘ₗ d i = d i ∘ₗ φ i)
    (s0 : s 0 ∘ₗ d 0 = LinearMap.id)
    (ssucc : ∀ i, d i ∘ₗ s i + s (i + 1) ∘ₗ d (i + 1) = LinearMap.id)
    (N : ℕ) (hN : d N = 0) :
    lefschetz ρ N φ = 0 := by
  have h0 : φ 0 - 0 = (φ 0 ∘ₗ s 0) ∘ₗ d 0 := by
    rw [sub_zero, LinearMap.comp_assoc, s0, LinearMap.comp_id]
  have hsucc : ∀ i, φ (i + 1) - 0 = d i ∘ₗ (φ i ∘ₗ s i) + (φ (i + 1) ∘ₗ s (i + 1)) ∘ₗ d (i + 1) := by
    intro i
    refine LinearMap.ext fun x => ?_
    have e1 := LinearMap.congr_fun (ssucc i) x
    have e2 := LinearMap.congr_fun (hchain i) (s i x)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at e1 e2
    simp only [sub_zero, LinearMap.add_apply,
      LinearMap.comp_apply]
    calc φ (i + 1) x = φ (i + 1) (d i (s i x) + s (i + 1) (d (i + 1) x)) := by rw [e1]
      _ = _ := by rw [map_add, e2]
  have hzero : ∀ i, IsEquivariant (ρ i) (ρ i) (0 : P i →ₗ[R] P i) := fun _ => isEquivariant_zero
  rw [lefschetz_homotopy hρ hφ hzero hd (fun i => (hφ i).comp (hsE i)) h0 hsucc N hN]
  simp [lefschetz, hs_zero (hρ _)]

/-- **Additivity on short exact sequences of complexes** (termwise exact, with `P` and `P''`
projective): the kernel complex is projective and `L(φ) = L(φ') + L(φ'')`. -/
theorem lefschetz_ses {P' : ℕ → Type*} [∀ i, AddCommGroup (P' i)] [∀ i, Module R (P' i)]
    [∀ i, Module.Free R (P' i)] [∀ i, Module.Finite R (P' i)]
    {P'' : ℕ → Type*} [∀ i, AddCommGroup (P'' i)] [∀ i, Module R (P'' i)]
    [∀ i, Module.Free R (P'' i)] [∀ i, Module.Finite R (P'' i)]
    {ρ' : ∀ i, Representation R G (P' i)} {ρ'' : ∀ i, Representation R G (P'' i)}
    (hρ : ∀ i, IsProj (ρ i)) (hρ'' : ∀ i, IsProj (ρ'' i))
    {ι : ∀ i, P' i →ₗ[R] P i} {π : ∀ i, P i →ₗ[R] P'' i}
    (hι : ∀ i, IsEquivariant (ρ' i) (ρ i) (ι i)) (hπ : ∀ i, IsEquivariant (ρ i) (ρ'' i) (π i))
    (hinj : ∀ i, Function.Injective (ι i)) (hsurj : ∀ i, Function.Surjective (π i))
    (hex : ∀ i, LinearMap.range (ι i) = LinearMap.ker (π i))
    {φ' : ∀ i, P' i →ₗ[R] P' i} {φ : ∀ i, P i →ₗ[R] P i} {φ'' : ∀ i, P'' i →ₗ[R] P'' i}
    (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i)) (hφ'' : ∀ i, IsEquivariant (ρ'' i) (ρ'' i) (φ'' i))
    (h1 : ∀ i, φ i ∘ₗ ι i = ι i ∘ₗ φ' i) (h2 : ∀ i, π i ∘ₗ φ i = φ'' i ∘ₗ π i) (N : ℕ) :
    (∀ i, IsProj (ρ' i)) ∧ lefschetz ρ N φ = lefschetz ρ' N φ' + lefschetz ρ'' N φ'' := by
  have key := fun i => hs_ses (hρ i) (hρ'' i) (hι i) (hπ i) (hinj i) (hsurj i) (hex i) (hφ i)
    (hφ'' i) (h1 i) (h2 i)
  have key2 : ∀ i, hs (ρ i) (φ i) = hs (ρ' i) (φ' i) + hs (ρ'' i) (φ'' i) := fun i => (key i).2
  refine ⟨fun i => (key i).1, ?_⟩
  simp only [lefschetz, key2, smul_add, Finset.sum_add_distrib]

/-- **Twisted trace formula for complexes** (SGA 4½ *Rapport*): for a bounded complex of
projectives `P` and an `R[G]`-module `M` with endomorphism `ψ`,
`∑ (-1)^i Tr (φ i ⊗ ψ | P i ⊗_{R[G]} M) = ∑_c L(φ)[c] · Tr (c⁻¹ ∘ ψ | M)`. -/
theorem lefschetz_coinv [Fintype (ConjClasses G)]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {τ : Representation R G M}
    [∀ i, Module.Free R (Representation.Coinvariants (Representation.tprod (ρ i) τ))]
    [∀ i, Module.Finite R (Representation.Coinvariants (Representation.tprod (ρ i) τ))]
    (hρ : ∀ i, IsProj (ρ i)) {φ : ∀ i, P i →ₗ[R] P i}
    (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i)) {ψ : M →ₗ[R] M} (hψ : IsEquivariant τ τ ψ)
    (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (-1 : R) ^ i *
        trace R _ (coinvMap (Representation.tprod (ρ i) τ) (TensorProduct.map (φ i) ψ)
          (isEquivariant_tensorMap (hφ i) hψ)) =
      ∑ c : ConjClasses G, lefschetz ρ N φ c * twChar τ ψ c := by
  have key : ∀ i, trace R _ (coinvMap (Representation.tprod (ρ i) τ) (TensorProduct.map (φ i) ψ)
      (isEquivariant_tensorMap (hφ i) hψ)) = ∑ c : ConjClasses G, hs (ρ i) (φ i) c * twChar τ ψ c :=
    fun i => trace_coinvMap_tprod_eq_sum_hs (hρ i) (hφ i) hψ
  simp only [key, lefschetz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Compatibility with base change** (e.g. reduction `ZMod (ℓ^n) → ZMod (ℓ^m)`). -/
theorem lefschetz_baseChange (A : Type*) [CommRing A] [Algebra R A] (hρ : ∀ i, IsProj (ρ i))
    {φ : ∀ i, P i →ₗ[R] P i} (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i)) (N : ℕ)
    (c : ConjClasses G) :
    lefschetz (fun i => repBaseChange A (ρ i)) N (fun i => (φ i).baseChange A) c =
      algebraMap R A (lefschetz ρ N φ c) := by
  simp only [lefschetz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_pow,
    map_neg, map_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs_baseChange (hρ i) (hφ i) c]

/-- `∑ (-1)^i Tr_R (ρ γ⁻¹ ∘ φ i) = |Z(γ)| · L(φ)[γ]`. -/
theorem lefschetz_trace_inv_comp (hρ : ∀ i, IsProj (ρ i)) {φ : ∀ i, P i →ₗ[R] P i}
    (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i)) (N : ℕ) (γ : G) :
    ∑ i ∈ Finset.range (N + 1), (-1 : R) ^ i * trace R (P i) (ρ i γ⁻¹ ∘ₗ φ i) =
      (Nat.card {z : G // z⁻¹ * γ * z = γ} : R) * lefschetz ρ N φ (ConjClasses.mk γ) := by
  have key : ∀ i, trace R (P i) (ρ i γ⁻¹ ∘ₗ φ i) =
      (Nat.card {z : G // z⁻¹ * γ * z = γ} : R) * hs (ρ i) (φ i) (ConjClasses.mk γ) :=
    fun i => trace_inv_comp_eq_card_mul_hs (hρ i) (hφ i) γ
  simp only [key, lefschetz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `∑ (-1)^i Tr_R (φ i) = |G| · L(φ)[1]`. -/
theorem lefschetz_trace (hρ : ∀ i, IsProj (ρ i)) {φ : ∀ i, P i →ₗ[R] P i}
    (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i)) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (-1 : R) ^ i * trace R (P i) (φ i) =
      (Fintype.card G : R) * lefschetz ρ N φ (ConjClasses.mk 1) := by
  have key : ∀ i, trace R (P i) (φ i) = (Fintype.card G : R) * hs (ρ i) (φ i) (ConjClasses.mk 1) :=
    fun i => trace_eq_card_mul_hs_one (hρ i) (hφ i)
  simp only [key, lefschetz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Complex

end RamanujanPetersson.HattoriStallings

end

-- ===== S4.Def_RP_PerfectCx_Tri =====
section

/-!
# S4-PD (5), E3: three-term complexes as `ℕ`-indexed families

The Hattori–Stallings Lefschetz formalism (`HattoriStallings.lefschetz`) consumes a family `P : ℕ → Type` of
representations. `Tri V0 V1 V2` is the family `V0, V1, V2, 0, 0, …`, with its module structure, representation
(`triRep`), projectivity (`isProj_tri`) and freeness/finiteness instances. Over a local ring the twisted trace formula
holds with no extra hypotheses on the coinvariants (`lefschetz_coinv_of_local`, via `coinv_free_finite`), and the
Lefschetz number of a three-term complex is `hs₀ - hs₁ + hs₂` (`lefschetz_tri`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open HattoriStallings Representation LinearMap

section Tri

variable (V0 V1 V2 : Type)

/-- The family `V0, V1, V2, 0, 0, …`. -/
def Tri : ℕ → Type
  | 0 => V0
  | 1 => V1
  | 2 => V2
  | _ + 3 => PUnit

variable [AddCommGroup V0] [AddCommGroup V1] [AddCommGroup V2]

instance instAddCommGroupTri : ∀ i, AddCommGroup (Tri V0 V1 V2 i)
  | 0 => inferInstanceAs (AddCommGroup V0)
  | 1 => inferInstanceAs (AddCommGroup V1)
  | 2 => inferInstanceAs (AddCommGroup V2)
  | _ + 3 => inferInstanceAs (AddCommGroup PUnit)

variable {R : Type} [CommRing R] [Module R V0] [Module R V1] [Module R V2]

instance instModuleTri : ∀ i, Module R (Tri V0 V1 V2 i)
  | 0 => inferInstanceAs (Module R V0)
  | 1 => inferInstanceAs (Module R V1)
  | 2 => inferInstanceAs (Module R V2)
  | _ + 3 => inferInstanceAs (Module R PUnit)

instance instFreeTri [Module.Free R V0] [Module.Free R V1] [Module.Free R V2] :
    ∀ i, Module.Free R (Tri V0 V1 V2 i)
  | 0 => inferInstanceAs (Module.Free R V0)
  | 1 => inferInstanceAs (Module.Free R V1)
  | 2 => inferInstanceAs (Module.Free R V2)
  | _ + 3 => inferInstanceAs (Module.Free R PUnit)

instance instFiniteTri [Module.Finite R V0] [Module.Finite R V1] [Module.Finite R V2] :
    ∀ i, Module.Finite R (Tri V0 V1 V2 i)
  | 0 => inferInstanceAs (Module.Finite R V0)
  | 1 => inferInstanceAs (Module.Finite R V1)
  | 2 => inferInstanceAs (Module.Finite R V2)
  | _ + 3 => inferInstanceAs (Module.Finite R PUnit)

variable {G : Type} [Group G] {V0 V1 V2}

/-- The representation on `Tri V0 V1 V2` (trivial on the zero terms). -/
def triRep (ρ0 : Representation R G V0) (ρ1 : Representation R G V1) (ρ2 : Representation R G V2) :
    ∀ i, Representation R G (Tri V0 V1 V2 i)
  | 0 => ρ0
  | 1 => ρ1
  | 2 => ρ2
  | _ + 3 => Representation.trivial R G PUnit

variable (ρ0 : Representation R G V0) (ρ1 : Representation R G V1) (ρ2 : Representation R G V2)

theorem triRep_zero : triRep ρ0 ρ1 ρ2 0 = ρ0 := rfl
theorem triRep_one : triRep ρ0 ρ1 ρ2 1 = ρ1 := rfl
theorem triRep_two : triRep ρ0 ρ1 ρ2 2 = ρ2 := rfl

variable [Fintype G]

theorem isProj_trivial_punit : IsProj (Representation.trivial R G PUnit) :=
  ⟨0, LinearMap.ext fun _ => Subsingleton.elim _ _⟩

variable {ρ0 ρ1 ρ2} in
theorem isProj_tri (h0 : IsProj ρ0) (h1 : IsProj ρ1) (h2 : IsProj ρ2) : ∀ i, IsProj (triRep ρ0 ρ1 ρ2 i)
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | _ + 3 => isProj_trivial_punit

/-- The Lefschetz number of a three-term complex. -/
theorem lefschetz_tri [Module.Free R V0] [Module.Free R V1] [Module.Free R V2] [Module.Finite R V0]
    [Module.Finite R V1] [Module.Finite R V2] (φ : ∀ i, Tri V0 V1 V2 i →ₗ[R] Tri V0 V1 V2 i) :
    lefschetz (triRep ρ0 ρ1 ρ2) 2 φ = hs ρ0 (φ 0) - hs ρ1 (φ 1) + hs ρ2 (φ 2) := by
  have e : lefschetz (triRep ρ0 ρ1 ρ2) 2 φ = hs (triRep ρ0 ρ1 ρ2 0) (φ 0) -
      hs (triRep ρ0 ρ1 ρ2 1) (φ 1) + hs (triRep ρ0 ρ1 ρ2 2) (φ 2) := by
    simp only [lefschetz, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      one_smul, neg_smul, neg_one_sq, sub_eq_add_neg]
  exact e

end Tri

/-- `∑_{i ≤ 2} (-1)^i f i = f 0 - f 1 + f 2`. -/
theorem sum_range_three_alt {R : Type} [CommRing R] (f : ℕ → R) :
    ∑ i ∈ Finset.range (2 + 1), (-1 : R) ^ i * f i = f 0 - f 1 + f 2 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, one_mul,
    neg_one_mul, neg_one_sq, sub_eq_add_neg]

section Local

variable {R : Type} [CommRing R] [IsLocalRing R] {G : Type} [Group G] [Fintype G]
variable {P : ℕ → Type} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
variable [∀ i, Module.Free R (P i)] [∀ i, Module.Finite R (P i)]

/-- Over a local ring the coinvariants `P i ⊗_{R[G]} M` of a projective complex and a free finite `M` are free and
finite, so the twisted trace formula `lefschetz_coinv` needs no further hypotheses. -/
theorem lefschetz_coinv_of_local [Fintype (ConjClasses G)] {ρ : ∀ i, Representation R G (P i)}
    {M : Type} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {τ : Representation R G M} (hρ : ∀ i, IsProj (ρ i)) {φ : ∀ i, P i →ₗ[R] P i}
    (hφ : ∀ i, IsEquivariant (ρ i) (ρ i) (φ i)) {ψ : M →ₗ[R] M} (hψ : IsEquivariant τ τ ψ)
    (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), (-1 : R) ^ i *
        trace R _ (coinvMap (Representation.tprod (ρ i) τ) (TensorProduct.map (φ i) ψ)
          (isEquivariant_tensorMap (hφ i) hψ)) =
      ∑ c : ConjClasses G, lefschetz ρ N φ c * twChar τ ψ c := by
  have : ∀ i, Module.Free R (Representation.Coinvariants (Representation.tprod (ρ i) τ)) :=
    fun i => (coinv_free_finite (τ := τ) (hρ i).choose_spec).1
  have : ∀ i, Module.Finite R (Representation.Coinvariants (Representation.tprod (ρ i) τ)) :=
    fun i => (coinv_free_finite (τ := τ) (hρ i).choose_spec).2
  exact lefschetz_coinv hρ hφ hψ N

end Local

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_Frob =====
section

/-!
# S4-PD (5), E3: the Frobenius chain map on the cone complex

For `x ∈ G` with `x⁻¹ Δ x ⊆ Δ'`, `conjMap ρ x : Z¹(Δ'; M) → Z¹(Δ; M)`, `c ↦ (g ↦ ρ x (c (x⁻¹ g x)))`. For a Frobenius
lift `ψ` normalising `Γ`, a permutation datum `t : S → S`, `h : S → Γ` compatible with the boundary
(`CurveCoh.BdryCompat`), the maps `ρ ψ` (degree 0), `frob1` (degree 1, the `twistc` of `CurveCoh_Pair`) and `frob2`
(degree 2, `e ↦ (s ↦ conjMap (ψ h_s) (e (t s)))`) form a chain endomorphism of the cone complex `K(M)` (`cx0_frob`,
`cx1_frob`), natural in the coefficients (`frob1_natural`, `frob2_natural`). At `ρ = regRep Λ π` the three maps are
`Gf`-equivariant (`frob0_equiv`, `frob1_equiv`, `frob2_equiv`). `triMap` assembles endomorphisms of a `Tri` family.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings

noncomputable section

section Conj

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N)

/-- `g ↦ x⁻¹ g x` from `Δ` to `Δ'` when `x⁻¹ Δ x ⊆ Δ'`. -/
def conjSub (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (g : Δ) : Δ' :=
  ⟨x⁻¹ * g * x, hx g g.2⟩

theorem conjSub_val (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (g : Δ) :
    (conjSub x hx g : G) = x⁻¹ * g * x := rfl

theorem conjSub_mul (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (g g' : Δ) :
    conjSub x hx (g * g') = conjSub x hx g * conjSub x hx g' := by
  apply Subtype.ext
  show x⁻¹ * ((g : G) * g') * x = (x⁻¹ * g * x) * (x⁻¹ * g' * x)
  group

theorem continuous_conjSub (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') :
    Continuous (conjSub x hx) := by
  have : Continuous fun g : Δ => x⁻¹ * (g : G) * x :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  exact this.subtype_mk _

theorem rho_conjSub (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (g : Δ) (m : M) :
    ρ x (ρ (conjSub x hx g : G) m) = ρ (g : G) (ρ x m) := by
  have e : x * (x⁻¹ * (g : G) * x) = (g : G) * x := by group
  calc ρ x (ρ (conjSub x hx g : G) m) = ρ (x * (x⁻¹ * (g : G) * x)) m := by rw [map_mul]; rfl
    _ = ρ (g : G) (ρ x m) := by rw [e, map_mul]; rfl

/-- Transport of cocycles along conjugation: `c ↦ (g ↦ ρ x (c (x⁻¹ g x)))`. -/
def conjMap (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') : Z1 ρ Δ' →ₗ[k] Z1 ρ Δ where
  toFun c := ⟨fun g => ρ x ((c : Δ' → M) (conjSub x hx g)), (mem_Z1 ρ Δ _).2
    ⟨(((mem_Z1 ρ Δ' _).1 c.2).1.comp_continuous (continuous_conjSub x hx)).comp (ρ x), fun g g' => by
      show ρ x ((c : Δ' → M) (conjSub x hx (g * g'))) =
        ρ x ((c : Δ' → M) (conjSub x hx g)) + ρ (g : G) (ρ x ((c : Δ' → M) (conjSub x hx g')))
      rw [conjSub_mul, ((mem_Z1 ρ Δ' _).1 c.2).2, map_add, rho_conjSub]⟩⟩
  map_add' c d := Subtype.ext (funext fun g => by
    show ρ x ((c : Δ' → M) (conjSub x hx g) + (d : Δ' → M) (conjSub x hx g)) =
      ρ x ((c : Δ' → M) (conjSub x hx g)) + ρ x ((d : Δ' → M) (conjSub x hx g))
    exact map_add _ _ _)
  map_smul' r c := Subtype.ext (funext fun g => by
    show ρ x (r • (c : Δ' → M) (conjSub x hx g)) = r • ρ x ((c : Δ' → M) (conjSub x hx g))
    exact map_smul _ _ _)

theorem conjMap_apply (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (c : Z1 ρ Δ') (g : Δ) :
    (conjMap ρ x hx c : Δ → M) g = ρ x ((c : Δ' → M) (conjSub x hx g)) := rfl

/-- `ρ(a) c(a⁻¹ x a) = c(x) + ρ(x) c(a) - c(a)` for a cocycle `c`. -/
theorem z1_conj {Δ : Subgroup G} (c : Z1 ρ Δ) (a x : Δ) :
    ρ (a : G) ((c : Δ → M) (a⁻¹ * x * a)) = (c : Δ → M) x + ρ (x : G) ((c : Δ → M) a) - (c : Δ → M) a := by
  have hc := ((mem_Z1 ρ Δ _).1 c.2).2
  have e : a * (a⁻¹ * x * a) = x * a := by group
  have h1 := hc a (a⁻¹ * x * a)
  rw [e, hc x a] at h1
  rw [h1]
  abel

variable {ρ σ} in
theorem conjMap_natural (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m)) (x : G)
    {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') :
    z1Map ρ σ Δ q hq ∘ₗ conjMap ρ x hx = conjMap σ x hx ∘ₗ z1Map ρ σ Δ' q hq :=
  LinearMap.ext fun _ => Subtype.ext (funext fun _ => hq x _)

end Conj

section Frob

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N)
  (Γ : Subgroup G) [hΓ : Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ)

theorem conj_mem_normal : ∀ g ∈ Γ, ψ⁻¹ * g * ψ ∈ Γ := fun g hg => by
  simpa using hΓ.conj_mem g hg ψ⁻¹

theorem bdry_mem (hI : BdryCompat Γ I ψ t h) (s : S) :
    ∀ g ∈ Γ ⊓ I s, (ψ * (h s : G))⁻¹ * g * (ψ * (h s : G)) ∈ Γ ⊓ I (t s) := by
  intro g hg
  have hgΓ := (Subgroup.mem_inf.1 hg).1
  have e : (ψ * (h s : G))⁻¹ * g * (ψ * (h s : G)) = (h s : G)⁻¹ * (ψ⁻¹ * g * ψ) * (h s : G) := by group
  rw [e]
  exact Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (h s).2) (conj_mem_normal Γ ψ g hgΓ)) (h s).2,
    hI s ⟨g, hgΓ⟩ (Subgroup.mem_inf.1 hg).2⟩

/-- Frobenius on `K¹ = Z¹(Γ; M) × M^S`: `(c, b) ↦ (T_ψ c, s ↦ ρ ψ (ρ (h s) (b (t s)) - c (h s)))`. -/
def frob1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 ρ Γ × (S → M) :=
  (conjMap ρ ψ (conj_mem_normal Γ ψ) ∘ₗ LinearMap.fst k _ _).prod (LinearMap.pi fun s =>
    ρ ψ ∘ₗ (ρ (h s : G) ∘ₗ LinearMap.proj (t s) ∘ₗ LinearMap.snd k _ _ -
      LinearMap.proj (h s) ∘ₗ (Z1 ρ Γ).subtype ∘ₗ LinearMap.fst k _ _))

theorem frob1_fst (p : Z1 ρ Γ × (S → M)) :
    (frob1 ρ Γ ψ t h p).1 = conjMap ρ ψ (conj_mem_normal Γ ψ) p.1 := rfl

theorem frob1_snd (p : Z1 ρ Γ × (S → M)) (s : S) :
    (frob1 ρ Γ ψ t h p).2 s = ρ ψ (ρ (h s : G) (p.2 (t s)) - (p.1 : Γ → M) (h s)) := rfl

/-- Frobenius on `K² = Π_s Z¹(Γ ⊓ I s; M)`: `e ↦ (s ↦ conjMap (ψ h_s) (e (t s)))`. -/
def frob2 (hI : BdryCompat Γ I ψ t h) : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 ρ (Γ ⊓ I s)) :=
  LinearMap.pi fun s => conjMap ρ (ψ * h s) (bdry_mem Γ I ψ t h hI s) ∘ₗ
    (LinearMap.proj (R := k) (t s) : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] Z1 ρ (Γ ⊓ I (t s)))

theorem frob2_apply (hI : BdryCompat Γ I ψ t h) (e : (s : S) → Z1 ρ (Γ ⊓ I s)) (s : S) (g : ↥(Γ ⊓ I s)) :
    (frob2 ρ Γ I ψ t h hI e s : ↥(Γ ⊓ I s) → M) g =
      ρ (ψ * h s) ((e (t s) : ↥(Γ ⊓ I (t s)) → M) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) g)) := rfl

variable (hρ : IsOpen (ρ.ker : Set G))

/-- Frobenius commutes with `d⁰`. -/
theorem cx0_frob : cx0 ρ Γ S hρ ∘ₗ ρ ψ = frob1 ρ Γ ψ t h ∘ₗ cx0 ρ Γ S hρ :=
  LinearMap.ext fun m => Prod.ext (Subtype.ext (funext fun g => by
    show ρ (g : G) (ρ ψ m) - ρ ψ m = ρ ψ (ρ (conjSub ψ (conj_mem_normal Γ ψ) g : G) m - m)
    rw [map_sub, rho_conjSub])) (funext fun s => by
    show ρ ψ m = ρ ψ (ρ (h s : G) m - (ρ (h s : G) m - m))
    rw [sub_sub_cancel])

/-- Frobenius commutes with `d¹`. -/
theorem cx1_frob (hI : BdryCompat Γ I ψ t h) :
    cx1 ρ Γ I hρ ∘ₗ frob1 ρ Γ ψ t h = frob2 ρ Γ I ψ t h hI ∘ₗ cx1 ρ Γ I hρ := by
  refine LinearMap.ext fun p => funext fun s => Subtype.ext (funext fun g => ?_)
  simp only [LinearMap.comp_apply, cx1_apply, frob1_fst, frob1_snd, frob2_apply, conjMap_apply]
  have hgΓ : (g : G) ∈ Γ := (Subgroup.mem_inf.1 g.2).1
  have F1 : ∀ y, ρ (g : G) (ρ ψ y) =
      ρ ψ (ρ (conjSub ψ (conj_mem_normal Γ ψ) (⟨g.1, hgΓ⟩ : Γ) : G) y) := fun y =>
    (rho_conjSub ρ ψ (conj_mem_normal Γ ψ) ⟨g.1, hgΓ⟩ y).symm
  have F2 : ∀ z, ρ (ψ * (h s : G)) z = ρ ψ (ρ (h s : G) z) := fun z => by rw [map_mul]; rfl
  have F3 : ∀ y, ρ (h s : G) (ρ (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) g : G) y) =
      ρ (conjSub ψ (conj_mem_normal Γ ψ) (⟨g.1, hgΓ⟩ : Γ) : G) (ρ (h s : G) y) := fun y => by
    have e : (h s : G) * ((ψ * (h s : G))⁻¹ * (g : G) * (ψ * (h s : G))) = (ψ⁻¹ * (g : G) * ψ) * (h s : G) := by
      group
    calc ρ (h s : G) (ρ (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) g : G) y) =
        ρ ((h s : G) * ((ψ * (h s : G))⁻¹ * (g : G) * (ψ * (h s : G)))) y := by rw [map_mul]; rfl
      _ = ρ (conjSub ψ (conj_mem_normal Γ ψ) (⟨g.1, hgΓ⟩ : Γ) : G) (ρ (h s : G) y) := by rw [e, map_mul]; rfl
  have F4 : ∀ hmem, (p.1 : Γ → M) ⟨(conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) g : G), hmem⟩ =
      (p.1 : Γ → M) ((h s)⁻¹ * conjSub ψ (conj_mem_normal Γ ψ) (⟨g.1, hgΓ⟩ : Γ) * h s) := fun _ =>
    congrArg _ (Subtype.ext (by
      show (ψ * (h s : G))⁻¹ * (g : G) * (ψ * (h s : G)) = (h s : G)⁻¹ * (ψ⁻¹ * (g : G) * ψ) * (h s : G)
      group))
  have F5 := z1_conj ρ p.1 (h s) (conjSub ψ (conj_mem_normal Γ ψ) (⟨g.1, hgΓ⟩ : Γ))
  simp only [map_sub, F2, F3, F4, F5, F1, map_add]
  abel

variable {ρ σ} in
/-- `frob1` is natural in the coefficients. -/
theorem frob1_natural (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m)) :
    frob1 σ Γ ψ t h ∘ₗ K1map ρ σ Γ q hq = K1map ρ σ Γ q hq ∘ₗ frob1 ρ Γ ψ t h :=
  LinearMap.ext fun p => Prod.ext (Subtype.ext (funext fun g => (hq ψ _).symm)) (funext fun s => by
    show σ ψ (σ (h s : G) (q (p.2 (t s))) - q ((p.1 : Γ → M) (h s))) =
      q (ρ ψ (ρ (h s : G) (p.2 (t s)) - (p.1 : Γ → M) (h s)))
    simp only [map_sub, hq])

variable {ρ σ} in
/-- `frob2` is natural in the coefficients. -/
theorem frob2_natural (hI : BdryCompat Γ I ψ t h) (q : M →ₗ[k] N)
    (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m)) :
    frob2 σ Γ I ψ t h hI ∘ₗ K2map ρ σ Γ I q hq = K2map ρ σ Γ I q hq ∘ₗ frob2 ρ Γ I ψ t h hI :=
  LinearMap.ext fun _ => funext fun _ => Subtype.ext (funext fun _ => (hq _ _).symm)

end Frob

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ)

theorem frob0_equiv : IsEquivariant (rRep Λ Gf) (rRep Λ Gf) (regRep Λ π ψ) := fun x =>
  LinearMap.ext fun a => (mulRight_regRep π (single x⁻¹ 1) ψ a).symm

theorem frob1_equiv : IsEquivariant (rho1 Λ π Γ S) (rho1 Λ π Γ S) (frob1 (regRep Λ π) Γ ψ t h) := fun x =>
  frob1_natural (ρ := regRep Λ π) (σ := regRep Λ π) Γ ψ t h (LinearMap.mulRight Λ (single x⁻¹ 1)) (mulRight_regRep π _)

theorem frob2_equiv (hI : BdryCompat Γ I ψ t h) :
    IsEquivariant (rho2 Λ π Γ I) (rho2 Λ π Γ I) (frob2 (regRep Λ π) Γ I ψ t h hI) := fun x =>
  frob2_natural (ρ := regRep Λ π) (σ := regRep Λ π) Γ I ψ t h hI (LinearMap.mulRight Λ (single x⁻¹ 1)) (mulRight_regRep π _)

end Model

section TriMap

variable {R : Type} [CommRing R] {G : Type} [Group G] {V0 V1 V2 : Type} [AddCommGroup V0] [AddCommGroup V1]
  [AddCommGroup V2] [Module R V0] [Module R V1] [Module R V2]

/-- Termwise endomorphism of `Tri V0 V1 V2` (zero on the zero terms). -/
def triMap (f0 : V0 →ₗ[R] V0) (f1 : V1 →ₗ[R] V1) (f2 : V2 →ₗ[R] V2) :
    ∀ i, Tri V0 V1 V2 i →ₗ[R] Tri V0 V1 V2 i
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | _ + 3 => 0

theorem triMap_equiv {ρ0 : Representation R G V0} {ρ1 : Representation R G V1} {ρ2 : Representation R G V2}
    {f0 : V0 →ₗ[R] V0} {f1 : V1 →ₗ[R] V1} {f2 : V2 →ₗ[R] V2} (h0 : IsEquivariant ρ0 ρ0 f0)
    (h1 : IsEquivariant ρ1 ρ1 f1) (h2 : IsEquivariant ρ2 ρ2 f2) :
    ∀ i, IsEquivariant (triRep ρ0 ρ1 ρ2 i) (triRep ρ0 ρ1 ρ2 i) (triMap f0 f1 f2 i)
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | _ + 3 => fun _ => LinearMap.ext fun _ => rfl

end TriMap

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_CxNat =====
section

/-!
# S4-PD (5), E3: the identification `P ⊗_{Λ[Gf]} M ≅ K(M)` is natural in `M`

For an intertwining map `f : M → M'` of `Gf`-representations, the termwise isos `coinvA`, `iso1`, `iso2` carry
`P^i ⊗ f` to the coefficient maps `f`, `K1map f`, `K2map f` of the cone complex (`coinvA_natural`, `iso1_natural`,
`iso2_natural`); with `cx0_natural`, `cx1_natural` this is functoriality of `P ⊗ M ≅ K(M)` in `M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))
  {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)
  {M' : Type} [AddCommGroup M'] [Module Λ M'] (τ' : Representation Λ Gf M') (f : IntertwiningMap τ τ')

theorem coinvA_natural (u : Coinvariants ((rRep Λ Gf).tprod τ)) :
    coinvA τ' (Coinvariants.map _ _ (f.lTensor (rRep Λ Gf)) u) = f (coinvA τ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m =>
    simp only [Coinvariants.map_mk, IntertwiningMap.lTensor_apply, coinvA_mk_tmul]
    exact (asAlgebraHom_natural τ f a m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Finite Λ] [Finite Gf] [Finite M] [Finite M'] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

variable (S) in
/-- `iso1` is natural in the coefficients. -/
theorem iso1_natural [Fintype S] [DecidableEq S] (u : Coinvariants ((rho1 Λ π Γ S).tprod τ)) :
    iso1 π Γ S hπ τ' hΛ hall (Coinvariants.map _ _ (f.lTensor (rho1 Λ π Γ S)) u) =
      K1map (τ.comp π) (τ'.comp π) Γ f.toLinearMap (fun g m => LinearMap.congr_fun (f.isIntertwining' (π g)) m)
        (iso1 π Γ S hπ τ hΛ hall u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    simp only [Coinvariants.map_mk, IntertwiningMap.lTensor_apply, iso1_mk_tmul, K1map, LinearMap.prodMap_apply,
      LinearMap.coe_piMap]
    refine Prod.ext (Subtype.ext (funext fun g => ?_)) (funext fun s => ?_)
    · simp only [Phi_mk_tmul, z1Map_apply]
      exact (asAlgebraHom_natural τ f _ m).symm
    · exact (asAlgebraHom_natural τ f _ m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `iso2` is natural in the coefficients. -/
theorem iso2_natural [Fintype S] [DecidableEq S] (u : Coinvariants ((rho2 Λ π Γ I).tprod τ)) :
    iso2 π Γ I hπ τ' hΛ hallI (Coinvariants.map _ _ (f.lTensor (rho2 Λ π Γ I)) u) =
      K2map (τ.comp π) (τ'.comp π) Γ I f.toLinearMap (fun g m => LinearMap.congr_fun (f.isIntertwining' (π g)) m)
        (iso2 π Γ I hπ τ hΛ hallI u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    refine funext fun s => Subtype.ext (funext fun g => ?_)
    simp only [Coinvariants.map_mk, IntertwiningMap.lTensor_apply, iso2_mk_tmul, K2map, LinearMap.coe_piMap, Pi.map_apply,
      Phi_mk_tmul, z1Map_apply]
    exact (asAlgebraHom_natural τ f _ m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_HattoriStallings_CT =====
section

/-!
# Hattori–Stallings traces, part C: cohomologically trivial modules are projective

The classical statement "a finitely generated cohomologically trivial `ℤ/ℓⁿ[G]`-module is
projective" is false as literally stated (for `G = 1`, `ℤ/ℓ` over `ℤ/ℓ²` is cohomologically trivial
but not projective); the correct form needs the module to be free over `ℤ/ℓⁿ`, and the cohomological
input is only `Ĥ⁰(S, P/𝔪P) = 0` for a Sylow subgroup `S`. We prove it over any local ring `R`
with finite residue field `k` of characteristic `p` (e.g. `R = ZMod (p^n)`):

* `eq_bot_of_no_invariants`: the fixed-point lemma for `p`-groups.
* `isProj_of_isPGroup` (field case): a finite-dimensional representation `M` of a `p`-group `S`
  over a finite field of characteristic `p` with `M^S = N_S M` (i.e. `Ĥ⁰(S, M) = 0`) is projective.
* `IsHigman.of_subgroup`: relative Higman criterion (`[G : S]` invertible).
* `isProj_of_residue`: a free finite `R[G]`-module whose reduction to `k` is projective is projective.
* `isProj_of_sylow`: **main theorem**: `P` free finite over `R`, `S ≤ G` a `p`-subgroup of index
  prime to `p`, and `Ĥ⁰(S, k ⊗ P) = 0`, then `P` is projective over `R[G]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap TensorProduct

section FixedPoint

variable {k : Type*} [Field k] {S : Type*} [Group S] [Fintype S]
variable {V : Type*} [AddCommGroup V] [Module k V] {θ : Representation k S V}

/-- **Fixed-point lemma.** A `θ`-stable subspace of a finite representation of a `p`-group over a
field of characteristic `p` without nonzero invariants is zero. -/
theorem eq_bot_of_no_invariants (p : ℕ) [Fact p.Prime] [CharP k p] [Finite V] (hS : IsPGroup p S)
    (K : Submodule k V) (hK : ∀ (s : S), ∀ x ∈ K, θ s x ∈ K)
    (h0 : ∀ x ∈ K, (∀ s : S, θ s x = x) → x = 0) : K = ⊥ := by
  by_contra hne
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let act : MulAction S K :=
    { smul := fun s y => ⟨θ s y, hK s y y.2⟩
      one_smul := fun y => Subtype.ext (by
        show θ 1 (y : V) = (y : V)
        rw [map_one, Module.End.one_apply])
      mul_smul := fun a b y => Subtype.ext (by
        show θ (a * b) (y : V) = θ a (θ b (y : V))
        rw [map_mul, Module.End.mul_apply]) }
  have hfix : Nat.card (MulAction.fixedPoints S K) = 1 := by
    refine Nat.card_eq_one_iff_exists.2
      ⟨⟨0, MulAction.mem_fixedPoints.2 fun s => Subtype.ext (by
        show θ s 0 = 0
        exact map_zero _)⟩, fun y => ?_⟩
    have hy : ∀ s : S, θ s ((y.1 : K) : V) = (y.1 : V) := fun s =>
      congrArg Subtype.val (MulAction.mem_fixedPoints.1 y.2 s)
    exact Subtype.ext (Subtype.ext (h0 _ y.1.2 hy))
  have hmod := hS.card_modEq_card_fixedPoints K
  rw [hfix] at hmod
  have hord : addOrderOf (⟨x, hxK⟩ : K) = p := by
    refine addOrderOf_eq_prime ?_ ?_
    · rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]
    · intro h
      exact hx0 (congrArg Subtype.val h)
  have hdvd : p ∣ Nat.card K := by
    rw [← hord]
    exact addOrderOf_dvd_natCard _
  have h1 : 1 ≡ 0 [MOD p] := hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd)
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 (Nat.modEq_zero_iff_dvd.1 h1))

end FixedPoint

section FieldCase

/-- `S` acting on `J × S` by left multiplication on the second factor (a free action). -/
@[instance_reducible]
def prodRightAction (J : Type*) (S : Type*) [Group S] : MulAction S (J × S) where
  smul s x := (x.1, s * x.2)
  one_smul x := Prod.ext rfl (one_mul x.2)
  mul_smul a b x := Prod.ext rfl (mul_assoc a b x.2)

variable {k : Type*} [Field k] {S : Type*} [Group S] [Fintype S]
variable {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
variable {σ : Representation k S M}

/-- **Field case.** A finite-dimensional representation of a `p`-group over a finite field of
characteristic `p` whose invariants are norms (`Ĥ⁰(S, M) = 0`) is projective (in fact free). -/
theorem isProj_of_isPGroup (p : ℕ) [Fact p.Prime] [CharP k p] [Finite k] (hS : IsPGroup p S)
    (hN : ∀ x : M, (∀ s : S, σ s x = x) → ∃ y : M, x = ∑ s : S, σ s y) : IsProj σ := by
  classical
  -- a basis of the invariants, written as norms
  let I := σ.invariants
  let n := Module.finrank k I
  let bI : Module.Basis (Fin n) k I := Module.finBasis k I
  have hyex : ∀ j : Fin n, ∃ y : M, ((bI j : I) : M) = ∑ s : S, σ s y := fun j =>
    hN _ ((Representation.mem_invariants σ _).1 (bI j).2)
  choose y hy using hyex
  -- the free permutation module on `Fin n × S`
  letI : MulAction S (Fin n × S) := prodRightAction (Fin n) S
  have hsmul : ∀ (s : S) (x : Fin n × S), s • x = (x.1, s * x.2) := fun _ _ => rfl
  let ρF := permRep k S (Fin n × S)
  have hρF : ∀ (s : S) (f : Fin n × S → k) (x : Fin n × S), ρF s f x = f (x.1, s⁻¹ * x.2) :=
    fun s f x => by simp only [ρF, permRep_apply, hsmul]
  -- `φ (e_(j,t)) = σ t (y j)`
  let φ : (Fin n × S → k) →ₗ[k] M := Fintype.linearCombination k (fun x : Fin n × S => σ x.2 (y x.1))
  have hφ : ∀ f : Fin n × S → k, φ f = ∑ x : Fin n × S, f x • σ x.2 (y x.1) := fun _ => rfl
  have hφE : IsEquivariant ρF σ φ := by
    refine isEquivariant_iff.2 fun g f => ?_
    rw [hφ, hφ, map_sum]
    refine Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl _) (Equiv.mulLeft g⁻¹)) _ _ fun x => ?_
    simp only [hρF, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
      Equiv.refl_apply, Equiv.coe_mulLeft, map_smul, rep_apply_apply σ, mul_inv_cancel_left]
    rfl
  have hinvF : ∀ f : Fin n × S → k, (∀ s : S, ρF s f = f) → f = fun x => f (x.1, 1) := by
    intro f hf
    funext x
    have h := congrFun (hf x.2⁻¹) (x.1, 1)
    simp only [hρF, inv_inv, mul_one] at h
    exact h
  have hφc : ∀ c : Fin n → k, φ (fun x => c x.1) = ∑ j, c j • ((bI j : I) : M) := by
    intro c
    simp only [hφ, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy j, Finset.smul_sum]
  have hli : ∀ c : Fin n → k, ∑ j, c j • ((bI j : I) : M) = 0 → c = 0 := by
    intro c hc
    have hc' : ∑ j, c j • bI j = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
      exact hc
    funext j
    exact Fintype.linearIndependent_iff.1 bI.linearIndependent c hc' j
  -- `φ` is injective (fixed-point lemma)
  have hker : LinearMap.ker φ = ⊥ := by
    refine eq_bot_of_no_invariants (θ := ρF) p hS (LinearMap.ker φ) (fun s f hf => ?_)
      (fun f hf hinv => ?_)
    · rw [LinearMap.mem_ker] at hf ⊢
      rw [hφE.apply, hf, map_zero]
    · rw [LinearMap.mem_ker] at hf
      have hfc := hinvF f hinv
      have h2 : φ (fun x => f (x.1, 1)) = ∑ j, f (j, 1) • ((bI j : I) : M) :=
        hφc (fun j => f (j, 1))
      rw [← hfc] at h2
      rw [h2] at hf
      have h3 := hli _ hf
      rw [hfc]
      funext x
      exact congrFun h3 x.1
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective φ hker
  -- the equivariant retraction `r m (j, t) = L (σ t⁻¹ m) (j, 1)`
  let r : M →ₗ[k] (Fin n × S → k) :=
    LinearMap.pi fun x : Fin n × S =>
      (LinearMap.proj ((x.1, 1) : Fin n × S) ∘ₗ L) ∘ₗ σ x.2⁻¹
  have hr : ∀ (m : M) (x : Fin n × S), r m x = L (σ x.2⁻¹ m) (x.1, 1) := fun _ _ => rfl
  have hrE : IsEquivariant σ ρF r := by
    refine isEquivariant_iff.2 fun g m => ?_
    funext x
    rw [hρF, hr, hr, rep_apply_apply σ]
    simp only
    rw [show (g⁻¹ * x.2)⁻¹ = x.2⁻¹ * g by group]
  have hrφ : ∀ f, r (φ f) = f := by
    intro f
    funext x
    rw [hr, ← hφE.apply, ← LinearMap.comp_apply L φ, hL, LinearMap.id_apply]
    simp only [hρF, inv_inv, mul_one, Prod.mk.eta]
  -- `r` is injective (fixed-point lemma again)
  have : Finite M := Module.finite_of_finite k
  have hrker : LinearMap.ker r = ⊥ := by
    refine eq_bot_of_no_invariants (θ := σ) p hS (LinearMap.ker r) (fun s m hm => ?_)
      (fun m hm hinv => ?_)
    · rw [LinearMap.mem_ker] at hm ⊢
      rw [hrE.apply, hm, map_zero]
    · rw [LinearMap.mem_ker] at hm
      have hmI : m ∈ I := (Representation.mem_invariants σ m).2 hinv
      obtain ⟨c, hm'⟩ : ∃ c : Fin n → k, m = ∑ j, c j • ((bI j : I) : M) := by
        refine ⟨bI.repr ⟨m, hmI⟩, ?_⟩
        have h := congrArg Subtype.val (bI.sum_repr ⟨m, hmI⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        exact h.symm
      have hmφ : m = φ (fun x => c x.1) := by rw [hφc]; exact hm'
      rw [hmφ, hrφ] at hm
      have hc0 : ∀ j, c j = 0 := fun j => by simpa using congrFun hm (j, 1)
      rw [hm']
      simp [hc0]
  have hrinj : Function.Injective r := LinearMap.ker_eq_bot.1 hrker
  have hφr : φ ∘ₗ r = LinearMap.id :=
    LinearMap.ext fun m => hrinj (by simp only [LinearMap.comp_apply, LinearMap.id_apply, hrφ])
  refine IsProj.retract (isProj_permRep fun s x hx => ?_) hrE hφE hφr
  rw [hsmul] at hx
  simpa using congrArg Prod.snd hx

end FieldCase

section Relative

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

/-- **Relative Higman criterion.** If `P` is projective over `R[S]` and `[G : S]` is invertible
in `R`, then `P` is projective over `R[G]`, with Higman datum `[G : S]⁻¹ • E_S`. -/
theorem IsHigman.of_subgroup (S : Subgroup G) [Fintype S] {E : P →ₗ[R] P}
    (hE : IsHigman (ρ.comp S.subtype) E) {u : R} (hu : u * (S.index : R) = 1) :
    IsHigman ρ (u • E) := by
  classical
  have hE' : ∀ v : P, ∑ s : S, ρ s (E (ρ (s : G)⁻¹ v)) = v := fun v => by
    have h := LinearMap.congr_fun hE v
    simpa [LinearMap.sum_apply] using h
  let e : ∀ q : G ⧸ S, {g : G // (g : G ⧸ S) = q} ≃ S := fun q =>
    { toFun := fun g => ⟨q.out⁻¹ * g, by
        exact QuotientGroup.eq.1 ((QuotientGroup.out_eq' q).trans g.2.symm)⟩
      invFun := fun s => ⟨q.out * s, by
        rw [QuotientGroup.mk_mul_of_mem _ s.2, QuotientGroup.out_eq']⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp) }
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
    LinearMap.id_apply]
  rw [← Finset.smul_sum]
  have hsum : ∑ g : G, ρ g (E (ρ g⁻¹ v)) = (S.index : R) • v := by
    calc ∑ g : G, ρ g (E (ρ g⁻¹ v))
        = ∑ q : G ⧸ S, ∑ g : {g : G // (g : G ⧸ S) = q}, ρ (g : G) (E (ρ (g : G)⁻¹ v)) :=
          (Fintype.sum_fiberwise (fun g : G => (g : G ⧸ S)) (fun g => ρ g (E (ρ g⁻¹ v)))).symm
      _ = ∑ q : G ⧸ S, ∑ s : S, ρ (q.out * (s : G)) (E (ρ (q.out * (s : G))⁻¹ v)) := by
          refine Finset.sum_congr rfl fun q _ => Fintype.sum_equiv (e q) _ _ fun g => ?_
          simp [e]
      _ = ∑ _q : G ⧸ S, v := by
          refine Finset.sum_congr rfl fun q _ => ?_
          have h1 : ∀ s : S, ρ (q.out * (s : G)) (E (ρ (q.out * (s : G))⁻¹ v)) =
              ρ q.out (ρ (s : G) (E (ρ (s : G)⁻¹ (ρ q.out⁻¹ v)))) := fun s => by
            rw [mul_inv_rev, ← rep_apply_apply ρ q.out (s : G),
              ← rep_apply_apply ρ (s : G)⁻¹ q.out⁻¹]
          rw [Finset.sum_congr rfl fun s _ => h1 s, ← map_sum (ρ q.out), hE', rep_apply_inv_apply]
      _ = (S.index : R) • v := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
            ← Subgroup.index_eq_card, Nat.cast_smul_eq_nsmul]
  rw [hsum, smul_smul, hu, one_smul]

theorem IsProj.of_subgroup (S : Subgroup G) [Fintype S] (hS : IsProj (ρ.comp S.subtype))
    (hu : IsUnit (S.index : R)) : IsProj ρ := by
  obtain ⟨E, hE⟩ := hS
  obtain ⟨u, hu⟩ := hu
  exact ⟨_, hE.of_subgroup S (u := ↑u⁻¹) (by rw [← hu, Units.inv_mul])⟩

end Relative

section Lift

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

lemma avg_baseChange (A : Type*) [CommRing A] [Algebra R A] (f : P →ₗ[R] P) :
    (avg ρ ρ f).baseChange A = avg (repBaseChange A ρ) (repBaseChange A ρ) (f.baseChange A) := by
  have h1 : (∑ h : G, ρ h ∘ₗ f ∘ₗ ρ h⁻¹).baseChange A =
      ∑ h : G, (ρ h ∘ₗ f ∘ₗ ρ h⁻¹).baseChange A :=
    map_sum (LinearMap.baseChangeHom R A P P) _ _
  rw [avg, avg, h1]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [repBaseChange_apply, repBaseChange_apply, LinearMap.baseChange_comp,
    LinearMap.baseChange_comp]

variable [IsLocalRing R] [Module.Free R P] [Module.Finite R P]

/-- Every endomorphism of `k ⊗ P` lifts to an endomorphism of `P` (`P` free finite). -/
lemma exists_baseChange_eq (F : IsLocalRing.ResidueField R ⊗[R] P →ₗ[IsLocalRing.ResidueField R]
    IsLocalRing.ResidueField R ⊗[R] P) :
    ∃ E : P →ₗ[R] P, E.baseChange (IsLocalRing.ResidueField R) = F := by
  classical
  let b := Module.Free.chooseBasis R P
  let bk := Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b
  obtain ⟨l, hl⟩ : ∃ l : IsLocalRing.ResidueField R → R,
      ∀ x, IsLocalRing.residue R (l x) = x :=
    ⟨Function.surjInv (IsLocalRing.residue_surjective), fun x => Function.surjInv_eq _ x⟩
  refine ⟨Matrix.toLin b b ((LinearMap.toMatrix bk bk F).map l), ?_⟩
  apply (LinearMap.toMatrix bk bk).injective
  rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_toLin]
  ext i j
  simp [hl]

/-- **Lifting projectivity from the residue field.** Over a local ring, a free finite `R[G]`-module
whose reduction `k ⊗ P` is projective over `k[G]` is projective. -/
theorem isProj_of_residue {F : IsLocalRing.ResidueField R ⊗[R] P →ₗ[IsLocalRing.ResidueField R]
    IsLocalRing.ResidueField R ⊗[R] P}
    (hF : IsHigman (repBaseChange (IsLocalRing.ResidueField R) ρ) F) : IsProj ρ := by
  obtain ⟨E0, hE0⟩ := exists_baseChange_eq F
  have hDk : (avg ρ ρ E0).baseChange (IsLocalRing.ResidueField R) = LinearMap.id := by
    rw [avg_baseChange, hE0]
    exact hF
  have hdet : IsUnit (LinearMap.det (avg ρ ρ E0)) := by
    have h : LinearMap.det ((avg ρ ρ E0).baseChange (IsLocalRing.ResidueField R)) =
        algebraMap R (IsLocalRing.ResidueField R) (LinearMap.det (avg ρ ρ E0)) := by
      rw [LinearMap.det_baseChange]
    rw [hDk, LinearMap.det_id, IsLocalRing.ResidueField.algebraMap_eq] at h
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [← h]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_isUnit_det (avg ρ ρ E0)).2 hdet
  have hD : IsEquivariant ρ ρ (avg ρ ρ E0) := isEquivariant_avg E0
  have hinv : IsEquivariant ρ ρ (↑u⁻¹ : P →ₗ[R] P) := fun g => by
    have hc : Commute (↑u : Module.End R P) (ρ g) := by
      rw [hu]
      exact hD g
    exact hc.units_inv_left
  refine ⟨E0 ∘ₗ ↑u⁻¹, ?_⟩
  show avg ρ ρ (E0 ∘ₗ ↑u⁻¹) = LinearMap.id
  rw [hinv.avg_comp_right, ← hu]
  exact u.mul_inv

end Lift

section Main

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
variable {ρ : Representation R G P}

/-- **Cohomologically trivial ⇒ projective** (corrected form). Let `R` be a local ring with finite
residue field `k` of characteristic `p` (e.g. `R = ZMod (p^n)`), `P` a free finite `R`-module with a
`G`-action, and `S ≤ G` a `p`-subgroup of index prime to `p` (e.g. a Sylow subgroup). If
`Ĥ⁰(S, k ⊗ P) = 0`, i.e. every `S`-invariant of `k ⊗ P` is a norm, then `P` is projective over
`R[G]`. -/
theorem isProj_of_sylow (p : ℕ) [Fact p.Prime] [Finite (IsLocalRing.ResidueField R)]
    [CharP (IsLocalRing.ResidueField R) p] (S : Subgroup G) [Fintype S] (hS : IsPGroup p S)
    (hindex : ¬ p ∣ S.index)
    (hN : ∀ x : IsLocalRing.ResidueField R ⊗[R] P,
      (∀ s : S, repBaseChange (IsLocalRing.ResidueField R) ρ s x = x) →
        ∃ y, x = ∑ s : S, repBaseChange (IsLocalRing.ResidueField R) ρ s y) :
    IsProj ρ := by
  have hσ : IsProj ((repBaseChange (IsLocalRing.ResidueField R) ρ).comp S.subtype) :=
    isProj_of_isPGroup p hS hN
  have hunit : IsUnit (S.index : IsLocalRing.ResidueField R) := by
    refine isUnit_iff_ne_zero.2 ?_
    rwa [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) p]
  obtain ⟨F, hF⟩ := IsProj.of_subgroup S hσ hunit
  exact isProj_of_residue hF

end Main

end RamanujanPetersson.HattoriStallings

end

-- ===== S4.Def_RP_PerfectCx_Proj =====
section

/-!
# S4-PD (5), E2(b): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ[Gf]`-projective

* `isProj_of_sylow_mod`: the `S4-HattoriStallings` Sylow criterion with the residue-field hypothesis stated in `P`
  itself: if every `x` with `s x - x ∈ ϖP` (`s ∈ S`) is a norm `∑ₛ s y` modulo `ϖP`, then `P` is projective;
* `exists_norm_add`: the norm step on `Λ[Gf]` (coefficients constant mod `ϖ` on the cosets `hS` come from the
  transversal truncation `trunc`);
* `norm_E`: the same norm step on cocycles (lift along `psi : (a, b) ↦ a·N_S + ϖ b`, `lift_of_values`);
* `proj_E`: **E2(b)**, `E` is projective over `Λ[Gf]` (given `H² = 0` on `Γ` and finiteness of `E`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra IsLocalRing TensorProduct

noncomputable section

section Mod

variable {R : Type} [CommRing R] [IsLocalRing R] {P : Type} [AddCommGroup P] [Module R P]

theorem one_tmul_eq_zero_iff (v : P) :
    (1 : ResidueField R) ⊗ₜ[R] v = 0 ↔ v ∈ maximalIdeal R • (⊤ : Submodule R P) := by
  change (1 : R ⧸ maximalIdeal R) ⊗ₜ[R] v = 0 ↔ _
  rw [← (quotTensorEquivQuotSMul P (maximalIdeal R)).map_eq_zero_iff, quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.Quotient.mk_eq_zero]

theorem exists_one_tmul (x : ResidueField R ⊗[R] P) : ∃ v : P, (1 : ResidueField R) ⊗ₜ[R] v = x := by
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective (p := maximalIdeal R • (⊤ : Submodule R P))
    (quotTensorEquivQuotSMul P (maximalIdeal R) x)
  refine ⟨v, (quotTensorEquivQuotSMul P (maximalIdeal R)).injective ?_⟩
  rw [← hv]
  exact quotTensorEquivQuotSMul_mk_one_tmul _ v

theorem mem_smul_top_iff_of_span {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (v : P) :
    v ∈ maximalIdeal R • (⊤ : Submodule R P) ↔ ∃ z, v = ϖ • z := by
  rw [hϖ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, Submodule.mem_top, rfl⟩

variable {Gf : Type} [Group Gf] [Fintype Gf]

/-- The Sylow projectivity criterion with the residue-field norm hypothesis stated modulo `ϖ` in `P`. -/
theorem isProj_of_sylow_mod [Module.Free R P] [Module.Finite R P] {ρ : Representation R Gf P} {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (p : ℕ) [Fact p.Prime] [Finite (ResidueField R)]
    [CharP (ResidueField R) p] (S : Subgroup Gf) [Fintype S] (hS : IsPGroup p S) (hindex : ¬ p ∣ S.index)
    (hN : ∀ x : P, (∀ s : S, ∃ z, ρ s x - x = ϖ • z) → ∃ y w, x - ∑ s : S, ρ s y = ϖ • w) :
    HattoriStallings.IsProj ρ := by
  refine HattoriStallings.isProj_of_sylow p S hS hindex fun x hx => ?_
  obtain ⟨v, rfl⟩ := exists_one_tmul x
  have hv : ∀ s : S, ∃ z, ρ s v - v = ϖ • z := fun s => by
    have h1 := hx s
    rw [HattoriStallings.repBaseChange_apply, LinearMap.baseChange_tmul] at h1
    have h2 : (1 : ResidueField R) ⊗ₜ[R] (ρ s v - v) = 0 := by rw [tmul_sub, h1, sub_self]
    exact (mem_smul_top_iff_of_span hϖ _).1 ((one_tmul_eq_zero_iff _).1 h2)
  obtain ⟨y, w, hyw⟩ := hN v hv
  refine ⟨1 ⊗ₜ[R] y, ?_⟩
  simp only [HattoriStallings.repBaseChange_apply, LinearMap.baseChange_tmul]
  rw [← tmul_sum, ← sub_eq_zero, ← tmul_sub, hyw]
  exact (one_tmul_eq_zero_iff _).2 ((mem_smul_top_iff_of_span hϖ _).2 ⟨w, rfl⟩)

end Mod

section Norm

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] (S : Subgroup Gf) [Fintype S]

/-- Keep the coefficients of `a` on the transversal `{(hS).out}` of `Gf ⧸ S`. -/
def trunc [DecidableEq Gf] (a : MonoidAlgebra Λ Gf) : MonoidAlgebra Λ Gf :=
  ofCoeff (Finsupp.equivFunOnFinite.symm fun x =>
    if (QuotientGroup.mk x : Gf ⧸ S).out = x then a.coeff x else 0)

theorem trunc_coeff [DecidableEq Gf] (a : MonoidAlgebra Λ Gf) (x : Gf) :
    (trunc S a).coeff x = if (QuotientGroup.mk x : Gf ⧸ S).out = x then a.coeff x else 0 := rfl

theorem sum_coeff_trunc [DecidableEq Gf] (a : MonoidAlgebra Λ Gf) (h : Gf) :
    ∑ s : S, (trunc S a).coeff (h * s) = a.coeff (QuotientGroup.mk h : Gf ⧸ S).out := by
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul S h
  have hmk : ∀ s : S, (QuotientGroup.mk (h * s) : Gf ⧸ S) = QuotientGroup.mk h := fun s =>
    QuotientGroup.eq.2 (by rw [mul_inv_rev, inv_mul_cancel_right]; exact S.inv_mem s.2)
  have h0 : ∀ s ∈ (Finset.univ : Finset S), s ≠ t → (trunc S a).coeff (h * s) = 0 := fun s _ hs => by
    rw [trunc_coeff, hmk s, ht, if_neg fun h' => hs (Subtype.ext (mul_left_cancel h')).symm]
  rw [Finset.sum_eq_single t h0 (fun ht' => absurd (Finset.mem_univ t) ht'), trunc_coeff, hmk t, ht, if_pos rfl]

theorem coeff_sum_mul_single (a : MonoidAlgebra Λ Gf) (h : Gf) :
    (∑ s : S, a * single ((s : Gf)⁻¹) (1 : Λ)).coeff h = ∑ s : S, a.coeff (h * s) := by
  rw [coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_mul_single_apply, inv_inv, mul_one]

/-- The norm step on `Λ[Gf]`: coefficients constant modulo `ϖ` on the cosets `hS` give a norm modulo `ϖ`. -/
theorem exists_norm_add [DecidableEq Gf] (a : MonoidAlgebra Λ Gf) {ϖ : Λ}
    (ha : ∀ s : S, ∃ z : MonoidAlgebra Λ Gf, a * single ((s : Gf)⁻¹) 1 - a = ϖ • z) :
    ∃ b : MonoidAlgebra Λ Gf, a = ∑ s : S, trunc S a * single ((s : Gf)⁻¹) 1 + ϖ • b := by
  have hx : ∀ h : Gf, ∃ y, a.coeff h - ∑ s : S, (trunc S a).coeff (h * s) = ϖ * y := fun h => by
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul S h
    obtain ⟨z, hz⟩ := ha t
    refine ⟨-z.coeff h, ?_⟩
    have h1 := congrArg (fun x : MonoidAlgebra Λ Gf => x.coeff h) hz
    simp only [coeff_sub, Finsupp.sub_apply, coeff_mul_single_apply, inv_inv, mul_one, coeff_smul_apply,
      smul_eq_mul] at h1
    rw [sum_coeff_trunc, ht, mul_neg, ← h1]
    ring
  choose y hy using hx
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm y), ?_⟩
  ext h
  have hc : (ofCoeff (Finsupp.equivFunOnFinite.symm y) : MonoidAlgebra Λ Gf).coeff h = y h := rfl
  rw [coeff_add, Finsupp.add_apply, coeff_sum_mul_single, coeff_smul_apply, hc, smul_eq_mul, ← hy h]
  abel

/-- `N_S = ∑_{s ∈ S} s⁻¹`. -/
def nS : MonoidAlgebra Λ Gf := ∑ s : S, single ((s : Gf)⁻¹) 1

theorem mul_nS (a : MonoidAlgebra Λ Gf) : a * nS S = ∑ s : S, a * single ((s : Gf)⁻¹) (1 : Λ) :=
  Finset.mul_sum _ _ _

theorem nS_mul_single (s : S) : nS S * single ((s : Gf)⁻¹) (1 : Λ) = nS S := by
  unfold nS
  rw [Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp only [single_mul_single, one_mul, Equiv.coe_mulLeft, Subgroup.coe_mul, mul_inv_rev]

/-- `{a | a s⁻¹ - a ∈ ϖA for all s ∈ S}`. -/
def normSub (ϖ : Λ) : Submodule Λ (MonoidAlgebra Λ Gf) where
  carrier := {a | ∀ s : S, ∃ z, a * single ((s : Gf)⁻¹) 1 - a = ϖ • z}
  add_mem' {a b} ha hb s := by
    obtain ⟨z, hz⟩ := ha s
    obtain ⟨w, hw⟩ := hb s
    exact ⟨z + w, by rw [add_mul, smul_add, ← hz, ← hw]; abel⟩
  zero_mem' s := ⟨0, by simp⟩
  smul_mem' c {a} ha s := by
    obtain ⟨z, hz⟩ := ha s
    exact ⟨c • z, by rw [smul_mul_assoc, ← smul_sub, hz, smul_comm]⟩

theorem mem_normSub (ϖ : Λ) (a : MonoidAlgebra Λ Gf) :
    a ∈ normSub S ϖ ↔ ∀ s : S, ∃ z, a * single ((s : Gf)⁻¹) 1 - a = ϖ • z := Iff.rfl

/-- `(a, b) ↦ a·N_S + ϖ b`. -/
def psi (ϖ : Λ) : MonoidAlgebra Λ Gf × MonoidAlgebra Λ Gf →ₗ[Λ] MonoidAlgebra Λ Gf :=
  LinearMap.coprod (LinearMap.mulRight Λ (nS S)) (LinearMap.lsmul Λ _ ϖ)

theorem psi_apply (ϖ : Λ) (p : MonoidAlgebra Λ Gf × MonoidAlgebra Λ Gf) : psi S ϖ p = p.1 * nS S + ϖ • p.2 := rfl

theorem psi_mem (ϖ : Λ) (p : MonoidAlgebra Λ Gf × MonoidAlgebra Λ Gf) : psi S ϖ p ∈ normSub S ϖ :=
  (mem_normSub S ϖ _).2 fun s => ⟨p.2 * single ((s : Gf)⁻¹) 1 - p.2, by
    rw [psi_apply, add_mul, mul_assoc, nS_mul_single, smul_mul_assoc, smul_sub]; abel⟩

theorem psi_surj [DecidableEq Gf] (ϖ : Λ) (w : MonoidAlgebra Λ Gf) (hw : w ∈ normSub S ϖ) :
    ∃ p, psi S ϖ p = w := by
  obtain ⟨b, hb⟩ := exists_norm_add S w hw
  exact ⟨(trunc S w, b), by rw [psi_apply, mul_nS]; exact hb.symm⟩

end Norm

section Cocycles

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

theorem isOpen_prod_ker (hπ : IsOpen (π.ker : Set G)) :
    IsOpen (((regRep Λ π).prod (regRep Λ π)).ker : Set G) := by
  refine Subgroup.isOpen_mono (fun g hg => ?_) hπ
  rw [MonoidHom.mem_ker] at hg ⊢
  have h1 : regRep Λ π g = 1 := by
    show leftRep Λ Gf (π g) = 1
    rw [hg, map_one]
  show (regRep Λ π g).prodMap (regRep Λ π g) = 1
  rw [h1, LinearMap.prodMap_one]

variable [Finite Gf] (S : Subgroup Gf) [Fintype S]

theorem psi_equiv (ϖ : Λ) (g : G) (p : MonoidAlgebra Λ Gf × MonoidAlgebra Λ Gf) :
    psi S ϖ (((regRep Λ π).prod (regRep Λ π)) g p) = regRep Λ π g (psi S ϖ p) := by
  show single (π g) 1 * p.1 * nS S + ϖ • (single (π g) 1 * p.2) = single (π g) 1 * (p.1 * nS S + ϖ • p.2)
  rw [mul_add, mul_assoc, mul_smul_comm]

/-- `normSub` as a subrepresentation of `regRep` (left multiplication commutes with right multiplication). -/
def normRep (ϖ : Λ) : Subrepresentation (regRep Λ π) where
  toSubmodule := normSub S ϖ
  apply_mem_toSubmodule g v hv := (mem_normSub S ϖ _).2 fun s => by
    obtain ⟨z, hz⟩ := (mem_normSub S ϖ _).1 hv s
    exact ⟨regRep Λ π g z, by rw [regRep_apply, regRep_apply, mul_assoc, ← mul_sub, hz, mul_smul_comm]⟩

theorem sum_eRep (y : Z1 (regRep Λ π) Γ) (g : Γ) :
    ((∑ s : S, eRep π Γ s y : Z1 (regRep Λ π) Γ) : Γ → MonoidAlgebra Λ Gf) g =
      (y : Γ → MonoidAlgebra Λ Gf) g * nS S := by
  rw [Submodule.coe_sum, Finset.sum_apply, mul_nS]
  rfl

/-- The norm step on cocycles: `x` with `s x - x ∈ ϖE` (`s ∈ S`) is a norm modulo `ϖE`. -/
theorem norm_E [Finite Λ] {ϖ : Λ} {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N)
    (hπ : IsOpen (π.ker : Set G)) (x : Z1 (regRep Λ π) Γ) (hx : ∀ s : S, ∃ z, eRep π Γ s x - x = ϖ • z) :
    ∃ y w, x - ∑ s : S, eRep π Γ s y = ϖ • w := by
  classical
  have := finite_A Λ Gf
  have hz : ∀ g, (x : Γ → MonoidAlgebra Λ Gf) g ∈ (normRep π S ϖ).toSubmodule := fun g =>
    (mem_normSub S ϖ _).2 fun s => by
      obtain ⟨z, hz⟩ := hx s
      exact ⟨(z : Γ → MonoidAlgebra Λ Gf) g,
        congrArg (fun c : Z1 (regRep Λ π) Γ => (c : Γ → MonoidAlgebra Λ Gf) g) hz⟩
  obtain ⟨c, hc⟩ := lift_of_values ((regRep Λ π).prod (regRep Λ π)) (regRep Λ π) Γ hall
    (nsmul_eq_zero_of_cast hΛ) (isOpen_prod_ker π hπ) (psi S ϖ) (psi_equiv π S ϖ) (normRep π S ϖ)
    (psi_mem S ϖ) (psi_surj S ϖ) x hz
  let y := z1Map ((regRep Λ π).prod (regRep Λ π)) (regRep Λ π) Γ (LinearMap.fst Λ _ _) (fun _ _ => rfl) c
  let w := z1Map ((regRep Λ π).prod (regRep Λ π)) (regRep Λ π) Γ (LinearMap.snd Λ _ _) (fun _ _ => rfl) c
  refine ⟨y, w, Subtype.ext (funext fun g => ?_)⟩
  rw [Submodule.coe_sub, Pi.sub_apply, sum_eRep, coe_smul_Z1, ← hc g, psi_apply]
  exact add_sub_cancel_left _ _

/-- **E2(b)**: `E = Z¹(Γ; Λ[Gf])` is projective over `Λ[Gf]` (`S` an `l`-subgroup of index prime to `l`, e.g. a
Sylow subgroup; `H² = 0` on `Γ`; `E` finite). -/
theorem proj_E [IsLocalRing Λ] [Finite Λ] [Fintype Gf] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) {n : ℕ}
    (hn : ϖ ^ n = 0) (hn' : ∀ m < n, ϖ ^ m ≠ 0) {l N : ℕ} [Fact l.Prime] [CharP (ResidueField Λ) l]
    (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G))
    [Module.Finite Λ (Z1 (regRep Λ π) Γ)] (hS : IsPGroup l S) (hindex : ¬ l ∣ S.index) :
    HattoriStallings.IsProj (eRep (Λ := Λ) π Γ) := by
  haveI := free_E π Γ hϖ hn hn' hΛ hall hπ
  haveI : Finite (ResidueField Λ) := Finite.of_surjective _ (residue_surjective (R := Λ))
  exact isProj_of_sylow_mod hϖ l S hS hindex fun x hx => norm_E π Γ S hΛ hall hπ x hx

end Cocycles

end

end PerfectCx
end RamanujanPetersson

end


