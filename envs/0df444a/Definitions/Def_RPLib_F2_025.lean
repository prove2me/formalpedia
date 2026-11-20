-- Prove2me | Definitions.Def_RPLib_F2_025
-- name    : RPLib_F2_025
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T11:06:58.752565+00:00
-- url     : https://prove2.me/theorems/aa20e0ec-6290-447f-b491-cf61834febd3
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 025 of 70
-- statement:
--   File 025 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_HattoriStallings_Core`: Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)
--   * `S4.Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
--   * `S4.Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
--   * `S4.Def_RP_PerfectCx_Cx`: S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model
--   * `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
--   * `S4.Def_RP_HattoriStallings_Twisted`: Hattori–Stallings traces, part B1: trace relations, the twisted-trace formula, base change
--   * `S4.Def_RP_HattoriStallings_Complex`: Hattori–Stallings traces, part B2: bounded complexes (Lefschetz numbers)
--   * `S4.Def_RP_PerfectCx_Tri`: S4-PD (5), E3: three-term complexes as `ℕ`-indexed families
--   * `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
--   * `S4.Def_RP_HattoriStallings_CT`: Hattori–Stallings traces, part C: cohomologically trivial modules are projective
--   * `S4.Def_RP_PerfectCx_Proj`: S4-PD (5), E2(b): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ[Gf]`-projective
--   * `S4.Def_RP_PerfectCx_Pkg`: S4-PD (5), E3: the perfect complex as a Hattori–Stallings package
--   * `S4.Def_RP_PerfectCx_CxH`: S4-PD (5), E3: the cohomology of the cone complex
--   * `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
--   * `S4.Def_RP_Lefschetz_ConeMapG`: S4-Lefschetz, L3c: cone maps for coefficient maps that are only `Γ`-equivariant, across ambients
--   * `S4.Def_RP_Lefschetz_BlockTr`: S4-Lefschetz, L3b: traces over a block decomposition
--   * `S4.Def_RP_Lefschetz_BlockAlg`: S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`
--   * `S4.Def_RP_Lefschetz_BlockIso`: S4-Lefschetz, L3d2: a block of `Λ[Gf]` as a coinduced module
--   * `S4.Def_RP_Lefschetz_BlockCone1`: S4-Lefschetz, L3e1a: the block decomposition of the perfect complex
--   * `S4.Def_RP_Lefschetz_BlockCone2`: S4-Lefschetz, L3e1b: a fixed block of the perfect complex is the cone of an open subgroup
--   * `S4.Def_RP_Lefschetz_H2Block`: S4-Lefschetz, L3e2c1: block projections on `H²(K) = coker d¹`
--   * `S4.Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
--   * `S4.Def_RP_Lefschetz_ShapFrob`: S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius
--   * `S4.Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
--   * `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
--   * `S4.Def_RP_CoreB_Pert`: Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only
--   * `S4.Def_RP_PerfectCx_Red`: S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)
--   * `S4.Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
--   * `S4.Def_RP_CupDuality_KumPicDiv`: S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_010
import Definitions.Def_RPLib_F2_022

/-!
# Ramanujan-Petersson curve library (flat edition), file 025 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_HattoriStallings_Core`: Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)
* `S4.Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
* `S4.Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
* `S4.Def_RP_PerfectCx_Cx`: S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model
* `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
* `S4.Def_RP_HattoriStallings_Twisted`: Hattori–Stallings traces, part B1: trace relations, the twisted-trace formula, base change
* `S4.Def_RP_HattoriStallings_Complex`: Hattori–Stallings traces, part B2: bounded complexes (Lefschetz numbers)
* `S4.Def_RP_PerfectCx_Tri`: S4-PD (5), E3: three-term complexes as `ℕ`-indexed families
* `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
* `S4.Def_RP_HattoriStallings_CT`: Hattori–Stallings traces, part C: cohomologically trivial modules are projective
* `S4.Def_RP_PerfectCx_Proj`: S4-PD (5), E2(b): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ[Gf]`-projective
* `S4.Def_RP_PerfectCx_Pkg`: S4-PD (5), E3: the perfect complex as a Hattori–Stallings package
* `S4.Def_RP_PerfectCx_CxH`: S4-PD (5), E3: the cohomology of the cone complex
* `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
* `S4.Def_RP_Lefschetz_ConeMapG`: S4-Lefschetz, L3c: cone maps for coefficient maps that are only `Γ`-equivariant, across ambients
* `S4.Def_RP_Lefschetz_BlockTr`: S4-Lefschetz, L3b: traces over a block decomposition
* `S4.Def_RP_Lefschetz_BlockAlg`: S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`
* `S4.Def_RP_Lefschetz_BlockIso`: S4-Lefschetz, L3d2: a block of `Λ[Gf]` as a coinduced module
* `S4.Def_RP_Lefschetz_BlockCone1`: S4-Lefschetz, L3e1a: the block decomposition of the perfect complex
* `S4.Def_RP_Lefschetz_BlockCone2`: S4-Lefschetz, L3e1b: a fixed block of the perfect complex is the cone of an open subgroup
* `S4.Def_RP_Lefschetz_H2Block`: S4-Lefschetz, L3e2c1: block projections on `H²(K) = coker d¹`
* `S4.Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
* `S4.Def_RP_Lefschetz_ShapFrob`: S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius
* `S4.Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
* `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
* `S4.Def_RP_CoreB_Pert`: Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only
* `S4.Def_RP_PerfectCx_Red`: S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)
* `S4.Def_RP_PerfectCx_RedPC`: S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)
* `S4.Def_RP_CupDuality_KumPicDiv`: S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_HattoriStallings_Core =====
section

/-!
# Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)

A `R[G]`-module is a representation `ρ : Representation R G P` on a free finite `R`-module `P`.
Projectivity over `R[G]` is expressed by Higman's criterion (`IsHigman ρ E`:
`∑ h, ρ h ∘ E ∘ ρ h⁻¹ = id`). The Hattori–Stallings trace of an equivariant `φ` is the class function
`hs ρ φ c = ∑_{g ∈ c} Tr_R (ρ g⁻¹ ∘ φ ∘ E)`; it is independent of `E` and is the vector of class-sum
coordinates of the classical HS trace in `R[G]/[R[G], R[G]]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap

section ClassSum

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]

end ClassSum

section Higman

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {T : Type*} [AddCommGroup T] [Module R T]

/-- Projective over `R[G]` (Higman's criterion). -/
def IsProj (ρ : Representation R G P) : Prop := ∃ E : P →ₗ[R] P, IsHigman ρ E

variable {ρ : Representation R G P} {σ : Representation R G Q} {τ : Representation R G T}

lemma IsEquivariant.apply {f : P →ₗ[R] Q} (hf : IsEquivariant ρ σ f) (g : G) (x : P) :
    f (ρ g x) = σ g (f x) := LinearMap.congr_fun (hf g) x

lemma isEquivariant_iff {f : P →ₗ[R] Q} :
    IsEquivariant ρ σ f ↔ ∀ g x, f (ρ g x) = σ g (f x) :=
  ⟨fun h => h.apply, fun h g => LinearMap.ext fun x => h g x⟩

lemma isEquivariant_id : IsEquivariant ρ ρ LinearMap.id := fun _ => by
  rw [LinearMap.id_comp, LinearMap.comp_id]

lemma IsEquivariant.comp {f : P →ₗ[R] Q} {g : Q →ₗ[R] T} (hg : IsEquivariant σ τ g)
    (hf : IsEquivariant ρ σ f) : IsEquivariant ρ τ (g ∘ₗ f) :=
  isEquivariant_iff.2 fun x v => by simp [hf.apply, hg.apply]

lemma IsHigman.apply {E : P →ₗ[R] P} (hE : IsHigman ρ E) (x : P) :
    ∑ h : G, ρ h (E (ρ h⁻¹ x)) = x := by
  have := LinearMap.congr_fun hE x
  simpa [LinearMap.sum_apply] using this

lemma IsHigman.apply_inv {E : P →ₗ[R] P} (hE : IsHigman ρ E) (x : P) :
    ∑ h : G, ρ h⁻¹ (E (ρ h x)) = x := by
  conv_rhs => rw [← hE.apply x]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun h => by simp)

/-- The HS density `g ↦ Tr_R (ρ g⁻¹ ∘ φ ∘ E)`. -/
noncomputable def hsFun (ρ : Representation R G P) (E φ : P →ₗ[R] P) (g : G) : R :=
  LinearMap.trace R P (ρ g⁻¹ ∘ₗ φ ∘ₗ E)

variable [Module.Free R P] [Module.Finite R P] [Module.Free R Q] [Module.Finite R Q]

/-- The cross trace property, the heart of the theory. -/
theorem classSum_hsFun_comp_comm {EP : P →ₗ[R] P} {EQ : Q →ₗ[R] Q}
    (hP : IsHigman ρ EP) (hQ : IsHigman σ EQ) (f : P →ₗ[R] Q) (g : Q →ₗ[R] P)
    (hf : IsEquivariant ρ σ f) (hg : IsEquivariant σ ρ g) :
    classSum (hsFun ρ EP (g ∘ₗ f)) = classSum (hsFun σ EQ (f ∘ₗ g)) := by
  set F : G → G → R := fun h y =>
    LinearMap.trace R Q (f ∘ₗ (ρ h⁻¹ ∘ₗ EP ∘ₗ ρ h) ∘ₗ ρ y⁻¹ ∘ₗ g ∘ₗ EQ) with hF
  have step1 : ∀ x : G, hsFun ρ EP (g ∘ₗ f) x = ∑ h : G, F h (h⁻¹ * x * h) := by
    intro x
    have hsplit : ρ x⁻¹ ∘ₗ (g ∘ₗ f) ∘ₗ EP
        = ∑ h : G, (ρ x⁻¹ ∘ₗ g ∘ₗ σ h ∘ₗ EQ) ∘ₗ (σ h⁻¹ ∘ₗ f ∘ₗ EP) := by
      ext v
      have := hQ.apply (f (EP v))
      simp only [LinearMap.comp_apply, LinearMap.sum_apply]
      conv_lhs => rw [← this]
      simp [map_sum]
    simp only [hsFun]
    rw [hsplit, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [LinearMap.trace_comp_comm']
    simp only [hF]
    congr 1
    ext v
    simp only [LinearMap.comp_apply]
    rw [← hf.apply, hg.apply, rep_apply_apply, rep_apply_apply,
      show h * (h⁻¹ * x * h)⁻¹ = x⁻¹ * h by group]
  have step2 : classSum (hsFun ρ EP (g ∘ₗ f)) = ∑ h : G, classSum (F h) := by
    have e : hsFun ρ EP (g ∘ₗ f) = ∑ h : G, (fun x => F h (h⁻¹ * x * h)) := by
      funext x; rw [step1 x, Finset.sum_apply]
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have := classSum_conj (F h) h⁻¹
    simpa [inv_inv] using this
  have step3 : ∀ y, ∑ h : G, F h y = hsFun σ EQ (f ∘ₗ g) y := by
    intro y
    simp only [hF, hsFun]
    rw [← map_sum]
    congr 1
    ext v
    have := hP.apply_inv (ρ y⁻¹ (g (EQ v)))
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [← map_sum f, this, hf.apply]
  rw [step2, ← map_sum]
  congr 1
  funext y
  rw [Finset.sum_apply]
  exact step3 y

open Classical in
/-- The Hattori–Stallings trace (class-sum coordinates), `0` if `ρ` is not projective. -/
noncomputable def hs (ρ : Representation R G P) (φ : P →ₗ[R] P) : ConjClasses G → R :=
  if h : IsProj ρ then classSum (hsFun ρ h.choose φ) else 0

/-- `hs` is computed by ANY Higman datum. -/
theorem hs_eq {E : P →ₗ[R] P} (hE : IsHigman ρ E) {φ : P →ₗ[R] P} (hφ : IsEquivariant ρ ρ φ) :
    hs ρ φ = classSum (hsFun ρ E φ) := by
  have hp : IsProj ρ := ⟨E, hE⟩
  rw [hs, dif_pos hp]
  have := classSum_hsFun_comp_comm hp.choose_spec hE LinearMap.id φ isEquivariant_id hφ
  simpa using this

/-- Trace property across two projective representations. -/
theorem hs_comp_comm (hρ : IsProj ρ) (hσ : IsProj σ) (f : P →ₗ[R] Q) (g : Q →ₗ[R] P)
    (hf : IsEquivariant ρ σ f) (hg : IsEquivariant σ ρ g) :
    hs ρ (g ∘ₗ f) = hs σ (f ∘ₗ g) := by
  obtain ⟨EP, hP⟩ := hρ
  obtain ⟨EQ, hQ⟩ := hσ
  rw [hs_eq hP (hg.comp hf), hs_eq hQ (hf.comp hg)]
  exact classSum_hsFun_comp_comm hP hQ f g hf hg

end Higman

end RamanujanPetersson.HattoriStallings


end

-- ===== S4.Def_RP_PerfectCx_CxAlg =====
section

/-!
# S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module

* `repPi`: the pointwise representation on a dependent product; `isProj_prod`, `isProj_pi`;
* `coinvProd`, `coinvPi`: `((P × Q) ⊗ M)_G ≃ (P ⊗ M)_G × (Q ⊗ M)_G` and the same for finite products;
* `rRep`: `Gf` acting on `k[Gf]` by right multiplication by `h⁻¹`; `isProj_rRep`; balancedness `mk_mul_tmul`;
  `coinvA : (k[Gf] ⊗ M)_{Gf} ≃ M`, `⟦a ⊗ m⟧ ↦ a · m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open MonoidAlgebra TensorProduct HattoriStallings Representation

noncomputable section

section Gen

variable {k : Type} [CommRing k] {Gf : Type} [Group Gf]

theorem isProj_pi [Fintype Gf] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    {σ : ∀ i, Representation k Gf (V i)} (h : ∀ i, IsProj (σ i)) : IsProj (repPi σ) := by
  have h' : ∀ i, ∃ E : V i →ₗ[k] V i, IsHigman (σ i) E := h
  choose E hE using h'
  refine ⟨LinearMap.piMap E, LinearMap.ext fun f => funext fun i => ?_⟩
  rw [LinearMap.sum_apply, Finset.sum_apply]
  exact (hE i).apply (f i)

theorem isProj_prod [Fintype Gf] {P Q : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
    {ρ : Representation k Gf P} {σ : Representation k Gf Q} (hρ : IsProj ρ) (hσ : IsProj σ) :
    IsProj (ρ.prod σ) := by
  obtain ⟨E, hE⟩ := hρ
  obtain ⟨F, hF⟩ := hσ
  refine ⟨E.prodMap F, LinearMap.ext fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]; exact hE.apply x.1
  · rw [Prod.snd_sum]; exact hF.apply x.2

variable {M : Type} [AddCommGroup M] [Module k M] (τ : Representation k Gf M)

section Prod

variable {P Q : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
  (ρ : Representation k Gf P) (σ : Representation k Gf Q)

end Prod

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (σ : ∀ i, Representation k Gf (V i))

end Pi

end Gen

section Right

variable (k : Type) [CommRing k] (Gf : Type) [Group Gf]

variable {k Gf}

/-- The free rank-one module `k[Gf]` is projective. -/
theorem isProj_rRep [Fintype Gf] : IsProj (rRep k Gf) := by
  classical
  refine ⟨e1, LinearMap.ext fun a => ?_⟩
  rw [LinearMap.sum_apply]
  ext y
  have hterm : ∀ h : Gf, (rRep k Gf h (e1 (rRep k Gf h⁻¹ a))).coeff y =
      if h⁻¹ = y then a.coeff h⁻¹ else 0 := fun h => by
    simp only [rRep_apply, e1_apply, inv_inv, coeff_mul_single_apply, one_mul, mul_one, single_mul_single,
      coeff_single, Finsupp.single_apply]
  have h0 : ∀ h ∈ (Finset.univ : Finset Gf), h ≠ y⁻¹ → (rRep k Gf h (e1 (rRep k Gf h⁻¹ a))).coeff y = 0 :=
    fun h _ hh => by rw [hterm, if_neg fun h' => hh (by rw [← h', inv_inv])]
  simp only [LinearMap.comp_apply, LinearMap.id_apply, coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single y⁻¹ h0 (fun hh => absurd (Finset.mem_univ _) hh), hterm, inv_inv, if_pos rfl]

variable {M : Type} [AddCommGroup M] [Module k M] (τ : Representation k Gf M)

theorem coinvA_mk_tmul (a : MonoidAlgebra k Gf) (m : M) :
    coinvA τ (Coinvariants.mk _ (a ⊗ₜ m)) = τ.asAlgebraHom a m := rfl

end Right

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_Alg =====
section

/-!
# S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free

`π : G →* Gf` (open kernel, `Gf` finite), `A = Λ[Gf]` (`MonoidAlgebra`) with `G` acting by left multiplication
through `π` (`regRep`), `E = Z¹(Γ; A)` (locally constant cocycles, `S4-CurveCoh`), and `Gf` acting on `E` by right
multiplication by `h⁻¹` on values (`eRep`; the convention of the `S4-HattoriStallings` coinvariants
`(E ⊗ M)_{Gf} = Coinvariants (tprod eRep τ)`).

* `lift_of_values`: under `H2All`, a cocycle with values in a subrepresentation `W` lifts along any equivariant `q`
  onto `W`;
* `free_E`: over a local `Λ` with `𝔪 = (ϖ)`, `ϖⁿ = 0`, `ϖᵐ ≠ 0` (`m < n`), `E` is free (if finite), via
  `free_of_torsion` and the lift along `ϖ • : A → ϖA`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra IsLocalRing

noncomputable section

section Regular

variable (Λ : Type) [CommRing Λ] (Gf : Type) [Group Gf]

end Regular

section Lift

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G)

end Lift

section Cocycles

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

/-- The subrepresentation `ϖ • A`. -/
def smulRep (ϖ : Λ) : Subrepresentation (regRep Λ π) where
  toSubmodule := LinearMap.range (LinearMap.lsmul Λ (MonoidAlgebra Λ Gf) ϖ)
  apply_mem_toSubmodule g v hv := by
    obtain ⟨b, rfl⟩ := hv
    exact ⟨regRep Λ π g b, by simp⟩

theorem coe_smul_Z1 (r : Λ) (c : Z1 (regRep Λ π) Γ) (g : Γ) :
    ((r • c : Z1 (regRep Λ π) Γ) : Γ → MonoidAlgebra Λ Gf) g = r • (c : Γ → MonoidAlgebra Λ Gf) g := rfl

/-- **E2(a)**: `E = Z¹(Γ; Λ[Gf])` is `Λ`-free (given `H² = 0` and finiteness of `E`). -/
theorem free_E [IsLocalRing Λ] [Finite Λ] [Finite Gf] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) {n : ℕ}
    (hn : ϖ ^ n = 0) (hn' : ∀ m < n, ϖ ^ m ≠ 0) {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G)) [Module.Finite Λ (Z1 (regRep Λ π) Γ)] :
    Module.Free Λ (Z1 (regRep Λ π) Γ) := by
  haveI := finite_A Λ Gf
  refine free_of_torsion hϖ hn fun m hm z hz => ?_
  have hzv : ∀ g, (z : Γ → MonoidAlgebra Λ Gf) g ∈ (smulRep π ϖ).toSubmodule := fun g => by
    have h1 : ϖ ^ m • (z : Γ → MonoidAlgebra Λ Gf) g = 0 := by
      rw [← coe_smul_Z1, hz]
      rfl
    obtain ⟨b, hb⟩ := exists_smul_of_pow_smul hϖ (hn' m hm) _ h1
    exact ⟨b, by simp [hb]⟩
  obtain ⟨c, hc⟩ := lift_of_values (regRep Λ π) (regRep Λ π) Γ hall (nsmul_eq_zero_of_cast hΛ)
    (isOpen_regRep_ker π hπ) (LinearMap.lsmul Λ (MonoidAlgebra Λ Gf) ϖ) (fun g a => by simp)
    (smulRep π ϖ) (fun a => ⟨a, rfl⟩) (fun w hw => hw) z hzv
  refine ⟨c, Subtype.ext (funext fun g => ?_)⟩
  rw [coe_smul_Z1, ← hc g]
  rfl

end Cocycles

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_Cx =====
section

/-!
# S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model

For a representation `ρ` of `G` with open kernel, `Γ ≤ G` and boundary subgroups `I : S → Subgroup G`, the cone
complex `K(M) : M → Z¹(Γ; M) × (S → M) → Π_s Z¹(Γ ⊓ I s; M)` (`cx0`, `cx1`; `cx1_comp_cx0`), natural in the
coefficients (`cx0_natural`, `cx1_natural`). At `ρ = regRep Λ π` (`A = Λ[Gf]`) the right `Gf`-actions are the
naturality maps of right multiplication, so `d0 = cx0`, `d1 = cx1` are `Gf`-equivariant (`d0_equiv`, `d1_equiv`) and
the terms `A`, `E_Γ × A^S`, `Π_s E_s` are projective once the `E`'s are (`isProj_rho1`, `isProj_rho2`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings

noncomputable section

section Generic

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

variable (hρ : IsOpen (ρ.ker : Set G)) (hσ : IsOpen (σ.ker : Set G))

variable (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m))

end Generic

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))

theorem isProj_rho1 [Fintype Gf] (hE : IsProj (eRep (Λ := Λ) π Γ)) :
    IsProj (rho1 Λ π Γ S) :=
  isProj_prod hE (isProj_pi fun _ => isProj_rRep)

theorem isProj_rho2 [Fintype Gf] (hE : ∀ s, IsProj (eRep (Λ := Λ) π (Γ ⊓ I s))) : IsProj (rho2 Λ π Γ I) :=
  isProj_pi hE

end Model

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_HattoriStallings_SES =====
section

/-!
# Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules

* `avg ρ σ f = ∑_g σ g ∘ f ∘ ρ g⁻¹` is always equivariant; `IsHigman ρ E ↔ avg ρ ρ E = id`.
* `exists_equivariant_lift`: a projective (Higman) representation lifts equivariantly along
  equivariant surjections.
* `exists_equivariant_splitting`: a short exact sequence with projective quotient splits equivariantly.
* `hs_ses`: additivity of the HS trace on short exact sequences (and the sub is projective).
* `isHigman_of_basis`, `isProj_permRep`: permutation modules of free `G`-sets are projective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap

section Avg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {T : Type*} [AddCommGroup T] [Module R T]
variable {ρ : Representation R G P} {σ : Representation R G Q} {τ : Representation R G T}

lemma isHigman_iff_avg (E : P →ₗ[R] P) : IsHigman ρ E ↔ avg ρ ρ E = LinearMap.id := Iff.rfl

lemma isEquivariant_avg (f : P →ₗ[R] Q) : IsEquivariant ρ σ (avg ρ σ f) := by
  refine isEquivariant_iff.2 fun x v => ?_
  rw [avg_apply, avg_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [rep_apply_apply ρ, rep_apply_apply σ, show x * (x⁻¹ * g) = g by group,
    show (x⁻¹ * g)⁻¹ = g⁻¹ * x by group]

lemma IsEquivariant.avg_comp_right {i : Q →ₗ[R] P} (hi : IsEquivariant σ ρ i) (f : P →ₗ[R] T) :
    avg σ τ (f ∘ₗ i) = avg ρ τ f ∘ₗ i := by
  ext v
  simp [avg_apply, hi.apply]

/-- An equivariant retract of a Higman representation is Higman. -/
theorem IsHigman.retract {E : P →ₗ[R] P} (hE : IsHigman ρ E) {i : Q →ₗ[R] P} {r : P →ₗ[R] Q}
    (hi : IsEquivariant σ ρ i) (hr : IsEquivariant ρ σ r) (hri : r ∘ₗ i = LinearMap.id) :
    IsHigman σ (r ∘ₗ E ∘ₗ i) := by
  refine LinearMap.ext fun v => ?_
  have key := hE.apply (i v)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  calc ∑ h : G, σ h (r (E (i (σ h⁻¹ v)))) = r (∑ h : G, ρ h (E (ρ h⁻¹ (i v)))) := by
        simp [map_sum, hr.apply, hi.apply]
    _ = v := by rw [key]; exact LinearMap.congr_fun hri v

theorem IsProj.retract (hρ : IsProj ρ) {i : Q →ₗ[R] P} {r : P →ₗ[R] Q}
    (hi : IsEquivariant σ ρ i) (hr : IsEquivariant ρ σ r) (hri : r ∘ₗ i = LinearMap.id) :
    IsProj σ :=
  let ⟨_, hE⟩ := hρ
  ⟨_, hE.retract hi hr hri⟩

end Avg

section SES

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P' : Type*} [AddCommGroup P'] [Module R P'] {P : Type*} [AddCommGroup P] [Module R P]
variable {P'' : Type*} [AddCommGroup P''] [Module R P'']
variable {ρ' : Representation R G P'} {ρ : Representation R G P} {ρ'' : Representation R G P''}

variable [Module.Free R P'] [Module.Finite R P'] [Module.Free R P] [Module.Finite R P]
  [Module.Free R P''] [Module.Finite R P'']

end SES

section Perm

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

open Classical in
/-- Higman datum of a module with a basis permuted by `G` with free orbits and a transversal `S`. -/
theorem isHigman_of_basis {ι : Type*} [MulAction G ι] (b : Module.Basis ι R P)
    (hb : ∀ (g : G) (i : ι), ρ g (b i) = b (g • i)) (S : Set ι)
    (hS : ∀ i, ∃! g : G, g⁻¹ • i ∈ S) :
    IsHigman ρ (b.constr R (fun i => if i ∈ S then b i else 0)) := by
  refine b.ext fun i => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  simp_rw [hb, Module.Basis.constr_basis]
  obtain ⟨g, hg, huniq⟩ := hS i
  rw [Finset.sum_eq_single g]
  · rw [if_pos hg, hb, smul_inv_smul]
  · intro h _ hne
    rw [if_neg (fun hh => hne (huniq h hh)), map_zero]
  · simp

/-- **The permutation module of a finite free `G`-set is projective over `R[G]`.** -/
theorem isProj_permRep {X : Type*} [Finite X] [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) : IsProj (permRep R G X) := by
  classical
  let rep : X → X := fun x => (Quotient.mk'' x : Quotient (MulAction.orbitRel G X)).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x =>
    MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out' x))
  have hrep_smul : ∀ (g : G) (x : X), rep (g • x) = rep x := fun g x =>
    congrArg Quotient.out
      (Quotient.sound' (MulAction.orbitRel_apply.2 (MulAction.mem_orbit x g)) :
        (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' x)
  let S : Set X := {x | rep x = x}
  refine ⟨_, isHigman_of_basis (Pi.basisFun R X) (fun g x => ?_) S fun x => ?_⟩
  · simp [Pi.basisFun_apply, permRep_single]
  · obtain ⟨g, hg⟩ := hrep x
    refine ⟨g⁻¹, ?_, ?_⟩
    · show rep ((g⁻¹)⁻¹ • x) = (g⁻¹)⁻¹ • x
      rw [inv_inv, hrep_smul]
      exact hg.symm
    · intro h hh
      have hh' : rep (h⁻¹ • x) = h⁻¹ • x := hh
      have e2 : h⁻¹ • x = g • x := by rw [← hh', hrep_smul, hg]
      have e3 : (g⁻¹ * h⁻¹) • x = x := by rw [mul_smul, e2, inv_smul_smul]
      have h4 := mul_eq_one_iff_eq_inv.1 (hfree _ _ e3)
      rw [inv_inv] at h4
      exact h4.symm

end Perm

end RamanujanPetersson.HattoriStallings


end

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

/-- `Tr_R (ρ γ⁻¹ ∘ φ) = |Z(γ)| · hs φ [γ]`. -/
theorem trace_inv_comp_eq_card_mul_hs (hρ : IsProj ρ) {φ : P →ₗ[R] P}
    (hφ : IsEquivariant ρ ρ φ) (γ : G) :
    trace R P (ρ γ⁻¹ ∘ₗ φ) =
      (Nat.card {z : G // z⁻¹ * γ * z = γ} : R) * hs ρ φ (ConjClasses.mk γ) := by
  obtain ⟨E, hE⟩ := hρ
  rw [trace_inv_comp_eq_sum hE hφ, hs_eq hE hφ, sum_conj_eq_card_mul_classSum]

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

variable [AddCommGroup V0] [AddCommGroup V1] [AddCommGroup V2]

variable {R : Type} [CommRing R] [Module R V0] [Module R V1] [Module R V2]

variable {G : Type} [Group G] {V0 V1 V2}

variable (ρ0 : Representation R G V0) (ρ1 : Representation R G V1) (ρ2 : Representation R G V2)

variable [Fintype G]

theorem isProj_trivial_punit : IsProj (Representation.trivial R G PUnit) :=
  ⟨0, LinearMap.ext fun _ => Subsingleton.elim _ _⟩

variable {ρ0 ρ1 ρ2} in
theorem isProj_tri (h0 : IsProj ρ0) (h1 : IsProj ρ1) (h2 : IsProj ρ2) : ∀ i, IsProj (triRep ρ0 ρ1 ρ2 i)
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | _ + 3 => isProj_trivial_punit

end Tri

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

theorem conjSub_val (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (g : Δ) :
    (conjSub x hx g : G) = x⁻¹ * g * x := rfl

end Conj

section Frob

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N)
  (Γ : Subgroup G) [hΓ : Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ)

variable (hρ : IsOpen (ρ.ker : Set G))

/-- Frobenius commutes with `d⁰`. -/
theorem cx0_frob : cx0 ρ Γ S hρ ∘ₗ ρ ψ = frob1 ρ Γ ψ t h ∘ₗ cx0 ρ Γ S hρ :=
  LinearMap.ext fun m => Prod.ext (Subtype.ext (funext fun g => by
    show ρ (g : G) (ρ ψ m) - ρ ψ m = ρ ψ (ρ (conjSub ψ (conj_mem_normal Γ ψ) g : G) m - m)
    rw [map_sub, rho_conjSub])) (funext fun s => by
    show ρ ψ m = ρ ψ (ρ (h s : G) m - (ρ (h s : G) m - m))
    rw [sub_sub_cancel])

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

theorem frob1_equiv : IsEquivariant (rho1 Λ π Γ S) (rho1 Λ π Γ S) (frob1 (regRep Λ π) Γ ψ t h) := fun x =>
  frob1_natural (ρ := regRep Λ π) (σ := regRep Λ π) Γ ψ t h (LinearMap.mulRight Λ (single x⁻¹ 1)) (mulRight_regRep π _)

theorem frob2_equiv (hI : BdryCompat Γ I ψ t h) :
    IsEquivariant (rho2 Λ π Γ I) (rho2 Λ π Γ I) (frob2 (regRep Λ π) Γ I ψ t h hI) := fun x =>
  frob2_natural (ρ := regRep Λ π) (σ := regRep Λ π) Γ I ψ t h hI (LinearMap.mulRight Λ (single x⁻¹ 1)) (mulRight_regRep π _)

end Model

section TriMap

variable {R : Type} [CommRing R] {G : Type} [Group G] {V0 V1 V2 : Type} [AddCommGroup V0] [AddCommGroup V1]
  [AddCommGroup V2] [Module R V0] [Module R V1] [Module R V2]

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

end FixedPoint

section FieldCase

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

-- ===== S4.Def_RP_PerfectCx_Pkg =====
section

/-!
# S4-PD (5), E3: the perfect complex as a Hattori–Stallings package

`PC Λ π Γ I = [A → E_Γ × A^S → Π_s E_s]` (`A = Λ[Gf]`, `E_Δ = Z¹(Δ; A)`) as the `ℕ`-indexed family consumed by
`HattoriStallings.lefschetz`, with its `Gf`-representations `ρPC`, projectivity (`isProj_ρPC`, from a Sylow subgroup:
`isProj_ρPC_of_sylow`), freeness and finiteness (`pc_free_finite`), the identifications `(PC i ⊗ M)_{Gf} ≅ K^i(M)`
(`pcIso0`, `pcIso1`, `pcIso2`) and the twisted trace formula (`lefschetz_PC`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct IsLocalRing LinearMap

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

variable (Λ) in
/-- The perfect complex `P = [A → E_Γ × A^S → Π_s E_s]` as an `ℕ`-indexed family. -/
abbrev PC : ℕ → Type :=
  Tri (MonoidAlgebra Λ Gf) (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf))
    ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s))

variable (Λ) in
/-- The `Gf`-representations on the terms of `PC` (right multiplication on `A`). -/
def ρPC : ∀ i, Representation Λ Gf (PC Λ π Γ I i) :=
  triRep (rRep Λ Gf) (rho1 Λ π Γ S) (rho2 Λ π Γ I)

theorem isProj_ρPC [Fintype Gf] (hE : IsProj (eRep (Λ := Λ) π Γ))
    (hEs : ∀ s, IsProj (eRep (Λ := Λ) π (Γ ⊓ I s))) : ∀ i, IsProj (ρPC Λ π Γ I i) :=
  isProj_tri isProj_rRep (isProj_rho1 π Γ hE) (isProj_rho2 π Γ I hEs)

section Hyps

variable [IsLocalRing Λ] [Finite Λ] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) {n : ℕ}
  (hn : ϖ ^ n = 0) (hn' : ∀ m < n, ϖ ^ m ≠ 0) {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N) (hπ : IsOpen (π.ker : Set G))
  [Module.Finite Λ (Z1 (regRep Λ π) Γ)] [∀ s, Module.Finite Λ (Z1 (regRep Λ π) (Γ ⊓ I s))]

include hϖ hn hn' hΛ hall hallI hπ in
/-- Projectivity of all terms from an `ℓ`-Sylow subgroup `Q` of `Gf` (E2(b), `proj_E`). -/
theorem isProj_ρPC_of_sylow [Fintype Gf] [Fact l.Prime] [CharP (ResidueField Λ) l] (Q : Subgroup Gf) [Fintype Q]
    (hQ : IsPGroup l Q) (hindex : ¬ l ∣ Q.index) : ∀ i, IsProj (ρPC Λ π Γ I i) :=
  isProj_ρPC π Γ I (proj_E π Γ Q hϖ hn hn' hΛ hall hπ hQ hindex)
    (fun s => proj_E π (Γ ⊓ I s) Q hϖ hn hn' hΛ (hallI s) hπ hQ hindex)

include hϖ hn hn' hΛ hall hallI hπ in
/-- All terms of `PC` are free and finite over `Λ` (E2(a), `free_E`). -/
theorem pc_free_finite [Finite Gf] [Finite S] :
    (∀ i, Module.Free Λ (PC Λ π Γ I i)) ∧ ∀ i, Module.Finite Λ (PC Λ π Γ I i) := by
  have : Module.Free Λ (Z1 (regRep Λ π) Γ) := free_E π Γ hϖ hn hn' hΛ hall hπ
  have : ∀ s, Module.Free Λ (Z1 (regRep Λ π) (Γ ⊓ I s)) := fun s =>
    free_E π (Γ ⊓ I s) hϖ hn hn' hΛ (hallI s) hπ
  exact ⟨fun i => inferInstance, fun i => inferInstance⟩

end Hyps

section Iso

variable [Finite Λ] [Finite Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

/-- `(P⁰ ⊗ M)_{Gf} ≃ M`. -/
def pcIso0 : Coinvariants ((ρPC Λ π Γ I 0).tprod τ) ≃ₗ[Λ] M := coinvA τ

/-- `(P¹ ⊗ M)_{Gf} ≃ Z¹(Γ; M) × M^S`. -/
def pcIso1 [Fintype S] [DecidableEq S] :
    Coinvariants ((ρPC Λ π Γ I 1).tprod τ) ≃ₗ[Λ] Z1 (τ.comp π) Γ × (S → M) :=
  iso1 π Γ S hπ τ hΛ hall

/-- `(P² ⊗ M)_{Gf} ≃ Π_s Z¹(Γ ⊓ I s; M)`. -/
def pcIso2 [Fintype S] [DecidableEq S] :
    Coinvariants ((ρPC Λ π Γ I 2).tprod τ) ≃ₗ[Λ] ((s : S) → Z1 (τ.comp π) (Γ ⊓ I s)) :=
  iso2 π Γ I hπ τ hΛ hallI

end Iso

/-- **Twisted trace formula for the perfect complex** (SGA 4½, *Rapport*): for a free finite `Λ`-module `M` with a
`Gf`-action `τ`, an equivariant endomorphism `φ` of `PC` and an equivariant endomorphism `ψ` of `M`,
`Σ (-1)^i Tr(φ i ⊗ ψ | (PC i ⊗ M)_{Gf}) = Σ_c L(φ)[c] · Tr(c⁻¹ ∘ ψ | M)`. -/
theorem lefschetz_PC [IsLocalRing Λ] [Fintype Gf] [Fintype (ConjClasses Gf)]
    [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC Λ π Γ I i)) {M : Type} [AddCommGroup M] [Module Λ M] [Module.Free Λ M]
    [Module.Finite Λ M] {τ : Representation Λ Gf M} {φ : ∀ i, PC Λ π Γ I i →ₗ[Λ] PC Λ π Γ I i}
    (hφ : ∀ i, IsEquivariant (ρPC Λ π Γ I i) (ρPC Λ π Γ I i) (φ i)) {ψ : M →ₗ[Λ] M}
    (hψ : IsEquivariant τ τ ψ) :
    trace Λ _ (coinvMap ((ρPC Λ π Γ I 0).tprod τ) (TensorProduct.map (φ 0) ψ) (isEquivariant_tensorMap (hφ 0) hψ)) -
      trace Λ _ (coinvMap ((ρPC Λ π Γ I 1).tprod τ) (TensorProduct.map (φ 1) ψ)
        (isEquivariant_tensorMap (hφ 1) hψ)) +
      trace Λ _ (coinvMap ((ρPC Λ π Γ I 2).tprod τ) (TensorProduct.map (φ 2) ψ)
        (isEquivariant_tensorMap (hφ 2) hψ)) =
      ∑ c : ConjClasses Gf, lefschetz (ρPC Λ π Γ I) 2 φ c * twChar τ ψ c := by
  have h := lefschetz_coinv_of_local hρ hφ hψ 2
  rw [sum_range_three_alt] at h
  exact h

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_CxH =====
section

/-!
# S4-PD (5), E3: the cohomology of the cone complex

For the cone complex `K(M) : M → Z¹(Γ; M) × M^S → Π_s Z¹(Γ ⊓ I s; M)` (`cx0`, `cx1`):
* `H⁰(K) = 0` when `S` is nonempty (`cx0_injective`, `ker_cx0`);
* `ker d¹ ≃ Z1c` (`kerEquivZ1c`), carrying `im d⁰` onto `B1c` (`map_range_cx0`), hence
  `im d⁰ = B1c` inside `Z1c` (`cx0c`, `range_cx0c`), so `H¹(K) ≃ H1c ρ Γ I` (`h1Equiv`), the compactly supported `H¹` of S4-CurveCoh;
* `H²(K) := coker d¹` (`H2K`), identified with the cone `H²` in E4.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) {S : Type}
  (I : S → Subgroup G) (hρ : IsOpen (ρ.ker : Set G))

variable (S) in
/-- `H⁰(K(M)) = 0` for nonempty `S`: `d⁰` is injective. -/
theorem cx0_injective [Nonempty S] : Function.Injective (cx0 ρ Γ S hρ) := fun _ _ h =>
  congrArg (fun p : Z1 ρ Γ × (S → M) => p.2 (Classical.arbitrary S)) h

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_FrobIso =====
section

/-!
# S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula

The cone Frobenius (`frob1`, `frob2` of `Def_RP_PerfectCx_Frob`) preserves `ker d¹` (`frobKer`), where it is the
`twistc` operator of `CurveCoh_Pair` (`kerEquivZ1c_frobKer`), so it induces `frobH1c` on `H¹_c` (`frobH1c_kerEquiv`);
it also induces `frobH2K` on `H²(K) = coker d¹`. On the perfect complex `PC` the Frobenius `frobPC` is
`Gf`-equivariant (`frobPC_equiv`) and the identifications `(PC i ⊗ M)_{Gf} ≅ K^i(M)` carry `frobPC i ⊗ id` to the
cone Frobenius with coefficients `τ ∘ π` (`pcIso0_frob`, `pcIso1_frob`, `pcIso2_frob`). Hence (`lefschetz_frob`)
`Tr(F | M) - Tr(F | K¹(M)) + Tr(F | K²(M)) = Σ_c L(frobPC)[c] · Tr(τ(c)⁻¹ | M)` (SGA 4½, *Rapport*).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct

noncomputable section

section H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) [Γ.Normal] {S : Type}
  (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ) (hρ : IsOpen (ρ.ker : Set G))

end H

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

variable (Λ) in
/-- The Frobenius endomorphism of the perfect complex `PC`. -/
def frobPC : ∀ i, PC Λ π Γ I i →ₗ[Λ] PC Λ π Γ I i :=
  triMap (regRep Λ π ψ) (frob1 (regRep Λ π) Γ ψ t h) (frob2 (regRep Λ π) Γ I ψ t h hI)

theorem frobPC_equiv : ∀ i, IsEquivariant (ρPC Λ π Γ I i) (ρPC Λ π Γ I i) (frobPC Λ π Γ I ψ t h hI i) :=
  triMap_equiv (show IsEquivariant (rRep Λ Gf) (rRep Λ Gf) (regRep Λ π ψ) from
      fun x => LinearMap.ext fun a => (mulRight_regRep π (single x⁻¹ 1) ψ a).symm)
    (frob1_equiv (Λ := Λ) (π := π) (Γ := Γ) (ψ := ψ) (t := t) (h := h))
    (frob2_equiv (Λ := Λ) (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) hI)

variable [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

theorem coinvA_frob_mk (a : MonoidAlgebra Λ Gf) (m : M) :
    coinvA τ (Coinvariants.mk _ (regRep Λ π ψ a ⊗ₜ m)) = τ (π ψ) (coinvA τ (Coinvariants.mk _ (a ⊗ₜ m))) := by
  rw [coinvA_mk_tmul, coinvA_mk_tmul, regRep_apply, act_single_mul]

theorem iso1_frob_mk [Fintype S] [DecidableEq S] (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (m : M) :
    iso1 π Γ S hπ τ hΛ hall (Coinvariants.mk _ (frob1 (regRep Λ π) Γ ψ t h p ⊗ₜ m)) =
      frob1 (τ.comp π) Γ ψ t h (iso1 π Γ S hπ τ hΛ hall (Coinvariants.mk _ (p ⊗ₜ m))) := by
  refine Prod.ext (Subtype.ext (funext fun g => ?_)) (funext fun s => ?_)
  · simp only [iso1_mk_tmul, frob1_fst, conjMap_apply, Phi_mk_tmul, regRep_apply, act_single_mul,
      MonoidHom.comp_apply]
  · simp only [iso1_mk_tmul, frob1_snd, Phi_mk_tmul, regRep_apply, act_single_mul, map_sub, LinearMap.sub_apply,
      MonoidHom.comp_apply]

/-- Degree 0: `(P⁰ ⊗ M)_{Gf} ≃ M` carries `frobPC 0 ⊗ id` to `τ (π ψ)`. -/
theorem pcIso0_frob (u : Coinvariants ((ρPC Λ π Γ I 0).tprod τ)) :
    pcIso0 π Γ I τ (coinvMap ((ρPC Λ π Γ I 0).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 0) LinearMap.id)
      (isEquivariant_tensorMap (frobPC_equiv π Γ I ψ t h hI 0) (isEquivariant_id (ρ := τ))) u) =
      τ (π ψ) (pcIso0 π Γ I τ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m =>
    rw [coinvMap_mk, TensorProduct.map_tmul, LinearMap.id_apply]
    exact coinvA_frob_mk (π := π) (ψ := ψ) τ a m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Degree 1: `(P¹ ⊗ M)_{Gf} ≃ Z¹(Γ; M) × M^S` carries `frobPC 1 ⊗ id` to `frob1`. -/
theorem pcIso1_frob [Fintype S] [DecidableEq S] (u : Coinvariants ((ρPC Λ π Γ I 1).tprod τ)) :
    pcIso1 π Γ I τ hΛ hall hπ (coinvMap ((ρPC Λ π Γ I 1).tprod τ)
      (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 1) LinearMap.id)
      (isEquivariant_tensorMap (frobPC_equiv π Γ I ψ t h hI 1) (isEquivariant_id (ρ := τ))) u) =
      frob1 (τ.comp π) Γ ψ t h (pcIso1 π Γ I τ hΛ hall hπ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    rw [coinvMap_mk, TensorProduct.map_tmul, LinearMap.id_apply]
    exact iso1_frob_mk (π := π) (Γ := Γ) (ψ := ψ) (t := t) (h := h) (τ := τ) (hΛ := hΛ) (hall := hall)
      (hπ := hπ) p m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Degree 2: `(P² ⊗ M)_{Gf} ≃ Π_s Z¹(Γ ⊓ I s; M)` carries `frobPC 2 ⊗ id` to `frob2`. -/
theorem pcIso2_frob [Fintype S] [DecidableEq S] (u : Coinvariants ((ρPC Λ π Γ I 2).tprod τ)) :
    pcIso2 π Γ I τ hΛ hallI hπ (coinvMap ((ρPC Λ π Γ I 2).tprod τ)
      (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 2) LinearMap.id)
      (isEquivariant_tensorMap (frobPC_equiv π Γ I ψ t h hI 2) (isEquivariant_id (ρ := τ))) u) =
      frob2 (τ.comp π) Γ I ψ t h hI (pcIso2 π Γ I τ hΛ hallI hπ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    rw [coinvMap_mk, TensorProduct.map_tmul, LinearMap.id_apply]
    exact iso2_frob_mk (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hI := hI) (τ := τ) (hΛ := hΛ)
      (hallI := hallI) (hπ := hπ) p m
  | add x y hx hy => simp only [map_add, hx, hy]

end Model

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ConeMapG =====
section

/-!
# S4-Lefschetz, L3c: cone maps for coefficient maps that are only `Γ`-equivariant, across ambients

Two ambients `A`, `B` (topological groups), `Γ ≤ A`, `Γ' ≤ B`, boundary subgroups `I`, `I'`, and continuous homs
`φ : Γ' → Γ`, `φs s : Γ' ⊓ I' s → Γ ⊓ I s`. A linear map `q : M → N` with `q (ρ (φ x) m) = σ x (q m)` induces
* `zPull`: `Z¹(Γ; M) → Z¹(Γ'; N)`, `c ↦ q ∘ c ∘ φ`; `K1pull`, `K2pull` on the cone terms;
* `cx0_pull`, `cx1_pull`: naturality with the cone differentials;
* `frob0_pull`, `frob1_pull`, `frob2_pull`: `Q ∘ (f ∘ Frob_ψ) = (f' ∘ Frob_ψ') ∘ Q'` when
  `q ∘ f ∘ ρ ψ = f' ∘ σ ψ' ∘ q'` on coefficients (and `φ` matches the conjugations and correcting elements);
* `zPull_comp` (rfl), `zPull_eq_id`, `zPull_sum` and the `K1`/`K2` versions, for block idempotents.
Same-ambient use: `A = B`, `φ = id` (block idempotents `e_ω`, only `Γ`-equivariant).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

section Pull

variable {k : Type} [CommRing k] {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k A M) (σ : Representation k B N)

variable {Γ : Subgroup A} {Γ' : Subgroup B} {S : Type} (I : S → Subgroup A) (I' : S → Subgroup B)
  (φ : Γ' →* Γ) (hφ : Continuous φ)
  (φs : ∀ s, ↥(Γ' ⊓ I' s) →* ↥(Γ ⊓ I s)) (hφs : ∀ s, Continuous (φs s))

variable (q : M →ₗ[k] N) (hq : ∀ (x : Γ') (m : M), q (ρ (φ x : A) m) = σ (x : B) (q m))
  (hqs : ∀ s (x : ↥(Γ' ⊓ I' s)) (m : M), q (ρ (φs s x : A) m) = σ (x : B) (q m))

theorem cx1_pull (hρ : IsOpen (ρ.ker : Set A)) (hσ : IsOpen (σ.ker : Set B))
    (hφsc : ∀ s (x : ↥(Γ' ⊓ I' s)), (φs s x : A) = (φ ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩ : A)) :
    cx1 σ Γ' I' hσ ∘ₗ K1pull ρ σ φ hφ q hq = K2pull ρ σ I I' φs hφs q hqs ∘ₗ cx1 ρ Γ I hρ :=
  LinearMap.ext fun p => funext fun s => Subtype.ext (funext fun x => by
    have e : (⟨(φs s x : A), (Subgroup.mem_inf.1 (φs s x).2).1⟩ : Γ) = φ ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩ :=
      Subtype.ext (hφsc s x)
    show q ((p.1 : Γ → M) (φ ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩)) - (σ (x : B) (q (p.2 s)) - q (p.2 s)) =
      q ((p.1 : Γ → M) ⟨(φs s x : A), (Subgroup.mem_inf.1 (φs s x).2).1⟩ - (ρ (φs s x : A) (p.2 s) - p.2 s))
    rw [e, map_sub, map_sub, hqs])

variable (f : M →ₗ[k] M) (hf : ∀ (g : A) (m : M), f (ρ g m) = ρ g (f m))
  (f' : N →ₗ[k] N) (hf' : ∀ (g : B) (n : N), f' (σ g n) = σ g (f' n))
  (q' : M →ₗ[k] N) (hq' : ∀ (x : Γ') (m : M), q' (ρ (φ x : A) m) = σ (x : B) (q' m))
  (hqs' : ∀ s (x : ↥(Γ' ⊓ I' s)) (m : M), q' (ρ (φs s x : A) m) = σ (x : B) (q' m))
  (ψ : A) (ψ' : B) (t : S → S) (h : S → Γ) (h' : S → Γ')

theorem frob1_pull [Γ.Normal] [Γ'.Normal]
    (hconj : ∀ x : Γ', (φ (conjSub ψ' (conj_mem_normal Γ' ψ') x) : A) = ψ⁻¹ * (φ x : A) * ψ)
    (hh : ∀ s, φ (h' s) = h s) (hop : ∀ m, q (f (ρ ψ m)) = f' (σ ψ' (q' m))) :
    K1pull ρ σ φ hφ q hq ∘ₗ (K1map ρ ρ Γ f hf ∘ₗ frob1 ρ Γ ψ t h) =
      (K1map σ σ Γ' f' hf' ∘ₗ frob1 σ Γ' ψ' t h') ∘ₗ K1pull ρ σ φ hφ q' hq' :=
  LinearMap.ext fun p => Prod.ext (Subtype.ext (funext fun x => by
    have e : conjSub ψ (conj_mem_normal Γ ψ) (φ x) = φ (conjSub ψ' (conj_mem_normal Γ' ψ') x) :=
      Subtype.ext (by rw [conjSub_val, hconj])
    show q (f (ρ ψ ((p.1 : Γ → M) (conjSub ψ (conj_mem_normal Γ ψ) (φ x))))) =
      f' (σ ψ' (q' ((p.1 : Γ → M) (φ (conjSub ψ' (conj_mem_normal Γ' ψ') x)))))
    rw [e, hop])) (funext fun s => by
    have e : (h s : A) = (φ (h' s) : A) := by rw [hh]
    show q (f (ρ ψ (ρ (h s : A) (p.2 (t s)) - (p.1 : Γ → M) (h s)))) =
      f' (σ ψ' (σ (h' s : B) (q' (p.2 (t s))) - q' ((p.1 : Γ → M) (φ (h' s)))))
    rw [hop]
    simp only [map_sub]
    rw [e, hq', hh])

include hq' in
theorem frob2_pull [Γ.Normal] [Γ'.Normal] (hI : BdryCompat Γ I ψ t h) (hI' : BdryCompat Γ' I' ψ' t h')
    (hconj2 : ∀ s (x : ↥(Γ' ⊓ I' s)),
      (φs (t s) (conjSub (ψ' * h' s) (bdry_mem Γ' I' ψ' t h' hI' s) x) : A) =
        (ψ * h s)⁻¹ * (φs s x : A) * (ψ * h s))
    (hh : ∀ s, φ (h' s) = h s) (hop : ∀ m, q (f (ρ ψ m)) = f' (σ ψ' (q' m))) :
    K2pull ρ σ I I' φs hφs q hqs ∘ₗ (K2map ρ ρ Γ I f hf ∘ₗ frob2 ρ Γ I ψ t h hI) =
      (K2map σ σ Γ' I' f' hf' ∘ₗ frob2 σ Γ' I' ψ' t h' hI') ∘ₗ K2pull ρ σ I I' φs hφs q' hqs' :=
  LinearMap.ext fun e => funext fun s => Subtype.ext (funext fun x => by
    have e1 : conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (φs s x) =
        φs (t s) (conjSub (ψ' * h' s) (bdry_mem Γ' I' ψ' t h' hI' s) x) :=
      Subtype.ext (by rw [conjSub_val, hconj2])
    have e2 : (h s : A) = (φ (h' s) : A) := by rw [hh]
    show q (f (ρ (ψ * h s) ((e (t s) : ↥(Γ ⊓ I (t s)) → M)
        (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (φs s x))))) =
      f' (σ (ψ' * h' s) (q' ((e (t s) : ↥(Γ ⊓ I (t s)) → M)
        (φs (t s) (conjSub (ψ' * h' s) (bdry_mem Γ' I' ψ' t h' hI' s) x)))))
    rw [e1]
    simp only [map_mul, Module.End.mul_apply]
    rw [hop, e2, hq'])

end Pull

section Ids

variable {k : Type} [CommRing k] {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  {C : Type} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  {P : Type} [AddCommGroup P] [Module k P]
  (ρ : Representation k A M) (σ : Representation k B N) (τ : Representation k C P)

end Ids

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockTr =====
section

/-!
# S4-Lefschetz, L3b: traces over a block decomposition

Pure linear algebra over a commutative ring `R`, on a free finite module `V`.
* `trace_eq_sum_blocks`: for a family of endomorphisms `P ω` summing to `1`, `tr f = Σ_ω tr (P ω * f)`;
* `trace_block_eq_zero`: if the `P ω` are orthogonal idempotents and `f` moves block `ω` to block `s ω`
  (`P (s ω) * f = f * P ω`), then a block that is not fixed by `s` contributes `0`;
* `trace_eq_sum_fixed` (headline): `tr f = Σ_{ω, s ω = ω} tr (P ω * f)`;
* `trace_transfer`: if `q : V → W`, `j : W → V` with `q ∘ j = id` and `q ∘ op = g ∘ q`, then
  `tr (j ∘ q ∘ op) = tr g`; `trace_block_transfer` is the same with `P ω = j ∘ q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

section BlockTr

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {W : Type*} [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

/-- Trace transfer through a retraction: `q ∘ j = id`, `q ∘ op = g ∘ q`. -/
theorem trace_transfer (q : V →ₗ[R] W) (j : W →ₗ[R] V) (hqj : q ∘ₗ j = LinearMap.id)
    (op : Module.End R V) (g : Module.End R W) (hop : q ∘ₗ op = g ∘ₗ q) :
    LinearMap.trace R V (j ∘ₗ q ∘ₗ op) = LinearMap.trace R W g := by
  have h := LinearMap.trace_comp_comm' (R := R) (M := W) (N := V) (f := j) (g := q ∘ₗ op)
  rw [← h, hop, LinearMap.comp_assoc, hqj, LinearMap.comp_id]

theorem trace_block_transfer (P : Module.End R V) (q : V →ₗ[R] W) (j : W →ₗ[R] V)
    (hP : P = j ∘ₗ q) (hqj : q ∘ₗ j = LinearMap.id)
    (op : Module.End R V) (g : Module.End R W) (hop : q ∘ₗ op = g ∘ₗ q) :
    LinearMap.trace R V (P * op) = LinearMap.trace R W g := by
  rw [hP, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  exact trace_transfer q j hqj op g hop

end BlockTr

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockAlg =====
section

/-!
# S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`

Pure algebra. For a subgroup `P` of a group `Gf`, the blocks are the right cosets `P x`
(`Blk P`, the quotient by `QuotientGroup.rightRel P`), and `eB P ω` is the coefficient projection of
`Λ[Gf]` onto the block `ω`.
* `sum_eB`, `eB_mul`: the `eB P ω` are orthogonal idempotents summing to `1`;
* `eB_left`: left multiplication by `single p 1`, `p ∈ P`, commutes with every `eB P ω`;
* `blkShift`, `eB_shift`: for `u` normalizing `P`, `F ↦ single u 1 * F * single v 1` maps block `ω`
  to block `blkShift P u v hu ω` (the block of `u x v`);
* `blkShift_fixed_iff`: the block of `a` is fixed iff `u * a * v * a⁻¹ ∈ P`.
-/

set_option autoImplicit false

universe u

namespace RamanujanPetersson
namespace Lefschetz

open MonoidAlgebra

section BlockAlg

variable {Λ : Type*} [CommRing Λ] {Gf : Type u} [Group Gf] (P : Subgroup Gf)

theorem blk_mul_left {p : Gf} (hp : p ∈ P) (x : Gf) : blk P (p * x) = blk P x := by
  rw [blk_eq_iff, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact P.inv_mem hp

open Classical in
/-- The projection of `Λ[Gf]` onto the coefficients in block `ω`. -/
noncomputable def eB (ω : Blk P) : MonoidAlgebra Λ Gf →ₗ[Λ] MonoidAlgebra Λ Gf where
  toFun F := ofCoeff (F.coeff.filter fun x => blk P x = ω)
  map_add' F F' := by
    show ofCoeff ((F + F').coeff.filter _) = ofCoeff (F.coeff.filter _) + ofCoeff (F'.coeff.filter _)
    rw [coeff_add, Finsupp.filter_add, ofCoeff_add]
  map_smul' c F := by
    show ofCoeff ((c • F).coeff.filter _) = c • ofCoeff (F.coeff.filter _)
    rw [coeff_smul, Finsupp.filter_smul, ofCoeff_smul]

open Classical in
theorem coeff_eB (ω : Blk P) (F : MonoidAlgebra Λ Gf) (x : Gf) :
    (eB P ω F).coeff x = if blk P x = ω then F.coeff x else 0 := rfl

theorem coeff_eB_of_eq {ω : Blk P} {x : Gf} (h : blk P x = ω) (F : MonoidAlgebra Λ Gf) :
    (eB P ω F).coeff x = F.coeff x := by
  rw [coeff_eB, if_pos h]

theorem coeff_eB_of_ne {ω : Blk P} {x : Gf} (h : blk P x ≠ ω) (F : MonoidAlgebra Λ Gf) :
    (eB P ω F).coeff x = 0 := by
  rw [coeff_eB, if_neg h]

theorem sum_eB [Finite Gf] : ∑ ω, (eB P ω : Module.End Λ (MonoidAlgebra Λ Gf)) = 1 := by
  refine LinearMap.ext fun F => MonoidAlgebra.ext (Finsupp.ext fun x => ?_)
  rw [LinearMap.sum_apply, coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single (blk P x) (fun ω _ hω => coeff_eB_of_ne P (Ne.symm hω) F)
      (fun h => absurd (Finset.mem_univ _) h), coeff_eB_of_eq P rfl]
  rfl

theorem eB_mul (ω ω' : Blk P) :
    (eB P ω * eB P ω' : Module.End Λ (MonoidAlgebra Λ Gf)) = if ω = ω' then eB P ω else 0 := by
  refine LinearMap.ext fun F => MonoidAlgebra.ext (Finsupp.ext fun x => ?_)
  rw [Module.End.mul_apply]
  by_cases h : ω = ω'
  · rw [if_pos h, ← h]
    by_cases hx : blk P x = ω
    · rw [coeff_eB_of_eq P hx, coeff_eB_of_eq P hx]
    · rw [coeff_eB_of_ne P hx, coeff_eB_of_ne P hx]
  · rw [if_neg h, LinearMap.zero_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hx : blk P x = ω
    · rw [coeff_eB_of_eq P hx, coeff_eB_of_ne P fun h' => h (hx.symm.trans h')]
    · rw [coeff_eB_of_ne P hx]

theorem eB_single (ω : Blk P) (x : Gf) (r : Λ) :
    eB P ω (single x r) = if blk P x = ω then single x r else 0 := by
  classical
  by_cases h : blk P x = ω
  · rw [if_pos h]
    refine MonoidAlgebra.ext (Finsupp.ext fun y => ?_)
    by_cases hy : blk P y = ω
    · rw [coeff_eB_of_eq P hy]
    · rw [coeff_eB_of_ne P hy, coeff_single, Finsupp.single_apply, if_neg]
      rintro rfl
      exact hy h
  · rw [if_neg h]
    refine MonoidAlgebra.ext (Finsupp.ext fun y => ?_)
    rw [coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hy : blk P y = ω
    · rw [coeff_eB_of_eq P hy, coeff_single, Finsupp.single_apply, if_neg]
      rintro rfl
      exact h hy
    · rw [coeff_eB_of_ne P hy]

theorem eB_left {p : Gf} (hp : p ∈ P) (ω : Blk P) (F : MonoidAlgebra Λ Gf) :
    eB P ω (single p 1 * F) = single p 1 * eB P ω F := by
  refine MonoidAlgebra.ext (Finsupp.ext fun x => ?_)
  have hx : blk P (p⁻¹ * x) = blk P x := blk_mul_left P (P.inv_mem hp) x
  simp only [coeff_eB, coeff_single_mul_apply, one_mul]
  rw [hx]

/-- For `u` normalizing `P`, the permutation of blocks `P x ↦ P (u x v)`. -/
def blkShift (u v : Gf) (hu : u ∈ Subgroup.normalizer (P : Set Gf)) : Blk P ≃ Blk P :=
  Quotient.congr ((Equiv.mulLeft u).trans (Equiv.mulRight v)) fun a b => by
    show QuotientGroup.rightRel P a b ↔ QuotientGroup.rightRel P (u * a * v) (u * b * v)
    have e : u * b * v * (u * a * v)⁻¹ = u * (b * a⁻¹) * u⁻¹ := by group
    have hn := Subgroup.mem_normalizer_iff.1 hu (b * a⁻¹)
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, e]
    exact hn

theorem blkShift_blk (u v : Gf) (hu : u ∈ Subgroup.normalizer (P : Set Gf)) (x : Gf) :
    blkShift P u v hu (blk P x) = blk P (u * x * v) := rfl

theorem blkShift_fixed_iff (u v : Gf) (hu : u ∈ Subgroup.normalizer (P : Set Gf)) (a : Gf) :
    blkShift P u v hu (blk P a) = blk P a ↔ u * a * v * a⁻¹ ∈ P := by
  have e : (a * (u * a * v)⁻¹)⁻¹ = u * a * v * a⁻¹ := by group
  rw [blkShift_blk, blk_eq_iff, ← P.inv_mem_iff (x := a * (u * a * v)⁻¹), e]

theorem eB_shift (u v : Gf) (hu : u ∈ Subgroup.normalizer (P : Set Gf)) (ω : Blk P) (F : MonoidAlgebra Λ Gf) :
    eB P (blkShift P u v hu ω) (single u 1 * F * single v 1) = single u 1 * eB P ω F * single v 1 := by
  refine MonoidAlgebra.ext (Finsupp.ext fun x => ?_)
  have hx : blk P x = blkShift P u v hu (blk P (u⁻¹ * (x * v⁻¹))) := by
    rw [blkShift_blk]
    congr 1
    group
  simp only [coeff_eB, coeff_mul_single_apply, coeff_single_mul_apply, one_mul, mul_one]
  by_cases h : blk P (u⁻¹ * (x * v⁻¹)) = ω
  · rw [if_pos h, if_pos (hx.trans (congrArg (blkShift P u v hu) h))]
  · rw [if_neg h, if_neg fun h' => h ((blkShift P u v hu).injective (hx.symm.trans h'))]

end BlockAlg

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockIso =====
section

/-!
# S4-Lefschetz, L3d2: a block of `Λ[Gf]` as a coinduced module

Generic groups. `π : G →* Gf`, subgroups `Γ ≤ G'` and `H` of `G` with `H ∩ Γ = Γ ∩ ker π` (`hHΓ`) and
`G' = H Γ` (`hcov`: every `y ∈ G'` has some `c ∈ Γ` with `y c⁻¹ ∈ H`). `P := π(Γ)`, block `ω = P a`.
`N = coindV (H.subgroupOf G').subtype σH` for a trivial `σH`: functions `f : G' → Λ` with `f (h y) = f y`.
* `kap π hcov y = π c` for any `c ∈ Γ` with `y c⁻¹ ∈ H` (`kap_eq`), `kap_mul_left`, `kap_mul_right`;
* `qB : Λ[Gf] → N`, `qB F y = F.coeff ((kap y)⁻¹ a)`; `jB : N → Λ[Gf]`;
* `qB_jB : qB (jB f) = f`, `jB_qB : jB (qB F) = eB P (blk P a) F`;
* `qB_left`: `qB (single (π x) 1 * F) = coind x (qB F)` for `x ∈ Γ`;
* `qB_frob`: if `ψ = c0 g` (`c0 ∈ Γ`, `g ∈ H`, `π g = a γ⁻¹ a⁻¹`) then
  `qB (single (π ψ) 1 * F * single γ 1) = coind ψ (qB F)`;
* `map_mem_normalizer`: `π x` normalizes `π(Γ)` for `Γ` normal.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Lefschetz

open MonoidAlgebra Representation

section BlockIso

variable {k : Type*} [CommRing k] {Gf : Type} [Group Gf] {G : Type} [Group G]
  (π : G →* Gf) {Γ H G' : Subgroup G}

theorem map_mem_normalizer [hN : Γ.Normal] (x : G) :
    π x ∈ Subgroup.normalizer ((Γ.map π : Subgroup Gf) : Set Gf) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨x * c * x⁻¹, hN.conj_mem c hc x, by simp⟩
  · rintro ⟨c, hc, hce⟩
    refine ⟨x⁻¹ * c * x, by simpa using hN.conj_mem c hc x⁻¹, ?_⟩
    rw [map_mul, map_mul, hce, map_inv]
    group

/-- The `π`-image of the `Γ`-part of `y ∈ G' = H Γ`. -/
noncomputable def kap (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H) (y : G') : Gf :=
  π (Classical.choose (hcov y y.2))

theorem kap_spec (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H) (y : G') :
    ∃ c ∈ Γ, (y : G) * c⁻¹ ∈ H ∧ kap π hcov y = π c :=
  ⟨_, (Classical.choose_spec (hcov y y.2)).1, (Classical.choose_spec (hcov y y.2)).2, rfl⟩

theorem kap_mem (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H) (y : G') : kap π hcov y ∈ Γ.map π := by
  obtain ⟨c, hc, -, he⟩ := kap_spec π hcov y
  rw [he]
  exact Subgroup.mem_map_of_mem π hc

theorem kap_eq (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H) (y : G')
    {c : G} (hc : c ∈ Γ) (hyc : (y : G) * c⁻¹ ∈ H) : kap π hcov y = π c := by
  obtain ⟨c', hc', hyc', he⟩ := kap_spec π hcov y
  rw [he]
  have h1 : c * c'⁻¹ ∈ H := by
    have h := H.mul_mem (H.inv_mem hyc) hyc'
    have e : ((y : G) * c⁻¹)⁻¹ * ((y : G) * c'⁻¹) = c * c'⁻¹ := by group
    rwa [e] at h
  have h2 := (hHΓ _ (Γ.mul_mem hc (Γ.inv_mem hc'))).1 h1
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2.symm

theorem kap_mul_right (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (y x : G') (hx : (x : G) ∈ Γ) : kap π hcov (y * x) = kap π hcov y * π x := by
  obtain ⟨c, hc, hyc, he⟩ := kap_spec π hcov y
  rw [he, ← map_mul]
  apply kap_eq π hHΓ hcov _ (Γ.mul_mem hc hx)
  have e : ((y * x : G') : G) * (c * x)⁻¹ = (y : G) * c⁻¹ := by
    rw [Subgroup.coe_mul]
    group
  rw [e]
  exact hyc

theorem kap_mul_left (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (h' y : G') (hh : (h' : G) ∈ H) : kap π hcov (h' * y) = kap π hcov y := by
  obtain ⟨c, hc, hyc, he⟩ := kap_spec π hcov y
  rw [he]
  apply kap_eq π hHΓ hcov _ hc
  have e : ((h' * y : G') : G) * c⁻¹ = (h' : G) * ((y : G) * c⁻¹) := by
    rw [Subgroup.coe_mul]
    group
  rw [e]
  exact H.mul_mem hh hyc

variable (σH : Representation k (H.subgroupOf G') k)

theorem coindV_eq (hσ : ∀ h, σH h = 1) (f : coindV (H.subgroupOf G').subtype σH) {y y' : G'}
    (h : (y : G) * (y' : G)⁻¹ ∈ H) : (f : G' → k) y = (f : G' → k) y' := by
  have hm : y * y'⁻¹ ∈ H.subgroupOf G' := Subgroup.mem_subgroupOf.2 (by simpa using h)
  have h1 := (Representation.mem_coindV _ _ _).1 f.2 ⟨_, hm⟩ y'
  rw [hσ, Module.End.one_apply] at h1
  rw [← h1]
  simp

/-- `qB F y = F.coeff ((kap y)⁻¹ a)`: the coordinates of `F` on the block `π(Γ) a`, as a function on `G'`. -/
noncomputable def qB (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (hσ : ∀ h, σH h = 1) (a : Gf) : MonoidAlgebra k Gf →ₗ[k] coindV (H.subgroupOf G').subtype σH where
  toFun F := ⟨fun y => F.coeff ((kap π hcov y)⁻¹ * a), by
    rw [Representation.mem_coindV]
    intro h y
    rw [hσ, Module.End.one_apply]
    show F.coeff ((kap π hcov ((h : G') * y))⁻¹ * a) = F.coeff ((kap π hcov y)⁻¹ * a)
    rw [kap_mul_left π hHΓ hcov (h : G') y (Subgroup.mem_subgroupOf.1 h.2)]⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

theorem qB_apply (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (hσ : ∀ h, σH h = 1) (a : Gf) (F : MonoidAlgebra k Gf) (y : G') :
    (qB π σH hHΓ hcov hσ a F : G' → k) y = F.coeff ((kap π hcov y)⁻¹ * a) := rfl

/-- A point of `Γ` (inside `G'`) over `z ∈ π(Γ)`. -/
noncomputable def yOf (hΓ : Γ ≤ G') {z : Gf} (hz : z ∈ Γ.map π) : G' :=
  ⟨Classical.choose (Subgroup.mem_map.1 hz), hΓ (Classical.choose_spec (Subgroup.mem_map.1 hz)).1⟩

theorem yOf_mem (hΓ : Γ ≤ G') {z : Gf} (hz : z ∈ Γ.map π) : ((yOf π hΓ hz : G') : G) ∈ Γ :=
  (Classical.choose_spec (Subgroup.mem_map.1 hz)).1

theorem yOf_map (hΓ : Γ ≤ G') {z : Gf} (hz : z ∈ Γ.map π) : π ((yOf π hΓ hz : G') : G) = z :=
  (Classical.choose_spec (Subgroup.mem_map.1 hz)).2

open Classical in
/-- The inverse of `qB` on the block `π(Γ) a`: `x ∈ π(Γ) a` gets the value at a point of `Γ` over `a x⁻¹`. -/
noncomputable def jB [Finite Gf] (hΓ : Γ ≤ G') (a : Gf) :
    coindV (H.subgroupOf G').subtype σH →ₗ[k] MonoidAlgebra k Gf where
  toFun f := ofCoeff (Finsupp.equivFunOnFinite.symm fun x =>
    if hx : a * x⁻¹ ∈ Γ.map π then (f : G' → k) (yOf π hΓ hx) else 0)
  map_add' f f' := by
    refine MonoidAlgebra.ext (Finsupp.ext fun x => ?_)
    show (if hx : a * x⁻¹ ∈ Γ.map π then ((f + f' : coindV _ σH) : G' → k) (yOf π hΓ hx) else 0) =
      (if hx : a * x⁻¹ ∈ Γ.map π then (f : G' → k) (yOf π hΓ hx) else 0) +
      (if hx : a * x⁻¹ ∈ Γ.map π then (f' : G' → k) (yOf π hΓ hx) else 0)
    split_ifs <;> simp
  map_smul' c f := by
    refine MonoidAlgebra.ext (Finsupp.ext fun x => ?_)
    show (if hx : a * x⁻¹ ∈ Γ.map π then ((c • f : coindV _ σH) : G' → k) (yOf π hΓ hx) else 0) =
      c • (if hx : a * x⁻¹ ∈ Γ.map π then (f : G' → k) (yOf π hΓ hx) else 0)
    split_ifs <;> simp

open Classical in
theorem coeff_jB [Finite Gf] (hΓ : Γ ≤ G') (a : Gf) (f : coindV (H.subgroupOf G').subtype σH) (x : Gf) :
    (jB π σH hΓ a f).coeff x = if hx : a * x⁻¹ ∈ Γ.map π then (f : G' → k) (yOf π hΓ hx) else 0 := rfl

theorem qB_jB [Finite Gf] (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (hσ : ∀ h, σH h = 1) (hΓ : Γ ≤ G') (a : Gf) (f : coindV (H.subgroupOf G').subtype σH) :
    qB π σH hHΓ hcov hσ a (jB π σH hΓ a f) = f := by
  refine Subtype.ext (funext fun y => ?_)
  show (jB π σH hΓ a f).coeff ((kap π hcov y)⁻¹ * a) = (f : G' → k) y
  have hz : a * ((kap π hcov y)⁻¹ * a)⁻¹ ∈ Γ.map π := by
    rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
    exact kap_mem π hcov y
  rw [coeff_jB, dif_pos hz]
  apply coindV_eq σH hσ f
  obtain ⟨c, hc, hyc, he⟩ := kap_spec π hcov y
  have e1 : π ((yOf π hΓ hz : G') : G) = π c := by
    rw [yOf_map, ← he]
    group
  have h1 : ((yOf π hΓ hz : G') : G) * c⁻¹ ∈ H :=
    (hHΓ _ (Γ.mul_mem (yOf_mem π hΓ hz) (Γ.inv_mem hc))).2 (by rw [map_mul, map_inv, e1, mul_inv_cancel])
  have e2 : ((yOf π hΓ hz : G') : G) * (y : G)⁻¹ =
      (((yOf π hΓ hz : G') : G) * c⁻¹) * ((y : G) * c⁻¹)⁻¹ := by group
  rw [e2]
  exact H.mul_mem h1 (H.inv_mem hyc)

theorem jB_qB [Finite Gf] (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (hσ : ∀ h, σH h = 1) (hΓ : Γ ≤ G') (a : Gf) (F : MonoidAlgebra k Gf) :
    jB π σH hΓ a (qB π σH hHΓ hcov hσ a F) = eB (Γ.map π) (blk (Γ.map π) a) F := by
  refine MonoidAlgebra.ext (Finsupp.ext fun x => ?_)
  rw [coeff_jB]
  by_cases hx : a * x⁻¹ ∈ Γ.map π
  · rw [dif_pos hx, coeff_eB_of_eq _ ((blk_eq_iff _).2 hx)]
    show F.coeff ((kap π hcov (yOf π hΓ hx))⁻¹ * a) = F.coeff x
    rw [kap_eq π hHΓ hcov _ (yOf_mem π hΓ hx) (by rw [mul_inv_cancel]; exact H.one_mem), yOf_map]
    congr 1
    group
  · rw [dif_neg hx, coeff_eB_of_ne _ (fun h => hx ((blk_eq_iff _).1 h))]

theorem qB_left (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (hσ : ∀ h, σH h = 1) (a : Gf) (x : G') (hx : (x : G) ∈ Γ) (F : MonoidAlgebra k Gf) :
    qB π σH hHΓ hcov hσ a (single (π x) 1 * F) =
      coind (H.subgroupOf G').subtype σH x (qB π σH hHΓ hcov hσ a F) := by
  refine Subtype.ext (funext fun y => ?_)
  show (single (π x) 1 * F).coeff ((kap π hcov y)⁻¹ * a) = F.coeff ((kap π hcov (y * x))⁻¹ * a)
  rw [coeff_single_mul_apply, one_mul, kap_mul_right π hHΓ hcov y x hx]
  congr 1
  group

theorem qB_frob [Γ.Normal] (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
    (hσ : ∀ h, σH h = 1) (a : Gf) (ψ : G') {γ : Gf} {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H)
    (hψ : (ψ : G) = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹) (F : MonoidAlgebra k Gf) :
    qB π σH hHΓ hcov hσ a (single (π ψ) 1 * F * single γ 1) =
      coind (H.subgroupOf G').subtype σH ψ (qB π σH hHΓ hcov hσ a F) := by
  refine Subtype.ext (funext fun y => ?_)
  show (single (π ψ) 1 * F * single γ 1).coeff ((kap π hcov y)⁻¹ * a) =
    F.coeff ((kap π hcov (y * ψ))⁻¹ * a)
  obtain ⟨c, hc, hyc, he⟩ := kap_spec π hcov y
  have hk : kap π hcov (y * ψ) = π (g⁻¹ * (c * c0) * g) := by
    apply kap_eq π hHΓ hcov _ (by simpa using ‹Γ.Normal›.conj_mem _ (Γ.mul_mem hc hc0) g⁻¹)
    have e : ((y * ψ : G') : G) * (g⁻¹ * (c * c0) * g)⁻¹ = ((y : G) * c⁻¹) * g := by
      rw [Subgroup.coe_mul, hψ]
      group
    rw [e]
    exact H.mul_mem hyc hg
  rw [coeff_mul_single_apply, coeff_single_mul_apply, one_mul, mul_one, hk, he, hψ]
  congr 1
  simp only [map_mul, map_inv, hπg]
  group

end BlockIso

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockCone1 =====
section

/-!
# S4-Lefschetz, L3e1a: the block decomposition of the perfect complex

`P := π(Γ)`, blocks `ω ∈ Blk P` (right cosets `P a`). The block projections `eB P ω` of `Λ[Gf]` are only
`Γ`-equivariant, so they act on the cone terms through `K1pull`/`K2pull` with `φ = id` (`K1self`, `K2self`); `PB ω`
is the resulting termwise endomorphism of `PC`.
* `PB_sum`, `PB_mul`: a complete family of orthogonal idempotents;
* `PB_op`: `op = ρPC γ⁻¹ ∘ frobPC ψ` carries block `ω` to `π(ψ) ω γ` (`blkShift`);
* headline `trace_op_eq_sum_fixed`: `Tr(op | PC^i) = Σ_{ω fixed} Tr(PB ω ∘ op | PC^i)`;
* `jB_left`: `jB` is `Γ`-equivariant (complements `qB_left` of `Def_RP_Lefschetz_BlockIso`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx MonoidAlgebra Representation

section JB

variable {k : Type*} [CommRing k] {Gf : Type} [Group Gf] {G : Type} [Group G]
  (π : G →* Gf) {Γ H G' : Subgroup G} (σH : Representation k (H.subgroupOf G') k)

theorem jB_left [Finite Gf] (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hσ : ∀ h, σH h = 1) (hΓ : Γ ≤ G') (a : Gf)
    (x : G') (hx : (x : G) ∈ Γ) (f : coindV (H.subgroupOf G').subtype σH) :
    jB π σH hΓ a (coind (H.subgroupOf G').subtype σH x f) = single (π x) 1 * jB π σH hΓ a f := by
  have hpx : π (x : G) ∈ Γ.map π := Subgroup.mem_map_of_mem π hx
  have e : ∀ z : Gf, a * ((π (x : G))⁻¹ * z)⁻¹ = a * z⁻¹ * π (x : G) := fun z => by group
  refine MonoidAlgebra.ext (Finsupp.ext fun z => ?_)
  rw [coeff_single_mul_apply, one_mul, coeff_jB, coeff_jB]
  by_cases hz : a * z⁻¹ ∈ Γ.map π
  · have hz' : a * ((π (x : G))⁻¹ * z)⁻¹ ∈ Γ.map π := by
      rw [e]
      exact (Γ.map π).mul_mem hz hpx
    rw [dif_pos hz, dif_pos hz']
    show (f : G' → k) (yOf π hΓ hz * x) = (f : G' → k) (yOf π hΓ hz')
    apply coindV_eq σH hσ f
    rw [Subgroup.coe_mul]
    refine (hHΓ _ (Γ.mul_mem (Γ.mul_mem (yOf_mem π hΓ hz) hx) (Γ.inv_mem (yOf_mem π hΓ hz')))).2 ?_
    rw [map_mul, map_mul, map_inv, yOf_map, yOf_map, e]
    group
  · have hz' : a * ((π (x : G))⁻¹ * z)⁻¹ ∉ Γ.map π := fun hh => hz (by
      rw [e] at hh
      simpa using (Γ.map π).mul_mem hh ((Γ.map π).inv_mem hpx))
    rw [dif_neg hz, dif_neg hz']

end JB

section SelfPull

variable {k : Type} [CommRing k] {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k A M) (Γ : Subgroup A) {S : Type}
  (I : S → Subgroup A)

/-- Degree-1 cone map of a `Γ`-equivariant coefficient endomorphism (same ambient, `φ = id`). -/
def K1self (q : M →ₗ[k] M) (hq : ∀ (x : Γ) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m)) :
    Module.End k (Z1 ρ Γ × (S → M)) :=
  K1pull ρ ρ (MonoidHom.id Γ) continuous_id q hq

/-- Degree-2 cone map of a `Γ`-equivariant coefficient endomorphism. -/
def K2self (q : M →ₗ[k] M) (hqs : ∀ s (x : ↥(Γ ⊓ I s)) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m)) :
    Module.End k ((s : S) → Z1 ρ (Γ ⊓ I s)) :=
  K2pull ρ ρ I I (fun s => MonoidHom.id ↥(Γ ⊓ I s)) (fun _ => continuous_id) q hqs

variable {ρ Γ I}

theorem K1self_mul_eq {q q' q'' : M →ₗ[k] M} (e : q * q' = q'')
    (hq : ∀ (x : Γ) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m))
    (hq' : ∀ (x : Γ) (m : M), q' (ρ (x : A) m) = ρ (x : A) (q' m))
    (hq'' : ∀ (x : Γ) (m : M), q'' (ρ (x : A) m) = ρ (x : A) (q'' m)) :
    K1self ρ Γ (S := S) q hq * K1self ρ Γ q' hq' = K1self ρ Γ q'' hq'' := by
  subst e
  exact LinearMap.ext fun _ => rfl

theorem K1self_eq_zero {q : M →ₗ[k] M} (e : q = 0)
    (hq : ∀ (x : Γ) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m)) : K1self ρ Γ (S := S) q hq = 0 := by
  subst e
  exact LinearMap.ext fun _ => rfl

theorem K1self_eq_one {q : M →ₗ[k] M} (e : q = 1)
    (hq : ∀ (x : Γ) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m)) : K1self ρ Γ (S := S) q hq = 1 := by
  subst e
  exact LinearMap.ext fun _ => rfl

theorem K1self_sum_eq {ι : Type} (T : Finset ι) {q : ι → M →ₗ[k] M} {q'' : M →ₗ[k] M} (e : ∑ i ∈ T, q i = q'')
    (hq : ∀ i (x : Γ) (m : M), q i (ρ (x : A) m) = ρ (x : A) (q i m))
    (hq'' : ∀ (x : Γ) (m : M), q'' (ρ (x : A) m) = ρ (x : A) (q'' m)) :
    ∑ i ∈ T, K1self ρ Γ (S := S) (q i) (hq i) = K1self ρ Γ q'' hq'' := by
  subst e
  exact K1pull_sum (ρ := ρ) (σ := ρ) (φ := MonoidHom.id Γ) (hφ := continuous_id) T q hq hq''

theorem K2self_mul_eq {q q' q'' : M →ₗ[k] M} (e : q * q' = q'')
    (hq : ∀ s (x : ↥(Γ ⊓ I s)) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m))
    (hq' : ∀ s (x : ↥(Γ ⊓ I s)) (m : M), q' (ρ (x : A) m) = ρ (x : A) (q' m))
    (hq'' : ∀ s (x : ↥(Γ ⊓ I s)) (m : M), q'' (ρ (x : A) m) = ρ (x : A) (q'' m)) :
    K2self ρ Γ I q hq * K2self ρ Γ I q' hq' = K2self ρ Γ I q'' hq'' := by
  subst e
  exact LinearMap.ext fun _ => rfl

theorem K2self_eq_zero {q : M →ₗ[k] M} (e : q = 0)
    (hq : ∀ s (x : ↥(Γ ⊓ I s)) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m)) : K2self ρ Γ I q hq = 0 := by
  subst e
  exact LinearMap.ext fun _ => rfl

theorem K2self_eq_one {q : M →ₗ[k] M} (e : q = 1)
    (hq : ∀ s (x : ↥(Γ ⊓ I s)) (m : M), q (ρ (x : A) m) = ρ (x : A) (q m)) : K2self ρ Γ I q hq = 1 := by
  subst e
  exact LinearMap.ext fun _ => rfl

theorem K2self_sum_eq {ι : Type} (T : Finset ι) {q : ι → M →ₗ[k] M} {q'' : M →ₗ[k] M} (e : ∑ i ∈ T, q i = q'')
    (hq : ∀ i s (x : ↥(Γ ⊓ I s)) (m : M), q i (ρ (x : A) m) = ρ (x : A) (q i m))
    (hq'' : ∀ s (x : ↥(Γ ⊓ I s)) (m : M), q'' (ρ (x : A) m) = ρ (x : A) (q'' m)) :
    ∑ i ∈ T, K2self ρ Γ I (q i) (hq i) = K2self ρ Γ I q'' hq'' := by
  subst e
  exact K2pull_sum (ρ := ρ) (σ := ρ) (I := I) (I' := I) (φs := fun s => MonoidHom.id ↥(Γ ⊓ I s))
    (hφs := fun _ => continuous_id) T q hq hq''

end SelfPull

section Blocks

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

theorem eB_regRep (ω : Blk (Γ.map π)) {x : G} (hx : x ∈ Γ) (m : MonoidAlgebra Λ Gf) :
    eB (Γ.map π) ω (regRep Λ π x m) = regRep Λ π x (eB (Γ.map π) ω m) :=
  eB_left (Γ.map π) (Subgroup.mem_map_of_mem π hx) ω m

variable (Λ) in
/-- The block projection `PB ω` of the perfect complex (termwise `eB ω`). -/
def PB (ω : Blk (Γ.map π)) : ∀ i, Module.End Λ (PC Λ π Γ I i) :=
  triMap (eB (Γ.map π) ω) (K1self (regRep Λ π) Γ (eB (Γ.map π) ω) fun x m => eB_regRep π Γ ω x.2 m)
    (K2self (regRep Λ π) Γ I (eB (Γ.map π) ω) fun _ x m => eB_regRep π Γ ω (Subgroup.mem_inf.1 x.2).1 m)

theorem PB_sum : ∀ i, ∑ ω, PB Λ π Γ I ω i = 1
  | 0 => sum_eB (Γ.map π)
  | 1 => by
    show ∑ ω, K1self (regRep Λ π) Γ (S := S) (eB (Γ.map π) ω) (fun x m => eB_regRep π Γ ω x.2 m) = 1
    rw [K1self_sum_eq Finset.univ (sum_eB (Γ.map π)) (fun ω x m => eB_regRep π Γ ω x.2 m) (fun _ _ => rfl)]
    exact K1self_eq_one rfl _
  | 2 => by
    show ∑ ω, K2self (regRep Λ π) Γ I (eB (Γ.map π) ω)
      (fun _ x m => eB_regRep π Γ ω (Subgroup.mem_inf.1 x.2).1 m) = 1
    rw [K2self_sum_eq Finset.univ (sum_eB (Γ.map π))
      (fun ω _ x m => eB_regRep π Γ ω (Subgroup.mem_inf.1 x.2).1 m) (fun _ _ _ => rfl)]
    exact K2self_eq_one rfl _
  | _ + 3 => LinearMap.ext fun _ => rfl

theorem PB_mul (ω ω' : Blk (Γ.map π)) :
    ∀ i, PB Λ π Γ I ω i * PB Λ π Γ I ω' i = if ω = ω' then PB Λ π Γ I ω i else 0
  | 0 => eB_mul (Γ.map π) ω ω'
  | 1 => by
    show K1self (regRep Λ π) Γ (S := S) (eB (Γ.map π) ω) (fun x m => eB_regRep π Γ ω x.2 m) *
        K1self (regRep Λ π) Γ (eB (Γ.map π) ω') (fun x m => eB_regRep π Γ ω' x.2 m) =
      if ω = ω' then K1self (regRep Λ π) Γ (eB (Γ.map π) ω) (fun x m => eB_regRep π Γ ω x.2 m) else 0
    split_ifs with hw
    · exact K1self_mul_eq (by rw [eB_mul, if_pos hw]) _ _ _
    · exact (K1self_mul_eq (q'' := 0) (by rw [eB_mul, if_neg hw]) _ _ (fun _ _ => by simp)).trans
        (K1self_eq_zero rfl _)
  | 2 => by
    show K2self (regRep Λ π) Γ I (eB (Γ.map π) ω)
          (fun _ x m => eB_regRep π Γ ω (Subgroup.mem_inf.1 x.2).1 m) *
        K2self (regRep Λ π) Γ I (eB (Γ.map π) ω')
          (fun _ x m => eB_regRep π Γ ω' (Subgroup.mem_inf.1 x.2).1 m) =
      if ω = ω' then K2self (regRep Λ π) Γ I (eB (Γ.map π) ω)
          (fun _ x m => eB_regRep π Γ ω (Subgroup.mem_inf.1 x.2).1 m) else 0
    split_ifs with hw
    · exact K2self_mul_eq (by rw [eB_mul, if_pos hw]) _ _ _
    · exact (K2self_mul_eq (q'' := 0) (by rw [eB_mul, if_neg hw]) _ _ (fun _ _ _ => by simp)).trans
        (K2self_eq_zero rfl _)
  | _ + 3 => LinearMap.ext fun _ => rfl

variable [Γ.Normal]

theorem eB_op (ψ : G) (γ : Gf) (ω : Blk (Γ.map π)) (m : MonoidAlgebra Λ Gf) :
    eB (Γ.map π) (blkShift (Γ.map π) (π ψ) γ (map_mem_normalizer π ψ) ω)
        (LinearMap.mulRight Λ (single γ⁻¹⁻¹ (1 : Λ)) (regRep Λ π ψ m)) =
      LinearMap.mulRight Λ (single γ⁻¹⁻¹ (1 : Λ)) (regRep Λ π ψ (eB (Γ.map π) ω m)) := by
  rw [inv_inv]
  exact eB_shift (Γ.map π) (π ψ) γ (map_mem_normalizer π ψ) ω m

theorem PB_op (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (γ : Gf) (ω : Blk (Γ.map π)) :
    ∀ i, PB Λ π Γ I (blkShift (Γ.map π) (π ψ) γ (map_mem_normalizer π ψ) ω) i *
        (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i) =
      (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i) * PB Λ π Γ I ω i
  | 0 => LinearMap.ext fun m => eB_op π Γ ψ γ ω m
  | 1 => frob1_pull (ρ := regRep Λ π) (σ := regRep Λ π) (φ := MonoidHom.id Γ) (hφ := continuous_id)
      (q := eB (Γ.map π) (blkShift (Γ.map π) (π ψ) γ (map_mem_normalizer π ψ) ω))
      (hq := fun x m => eB_regRep π Γ _ x.2 m)
      (f := LinearMap.mulRight Λ (single γ⁻¹⁻¹ 1)) (hf := mulRight_regRep π _)
      (f' := LinearMap.mulRight Λ (single γ⁻¹⁻¹ 1)) (hf' := mulRight_regRep π _)
      (q' := eB (Γ.map π) ω) (hq' := fun x m => eB_regRep π Γ ω x.2 m)
      (ψ := ψ) (ψ' := ψ) (t := t) (h := h) (h' := h) (hconj := fun _ => rfl) (hh := fun _ => rfl)
      (hop := eB_op π Γ ψ γ ω)
  | 2 => frob2_pull (ρ := regRep Λ π) (σ := regRep Λ π) (I := I) (I' := I) (φ := MonoidHom.id Γ)
      (φs := fun s => MonoidHom.id ↥(Γ ⊓ I s)) (hφs := fun _ => continuous_id)
      (q := eB (Γ.map π) (blkShift (Γ.map π) (π ψ) γ (map_mem_normalizer π ψ) ω))
      (hqs := fun _ x m => eB_regRep π Γ _ (Subgroup.mem_inf.1 x.2).1 m)
      (f := LinearMap.mulRight Λ (single γ⁻¹⁻¹ 1)) (hf := mulRight_regRep π _)
      (f' := LinearMap.mulRight Λ (single γ⁻¹⁻¹ 1)) (hf' := mulRight_regRep π _)
      (q' := eB (Γ.map π) ω) (hq' := fun x m => eB_regRep π Γ ω x.2 m)
      (hqs' := fun _ x m => eB_regRep π Γ ω (Subgroup.mem_inf.1 x.2).1 m)
      (ψ := ψ) (ψ' := ψ) (t := t) (h := h) (h' := h) (hI := hI) (hI' := hI)
      (hconj2 := fun _ _ => rfl) (hh := fun _ => rfl) (hop := eB_op π Γ ψ γ ω)
  | _ + 3 => LinearMap.ext fun _ => rfl

/-- **Block decomposition of the twisted Frobenius trace**: only the blocks fixed by
`ω ↦ π(ψ) ω γ` contribute. -/
theorem trace_op_eq_sum_fixed [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (γ : Gf) (i : ℕ) :
    LinearMap.trace Λ _ (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i) =
      ∑ ω ∈ Finset.univ.filter (fun ω => blkShift (Γ.map π) (π ψ) γ (map_mem_normalizer π ψ) ω = ω),
        LinearMap.trace Λ _ (PB Λ π Γ I ω i * (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI i)) :=
  trace_eq_sum_fixed (fun ω => PB Λ π Γ I ω i) (PB_sum π Γ I i) (fun ω ω' => PB_mul π Γ I ω ω' i) _
    (blkShift (Γ.map π) (π ψ) γ (map_mem_normalizer π ψ)) (fun ω => PB_op π Γ I ψ t h hI γ ω i)

end Blocks

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockCone2 =====
section

/-!
# S4-Lefschetz, L3e1b: a fixed block of the perfect complex is the cone of an open subgroup

For a block `ω = π(Γ) a` fixed by `ω ↦ π(ψ') ω γ`, the block `PB ω (PC)` is a retract of the cone `KN` of
the coinduced module `NB = coind_{H ∩ G'}^{G'} σH` over `G' ⊇ Γ`, through `QB` (built from `qB`) and `JB` (built
from `jB`), compatibly with Frobenius:
* `QB_JB : QB ∘ JB = id`, `PB_eq_JB_QB : PB ω = JB ∘ QB`, `QB_op : QB ∘ op = frobKN ∘ QB`;
* headline `trace_block_eq`: `Tr(PB ω ∘ op | PC^i) = Tr(frobKN | KN^i)`;
* `KN_projective`, `KN_finite`, `KN_free` (over a local ring): `KN^i` is a retract of `PC^i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx MonoidAlgebra Representation

section Homs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) {S : Type}
  (I : S → Subgroup G) (G' : Subgroup G)

/-- `Γ ∩ G' → Γ` as a hom (for `Γ ≤ G'` an isomorphism). -/
def downΓh : ↥(Γ.subgroupOf G') →* ↥Γ where
  toFun y := ⟨((y : G') : G), Subgroup.mem_subgroupOf.1 y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem downΓh_cont : Continuous (downΓh Γ G') :=
  continuous_induced_rng.2 (show Continuous fun y : ↥(Γ.subgroupOf G') => ((y : G') : G) from
    continuous_subtype_val.comp continuous_subtype_val)

/-- `(Γ ∩ G') ⊓ (I s ∩ G') → Γ ⊓ I s`. -/
def downIs (s : S) : ↥(Γ.subgroupOf G' ⊓ (I s).subgroupOf G') →* ↥(Γ ⊓ I s) where
  toFun x := ⟨((x : G') : G), Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1,
    Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).2⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem downIs_cont (s : S) : Continuous (downIs Γ I G' s) :=
  continuous_induced_rng.2 (show Continuous fun x : ↥(Γ.subgroupOf G' ⊓ (I s).subgroupOf G') => ((x : G') : G) from
    continuous_subtype_val.comp continuous_subtype_val)

variable {Γ G'} (hΓ : Γ ≤ G')

/-- `Γ → Γ ∩ G'` for `Γ ≤ G'`. -/
def liftΓh : ↥Γ →* ↥(Γ.subgroupOf G') where
  toFun x := ⟨⟨x, hΓ x.2⟩, Subgroup.mem_subgroupOf.2 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem liftΓh_cont : Continuous (liftΓh hΓ) :=
  continuous_induced_rng.2 (continuous_induced_rng.2
    (show Continuous fun x : Γ => (x : G) from continuous_subtype_val))

/-- `Γ ⊓ I s → (Γ ∩ G') ⊓ (I s ∩ G')` for `Γ ≤ G'`. -/
def liftIs (s : S) : ↥(Γ ⊓ I s) →* ↥(Γ.subgroupOf G' ⊓ (I s).subgroupOf G') where
  toFun x := ⟨⟨x, hΓ (Subgroup.mem_inf.1 x.2).1⟩, Subgroup.mem_inf.2
    ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 x.2).1, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 x.2).2⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem liftIs_cont (s : S) : Continuous (liftIs I hΓ s) :=
  continuous_induced_rng.2 (continuous_induced_rng.2
    (show Continuous fun x : ↥(Γ ⊓ I s) => (x : G) from continuous_subtype_val))

end Homs

section Tri2

variable {R : Type} [CommRing R] {V0 V1 V2 W0 W1 W2 : Type} [AddCommGroup V0] [AddCommGroup V1]
  [AddCommGroup V2] [AddCommGroup W0] [AddCommGroup W1] [AddCommGroup W2] [Module R V0] [Module R V1]
  [Module R V2] [Module R W0] [Module R W1] [Module R W2]

/-- Termwise map `Tri V0 V1 V2 → Tri W0 W1 W2` (zero on the zero terms). -/
def tri2Map (f0 : V0 →ₗ[R] W0) (f1 : V1 →ₗ[R] W1) (f2 : V2 →ₗ[R] W2) :
    ∀ i, Tri V0 V1 V2 i →ₗ[R] Tri W0 W1 W2 i
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | _ + 3 => 0

end Tri2

section Cone

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G) {H G' : Subgroup G}
  (σH : Representation Λ (H.subgroupOf G') Λ)

/-- The coinduced coefficient module `coind_{H ∩ G'}^{G'} σH`. -/
abbrev NB : Type := coindV (H.subgroupOf G').subtype σH

/-- The `G'`-action on `NB`. -/
abbrev σB : Representation Λ G' (NB σH) := coind (H.subgroupOf G').subtype σH

/-- The cone `[NB → Z¹(Γ ∩ G'; NB) × NB^S → Π_s Z¹((Γ ⊓ I s) ∩ G'; NB)]` as an `ℕ`-indexed family. -/
abbrev KN : ℕ → Type :=
  Tri (NB σH) (Z1 (σB σH) (Γ.subgroupOf G') × (S → NB σH))
    ((s : S) → Z1 (σB σH) (Γ.subgroupOf G' ⊓ (I s).subgroupOf G'))

variable (hΓ : Γ ≤ G') (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
  (hσ : ∀ h, σH h = 1) (a : Gf)

/-- The retraction `PC → KN` (termwise `qB`). -/
def QB : ∀ i, PC Λ π Γ I i →ₗ[Λ] KN Γ I σH i :=
  tri2Map (qB π σH hHΓ hcov hσ a)
    (K1pull (S := S) (regRep Λ π) (σB σH) (downΓh Γ G') (downΓh_cont Γ G') (qB π σH hHΓ hcov hσ a)
      fun x m => qB_left π σH hHΓ hcov hσ a (x : G') (Subgroup.mem_subgroupOf.1 x.2) m)
    (K2pull (regRep Λ π) (σB σH) I (fun s => (I s).subgroupOf G') (downIs Γ I G') (downIs_cont Γ I G')
      (qB π σH hHΓ hcov hσ a)
      fun _ x m => qB_left π σH hHΓ hcov hσ a (x : G') (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1) m)

/-- The section `KN → PC` (termwise `jB`). -/
def JB : ∀ i, KN Γ I σH i →ₗ[Λ] PC Λ π Γ I i :=
  tri2Map (jB π σH hΓ a)
    (K1pull (S := S) (σB σH) (regRep Λ π) (liftΓh hΓ) (liftΓh_cont hΓ) (jB π σH hΓ a)
      fun x n => jB_left π σH hHΓ hσ hΓ a (liftΓh hΓ x : G') x.2 n)
    (K2pull (σB σH) (regRep Λ π) (fun s => (I s).subgroupOf G') I (liftIs I hΓ) (liftIs_cont I hΓ) (jB π σH hΓ a)
      fun s x n => jB_left π σH hHΓ hσ hΓ a (liftIs I hΓ s x : G') (Subgroup.mem_inf.1 x.2).1 n)

theorem QB_JB : ∀ i, QB π Γ I σH hHΓ hcov hσ a i ∘ₗ JB π Γ I σH hΓ hHΓ hσ a i = LinearMap.id
  | 0 => LinearMap.ext fun f => qB_jB π σH hHΓ hcov hσ hΓ a f
  | 1 => LinearMap.ext fun p => Prod.ext
      (Subtype.ext (funext fun x => qB_jB π σH hHΓ hcov hσ hΓ a ((p.1 : ↥(Γ.subgroupOf G') → NB σH) x)))
      (funext fun s => qB_jB π σH hHΓ hcov hσ hΓ a (p.2 s))
  | 2 => LinearMap.ext fun e => funext fun s => Subtype.ext (funext fun x =>
      qB_jB π σH hHΓ hcov hσ hΓ a ((e s : ↥(Γ.subgroupOf G' ⊓ (I s).subgroupOf G') → NB σH) x))
  | _ + 3 => LinearMap.ext fun _ => rfl

theorem PB_eq_JB_QB :
    ∀ i, PB Λ π Γ I (blk (Γ.map π) a) i = JB π Γ I σH hΓ hHΓ hσ a i ∘ₗ QB π Γ I σH hHΓ hcov hσ a i
  | 0 => LinearMap.ext fun F => (jB_qB π σH hHΓ hcov hσ hΓ a F).symm
  | 1 => LinearMap.ext fun p => Prod.ext
      (Subtype.ext (funext fun x => (jB_qB π σH hHΓ hcov hσ hΓ a ((p.1 : Γ → MonoidAlgebra Λ Gf) x)).symm))
      (funext fun s => (jB_qB π σH hHΓ hcov hσ hΓ a (p.2 s)).symm)
  | 2 => LinearMap.ext fun e => funext fun s => Subtype.ext (funext fun x =>
      (jB_qB π σH hHΓ hcov hσ hΓ a ((e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) x)).symm)
  | _ + 3 => LinearMap.ext fun _ => rfl

variable [Γ.Normal]

/-- Frobenius on the cone `KN`. -/
def frobKN (ψ' : G') (t : S → S) (h' : S → ↥(Γ.subgroupOf G'))
    (hI' : BdryCompat (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t h') :
    ∀ i, Module.End Λ (KN Γ I σH i) :=
  triMap (σB σH ψ') (frob1 (σB σH) (Γ.subgroupOf G') ψ' t h')
    (frob2 (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t h' hI')

theorem qB_op (ψ' : G') {γ : Gf} {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H) (hψ : (ψ' : G) = c0 * g)
    (hπg : π g = a * γ⁻¹ * a⁻¹) (m : MonoidAlgebra Λ Gf) :
    qB π σH hHΓ hcov hσ a (LinearMap.mulRight Λ (single γ⁻¹⁻¹ (1 : Λ)) (regRep Λ π (ψ' : G) m)) =
      (LinearMap.id : NB σH →ₗ[Λ] NB σH) (σB σH ψ' (qB π σH hHΓ hcov hσ a m)) := by
  rw [inv_inv]
  exact qB_frob π σH hHΓ hcov hσ a ψ' hc0 hg hψ hπg m

theorem QB_op (ψ' : G') (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I (ψ' : G) t h)
    (hI' : BdryCompat (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t (fun s => liftΓh hΓ (h s)))
    {γ : Gf} {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H) (hψ : (ψ' : G) = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹) :
    ∀ i, QB π Γ I σH hHΓ hcov hσ a i ∘ₗ (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I (ψ' : G) t h hI i) =
      frobKN Γ I σH ψ' t (fun s => liftΓh hΓ (h s)) hI' i ∘ₗ QB π Γ I σH hHΓ hcov hσ a i
  | 0 => LinearMap.ext fun m => qB_op π Γ σH hHΓ hcov hσ a ψ' hc0 hg hψ hπg m
  | 1 => (frob1_pull (ρ := regRep Λ π) (σ := σB σH) (φ := downΓh Γ G') (hφ := downΓh_cont Γ G')
      (q := qB π σH hHΓ hcov hσ a)
      (hq := fun x m => qB_left π σH hHΓ hcov hσ a (x : G') (Subgroup.mem_subgroupOf.1 x.2) m)
      (f := LinearMap.mulRight Λ (single γ⁻¹⁻¹ 1)) (hf := mulRight_regRep π _)
      (f' := LinearMap.id) (hf' := fun _ _ => rfl)
      (q' := qB π σH hHΓ hcov hσ a)
      (hq' := fun x m => qB_left π σH hHΓ hcov hσ a (x : G') (Subgroup.mem_subgroupOf.1 x.2) m)
      (ψ := (ψ' : G)) (ψ' := ψ') (t := t) (h := h) (h' := fun s => liftΓh hΓ (h s))
      (hconj := fun _ => rfl) (hh := fun _ => rfl)
      (hop := qB_op π Γ σH hHΓ hcov hσ a ψ' hc0 hg hψ hπg)).trans (LinearMap.ext fun _ => rfl)
  | 2 => (frob2_pull (ρ := regRep Λ π) (σ := σB σH) (I := I) (I' := fun s => (I s).subgroupOf G')
      (φ := downΓh Γ G') (φs := downIs Γ I G') (hφs := downIs_cont Γ I G')
      (q := qB π σH hHΓ hcov hσ a)
      (hqs := fun _ x m => qB_left π σH hHΓ hcov hσ a (x : G')
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1) m)
      (f := LinearMap.mulRight Λ (single γ⁻¹⁻¹ 1)) (hf := mulRight_regRep π _)
      (f' := LinearMap.id) (hf' := fun _ _ => rfl)
      (q' := qB π σH hHΓ hcov hσ a)
      (hq' := fun x m => qB_left π σH hHΓ hcov hσ a (x : G') (Subgroup.mem_subgroupOf.1 x.2) m)
      (hqs' := fun _ x m => qB_left π σH hHΓ hcov hσ a (x : G')
        (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1) m)
      (ψ := (ψ' : G)) (ψ' := ψ') (t := t) (h := h) (h' := fun s => liftΓh hΓ (h s)) (hI := hI) (hI' := hI')
      (hconj2 := fun _ _ => rfl) (hh := fun _ => rfl)
      (hop := qB_op π Γ σH hHΓ hcov hσ a ψ' hc0 hg hψ hπg)).trans (LinearMap.ext fun _ => rfl)
  | _ + 3 => LinearMap.ext fun _ => rfl

include hHΓ hcov hσ in
/-- **Trace of a fixed block**: `Tr(PB ω ∘ op | PC^i) = Tr(Frob_{ψ'} | KN^i)` for `ω = π(Γ) a`,
`ψ' = c0 g`, `c0 ∈ Γ`, `g ∈ H`, `π(g) = a γ⁻¹ a⁻¹`. -/
theorem trace_block_eq [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    [∀ i, Module.Free Λ (KN Γ I σH i)] [∀ i, Module.Finite Λ (KN Γ I σH i)]
    (ψ' : G') (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I (ψ' : G) t h)
    (hI' : BdryCompat (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t (fun s => liftΓh hΓ (h s)))
    {γ : Gf} {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H) (hψ : (ψ' : G) = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹)
    (i : ℕ) :
    LinearMap.trace Λ _ (PB Λ π Γ I (blk (Γ.map π) a) i * (ρPC Λ π Γ I i γ⁻¹ ∘ₗ frobPC Λ π Γ I (ψ' : G) t h hI i)) =
      LinearMap.trace Λ _ (frobKN Γ I σH ψ' t (fun s => liftΓh hΓ (h s)) hI' i) :=
  trace_block_transfer _ (QB π Γ I σH hHΓ hcov hσ a i) (JB π Γ I σH hΓ hHΓ hσ a i)
    (PB_eq_JB_QB π Γ I σH hΓ hHΓ hcov hσ a i) (QB_JB π Γ I σH hΓ hHΓ hcov hσ a i) _ _
    (QB_op π Γ I σH hΓ hHΓ hcov hσ a ψ' t h hI hI' hc0 hg hψ hπg i)

end Cone

section Free

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G) {H G' : Subgroup G}
  (σH : Representation Λ (H.subgroupOf G') Λ) (hΓ : Γ ≤ G') (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1)
  (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H) (hσ : ∀ h, σH h = 1) (a : Gf)

include hΓ hHΓ hcov hσ a

theorem KN_projective [∀ i, Module.Free Λ (PC Λ π Γ I i)] (i : ℕ) : Module.Projective Λ (KN Γ I σH i) :=
  Module.Projective.of_split (JB π Γ I σH hΓ hHΓ hσ a i) (QB π Γ I σH hHΓ hcov hσ a i)
    (QB_JB π Γ I σH hΓ hHΓ hcov hσ a i)

theorem KN_finite [∀ i, Module.Finite Λ (PC Λ π Γ I i)] (i : ℕ) : Module.Finite Λ (KN Γ I σH i) :=
  Module.Finite.of_surjective (QB π Γ I σH hHΓ hcov hσ a i) fun w =>
    ⟨JB π Γ I σH hΓ hHΓ hσ a i w, LinearMap.congr_fun (QB_JB π Γ I σH hΓ hHΓ hcov hσ a i) w⟩

theorem KN_free [IsLocalRing Λ] [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (i : ℕ) : Module.Free Λ (KN Γ I σH i) :=
  haveI := KN_projective π Γ I σH hΓ hHΓ hcov hσ a i
  haveI := KN_finite π Γ I σH hΓ hHΓ hcov hσ a i
  Module.free_of_flat_of_isLocalRing

end Free

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_H2Block =====
section

/-!
# S4-Lefschetz, L3e2c1: block projections on `H²(K) = coker d¹`

* `h2Map`: the map on `H2K` induced by degree-1/2 maps commuting with `d¹`, with its composition and
  intertwining laws (`h2Map_comp_eq`, `h2Map_comp_eq_id`, `h2Map_comm`) and `frobH2K_eq_h2Map`;
* for the total cone `PC` (coefficients `Λ[Gf]`): `h2Op γ ψ` (from `ρPC γ⁻¹ ∘ frobPC`) and the block projection
  `h2PB ω` (from `PB ω`);
* for a fixed block `ω = π(Γ) a`: `h2Q`/`h2J` (from `QB`/`JB`) with `h2Q ∘ h2J = id`, `h2PB ω = h2J ∘ h2Q`,
  `h2Q ∘ h2Op = frobH2K ∘ h2Q`, and the headline `trace_h2_block`:
  `Tr(h2PB ω ∘ h2Op | H²K(PC)) = Tr(frobH2K | H²K(KN))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx MonoidAlgebra Representation

section H2Map

variable {k : Type} [CommRing k] {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k A M) (σ : Representation k B N) (Γ : Subgroup A) (Γ' : Subgroup B) {S : Type}
  (I : S → Subgroup A) (I' : S → Subgroup B) (hρ : IsOpen (ρ.ker : Set A)) (hσ : IsOpen (σ.ker : Set B))

/-- The map on `H²(K) = coker d¹` induced by degree-1/2 maps commuting with `d¹`. -/
def h2Map (f1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ' × (S → N))
    (f2 : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ' ⊓ I' s)))
    (hf : ∀ p, cx1 σ Γ' I' hσ (f1 p) = f2 (cx1 ρ Γ I hρ p)) : H2K ρ Γ I hρ →ₗ[k] H2K σ Γ' I' hσ :=
  Submodule.mapQ _ _ f2 fun x hx => by
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
    exact Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨f1 p, hf p⟩)

theorem h2Map_mk (f1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ' × (S → N))
    (f2 : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ' ⊓ I' s)))
    (hf : ∀ p, cx1 σ Γ' I' hσ (f1 p) = f2 (cx1 ρ Γ I hρ p)) (e : (s : S) → Z1 ρ (Γ ⊓ I s)) :
    h2Map ρ σ Γ Γ' I I' hρ hσ f1 f2 hf (Submodule.Quotient.mk e) = Submodule.Quotient.mk (f2 e) :=
  rfl

variable {ρ σ Γ Γ' I I' hρ hσ}

/-- Round trip `ρ → σ → ρ`: determined by the degree-2 composite. -/
theorem h2Map_comp_eq {f1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ' × (S → N)}
    {f2 : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ' ⊓ I' s))}
    {hf : ∀ p, cx1 σ Γ' I' hσ (f1 p) = f2 (cx1 ρ Γ I hρ p)}
    {g1 : Z1 σ Γ' × (S → N) →ₗ[k] Z1 ρ Γ × (S → M)}
    {g2 : ((s : S) → Z1 σ (Γ' ⊓ I' s)) →ₗ[k] ((s : S) → Z1 ρ (Γ ⊓ I s))}
    {hg : ∀ p, cx1 ρ Γ I hρ (g1 p) = g2 (cx1 σ Γ' I' hσ p)}
    {k1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 ρ Γ × (S → M)}
    {k2 : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 ρ (Γ ⊓ I s))}
    {hk : ∀ p, cx1 ρ Γ I hρ (k1 p) = k2 (cx1 ρ Γ I hρ p)} (e : ∀ x, k2 x = g2 (f2 x)) :
    h2Map ρ ρ Γ Γ I I hρ hρ k1 k2 hk =
      h2Map σ ρ Γ' Γ I' I hσ hρ g1 g2 hg ∘ₗ h2Map ρ σ Γ Γ' I I' hρ hσ f1 f2 hf :=
  Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    congrArg (Submodule.Quotient.mk (p := LinearMap.range (cx1 ρ Γ I hρ))) (e x))

/-- Round trip `ρ → σ → ρ` equal to the identity in degree 2. -/
theorem h2Map_comp_eq_id {f1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ' × (S → N)}
    {f2 : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ' ⊓ I' s))}
    {hf : ∀ p, cx1 σ Γ' I' hσ (f1 p) = f2 (cx1 ρ Γ I hρ p)}
    {g1 : Z1 σ Γ' × (S → N) →ₗ[k] Z1 ρ Γ × (S → M)}
    {g2 : ((s : S) → Z1 σ (Γ' ⊓ I' s)) →ₗ[k] ((s : S) → Z1 ρ (Γ ⊓ I s))}
    {hg : ∀ p, cx1 ρ Γ I hρ (g1 p) = g2 (cx1 σ Γ' I' hσ p)} (e : ∀ x, g2 (f2 x) = x) :
    h2Map σ ρ Γ' Γ I' I hσ hρ g1 g2 hg ∘ₗ h2Map ρ σ Γ Γ' I I' hρ hσ f1 f2 hf = LinearMap.id :=
  Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    congrArg (Submodule.Quotient.mk (p := LinearMap.range (cx1 ρ Γ I hρ))) (e x))

/-- Intertwining: `f ∘ o = r ∘ f` in degree 2 gives the same on `H²`. -/
theorem h2Map_comm {f1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ' × (S → N)}
    {f2 : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ' ⊓ I' s))}
    {hf : ∀ p, cx1 σ Γ' I' hσ (f1 p) = f2 (cx1 ρ Γ I hρ p)}
    {o1 : Z1 ρ Γ × (S → M) →ₗ[k] Z1 ρ Γ × (S → M)}
    {o2 : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 ρ (Γ ⊓ I s))}
    {ho : ∀ p, cx1 ρ Γ I hρ (o1 p) = o2 (cx1 ρ Γ I hρ p)}
    {r1 : Z1 σ Γ' × (S → N) →ₗ[k] Z1 σ Γ' × (S → N)}
    {r2 : ((s : S) → Z1 σ (Γ' ⊓ I' s)) →ₗ[k] ((s : S) → Z1 σ (Γ' ⊓ I' s))}
    {hr : ∀ p, cx1 σ Γ' I' hσ (r1 p) = r2 (cx1 σ Γ' I' hσ p)} (e : ∀ x, f2 (o2 x) = r2 (f2 x)) :
    h2Map ρ σ Γ Γ' I I' hρ hσ f1 f2 hf ∘ₗ h2Map ρ ρ Γ Γ I I hρ hρ o1 o2 ho =
      h2Map σ σ Γ' Γ' I' I' hσ hσ r1 r2 hr ∘ₗ h2Map ρ σ Γ Γ' I I' hρ hσ f1 f2 hf :=
  Submodule.linearMap_qext _ (LinearMap.ext fun x =>
    congrArg (Submodule.Quotient.mk (p := LinearMap.range (cx1 σ Γ' I' hσ))) (e x))

variable (ρ Γ I hρ) in
theorem frobH2K_eq_h2Map [Γ.Normal] (ψ : A) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) :
    frobH2K ρ Γ I ψ t h hρ hI = h2Map ρ ρ Γ Γ I I hρ hρ (frob1 ρ Γ ψ t h) (frob2 ρ Γ I ψ t h hI)
      (fun p => LinearMap.congr_fun (cx1_frob (ρ := ρ) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h)
        (hρ := hρ) (hI := hI)) p) :=
  rfl

end H2Map

section Total

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))

theorem op_cx1 [Γ.Normal] (γ : Gf) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)
    (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :
    cx1 (regRep Λ π) Γ I (isOpen_regRep_ker π hπ) (ρPC Λ π Γ I 1 γ⁻¹ (frobPC Λ π Γ I ψ t h hI 1 p)) =
      ρPC Λ π Γ I 2 γ⁻¹ (frobPC Λ π Γ I ψ t h hI 2 (cx1 (regRep Λ π) Γ I (isOpen_regRep_ker π hπ) p)) := by
  have e1 := LinearMap.congr_fun (d1_equiv π Γ I hπ γ⁻¹) (frobPC Λ π Γ I ψ t h hI 1 p)
  have e2 := LinearMap.congr_fun (cx1_frob (ρ := regRep Λ π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h)
    (hρ := isOpen_regRep_ker π hπ) (hI := hI)) p
  exact e1.trans (congrArg (ρPC Λ π Γ I 2 γ⁻¹) e2)

variable (Λ) in
/-- The twisted Frobenius `ρPC γ⁻¹ ∘ frobPC ψ` on `H²K` of the total cone. -/
def h2Op [Γ.Normal] (γ : Gf) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) :
    Module.End Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :=
  h2Map (regRep Λ π) (regRep Λ π) Γ Γ I I (isOpen_regRep_ker π hπ) (isOpen_regRep_ker π hπ)
    (ρPC Λ π Γ I 1 γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI 1) (ρPC Λ π Γ I 2 γ⁻¹ ∘ₗ frobPC Λ π Γ I ψ t h hI 2)
    (op_cx1 π Γ I hπ γ ψ t h hI)

variable [Finite Gf]

variable (Λ) in
/-- The block projection `PB ω` on `H²K` of the total cone. -/
def h2PB (ω : Blk (Γ.map π)) : Module.End Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :=
  h2Map (regRep Λ π) (regRep Λ π) Γ Γ I I (isOpen_regRep_ker π hπ) (isOpen_regRep_ker π hπ)
    (PB Λ π Γ I ω 1) (PB Λ π Γ I ω 2) fun p => LinearMap.congr_fun
      (cx1_pull (ρ := regRep Λ π) (σ := regRep Λ π) (I := I) (I' := I) (φ := MonoidHom.id Γ)
        (hφ := continuous_id) (φs := fun s => MonoidHom.id ↥(Γ ⊓ I s)) (hφs := fun _ => continuous_id)
        (q := eB (Γ.map π) ω) (hq := fun x m => eB_regRep π Γ ω x.2 m)
        (hqs := fun _ x m => eB_regRep π Γ ω (Subgroup.mem_inf.1 x.2).1 m)
        (hρ := isOpen_regRep_ker π hπ) (hσ := isOpen_regRep_ker π hπ) (hφsc := fun _ _ => rfl)) p

end Total

section Block

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G) {H G' : Subgroup G}
  (σH : Representation Λ (H.subgroupOf G') Λ) (hπ : IsOpen (π.ker : Set G))
  (hσB : IsOpen ((σB σH).ker : Set G'))
  (hΓ : Γ ≤ G') (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
  (hσ : ∀ h, σH h = 1) (a : Gf)

/-- `QB` on `H²K`: total cone → `G'`-cone. -/
def h2Q : H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ) →ₗ[Λ]
    H2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB :=
  h2Map (regRep Λ π) (σB σH) Γ (Γ.subgroupOf G') I (fun s => (I s).subgroupOf G') (isOpen_regRep_ker π hπ) hσB
    (QB π Γ I σH hHΓ hcov hσ a 1) (QB π Γ I σH hHΓ hcov hσ a 2) fun p => LinearMap.congr_fun
      (cx1_pull (ρ := regRep Λ π) (σ := σB σH) (I := I) (I' := fun s => (I s).subgroupOf G')
        (φ := downΓh Γ G') (hφ := downΓh_cont Γ G') (φs := downIs Γ I G') (hφs := downIs_cont Γ I G')
        (q := qB π σH hHΓ hcov hσ a)
        (hq := fun x m => qB_left π σH hHΓ hcov hσ a (x : G') (Subgroup.mem_subgroupOf.1 x.2) m)
        (hqs := fun _ x m => qB_left π σH hHΓ hcov hσ a (x : G')
          (Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 x.2).1) m)
        (hρ := isOpen_regRep_ker π hπ) (hσ := hσB) (hφsc := fun _ _ => rfl)) p

/-- `JB` on `H²K`: `G'`-cone → total cone. -/
def h2J : H2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB →ₗ[Λ]
    H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ) :=
  h2Map (σB σH) (regRep Λ π) (Γ.subgroupOf G') Γ (fun s => (I s).subgroupOf G') I hσB (isOpen_regRep_ker π hπ)
    (JB π Γ I σH hΓ hHΓ hσ a 1) (JB π Γ I σH hΓ hHΓ hσ a 2) fun p => LinearMap.congr_fun
      (cx1_pull (ρ := σB σH) (σ := regRep Λ π) (I := fun s => (I s).subgroupOf G') (I' := I)
        (φ := liftΓh hΓ) (hφ := liftΓh_cont hΓ) (φs := liftIs I hΓ) (hφs := liftIs_cont I hΓ)
        (q := jB π σH hΓ a)
        (hq := fun x n => jB_left π σH hHΓ hσ hΓ a (liftΓh hΓ x : G') x.2 n)
        (hqs := fun s x n => jB_left π σH hHΓ hσ hΓ a (liftIs I hΓ s x : G') (Subgroup.mem_inf.1 x.2).1 n)
        (hρ := hσB) (hσ := isOpen_regRep_ker π hπ) (hφsc := fun _ _ => rfl)) p

theorem h2Q_h2J : h2Q π Γ I σH hπ hσB hHΓ hcov hσ a ∘ₗ h2J π Γ I σH hπ hσB hΓ hHΓ hσ a = LinearMap.id :=
  h2Map_comp_eq_id fun x => LinearMap.congr_fun (QB_JB π Γ I σH hΓ hHΓ hcov hσ a 2) x

theorem h2PB_eq_h2J_h2Q :
    h2PB Λ π Γ I hπ (blk (Γ.map π) a) = h2J π Γ I σH hπ hσB hΓ hHΓ hσ a ∘ₗ h2Q π Γ I σH hπ hσB hHΓ hcov hσ a :=
  h2Map_comp_eq fun x => LinearMap.congr_fun (PB_eq_JB_QB π Γ I σH hΓ hHΓ hcov hσ a 2) x

variable [Γ.Normal]

theorem h2Q_op (ψ' : G') (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I (ψ' : G) t h)
    (hI' : BdryCompat (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t (fun s => liftΓh hΓ (h s)))
    {γ : Gf} {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H) (hψ : (ψ' : G) = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹) :
    h2Q π Γ I σH hπ hσB hHΓ hcov hσ a ∘ₗ h2Op Λ π Γ I hπ γ (ψ' : G) t h hI =
      frobH2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t (fun s => liftΓh hΓ (h s)) hσB hI' ∘ₗ
        h2Q π Γ I σH hπ hσB hHΓ hcov hσ a := by
  rw [frobH2K_eq_h2Map]
  exact h2Map_comm fun x => LinearMap.congr_fun (QB_op π Γ I σH hΓ hHΓ hcov hσ a ψ' t h hI hI' hc0 hg hψ hπg 2) x

include hHΓ hcov hσ in
/-- **Trace of a fixed block on `H²`**: `Tr(h2PB ω ∘ h2Op | H²K(PC)) = Tr(Frob_{ψ'} | H²K(KN))` for `ω = π(Γ) a`,
`ψ' = c0 g`, `c0 ∈ Γ`, `g ∈ H`, `π(g) = a γ⁻¹ a⁻¹`. -/
theorem trace_h2_block [Module.Free Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ))]
    [Module.Finite Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ))]
    [Module.Free Λ (H2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB)]
    [Module.Finite Λ (H2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB)]
    (ψ' : G') (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I (ψ' : G) t h)
    (hI' : BdryCompat (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t (fun s => liftΓh hΓ (h s)))
    {γ : Gf} {c0 g : G} (hc0 : c0 ∈ Γ) (hg : g ∈ H) (hψ : (ψ' : G) = c0 * g) (hπg : π g = a * γ⁻¹ * a⁻¹) :
    LinearMap.trace Λ _ (h2PB Λ π Γ I hπ (blk (Γ.map π) a) * h2Op Λ π Γ I hπ γ (ψ' : G) t h hI) =
      LinearMap.trace Λ _
        (frobH2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') ψ' t (fun s => liftΓh hΓ (h s)) hσB hI') :=
  trace_block_transfer _ (h2Q π Γ I σH hπ hσB hHΓ hcov hσ a) (h2J π Γ I σH hπ hσB hΓ hHΓ hσ a)
    (h2PB_eq_h2J_h2Q π Γ I σH hπ hσB hΓ hHΓ hcov hσ a) (h2Q_h2J π Γ I σH hπ hσB hΓ hHΓ hcov hσ a) _ _
    (h2Q_op π Γ I σH hπ hσB hΓ hHΓ hcov hσ a ψ' t h hI hI' hc0 hg hψ hπg)

end Block

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_FrobCong =====
section

/-!
# S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`

Generic (any topological group `G`, normal `Γ`, boundary subgroups `I`):
* `twistc_comp`, `bdryCompat_comp`, `frobH1c_comp`: the composite of two cone Frobenii is the cone Frobenius of the
  product, with correcting elements `s ↦ ψ'⁻¹ h_s ψ' · h'_{τ s}`;
* `frobH1c_inner`: an element `γ0 ∈ Γ` (with `τ = id`, `h = γ0⁻¹`) acts trivially on `H¹_c`;
  `frobH1c_mul_geo`: `F(ψ γ0) = F(ψ)` (correcting elements `γ0⁻¹ h_s`);
* `hpow`, `bdryCompat_pow`, `frobH1c_pow`: `F(ψ, τ, h)^m = F(ψ^m, τ^[m], hpow m)`;
* `frobH1c_congr_h`: `F(ψ, τ, h)` only depends on `h_s` modulo `I (τ s)` on the right;
* `frobH2c_comp`, `frobH2c_geo`, `frobH2c_pow`, `frobH2c_mul_geo`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) [hΓ : Γ.Normal]
  {S : Type} (I : S → Subgroup G)

theorem conjΓ_one' (g : Γ) : conjΓ Γ (1 : G) g = g := by
  ext
  simp

theorem conjΓ_mul' (ψ ψ' : G) (g : Γ) : conjΓ Γ (ψ * ψ') g = conjΓ Γ ψ' (conjΓ Γ ψ g) := by
  ext
  simp [mul_assoc]

/-! ## Composition -/

theorem twistc_comp (ψ ψ' : G) (τ τ' : S → S) (h h' : S → Γ) {p : (Γ → M) × (S → M)}
    (hp : p.1 ∈ Z1 ρ Γ) :
    twistc ρ Γ ψ τ h (twistc ρ Γ ψ' τ' h' p) =
      twistc ρ Γ (ψ * ψ') (τ' ∘ τ) (fun s => conjΓ Γ ψ' (h s) * h' (τ s)) p := by
  refine Prod.ext (funext fun g => ?_) (funext fun s => ?_)
  · simp only [twistc_fst, twist_apply, conjΓ_mul', map_mul, Module.End.mul_apply]
  · simp only [twistc_snd, twistc_fst, twist_apply, Function.comp_apply]
    rw [← rho_conj ρ Γ ψ' (h s), hp.2 (conjΓ Γ ψ' (h s)) (h' (τ s))]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub, map_add]
    abel

theorem bdryCompat_comp {ψ ψ' : G} {τ τ' : S → S} {h h' : S → Γ} (hI : BdryCompat Γ I ψ τ h)
    (hI' : BdryCompat Γ I ψ' τ' h') :
    BdryCompat Γ I (ψ * ψ') (τ' ∘ τ) (fun s => conjΓ Γ ψ' (h s) * h' (τ s)) := by
  intro s g hg
  have h1 := hI' (τ s) _ (bdryCompat_mem Γ I hI s g hg)
  have e : (((conjΓ Γ ψ' (h s) * h' (τ s) : Γ) : G))⁻¹ * ((ψ * ψ')⁻¹ * g * (ψ * ψ')) *
      ((conjΓ Γ ψ' (h s) * h' (τ s) : Γ) : G) =
      ((h' (τ s) : Γ) : G)⁻¹ * (ψ'⁻¹ * ((((h s)⁻¹ * conjΓ Γ ψ g * h s : Γ)) : G) * ψ') * (h' (τ s) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjΓ_val]
    group
  beta_reduce
  rw [show (τ' ∘ τ) s = τ' (τ s) from rfl, e]
  exact h1

theorem frobH1c_congr {ψ ψ' : G} {τ τ' : S → S} {h h' : S → Γ} (hψ : ψ = ψ') (hτ : τ = τ')
    (hh : h = h') (hI : BdryCompat Γ I ψ τ h) (hI' : BdryCompat Γ I ψ' τ' h') :
    frobH1c ρ Γ I ψ τ h hI = frobH1c ρ Γ I ψ' τ' h' hI' := by
  subst hψ hτ hh
  rfl

theorem frobH1c_comp {ψ ψ' : G} {τ τ' : S → S} {h h' : S → Γ} (hI : BdryCompat Γ I ψ τ h)
    (hI' : BdryCompat Γ I ψ' τ' h') :
    frobH1c ρ Γ I ψ τ h hI ∘ₗ frobH1c ρ Γ I ψ' τ' h' hI' =
      frobH1c ρ Γ I (ψ * ψ') (τ' ∘ τ) _ (bdryCompat_comp Γ I hI hI') := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun p => ?_)
  show H1c.mk ρ Γ I _ = H1c.mk ρ Γ I _
  exact congrArg (H1c.mk ρ Γ I) (Subtype.ext (twistc_comp ρ Γ ψ ψ' τ τ' h h' p.2.1))

/-! ## Inner twists act trivially -/

/-! ## Powers -/

/-! ## Changing the correcting elements inside the inertia -/

/-! ## `H²_c` -/

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ShapFrob =====
section

/-!
# S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius

Setting of `Def_RP_CurveCoh_ShapiroCone`: `H = π₁(U) ≤ G = π₁(V)`, `Γ = π₁^geo(V)` normal, boundary data
`I`, `J`, `π`, `xT`. A Frobenius lift `ψ ∈ H` acts on the cone complex of `V` (with boundary data `τ`, `h`) and on the
cone complex of `U` (with `τ'`, `h'`).

* `FrobMatch`: the two sets of boundary data match: `π (τ' t) = τ (π t)` and
  `(h'_t x_{τ' t})⁻¹ (ψ⁻¹ x_t ψ h_{π t}) ∈ I (τ (π t))`;
* `resEvc_twistc` (cocycle level, exact equality) and `shapiroH1c_frob`:
  `shapiroH1c ∘ frobH1c(f_* M; ψ, τ, h) = frobH1c(M; ψ, τ', h') ∘ shapiroH1c`;
* `trace_pow_eq_of_comm`, `trace_frob_shapiro`: equal traces of all powers through `shapiroH1cEquiv`;
* `conjΓ_tr`, `h1cTr_frob`: the ambient transport `h1cTr` (along `e : Δ₁ ≃ₜ* Δ₂` restricting `E : G₁ ≃* G₂`)
  commutes with the Frobenius on `H¹_c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Representation

/-! ## Traces through a linear equivalence -/

/-! ## Shapiro and Frobenius -/

section Shap

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (Γ H : Subgroup G) [Γ.Normal] (σ : Representation k H M)
  {S T : Type} (I : S → Subgroup G) (J : T → Subgroup H) (π : T → S) (xT : T → Γ)

/-- The Frobenius data `(ψ, τ, h)` on `V` and `(ψ, τ', h')` on the cover `U` match. -/
def FrobMatch (ψ : H) (τ : S → S) (h : S → Γ) (τ' : T → T) (h' : T → geoU Γ H) : Prop :=
  ∀ t : T, π (τ' t) = τ (π t) ∧
    (((h' t : H) : G) * (xT (τ' t) : G))⁻¹ * ((ψ : G)⁻¹ * (xT t : G) * (ψ : G) * (h (π t) : G)) ∈ I (τ (π t))

end Shap

/-! ## Ambient transport commutes with Frobenius -/

section Amb

open CupDuality

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] {M : Type} [AddCommGroup M] [Module k M]
  {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M} {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂}
  [Δ₁.Normal] [Δ₂.Normal] {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

end Amb

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_JacAlg_Charpoly =====
section

/-!
# Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)

* C1 `norm_resultant_eq_of_int`, `norm_resultant_eq_of_int_rat`: for monic `P, Q` over `ℤ_l`, equal norms
  `‖Res(P, F)‖ = ‖Res(Q, F)‖` for all integer `F` with `p ∤ F(0)` (`p ≠ l` prime) extend to all `G` over `ℤ_l`
  (approximation mod `l^K`) and then over `ℚ_l` (clearing denominators; the degrees agree via `F = l`).
* C2 `charpoly_eq_of_norm_det`: if `‖Res(P₀, F)‖_l = ‖det F(M)‖_l` for those `F`, then `charpoly M = P₀`.
  `DegreeData.deg_eq_resultant`: `deg F = Res(P₀, F)` when `P_π = P₀` (Milne 10.22).
  `DegreeData.charpoly_eq`: `‖deg F‖_l = ‖det F(M)‖_l` for `p ∤ F(0)` gives `charpoly(M) = P_π` (Milne 10.20),
  and `DegreeData.finrank_eq`: the rank is `2g`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

variable {l : ℕ} [hl : Fact l.Prime]

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

/-- Milne 10.22 in resultant form: `deg F = Res(P₀, F)` when `P_π = P₀ ∈ ℤ[X]`. -/
theorem deg_eq_resultant {P0 : ℤ[X]} (hP0 : D.charPoly = P0.map (Int.castRingHom ℚ)) (F : ℤ[X]) :
    (D.deg F : ℤ) = resultant P0 F := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := (Int.castRingHom ℂ).injective_int
  have hmono : P0.Monic := monic_of_injective (Int.castRingHom ℚ).injective_int (hP0 ▸ D.charPoly_monic)
  have hmap : D.charPoly.map (algebraMap ℚ ℂ) = P0.map (Int.castRingHom ℂ) := by
    rw [hP0, Polynomial.map_map]
    congr 1
  have h1 := D.deg_eq_prod_roots (K := ℂ) F
  rw [hmap] at h1
  have h2 := resultant_eq_prod_eval (P0.map (Int.castRingHom ℂ)) (F.map (Int.castRingHom ℂ)) F.natDegree
    natDegree_map_le (IsAlgClosed.splits _)
  rw [(hmono.map _).leadingCoeff, one_pow, one_mul, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at h2
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_natCast]
  exact h1.trans (h2.symm.trans (eq_intCast _ _))

/-- **Milne 10.20 / route A4.** `charpoly(M) = P_π` over `ℤ_l` when `‖deg F‖_l = ‖det F(M)‖_l` for every
integer `F` with `p ∤ F(0)` (`p ≠ l` prime) and `P_π = P₀ ∈ ℤ[X]`. -/
theorem charpoly_eq (hp : p.Prime) (hpl : p ≠ l) {P0 : ℤ[X]}
    (hP0 : D.charPoly = P0.map (Int.castRingHom ℚ)) {T : Type*} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (M : Module.End ℤ_[l] T)
    (hkey : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖((D.deg F : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (aeval M (F.map (Int.castRingHom ℤ_[l])))‖) :
    M.charpoly = P0.map (Int.castRingHom ℤ_[l]) := by
  have hmono : P0.Monic := monic_of_injective (Int.castRingHom ℚ).injective_int (hP0 ▸ D.charPoly_monic)
  refine charpoly_eq_of_norm_det hp hpl hmono M fun F hF => ?_
  rw [← D.deg_eq_resultant hP0 F, Int.cast_natCast]
  exact hkey F hF

end DegreeData

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_CoreB_Key =====
section

/-!
# Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)

* Tate matrices are closed under `0`, `-`, `+`, integer constants and polynomial evaluation (`isTateMat_aeval`).
* `h1inj_of_injective`, `h1span_of_card`: the basis hypotheses of CoreA from injectivity of `tateMap 1` and the count
  `#D[l] ≤ l^s`.
* `iotaG`: `D = l^k0 A ↪ Pic⁰(X̄)`, `π`-equivariant; `card_kerD`: `#ker F(π|D) = l ^ v_l(#ker F(π))`.
* `norm_deg_eq_norm_det` (hkey for `deg F ≠ 0`).
-/

set_option autoImplicit false

open Polynomial
open scoped Matrix

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G] {l : ℕ} [Fact l.Prime]
variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- `D = l^k0 A ↪ Pic⁰(X̄)`. -/
noncomputable def iotaG (l k0 : ℕ) [hl : Fact l.Prime] :
    (smulHom (Aℓ Ω hk l) (l ^ k0)).range →+ PicBar0 Ω hk :=
  (AddSubgroup.inclusion (primary_le_PicBar0 (Ω := Ω) hk hl.out.ne_zero)).comp
    (smulHom (Aℓ Ω hk l) (l ^ k0)).range.subtype

variable (l k0 : ℕ) [hl : Fact l.Prime]

omit [IsAlgClosed Ω] in
theorem coe_iotaG (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range) :
    ((iotaG Fq F Ω hk l k0 x : PicBar0 Ω hk) : PicBar Ω hk) = ((x : Aℓ Ω hk l) : PicBar Ω hk) := rfl

omit [IsAlgClosed Ω] in
theorem iotaG_injective : Function.Injective (iotaG Fq F Ω hk l k0) :=
  fun _ _ h => Subtype.ext (Subtype.ext (by have h' := congrArg Subtype.val h; exact h'))

end Spec

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_CoreB_Pert =====
section

/-!
# Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only

`DegreeData.charpoly_eq` asks for `‖deg F‖_l = ‖det F(M)‖_l` for every `F` with `p ∤ F(0)`. When `deg F = 0`
(so `Res(P₀, F) = 0`) we perturb: `F + C (l^K p k)` keeps `p ∤ F(0)`, has `deg ≠ 0` for some `k` (a monic polynomial
in `c` has finitely many roots), and moves both resultants by at most `l^-K`; hence `det F(M) = 0`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg

variable {l : ℕ} [hl : Fact l.Prime]

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ}

omit hl in
/-- Some `F + C (a k)` has nonzero degree (`a ≠ 0`). -/
theorem exists_deg_add_ne (D : DegreeData π g p) (F : ℤ[X]) (a : ℤ) (ha : a ≠ 0) :
    ∃ k : ℕ, D.deg (F + C (a * k)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set R : ℂ[X] := ((D.charPoly.map (algebraMap ℚ ℂ)).roots.map
    fun z => X + C ((F.map (Int.castRingHom ℂ)).eval z)).prod with hR_def
  have hR : R.Monic := monic_multiset_prod_of_monic _ _ fun z _ => monic_X_add_C _
  have hroot : ∀ k : ℕ, R.IsRoot ((a * k : ℤ) : ℂ) := by
    intro k
    have h := D.deg_eq_prod_roots (K := ℂ) (F + C (a * k))
    rw [hcon k, Nat.cast_zero] at h
    rw [Polynomial.IsRoot.def, hR_def, eval_multiset_prod, Multiset.map_map, h]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, eval_add, eval_X, eval_C, Polynomial.map_add, eq_intCast]
    rw [Polynomial.map_intCast, Polynomial.eval_intCast]
    exact add_comm _ _
  apply hR.ne_zero
  refine eq_zero_of_infinite_isRoot R
    (Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((a * k : ℤ) : ℂ)) ?_ hroot)
  intro k1 k2 h
  have h' : ((a * k1 : ℤ) : ℂ) = ((a * k2 : ℤ) : ℂ) := h
  exact_mod_cast mul_left_cancel₀ ha (Int.cast_injective h')

/-- **O7.** `DegreeData.charpoly_eq` with the norm identity required only when `deg F ≠ 0`. -/
theorem charpoly_eq_of_deg_ne (D : DegreeData π g p) (hp : p.Prime) (hpl : p ≠ l) {P0 : ℤ[X]}
    (hP0 : D.charPoly = P0.map (Int.castRingHom ℚ)) {T : Type*} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (M : Module.End ℤ_[l] T)
    (hkey : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 → D.deg F ≠ 0 →
      ‖((D.deg F : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (aeval M (F.map (Int.castRingHom ℤ_[l])))‖) :
    M.charpoly = P0.map (Int.castRingHom ℤ_[l]) := by
  refine D.charpoly_eq hp hpl hP0 M fun F hF => ?_
  by_cases h0 : D.deg F = 0
  swap
  · exact hkey F hF h0
  rw [h0, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero, linearMap_det_aeval_eq_resultant]
  refine eq_zero_of_norm_le_pow fun K => ?_
  have ha : (l : ℤ) ^ K * p ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)) (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨k, hk⟩ := exists_deg_add_ne D F _ ha
  set c : ℤ := (l : ℤ) ^ K * p * k with hc_def
  have hpc : (p : ℤ) ∣ c := ⟨(l : ℤ) ^ K * k, by rw [hc_def]; ring⟩
  have hFc : ¬ (p : ℤ) ∣ (F + C c).coeff 0 := by
    rw [coeff_add, coeff_C_zero]
    exact fun h => hF ((dvd_add_left hpc).mp h)
  have hcK : PadicInt.toZModPow K (Int.castRingHom ℤ_[l] c) = 0 := by
    rw [eq_intCast, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨(p : ℤ) * k, by rw [hc_def]; push_cast; ring⟩
  have h1 := hkey (F + C c) hFc hk
  rw [linearMap_det_aeval_eq_resultant, Polynomial.map_add, map_C, natDegree_add_C] at h1
  have e1 := D.deg_eq_resultant hP0 (F + C c)
  rw [natDegree_add_C] at e1
  have e0 := D.deg_eq_resultant hP0 F
  rw [h0, Nat.cast_zero] at e0
  have r1 : ((D.deg (F + C c) : ℕ) : ℤ_[l]) =
      resultant (P0.map (Int.castRingHom ℤ_[l])) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
        P0.natDegree F.natDegree -
      resultant (P0.map (Int.castRingHom ℤ_[l])) (F.map (Int.castRingHom ℤ_[l])) P0.natDegree F.natDegree := by
    rw [← map_C, ← Polynomial.map_add, resultant_map_map, resultant_map_map, ← map_sub, ← e1, ← e0, sub_zero,
      map_natCast]
  have hb1 : ‖resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
      (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
    rw [← h1, r1]
    exact norm_resultant_add_C_sub_le _ _ hcK _ _
  have h2 := norm_resultant_add_C_sub_le (LinearMap.charpoly M) (F.map (Int.castRingHom ℤ_[l])) hcK
    (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree
  calc _ = ‖-(resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
          (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree -
        resultant (LinearMap.charpoly M) (F.map (Int.castRingHom ℤ_[l])) (Module.finrank ℤ_[l] T)
          (F.map (Int.castRingHom ℤ_[l])).natDegree) +
        resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
          (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree‖ := by
        rw [neg_sub, sub_add_cancel]
    _ ≤ max ‖-(resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) +
          C (Int.castRingHom ℤ_[l] c)) (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree -
        resultant (LinearMap.charpoly M) (F.map (Int.castRingHom ℤ_[l])) (Module.finrank ℤ_[l] T)
          (F.map (Int.castRingHom ℤ_[l])).natDegree)‖
        ‖resultant (LinearMap.charpoly M) ((F.map (Int.castRingHom ℤ_[l])) + C (Int.castRingHom ℤ_[l] c))
          (Module.finrank ℤ_[l] T) (F.map (Int.castRingHom ℤ_[l])).natDegree‖ :=
        PadicInt.nonarchimedean _ _
    _ ≤ (l : ℝ) ^ (-(K : ℤ)) := max_le (by rw [norm_neg]; exact h2) hb1

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_PerfectCx_Red =====
section

/-!
# S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)

`Λ' = Λ/(t)` is encoded as a `Λ`-algebra with `algebraMap` onto, `t ↦ 0` and kernel `t Λ`. A `Λ`-linear `f : V → V'`
onto a `Λ'`-module with kernel in `t V` induces `Λ' ⊗ V ≃ V'` (`redEquiv`), which intertwines base changes of maps
compatible with the reductions (`redEquiv_comm`); Hattori–Stallings traces then reduce (`hs_red_of`). For
`A = Λ[Gf]`: coefficientwise reduction `redA` (onto, kernel `t A`) and the induced map on cocycles
`redZ1 : Z¹(Δ; Λ[Gf]) → Z¹(Δ; Λ'[Gf])`, onto with kernel `t Z¹` under `H2All` (`redZ1_surjective`, `redZ1_ker`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct

noncomputable section

section BC

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] (t : Λ)
  (hsurj : Function.Surjective (algebraMap Λ Λ')) (ht : algebraMap Λ Λ' t = 0)
  {V V' : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup V'] [Module Λ V'] [Module Λ' V']
  [IsScalarTower Λ Λ' V']

variable {W W' : Type} [AddCommGroup W] [Module Λ W] [AddCommGroup W'] [Module Λ W'] [Module Λ' W']
  [IsScalarTower Λ Λ' W']

variable {G : Type} [Group G] [Fintype G]

include hsurj ht in
/-- **Reduction of Hattori–Stallings traces**: if `f : V → V'` is onto with kernel in `t • V` and intertwines `ρ, φ`
with `ρ', φ'`, then `hs ρ' φ' = algebraMap (hs ρ φ)`. -/
theorem hs_red_of [Module.Free Λ V] [Module.Finite Λ V] [Module.Free Λ' V'] [Module.Finite Λ' V']
    {ρ : Representation Λ G V} (hρ : IsProj ρ) {ρ' : Representation Λ' G V'} {φ : V →ₗ[Λ] V}
    (hφ : IsEquivariant ρ ρ φ) (φ' : V' →ₗ[Λ'] V') (f : V →ₗ[Λ] V') (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 → ∃ y, x = t • y) (hfρ : ∀ g x, f (ρ g x) = ρ' g (f x))
    (hfφ : ∀ x, f (φ x) = φ' (f x)) (c : ConjClasses G) :
    hs ρ' φ' c = algebraMap Λ Λ' (hs ρ φ c) := by
  let e := redEquiv t hsurj ht f hf hk
  have he : IsEquivariant (repBaseChange Λ' ρ) ρ' e.toLinearMap := isEquivariant_iff.2 fun g u =>
    redEquiv_comm t hsurj ht f hf hk f hf hk (ρ g) (ρ' g) (hfρ g) u
  have hφ' : e.toLinearMap ∘ₗ φ.baseChange Λ' ∘ₗ e.symm.toLinearMap = φ' := LinearMap.ext fun y => by
    obtain ⟨u, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact redEquiv_comm t hsurj ht f hf hk f hf hk φ φ' hfφ u
  rw [← hφ', hs_conj hρ.baseChange e he hφ.baseChange]
  exact hs_baseChange hρ hφ c

end BC

section RedA

variable (Λ Λ' : Type) [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] (Gf : Type) [Group Gf]

variable {Λ Λ' Gf}

end RedA

section RedZ1

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf)

theorem redA_regRep (g : G) (a : MonoidAlgebra Λ Gf) :
    redA Λ Λ' Gf (regRep Λ π g a) = regRep Λ' π g (redA Λ Λ' Gf a) :=
  redA_mul_single _ _

variable (Λ Λ') in
/-- `G` acting on `Λ'[Gf]` by left multiplication through `π`, as a `Λ`-representation. -/
def regRepR : Representation Λ G (MonoidAlgebra Λ' Gf) where
  toFun g := (regRep Λ' π g).restrictScalars Λ
  map_one' := LinearMap.ext fun a => show regRep Λ' π 1 a = a by rw [map_one]; rfl
  map_mul' x y := LinearMap.ext fun a =>
    show regRep Λ' π (x * y) a = regRep Λ' π x (regRep Λ' π y a) by rw [map_mul]; rfl

variable (Λ Λ') in
/-- Reduction of cocycles `Z¹(Δ; Λ[Gf]) → Z¹(Δ; Λ'[Gf])` (values reduced coefficientwise). -/
def redZ1 (Δ : Subgroup G) : Z1 (regRep Λ π) Δ →ₗ[Λ] Z1 (regRep Λ' π) Δ where
  toFun c := ⟨fun g => redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g), (mem_Z1 (regRep Λ' π) Δ _).2
    ⟨((mem_Z1 (regRep Λ π) Δ _).1 c.2).1.comp _, fun g g' => by
      simp only [((mem_Z1 (regRep Λ π) Δ _).1 c.2).2 g g', map_add, redA_regRep]⟩⟩
  map_add' c d := Subtype.ext (funext fun g => by
    show redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g + (d : Δ → MonoidAlgebra Λ Gf) g) =
      redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g) + redA Λ Λ' Gf ((d : Δ → MonoidAlgebra Λ Gf) g)
    exact map_add _ _ _)
  map_smul' r c := Subtype.ext (funext fun g => by
    show redA Λ Λ' Gf (r • (c : Δ → MonoidAlgebra Λ Gf) g) = r • redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g)
    exact map_smul _ _ _)

theorem redZ1_apply (Δ : Subgroup G) (c : Z1 (regRep Λ π) Δ) (g : Δ) :
    (redZ1 Λ Λ' π Δ c : Δ → MonoidAlgebra Λ' Gf) g = redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g) := rfl

/-- Reduction of cocycles is onto (`H2All`). -/
theorem redZ1_surjective [Finite Λ] [Finite Gf] (hsurj : Function.Surjective (algebraMap Λ Λ')) {l N : ℕ}
    (hΛ : ((l ^ N : ℕ) : Λ) = 0) (Δ : Subgroup G) (hall : H2All Λ G Δ l N) (hπ : IsOpen (π.ker : Set G)) :
    Function.Surjective (redZ1 Λ Λ' π Δ) := fun z => by
  have := finite_A Λ Gf
  obtain ⟨c, hc⟩ := z1Map_surjective_of_all (regRep Λ π) (regRepR Λ Λ' π) Δ hall (nsmul_eq_zero_of_cast hΛ)
    (isOpen_regRep_ker π hπ) (redA Λ Λ' Gf) (redA_regRep π) (redA_surjective hsurj)
    ⟨(z : Δ → MonoidAlgebra Λ' Gf), (mem_Z1 (regRepR Λ Λ' π) Δ _).2 ((mem_Z1 (regRep Λ' π) Δ _).1 z.2)⟩
  exact ⟨c, Subtype.ext (congrArg Subtype.val hc)⟩

/-- The kernel of the reduction of cocycles is `t • Z¹` (`H2All`). -/
theorem redZ1_ker [Finite Λ] [Finite Gf] {t : Λ} (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s) {l N : ℕ}
    (hΛ : ((l ^ N : ℕ) : Λ) = 0) (Δ : Subgroup G) (hall : H2All Λ G Δ l N) (hπ : IsOpen (π.ker : Set G))
    (c : Z1 (regRep Λ π) Δ) (hc : redZ1 Λ Λ' π Δ c = 0) : ∃ d, c = t • d := by
  have := finite_A Λ Gf
  have hv : ∀ g, (c : Δ → MonoidAlgebra Λ Gf) g ∈ (smulRep π t).toSubmodule := fun g => by
    have h0 : redA Λ Λ' Gf ((c : Δ → MonoidAlgebra Λ Gf) g) = 0 := by
      have := congrArg (fun z : Z1 (regRep Λ' π) Δ => (z : Δ → MonoidAlgebra Λ' Gf) g) hc
      exact this
    obtain ⟨b, hb⟩ := redA_ker hk _ h0
    exact ⟨b, by simp [hb]⟩
  obtain ⟨d, hd⟩ := lift_of_values (regRep Λ π) (regRep Λ π) Δ hall (nsmul_eq_zero_of_cast hΛ)
    (isOpen_regRep_ker π hπ) (LinearMap.lsmul Λ (MonoidAlgebra Λ Gf) t) (fun g a => by simp)
    (smulRep π t) (fun a => ⟨a, rfl⟩) (fun w hw => hw) c hv
  refine ⟨d, Subtype.ext (funext fun g => ?_)⟩
  rw [coe_smul_Z1, ← hd g]
  rfl

end RedZ1

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_RedPC =====
section

/-!
# S4-PD (5), E3: the perfect complex mod `t` (`Pₙ ⊗ Λₘ ≅ Pₘ`)

Termwise reductions `redA`, `red1`, `red2` of `PC Λ → PC Λ'` are onto with kernel `t • PC` (`H2All`), commute with
the `Gf`-actions, the Frobenius and the differentials, so `Λ' ⊗ PC Λ i ≃ PC Λ' i` (`pcRed0`, `pcRed1`, `pcRed2`,
compatibilities via `redEquiv_comm`) and the Lefschetz numbers of the Frobenius reduce (`lefschetz_frob_red`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings TensorProduct

noncomputable section

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

theorem redA_rRep (x : Gf) (a : MonoidAlgebra Λ Gf) :
    redA Λ Λ' Gf (rRep Λ Gf x a) = rRep Λ' Gf x (redA Λ Λ' Gf a) := redA_mul_single' _ _

theorem redZ1_eRep (Δ : Subgroup G) (x : Gf) (c : Z1 (regRep Λ π) Δ) :
    redZ1 Λ Λ' π Δ (eRep (Λ := Λ) π Δ x c) = eRep (Λ := Λ') π Δ x (redZ1 Λ Λ' π Δ c) :=
  Subtype.ext (funext fun _ => redA_mul_single' _ _)

theorem redZ1_conj (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (c : Z1 (regRep Λ π) Δ') :
    redZ1 Λ Λ' π Δ (conjMap (regRep Λ π) x hx c) = conjMap (regRep Λ' π) x hx (redZ1 Λ Λ' π Δ' c) :=
  Subtype.ext (funext fun _ => redA_regRep π x _)

variable (Λ Λ') in
/-- Reduction on `P¹ = E_Γ × A^S`. -/
def red1 : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf) →ₗ[Λ] Z1 (regRep Λ' π) Γ × (S → MonoidAlgebra Λ' Gf) :=
  (redZ1 Λ Λ' π Γ).prodMap (LinearMap.piMap fun _ => redA Λ Λ' Gf)

variable (Λ Λ') in
/-- Reduction on `P² = Π_s E_s`. -/
def red2 : ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) →ₗ[Λ] ((s : S) → Z1 (regRep Λ' π) (Γ ⊓ I s)) :=
  LinearMap.piMap fun s => redZ1 Λ Λ' π (Γ ⊓ I s)

theorem red1_rho1 (x : Gf) (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :
    red1 Λ Λ' π Γ (rho1 Λ π Γ S x p) = rho1 Λ' π Γ S x (red1 Λ Λ' π Γ p) :=
  Prod.ext (redZ1_eRep π Γ x p.1) (funext fun s => redA_rRep x (p.2 s))

theorem red2_rho2 (x : Gf) (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    red2 Λ Λ' π Γ I (rho2 Λ π Γ I x e) = rho2 Λ' π Γ I x (red2 Λ Λ' π Γ I e) :=
  funext fun s => redZ1_eRep π (Γ ⊓ I s) x (e s)

section Frob

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

theorem red1_frob (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :
    red1 Λ Λ' π Γ (frob1 (regRep Λ π) Γ ψ t h p) = frob1 (regRep Λ' π) Γ ψ t h (red1 Λ Λ' π Γ p) :=
  Prod.ext (redZ1_conj π ψ (conj_mem_normal Γ ψ) p.1) (funext fun s => by
    show redA Λ Λ' Gf (regRep Λ π ψ (regRep Λ π (h s) (p.2 (t s)) - (p.1 : Γ → MonoidAlgebra Λ Gf) (h s))) =
      regRep Λ' π ψ (regRep Λ' π (h s) (redA Λ Λ' Gf (p.2 (t s))) -
        redA Λ Λ' Gf ((p.1 : Γ → MonoidAlgebra Λ Gf) (h s)))
    rw [redA_regRep, map_sub, redA_regRep])

theorem red2_frob (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    red2 Λ Λ' π Γ I (frob2 (regRep Λ π) Γ I ψ t h hI e) = frob2 (regRep Λ' π) Γ I ψ t h hI (red2 Λ Λ' π Γ I e) :=
  funext fun s => redZ1_conj π (ψ * h s) (bdry_mem Γ I ψ t h hI s) (e (t s))

end Frob

section Red

variable [Finite Λ] [Fintype Gf] {ϖ : Λ} (hsurj : Function.Surjective (algebraMap Λ Λ'))
  (ht : algebraMap Λ Λ' ϖ = 0) (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = ϖ * s) {l N : ℕ}
  (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

include hsurj hΛ hall hπ in
theorem red1_surjective : Function.Surjective (red1 Λ Λ' π Γ (S := S)) := fun p => by
  obtain ⟨c, hc⟩ := redZ1_surjective π hsurj hΛ Γ hall hπ p.1
  choose a ha using fun s => redA_surjective (Gf := Gf) hsurj (p.2 s)
  exact ⟨(c, a), Prod.ext hc (funext ha)⟩

include hk hΛ hall hπ in
theorem red1_ker (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (hp : red1 Λ Λ' π Γ p = 0) :
    ∃ q, p = ϖ • q := by
  obtain ⟨d, hd⟩ := redZ1_ker π hk hΛ Γ hall hπ p.1 (congrArg Prod.fst hp)
  choose b hb using fun s => redA_ker hk (p.2 s) (congrFun (congrArg Prod.snd hp) s)
  exact ⟨(d, b), Prod.ext hd (funext hb)⟩

include hsurj hΛ hallI hπ in
theorem red2_surjective : Function.Surjective (red2 Λ Λ' π Γ I) := fun e => by
  choose c hc using fun s => redZ1_surjective π hsurj hΛ (Γ ⊓ I s) (hallI s) hπ (e s)
  exact ⟨c, funext hc⟩

include hk hΛ hallI hπ in
theorem red2_ker (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (he : red2 Λ Λ' π Γ I e = 0) : ∃ q, e = ϖ • q := by
  choose d hd using fun s => redZ1_ker π hk hΛ (Γ ⊓ I s) (hallI s) hπ (e s) (congrFun he s)
  exact ⟨d, funext hd⟩

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

end Red

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_KumPicDiv =====
section

/-!
# S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`

CB1 (`CoreB.divisible_Aℓ`) divides only the `l`-primary part. Here:
* `exists_pow_smul_of_torsion` (generic): in an abelian group whose `l`-primary part is `l`-divisible, a torsion element
  of a subgroup `H ⊇ G[l^∞]` is `l^n`-divisible inside `H`;
* `ofBar_mem_fixedBar`, **`torsion_PicBar0`**: `Pic⁰(X̄)` is torsion (each class lies in the finite `Pic⁰(X̄)^(π^m)`);
* **`pic0Bar_divisible`**, **`pic0K_divisible`**: every class of `Pic⁰(X̄)`, resp. of `Pic⁰(F̄ / k̄)`, is `l^n`-divisible.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.CupDuality

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G]

end Gen

section Pic

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- A level-`(j+1)!` class is fixed by `π ^ (j+1)!`. -/
theorem ofBar_mem_fixedBar (j : ℕ) (y : PicL Fq F Ω j) : ofBar Ω hk j y ∈ fixedBar Ω hk (lev j) := by
  have : Fact (lev j ∣ lev j) := ⟨dvd_rfl⟩
  have h := frobN_iterate_conNN (n := lev j) (N := lev j) hk y
  rw [conNN_self hk (lev j) y] at h
  rw [mem_fixedBar, piBar_iterate_of, h]

end Pic

end RamanujanPetersson.CupDuality


end


