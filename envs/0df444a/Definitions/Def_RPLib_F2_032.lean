-- Prove2me | Definitions.Def_RPLib_F2_032
-- name    : RPLib_F2_032
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T11:57:30.057475+00:00
-- url     : https://prove2.me/theorems/e189596b-5c68-446f-a741-7d50c2105167
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 032 of 70
-- statement:
--   File 032 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
--   * `S4.Def_RP_Lefschetz_ConeComp`: S4-Lefschetz, L3a: composition law for the cone Frobenius
--   * `S4.Def_RP_Lefschetz_H2Tot`: S4-Lefschetz, L3e2c2: `H²K` of the total cone is `A_Γ`, with block projections and twisted Frobenius
--   * `S4.Def_RP_Lefschetz_AGTrace`: S4-Lefschetz, L3e2c3: the block trace on `A_Γ = Λ[Gf]_Γ`
--   * `S4.Def_RP_Lefschetz_ShapFrob`: S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius
--   * `S4.Def_RP_Lefschetz_AmbSub`: S4-Lefschetz, L4i part 1: Shapiro with Frobenius inside an ambient subgroup `G' ≤ G`
--   * `S4.Def_RP_Lefschetz_ConstExt`: S4-Lefschetz L4a: a function field over its full constant field
--   * `S4.Def_RP_Lefschetz_UnrTower`: S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure
--   * `S4.Def_RP_Lefschetz_RinfKc`: S4-Lefschetz L4b part 2: the rings `R_fin`, `R_∞` do not see the constant field
--   * `S4.Def_RP_Lefschetz_UnrExt`: S4-Lefschetz L4d (part 1): `K_U` is unramified over a finite subextension `E ⊆ K_U`
--   * `S4.Def_RP_Lefschetz_UnrFix`: S4-Lefschetz L4d (part 2a): helpers for "unramified over `E ⊆ K_U` implies inside `K_U`"
--   * `S4.Def_RP_Lefschetz_UnrMax`: S4-Lefschetz L4c+d (part 2b): `K_U` is also the maximal unramified extension of a finite `E ⊆ K_U`
--   * `S4.Def_RP_Lefschetz_Pi1Sub`: S4-Lefschetz L4e: `π₁` of a finite subextension `E ⊆ K_U` is the subgroup of `π₁(K)` fixing `E`
--   * `S4.Def_RP_Lefschetz_Pi1Geo`: S4-Lefschetz L4f: geometric `π₁` and Frobenius lifts under `theta` and under a change of `A`
--   * `S4.Def_RP_Lefschetz_ChartE`: S4-Lefschetz L4g part 1: `K_U` of a finite subcover and the group map to `π₁(U)`
--   * `S4.Def_RP_Lefschetz_ChartE2`: S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover
--   * `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
--   * `S4.Def_RP_Lefschetz_BlockE`: S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart
--   * `S4.Def_RP_Lefschetz_PtLift`: S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_005
import Definitions.Def_RPLib_F2_023
import Definitions.Def_RPLib_F2_025

/-!
# Ramanujan-Petersson curve library (flat edition), file 032 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
* `S4.Def_RP_Lefschetz_ConeComp`: S4-Lefschetz, L3a: composition law for the cone Frobenius
* `S4.Def_RP_Lefschetz_H2Tot`: S4-Lefschetz, L3e2c2: `H²K` of the total cone is `A_Γ`, with block projections and twisted Frobenius
* `S4.Def_RP_Lefschetz_AGTrace`: S4-Lefschetz, L3e2c3: the block trace on `A_Γ = Λ[Gf]_Γ`
* `S4.Def_RP_Lefschetz_ShapFrob`: S4-Lefschetz, L4h part 2: Shapiro for `H¹_c` commutes with Frobenius; ambient transport of Frobenius
* `S4.Def_RP_Lefschetz_AmbSub`: S4-Lefschetz, L4i part 1: Shapiro with Frobenius inside an ambient subgroup `G' ≤ G`
* `S4.Def_RP_Lefschetz_ConstExt`: S4-Lefschetz L4a: a function field over its full constant field
* `S4.Def_RP_Lefschetz_UnrTower`: S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure
* `S4.Def_RP_Lefschetz_RinfKc`: S4-Lefschetz L4b part 2: the rings `R_fin`, `R_∞` do not see the constant field
* `S4.Def_RP_Lefschetz_UnrExt`: S4-Lefschetz L4d (part 1): `K_U` is unramified over a finite subextension `E ⊆ K_U`
* `S4.Def_RP_Lefschetz_UnrFix`: S4-Lefschetz L4d (part 2a): helpers for "unramified over `E ⊆ K_U` implies inside `K_U`"
* `S4.Def_RP_Lefschetz_UnrMax`: S4-Lefschetz L4c+d (part 2b): `K_U` is also the maximal unramified extension of a finite `E ⊆ K_U`
* `S4.Def_RP_Lefschetz_Pi1Sub`: S4-Lefschetz L4e: `π₁` of a finite subextension `E ⊆ K_U` is the subgroup of `π₁(K)` fixing `E`
* `S4.Def_RP_Lefschetz_Pi1Geo`: S4-Lefschetz L4f: geometric `π₁` and Frobenius lifts under `theta` and under a change of `A`
* `S4.Def_RP_Lefschetz_ChartE`: S4-Lefschetz L4g part 1: `K_U` of a finite subcover and the group map to `π₁(U)`
* `S4.Def_RP_Lefschetz_ChartE2`: S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover
* `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
* `S4.Def_RP_Lefschetz_BlockE`: S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart
* `S4.Def_RP_Lefschetz_PtLift`: S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers
-/

set_option autoImplicit false

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

/-! ## Composition -/

/-! ## Inner twists act trivially -/

theorem bdryCompat_mul_geo {ψ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ τ h) (γ0 : Γ) :
    BdryCompat Γ I (ψ * γ0) τ (fun s => γ0⁻¹ * h s) := by
  have h1 := bdryCompat_comp Γ I hI (bdryCompat_inner Γ I γ0)
  have e : (fun s => conjΓ Γ (γ0 : G) (h s) * γ0⁻¹) = fun s => γ0⁻¹ * h s := by
    funext s
    ext
    simp [mul_assoc]
  rw [e] at h1
  exact h1

/-- `F(ψ γ0) = F(ψ)` on `H¹_c` for `γ0 ∈ Γ`. -/
theorem frobH1c_mul_geo {ψ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ τ h) (γ0 : Γ)
    (hI' : BdryCompat Γ I (ψ * γ0) τ (fun s => γ0⁻¹ * h s)) :
    frobH1c ρ Γ I (ψ * γ0) τ (fun s => γ0⁻¹ * h s) hI' = frobH1c ρ Γ I ψ τ h hI := by
  rw [← LinearMap.comp_id (frobH1c ρ Γ I ψ τ h hI), ← frobH1c_inner ρ Γ I γ0, frobH1c_comp]
  refine frobH1c_congr ρ Γ I rfl rfl (funext fun s => ?_) _ _
  ext
  simp [mul_assoc]

/-! ## Powers -/

theorem bdryCompat_pow {ψ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ τ h) (m : ℕ) :
    BdryCompat Γ I (ψ ^ m) τ^[m] (hpow Γ ψ τ h m) := by
  induction m with
  | zero =>
    intro s g hg
    simpa [hpow] using hg
  | succ m ih =>
    have h1 := bdryCompat_comp Γ I hI ih
    rw [← pow_succ'] at h1
    exact h1

theorem twistc_pow_zero (ψ : G) (τ : S → S) (h : S → Γ) {p : (Γ → M) × (S → M)} (hp : p.1 ∈ Z1 ρ Γ) :
    twistc ρ Γ (ψ ^ 0) τ^[0] (hpow Γ ψ τ h 0) p = p := by
  refine Prod.ext (funext fun g => ?_) (funext fun s => ?_)
  · simp only [twistc_fst, twist_apply, pow_zero, conjΓ_one', map_one, Module.End.one_apply]
  · simp [twistc_snd, hpow, Z1_one ρ Γ hp]

/-! ## Changing the correcting elements inside the inertia -/

/-! ## `H²_c` -/

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ConeComp =====
section

/-!
# S4-Lefschetz, L3a: composition law for the cone Frobenius

Generic (any topological group `G`, normal `Γ`, boundary subgroups `I`, any representation `ρ`):
* `conjMap_comp_eq`, `conjMap_one_eq`: `conjMap x ∘ conjMap y = conjMap (x y)`, `conjMap 1 = id`;
* `frob1_comp`, `frob2_comp`, `frobPC_comp`: the composite of two cone Frobenii is the cone Frobenius of the product,
  with the correcting elements `s ↦ ψ'⁻¹ h_s ψ' · h'_{t s}` of `FrobCong.twistc_comp`;
* `frobPC_pow`: `frobPC(ψ, t, h)^m = frobPC(ψ^m, t^[m], hpow m)` on every term of the perfect complex.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M)

theorem conjMap_comp_eq {Δ Δ' Δ'' : Subgroup G} {x y z : G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ')
    (hy : ∀ g ∈ Δ', y⁻¹ * g * y ∈ Δ'') (hz : ∀ g ∈ Δ, z⁻¹ * g * z ∈ Δ'') (hxyz : z = x * y) (c : Z1 ρ Δ'') :
    conjMap ρ x hx (conjMap ρ y hy c) = conjMap ρ z hz c := by
  subst hxyz
  refine Subtype.ext (funext fun g => ?_)
  have e : conjSub y hy (conjSub x hx g) = conjSub (x * y) hz g := Subtype.ext (by
    simp only [conjSub_val]
    group)
  show ρ x (ρ y ((c : Δ'' → M) (conjSub y hy (conjSub x hx g)))) = ρ (x * y) ((c : Δ'' → M) (conjSub (x * y) hz g))
  rw [e, map_mul, Module.End.mul_apply]

theorem conjMap_one_eq {Δ : Subgroup G} {x : G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ) (h1 : x = 1) (c : Z1 ρ Δ) :
    conjMap ρ x hx c = c := by
  subst h1
  refine Subtype.ext (funext fun g => ?_)
  have e : conjSub (1 : G) hx g = g := Subtype.ext (by simp only [conjSub_val]; group)
  show ρ 1 ((c : Δ → M) (conjSub (1 : G) hx g)) = (c : Δ → M) g
  rw [e, map_one, Module.End.one_apply]

variable (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

theorem frob1_comp (ψ ψ' : G) (t t' : S → S) (h h' : S → Γ) :
    frob1 ρ Γ ψ t h ∘ₗ frob1 ρ Γ ψ' t' h' =
      frob1 ρ Γ (ψ * ψ') (t' ∘ t) (fun s => conjΓ Γ ψ' (h s) * h' (t s)) := by
  refine LinearMap.ext fun p => ?_
  have e := twistc_comp ρ Γ ψ ψ' t t' h h' (p := (((p.1 : Z1 ρ Γ) : Γ → M), p.2)) p.1.2
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  exact Prod.ext (Subtype.ext e1) e2

theorem frob1_pow_zero (ψ : G) (t : S → S) (h : S → Γ) :
    frob1 ρ Γ (ψ ^ 0) t^[0] (hpow Γ ψ t h 0) = LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  have e := twistc_pow_zero ρ Γ ψ t h (p := (((p.1 : Z1 ρ Γ) : Γ → M), p.2)) p.1.2
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  exact Prod.ext (Subtype.ext e1) e2

theorem frob2_comp {ψ ψ' : G} {t t' : S → S} {h h' : S → Γ} (hI : BdryCompat Γ I ψ t h)
    (hI' : BdryCompat Γ I ψ' t' h') :
    frob2 ρ Γ I ψ t h hI ∘ₗ frob2 ρ Γ I ψ' t' h' hI' =
      frob2 ρ Γ I (ψ * ψ') (t' ∘ t) (fun s => conjΓ Γ ψ' (h s) * h' (t s)) (bdryCompat_comp Γ I hI hI') := by
  refine LinearMap.ext fun e => funext fun s => ?_
  exact conjMap_comp_eq ρ _ _ _ (by
    show ψ * ψ' * ((ψ'⁻¹ * (h s : G) * ψ') * (h' (t s) : G)) = ψ * (h s : G) * (ψ' * (h' (t s) : G))
    group) _

theorem frob2_pow_zero {ψ : G} {t : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ t h) :
    frob2 ρ Γ I (ψ ^ 0) t^[0] (hpow Γ ψ t h 0) (bdryCompat_pow Γ I hI 0) = LinearMap.id := by
  refine LinearMap.ext fun e => funext fun s => ?_
  exact conjMap_one_eq ρ _ (by
    show ψ ^ 0 * ((1 : Γ) : G) = 1
    simp) _

end Gen

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)

theorem frobPC_congr {ψ ψ' : G} {t t' : S → S} {h h' : S → Γ} (hψ : ψ = ψ') (ht : t = t') (hh : h = h')
    (hI : BdryCompat Γ I ψ t h) (hI' : BdryCompat Γ I ψ' t' h') (i : ℕ) :
    frobPC Λ π Γ I ψ t h hI i = frobPC Λ π Γ I ψ' t' h' hI' i := by
  subst hψ ht hh
  rfl

theorem frobPC_comp {ψ ψ' : G} {t t' : S → S} {h h' : S → Γ} (hI : BdryCompat Γ I ψ t h)
    (hI' : BdryCompat Γ I ψ' t' h') :
    ∀ i, frobPC Λ π Γ I ψ t h hI i ∘ₗ frobPC Λ π Γ I ψ' t' h' hI' i =
      frobPC Λ π Γ I (ψ * ψ') (t' ∘ t) (fun s => conjΓ Γ ψ' (h s) * h' (t s)) (bdryCompat_comp Γ I hI hI') i
  | 0 => by
    show regRep Λ π ψ ∘ₗ regRep Λ π ψ' = regRep Λ π (ψ * ψ')
    rw [map_mul]
    rfl
  | 1 => frob1_comp (regRep Λ π) Γ ψ ψ' t t' h h'
  | 2 => frob2_comp (regRep Λ π) Γ I hI hI'
  | _ + 3 => LinearMap.ext fun _ => rfl

theorem frobPC_pow_zero {ψ : G} {t : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ t h) :
    ∀ i, frobPC Λ π Γ I (ψ ^ 0) t^[0] (hpow Γ ψ t h 0) (bdryCompat_pow Γ I hI 0) i = LinearMap.id
  | 0 => by
    show regRep Λ π (ψ ^ 0) = LinearMap.id
    rw [pow_zero, map_one]
    rfl
  | 1 => frob1_pow_zero (regRep Λ π) Γ ψ t h
  | 2 => frob2_pow_zero (regRep Λ π) Γ I hI
  | _ + 3 => LinearMap.ext fun _ => rfl

/-- **L3a**: `frobPC(ψ, t, h)^m = frobPC(ψ^m, t^[m], hpow m)` termwise. -/
theorem frobPC_pow {ψ : G} {t : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ t h) (m : ℕ) (i : ℕ) :
    frobPC Λ π Γ I ψ t h hI i ^ m =
      frobPC Λ π Γ I (ψ ^ m) t^[m] (hpow Γ ψ t h m) (bdryCompat_pow Γ I hI m) i := by
  induction m with
  | zero => rw [pow_zero, frobPC_pow_zero π Γ I hI i]; rfl
  | succ m ih =>
    rw [pow_succ' (frobPC Λ π Γ I ψ t h hI i) m, ih, Module.End.mul_eq_comp, frobPC_comp π Γ I hI]
    exact frobPC_congr π Γ I (pow_succ' ψ m).symm rfl rfl _ _ i

end Model

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_H2Tot =====
section

/-!
# S4-Lefschetz, L3e2c2: `H²K` of the total cone is `A_Γ`, with block projections and twisted Frobenius

Given a `ResHyp` `H` (E4S), `H.cokResEquiv : H²K(PC) = coker d¹ ≃ A_Γ = Λ[Gf]_Γ` carries
* the block projection `h2PB ω` to `eBΓ ω` (`eB ω` on `A_Γ`): `cok_h2PB` (via `h2PB_Psi`, checked on `resQ`);
* the twisted Frobenius `h2Op γ ψ^m` to `rRepΓ γ⁻¹ ∘ (c • lftΓ ψ)^m`: `cokE_h2R`, `h2Op_eq`, `frobH2K_pow`,
  `cokE_frob_pow` (under the hypotheses of `cokResEquiv_frob`; `cokE` = `cokResEquiv` on `H2K`);
* headline `trace_h2_tot`: `Tr(h2PB ω ∘ h2Op γ ψ^m | H²K(PC)) = Tr(eBΓ ω ∘ rRepΓ γ⁻¹ ∘ (c • lftΓ ψ)^m | A_Γ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx MonoidAlgebra Representation

section Tot

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (hπ : IsOpen (π.ker : Set G)) (H : ResHyp Λ π Γ I)

variable (Λ π Γ) in
/-- `eB ω` on `A_Γ = Λ[Gf]_Γ`. -/
def eBΓ (ω : Blk (Γ.map π)) : AΓ (Λ := Λ) π Γ →ₗ[Λ] AΓ (Λ := Λ) π Γ :=
  Coinvariants.lift _ (Coinvariants.mk _ ∘ₗ eB (Γ.map π) ω) fun g => LinearMap.ext fun a => by
    show Coinvariants.mk _ (eB (Γ.map π) ω (regRep Λ π (g : G) a)) = Coinvariants.mk _ (eB (Γ.map π) ω a)
    rw [eB_regRep π Γ ω g.2 a]
    exact Coinvariants.mk_self_apply ((regRep Λ π).comp Γ.subtype) g (eB (Γ.map π) ω a)

theorem eBΓ_mk (ω : Blk (Γ.map π)) (a : MonoidAlgebra Λ Gf) :
    eBΓ Λ π Γ ω (Coinvariants.mk _ a) = Coinvariants.mk _ (eB (Γ.map π) ω a) :=
  rfl

theorem eB_nrmS (D : Subgroup Gf) [Fintype D] (hD : D ≤ Γ.map π) (ω : Blk (Γ.map π)) (F : MonoidAlgebra Λ Gf) :
    eB (Γ.map π) ω (nrmS Λ D * F) = nrmS Λ D * eB (Γ.map π) ω F := by
  simp only [nrmS, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun d _ => eB_left (Γ.map π) (hD d.2) ω F

theorem h2PB_Psi (ω : Blk (Γ.map π)) (x : AΓ (Λ := Λ) π Γ) :
    h2PB Λ π Γ I hπ ω (H.Psi hπ x) = H.Psi hπ (eBΓ Λ π Γ ω x) := by
  induction x using Coinvariants.induction_on with
  | h w =>
    apply H.resQ_injective hπ
    have e1 : H.resQ hπ (h2PB Λ π Γ I hπ ω (H.Psi hπ (Coinvariants.mk _ w))) =
        ∑ s, H.Ns s * eB (Γ.map π) ω (((Pi.single (M := fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0 (H.epsL w) s :
          Z1 (regRep Λ π) (Γ ⊓ I s)) : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s)) := rfl
    have e2 : H.resQ hπ (H.Psi hπ (eBΓ Λ π Γ ω (Coinvariants.mk _ w))) =
        ∑ s, H.Ns s * (((Pi.single (M := fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0
          (H.epsL (eB (Γ.map π) ω w)) s : Z1 (regRep Λ π) (Γ ⊓ I s)) : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s)) :=
      rfl
    rw [e1, e2, Finset.sum_eq_single H.s0, Finset.sum_eq_single H.s0]
    · rw [Pi.single_eq_same, Pi.single_eq_same, ResHyp.epsL_apply, ResHyp.epsL_apply, (H.Lex' H.s0).choose_spec,
        eB_nrmS _ (Subgroup.map_mono inf_le_left)]
    all_goals first
      | (intro s _ hs; rw [Pi.single_eq_of_ne hs]; simp)
      | (intro hs; exact absurd (Finset.mem_univ _) hs)

/-- **`cokResEquiv` carries `h2PB ω` to `eBΓ ω`.** -/
theorem cok_h2PB (ω : Blk (Γ.map π)) (y : H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :
    H.cokResEquiv hπ (h2PB Λ π Γ I hπ ω y) = eBΓ Λ π Γ ω (H.cokResEquiv hπ y) := by
  obtain ⟨x, rfl⟩ := (H.cokResEquiv hπ).symm.surjective y
  rw [LinearEquiv.apply_symm_apply, ResHyp.cokResEquiv_symm_apply, h2PB_Psi, ← ResHyp.cokResEquiv_symm_apply,
    LinearEquiv.apply_symm_apply]

section Op

variable (γ : Gf) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (c : Λ)
  (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
  (ht : Function.Bijective t)
  (hTW : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I (t s))),
    (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (H.sg s)) =
      c • (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (H.sg (t s)))

/-- `cokResEquiv` with domain `H2K` of the total cone. -/
def cokE : H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ) ≃ₗ[Λ] AΓ (Λ := Λ) π Γ := H.cokResEquiv hπ

theorem cokE_h2PB (ω : Blk (Γ.map π)) (y : H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :
    cokE hπ H (h2PB Λ π Γ I hπ ω y) = eBΓ Λ π Γ ω (cokE hπ H y) :=
  cok_h2PB hπ H ω y

variable (Λ π Γ I) in
/-- `ρPC γ⁻¹` on `H²K` of the total cone. -/
def h2R : Module.End Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :=
  h2Map (regRep Λ π) (regRep Λ π) Γ Γ I I (isOpen_regRep_ker π hπ) (isOpen_regRep_ker π hπ)
    (ρPC Λ π Γ I 1 γ⁻¹) (ρPC Λ π Γ I 2 γ⁻¹) fun p => LinearMap.congr_fun (d1_equiv π Γ I hπ γ⁻¹) p

theorem cokE_h2R (y : H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :
    cokE hπ H (h2R Λ π Γ I hπ γ y) = rRepΓ π Γ γ⁻¹ (cokE hπ H y) := by
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact H.cokResEquiv_equiv hπ γ⁻¹ (Submodule.Quotient.mk e)

theorem h2Op_eq :
    h2Op Λ π Γ I hπ γ ψ t h hI = h2R Λ π Γ I hπ γ ∘ₗ frobH2K (regRep Λ π) Γ I ψ t h (isOpen_regRep_ker π hπ) hI :=
  Submodule.linearMap_qext _ (LinearMap.ext fun _ => rfl)

theorem frob2_pow (m : ℕ) :
    frob2 (regRep Λ π) Γ I ψ t h hI ^ m =
      frob2 (regRep Λ π) Γ I (ψ ^ m) t^[m] (hpow Γ ψ t h m) (bdryCompat_pow Γ I hI m) :=
  frobPC_pow π Γ I hI m 2

theorem frobH2K_pow (m : ℕ) :
    frobH2K (regRep Λ π) Γ I ψ t h (isOpen_regRep_ker π hπ) hI ^ m =
      frobH2K (regRep Λ π) Γ I (ψ ^ m) t^[m] (hpow Γ ψ t h m) (isOpen_regRep_ker π hπ) (bdryCompat_pow Γ I hI m) := by
  unfold frobH2K
  rw [← Submodule.mapQ_pow]
  exact Submodule.linearMap_qext _ (LinearMap.ext fun e =>
    congrArg (Submodule.Quotient.mk (p := LinearMap.range (cx1 (regRep Λ π) Γ I (isOpen_regRep_ker π hπ))))
      (LinearMap.congr_fun (frob2_pow (Λ := Λ) (π := π) ψ t h hI m) e))

include hD ht hTW in
theorem cokE_frob (y : H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :
    cokE hπ H (frobH2K (regRep Λ π) Γ I ψ t h (isOpen_regRep_ker π hπ) hI y) = (c • lftΓ π Γ ψ) (cokE hπ H y) := by
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact H.cokResEquiv_frob hπ ψ t h hI c hD ht hTW e

include hD ht hTW in
theorem cokE_frob_pow (m : ℕ) (y : H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :
    cokE hπ H ((frobH2K (regRep Λ π) Γ I ψ t h (isOpen_regRep_ker π hπ) hI ^ m) y) =
      ((c • lftΓ π Γ ψ) ^ m) (cokE hπ H y) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, cokE_frob hπ H ψ t h hI c hD ht hTW, ih]

include hD ht hTW in
/-- **Trace on the total `H²`**: `Tr(h2PB ω ∘ h2Op γ ψ^m | H²K(PC)) = Tr(eBΓ ω ∘ rRepΓ γ⁻¹ ∘ (c • lftΓ ψ)^m | A_Γ)`. -/
theorem trace_h2_tot (ω : Blk (Γ.map π)) (m : ℕ) :
    LinearMap.trace Λ _
        (h2PB Λ π Γ I hπ ω * h2Op Λ π Γ I hπ γ (ψ ^ m) t^[m] (hpow Γ ψ t h m) (bdryCompat_pow Γ I hI m)) =
      LinearMap.trace Λ (AΓ (Λ := Λ) π Γ) (eBΓ Λ π Γ ω * (rRepΓ π Γ γ⁻¹ * (c • lftΓ π Γ ψ) ^ m)) :=
  trace_eq_of_intertwine (cokE hπ H) _ _ fun y => by
    show _ = eBΓ Λ π Γ ω (rRepΓ π Γ γ⁻¹ (((c • lftΓ π Γ ψ) ^ m) (cokE hπ H y)))
    rw [Module.End.mul_apply, h2Op_eq, LinearMap.comp_apply, ← frobH2K_pow hπ ψ t h hI m, cokE_h2PB, cokE_h2R,
      cokE_frob_pow hπ H ψ t h hI c hD ht hTW m]

end Op

end Tot

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_AGTrace =====
section

/-!
# S4-Lefschetz, L3e2c3: the block trace on `A_Γ = Λ[Gf]_Γ`

* `qΓ ω : A_Γ → Λ`, `[F] ↦ Σ_{x ∈ ω} F_x` and `jΓ a : Λ → A_Γ`, `r ↦ r [a]`: `qΓ ω ∘ jΓ a = id` and
  `eBΓ ω = jΓ a ∘ qΓ ω` for `a ∈ ω` (`[x] = [a]` in `A_Γ` for `x, a` in one block: `mk_single_eq`).
* `aΓEquiv : A_Γ ≃ (Blk (π Γ) → Λ)`, so `A_Γ` is free and finite; `H²K` of the total cone is free and finite
  (`cokE`), and so is the retract `H²K` of the `G'`-cone (`h2Q ∘ h2J = id`, free over a local ring).
* `trace_aΓ_blk`: for `π(ψ^m) a γ a⁻¹ ∈ π(Γ)`, `Tr(eBΓ [a] ∘ rRepΓ γ⁻¹ ∘ (c • lftΓ ψ)^m | A_Γ) = c^m`;
  with `trace_h2_tot`: `trace_h2_tot_blk`, `Tr(h2PB [a] ∘ h2Op γ ψ^m | H²K) = c^m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx MonoidAlgebra Representation

section TotC

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf]

/-- A representative of each block. -/
def bRep (P : Subgroup Gf) (ω : Blk P) : Gf := (blk_surjective P ω).choose

theorem blk_bRep (P : Subgroup Gf) (ω : Blk P) : blk P (bRep P ω) = ω := (blk_surjective P ω).choose_spec

theorem totC_eB_single (P : Subgroup Gf) (ω : Blk P) (x : Gf) (r : Λ) :
    totC Λ Gf (eB P ω (single x r)) = if blk P x = ω then r else 0 := by
  rw [eB_single]
  split_ifs
  · exact totC_single x r
  · exact map_zero _

end TotC

section Blocks

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] [Fintype (Γ.map π)]

variable (Λ) in
/-- The block sum `[F] ↦ Σ_{x ∈ ω} F_x` on `A_Γ`. -/
def qΓ (ω : Blk (Γ.map π)) : AΓ (Λ := Λ) π Γ →ₗ[Λ] Λ :=
  Coinvariants.lift _ (totC Λ Gf ∘ₗ eB (Γ.map π) ω) fun g => LinearMap.ext fun F => by
    show totC Λ Gf (eB (Γ.map π) ω (single (π (g : G)) 1 * F)) = totC Λ Gf (eB (Γ.map π) ω F)
    rw [eB_left (Γ.map π) (Subgroup.mem_map_of_mem π g.2) ω F, totC_single_mul]

theorem qΓ_mk (ω : Blk (Γ.map π)) (F : MonoidAlgebra Λ Gf) :
    qΓ Λ π Γ ω (Coinvariants.mk _ F) = totC Λ Gf (eB (Γ.map π) ω F) := rfl

variable (Λ) in
/-- `r ↦ r [a]`. -/
def jΓ (a : Gf) : Λ →ₗ[Λ] AΓ (Λ := Λ) π Γ :=
  LinearMap.toSpanSingleton Λ _ (Coinvariants.mk _ (single a 1))

theorem jΓ_apply (a : Gf) (r : Λ) : jΓ Λ π Γ a r = r • Coinvariants.mk _ (single a 1) := rfl

theorem qΓ_jΓ_apply (a : Gf) (ω : Blk (Γ.map π)) (r : Λ) :
    qΓ Λ π Γ ω (jΓ Λ π Γ a r) = if blk (Γ.map π) a = ω then r else 0 := by
  rw [jΓ_apply, map_smul, qΓ_mk, totC_eB_single]
  split_ifs
  · rw [smul_eq_mul, mul_one]
  · rw [smul_zero]

theorem qΓ_jΓ {a : Gf} {ω : Blk (Γ.map π)} (h : blk (Γ.map π) a = ω) :
    qΓ Λ π Γ ω ∘ₗ jΓ Λ π Γ a = LinearMap.id :=
  LinearMap.ext fun r => by rw [LinearMap.comp_apply, qΓ_jΓ_apply, if_pos h, LinearMap.id_apply]

/-- `[x] = [a]` in `A_Γ` when `x` and `a` lie in the same block. -/
theorem mk_single_eq {a x : Gf} (h : blk (Γ.map π) x = blk (Γ.map π) a) (r : Λ) :
    (Coinvariants.mk ((regRep Λ π).comp Γ.subtype) (single x r) : AΓ (Λ := Λ) π Γ) =
      Coinvariants.mk _ (single a r) := by
  obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 ((blk_eq_iff (Γ.map π)).1 h.symm)
  have e : single x r = ((regRep Λ π).comp Γ.subtype) ⟨g, hg⟩ (single a r) := by
    show single x r = single (π g) 1 * single a r
    rw [single_mul_single, one_mul, hgx, inv_mul_cancel_right]
  rw [e]
  exact Coinvariants.mk_self_apply _ _ _

theorem eBΓ_eq_jΓ_qΓ {a : Gf} {ω : Blk (Γ.map π)} (h : blk (Γ.map π) a = ω) :
    eBΓ Λ π Γ ω = jΓ Λ π Γ a ∘ₗ qΓ Λ π Γ ω := by
  refine Coinvariants.hom_ext (LinearMap.ext fun F => ?_)
  simp only [LinearMap.comp_apply]
  rw [eBΓ_mk, qΓ_mk, jΓ_apply]
  induction F using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, zero_smul]
  | add F F' hF hF' => rw [map_add, map_add, map_add, hF, hF', add_smul]
  | single x r =>
    rw [totC_eB_single, eB_single]
    by_cases hx : blk (Γ.map π) x = ω
    · have e : single a r = r • single a (1 : Λ) := by rw [smul_single', mul_one]
      rw [if_pos hx, if_pos hx, mk_single_eq π Γ (hx.trans h.symm), e, map_smul]
    · rw [if_neg hx, if_neg hx, map_zero, zero_smul]

theorem sum_eBΓ : ∑ ω, eBΓ Λ π Γ ω = LinearMap.id := by
  refine Coinvariants.hom_ext (LinearMap.ext fun F => ?_)
  have hs := LinearMap.congr_fun (sum_eB (Λ := Λ) (Γ.map π)) F
  rw [LinearMap.sum_apply, Module.End.one_apply] at hs
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, eBΓ_mk, LinearMap.id_apply]
  conv_rhs => rw [← hs]
  rw [map_sum]

variable (Λ) in
/-- `A_Γ ≃ (Blk (π Γ) → Λ)`, `[F] ↦ (ω ↦ Σ_{x ∈ ω} F_x)`. -/
def aΓEquiv : AΓ (Λ := Λ) π Γ ≃ₗ[Λ] (Blk (Γ.map π) → Λ) :=
  LinearEquiv.ofLinearMap (LinearMap.pi fun ω => qΓ Λ π Γ ω)
    (∑ ω, jΓ Λ π Γ (bRep _ ω) ∘ₗ LinearMap.proj ω)
    (LinearMap.ext fun v => funext fun ω' => by
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, map_sum,
        LinearMap.id_apply]
      rw [Fintype.sum_eq_single ω', qΓ_jΓ_apply, blk_bRep, if_pos rfl]
      intro ω hω
      rw [qΓ_jΓ_apply, blk_bRep, if_neg hω])
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        LinearMap.id_apply]
      have hs := LinearMap.congr_fun (sum_eBΓ (Λ := Λ) π Γ) x
      rw [LinearMap.sum_apply, LinearMap.id_apply] at hs
      conv_rhs => rw [← hs]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [eBΓ_eq_jΓ_qΓ (Λ := Λ) π Γ (blk_bRep _ ω), LinearMap.comp_apply])

instance aΓ_free : Module.Free Λ (AΓ (Λ := Λ) π Γ) := Module.Free.of_equiv (aΓEquiv Λ π Γ).symm

instance aΓ_finite : Module.Finite Λ (AΓ (Λ := Λ) π Γ) := Module.Finite.equiv (aΓEquiv Λ π Γ).symm

end Blocks

section Trace

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] [Fintype (Γ.map π)]

theorem lftΓ_one : lftΓ π Γ (1 : G) = (1 : Module.End Λ (AΓ (Λ := Λ) π Γ)) :=
  Coinvariants.hom_ext (LinearMap.ext fun F => by
    show Coinvariants.mk _ (single (π 1) (1 : Λ) * F) = Coinvariants.mk _ F
    rw [π.map_one, ← one_def, one_mul])

theorem lftΓ_mul (x y : G) :
    lftΓ π Γ (x * y) = (lftΓ π Γ x * lftΓ π Γ y : Module.End Λ (AΓ (Λ := Λ) π Γ)) :=
  Coinvariants.hom_ext (LinearMap.ext fun F => by
    show Coinvariants.mk _ (single (π (x * y)) (1 : Λ) * F) =
      Coinvariants.mk _ (single (π x) (1 : Λ) * (single (π y) 1 * F))
    rw [π.map_mul, ← mul_assoc, single_mul_single, one_mul])

theorem smul_lftΓ_pow (c : Λ) (ψ : G) (m : ℕ) :
    (c • lftΓ π Γ ψ : Module.End Λ (AΓ (Λ := Λ) π Γ)) ^ m = c ^ m • lftΓ π Γ (ψ ^ m) := by
  induction m with
  | zero => simp only [pow_zero, one_smul, lftΓ_one]
  | succ m ih => rw [pow_succ, ih, pow_succ, pow_succ, lftΓ_mul, smul_mul_smul_comm]

/-- On a block fixed by `[x] ↦ [π(ψ) x γ]`, the block sum intertwines `rRepΓ γ⁻¹ ∘ (c • lftΓ ψ)` with `c`. -/
theorem qΓ_op (ψ : G) (γ a : Gf) (hfix : π ψ * a * γ * a⁻¹ ∈ Γ.map π) (c : Λ) :
    qΓ Λ π Γ (blk (Γ.map π) a) ∘ₗ (rRepΓ π Γ γ⁻¹ * (c • lftΓ π Γ ψ)) =
      (c • LinearMap.id) ∘ₗ qΓ Λ π Γ (blk (Γ.map π) a) := by
  have hu : π ψ ∈ Subgroup.normalizer ((Γ.map π : Subgroup Gf) : Set Gf) := map_mem_normalizer (Γ := Γ) π ψ
  have hω : blkShift (Γ.map π) (π ψ) γ hu (blk (Γ.map π) a) = blk (Γ.map π) a :=
    (blkShift_fixed_iff _ _ _ hu a).2 hfix
  refine Coinvariants.hom_ext (LinearMap.ext fun F => ?_)
  simp only [LinearMap.comp_apply, Module.End.mul_apply, LinearMap.smul_apply, lftΓ_mk, LinearMap.id_apply]
  rw [map_smul, map_smul, rRepΓ_mk, qΓ_mk, qΓ_mk, inv_inv]
  have key := eB_shift (Γ.map π) (π ψ) γ hu (blk (Γ.map π) a) F
  rw [hω] at key
  rw [key, totC_mul_single, totC_single_mul]

theorem trace_blk_op (ψ : G) (γ a : Gf) (hfix : π ψ * a * γ * a⁻¹ ∈ Γ.map π) (c : Λ) :
    LinearMap.trace Λ (AΓ (Λ := Λ) π Γ)
      (eBΓ Λ π Γ (blk (Γ.map π) a) * (rRepΓ π Γ γ⁻¹ * (c • lftΓ π Γ ψ))) = c := by
  rw [trace_block_transfer _ (qΓ Λ π Γ (blk _ a)) (jΓ Λ π Γ a) (eBΓ_eq_jΓ_qΓ π Γ rfl) (qΓ_jΓ π Γ rfl) _
    (c • LinearMap.id) (qΓ_op π Γ ψ γ a hfix c)]
  rcases subsingleton_or_nontrivial Λ with hΛ | hΛ
  · exact Subsingleton.elim _ _
  · rw [map_smul, LinearMap.trace_id, Module.finrank_self, Nat.cast_one, smul_eq_mul, mul_one]

/-- **Block trace on `A_Γ`**: `Tr(eBΓ [a] ∘ rRepΓ γ⁻¹ ∘ (c • lftΓ ψ)^m) = c^m` when `π(ψ^m) a γ a⁻¹ ∈ π(Γ)`. -/
theorem trace_aΓ_blk (ψ : G) (γ a : Gf) (c : Λ) (m : ℕ) (hfix : π (ψ ^ m) * a * γ * a⁻¹ ∈ Γ.map π) :
    LinearMap.trace Λ (AΓ (Λ := Λ) π Γ)
      (eBΓ Λ π Γ (blk (Γ.map π) a) * (rRepΓ π Γ γ⁻¹ * (c • lftΓ π Γ ψ) ^ m)) = c ^ m := by
  rw [smul_lftΓ_pow]
  exact trace_blk_op π Γ (ψ ^ m) γ a hfix (c ^ m)

end Trace

section TotH2

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (hπ : IsOpen (π.ker : Set G)) (H : ResHyp Λ π Γ I)

include H in
theorem h2K_free : Module.Free Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :=
  Module.Free.of_equiv (cokE hπ H).symm

include H in
theorem h2K_finite : Module.Finite Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)) :=
  Module.Finite.equiv (cokE hπ H).symm

variable (γ : Gf) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (c : Λ)
  (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
  (ht : Function.Bijective t)
  (hTW : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I (t s))),
    (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (H.sg s)) =
      c • (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (H.sg (t s)))

include hD ht hTW in
/-- **`H²` block trace, total cone**: `Tr(h2PB [a] ∘ h2Op γ ψ^m | H²K) = c^m` when `π(ψ^m) a γ a⁻¹ ∈ π(Γ)`. -/
theorem trace_h2_tot_blk (a : Gf) (m : ℕ) (hfix : π (ψ ^ m) * a * γ * a⁻¹ ∈ Γ.map π) :
    LinearMap.trace Λ _
        (h2PB Λ π Γ I hπ (blk (Γ.map π) a) *
          h2Op Λ π Γ I hπ γ (ψ ^ m) t^[m] (hpow Γ ψ t h m) (bdryCompat_pow Γ I hI m)) = c ^ m :=
  (trace_h2_tot hπ H γ ψ t h hI c hD ht hTW (blk (Γ.map π) a) m).trans (trace_aΓ_blk π Γ ψ γ a c m hfix)

end TotH2

section KN

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Finite Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G) {H G' : Subgroup G}
  (σH : Representation Λ (H.subgroupOf G') Λ) (hπ : IsOpen (π.ker : Set G))
  (hσB : IsOpen ((σB σH).ker : Set G'))
  (hΓ : Γ ≤ G') (hHΓ : ∀ x ∈ Γ, x ∈ H ↔ π x = 1) (hcov : ∀ y ∈ G', ∃ c ∈ Γ, y * c⁻¹ ∈ H)
  (hσ : ∀ h, σH h = 1) (a : Gf)

include hΓ hHΓ hcov hσ a in
theorem h2KN_projective [Module.Free Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ))] :
    Module.Projective Λ (H2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB) :=
  Module.Projective.of_split (h2J π Γ I σH hπ hσB hΓ hHΓ hσ a) (h2Q π Γ I σH hπ hσB hHΓ hcov hσ a)
    (h2Q_h2J π Γ I σH hπ hσB hΓ hHΓ hcov hσ a)

include hΓ hHΓ hcov hσ a in
theorem h2KN_finite [Module.Finite Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ))] :
    Module.Finite Λ (H2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB) :=
  Module.Finite.of_surjective (h2Q π Γ I σH hπ hσB hHΓ hcov hσ a) fun w =>
    ⟨h2J π Γ I σH hπ hσB hΓ hHΓ hσ a w, LinearMap.congr_fun (h2Q_h2J π Γ I σH hπ hσB hΓ hHΓ hcov hσ a) w⟩

include hΓ hHΓ hcov hσ a in
theorem h2KN_free [IsLocalRing Λ] [Module.Free Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ))]
    [Module.Finite Λ (H2K (regRep Λ π) Γ I (isOpen_regRep_ker π hπ))] :
    Module.Free Λ (H2K (σB σH) (Γ.subgroupOf G') (fun s => (I s).subgroupOf G') hσB) :=
  haveI := h2KN_projective π Γ I σH hπ hσB hΓ hHΓ hcov hσ a
  haveI := h2KN_finite π Γ I σH hπ hσB hΓ hHΓ hcov hσ a
  Module.free_of_flat_of_isLocalRing

end KN

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

/-- Cocycle level: the cone Shapiro map intertwines the two cone Frobenius operators (exact equality). -/
theorem resEvc_twistc {p : (Γ → coindV H.subtype σ) × (S → coindV H.subtype σ)}
    (hp : p ∈ Z1c (pushRep H σ) Γ I) (ψ : H) (τ : S → S) (h : S → Γ) (τ' : T → T) (h' : T → geoU Γ H)
    (hM : FrobMatch Γ H I π xT ψ τ h τ' h') :
    resEvc Γ H σ π xT (twistc (pushRep H σ) Γ (ψ : G) τ h p) =
      twistc σ (geoU Γ H) ψ τ' h' (resEvc Γ H σ π xT p) := by
  have hz : p.1 ∈ Z1 (pushRep H σ) Γ := ((mem_Z1c _ _ _ p).mp hp).1
  refine Prod.ext (funext fun u => ?_) (funext fun t => ?_)
  · change ((p.1 (conjΓ Γ (ψ : G) (geoToΓ Γ H u)) : coindV H.subtype σ) : G → M) (1 * (ψ : G)) =
      σ ψ ((((p.1 (geoToΓ Γ H (conjΓ (geoU Γ H) ψ u))) : coindV H.subtype σ) : G → M) 1)
    rw [one_mul, coind_apply_of_mem]
    rfl
  · obtain ⟨hπ, hmem⟩ := hM t
    change ((p.2 (τ (π t)) : coindV H.subtype σ) : G → M) ((xT t : G) * (ψ : G) * (h (π t) : G)) -
        ((p.1 (h (π t)) : coindV H.subtype σ) : G → M) ((xT t : G) * (ψ : G)) -
        ((p.1 (conjΓ Γ (ψ : G) (xT t)) : coindV H.subtype σ) : G → M) (1 * (ψ : G)) =
      σ ψ (σ (h' t : H) (((p.2 (π (τ' t)) : coindV H.subtype σ) : G → M) (xT (τ' t)) -
          ((p.1 (xT (τ' t)) : coindV H.subtype σ) : G → M) 1) -
        ((p.1 (geoToΓ Γ H (h' t)) : coindV H.subtype σ) : G → M) 1)
    rw [hπ, one_mul]
    simp only [map_sub]
    have r1 : σ ψ (σ (h' t : H) (((p.2 (τ (π t)) : coindV H.subtype σ) : G → M) (xT (τ' t)))) =
        ((p.2 (τ (π t)) : coindV H.subtype σ) : G → M) ((ψ : G) * ((h' t : H) : G) * xT (τ' t)) := by
      rw [mul_assoc, coind_mul_apply, coind_mul_apply]
    have r2 : σ ψ (σ (h' t : H) (((p.1 (xT (τ' t)) : coindV H.subtype σ) : G → M) 1)) =
        ((p.1 (xT (τ' t)) : coindV H.subtype σ) : G → M) ((ψ : G) * ((h' t : H) : G)) := by
      rw [coind_mul_apply, coind_apply_of_mem]
    have r3 : σ ψ (((p.1 (geoToΓ Γ H (h' t)) : coindV H.subtype σ) : G → M) 1) =
        ((p.1 (geoToΓ Γ H (h' t)) : coindV H.subtype σ) : G → M) (ψ : G) :=
      (coind_apply_of_mem _ ψ).symm
    rw [r1, r2, r3]
    have hgΓ : (((h' t : H) : G) * (xT (τ' t) : G))⁻¹ *
        ((ψ : G)⁻¹ * (xT t : G) * (ψ : G) * (h (π t) : G)) ∈ Γ :=
      Γ.mul_mem (Γ.inv_mem (Γ.mul_mem (Subgroup.mem_subgroupOf.mp (h' t).2) (xT (τ' t)).2))
        (Γ.mul_mem (conjΓ Γ (ψ : G) (xT t)).2 (h (π t)).2)
    obtain ⟨g, hgdef⟩ : ∃ g : Γ, (g : G) = (((h' t : H) : G) * (xT (τ' t) : G))⁻¹ *
        ((ψ : G)⁻¹ * (xT t : G) * (ψ : G) * (h (π t) : G)) := ⟨⟨_, hgΓ⟩, rfl⟩
    have hg : (g : G) ∈ I (τ (π t)) := by rw [hgdef]; exact hmem
    -- (A) `c(ψ⁻¹ x_t ψ · h_s)(ψ) = c(ψ⁻¹ x_t ψ)(ψ) + c(h_s)(x_t ψ)`
    have eA := Z1_coind_apply Γ H σ hz (conjΓ Γ (ψ : G) (xT t)) (h (π t)) (ψ : G)
    have e1 : (ψ : G) * ((conjΓ Γ (ψ : G) (xT t) : Γ) : G) = (xT t : G) * ψ := by
      rw [conjΓ_val]; group
    rw [e1] at eA
    -- (B) `c(h'_t x_{τ' t})(ψ) = c(h'_t)(ψ) + c(x_{τ' t})(ψ h'_t)`
    have eB := Z1_coind_apply Γ H σ hz (geoToΓ Γ H (h' t)) (xT (τ' t)) (ψ : G)
    rw [geoToΓ_coe] at eB
    -- (C) `c(h'_t x_{τ' t} g)(ψ) = c(h'_t x_{τ' t})(ψ) + c(g)(ψ h'_t x_{τ' t})`
    have eC := Z1_coind_apply Γ H σ hz (geoToΓ Γ H (h' t) * xT (τ' t)) g (ψ : G)
    have hyy : geoToΓ Γ H (h' t) * xT (τ' t) * g = conjΓ Γ (ψ : G) (xT t) * h (π t) :=
      Subtype.ext (by simp only [Subgroup.coe_mul, geoToΓ_coe, conjΓ_val, hgdef]; group)
    have e2 : (ψ : G) * ((geoToΓ Γ H (h' t) * xT (τ' t) : Γ) : G) =
        (ψ : G) * ((h' t : H) : G) * xT (τ' t) := by
      rw [Subgroup.coe_mul, geoToΓ_coe, mul_assoc]
    rw [hyy, e2] at eC
    -- (D) the cone relation at `g ∈ I (τ s)`
    have eD := Z1c_coind_cone Γ H σ I hp (τ (π t)) g hg ((ψ : G) * ((h' t : H) : G) * xT (τ' t))
    have e3 : (ψ : G) * ((h' t : H) : G) * xT (τ' t) * g = (xT t : G) * ψ * h (π t) := by
      rw [hgdef]; group
    rw [e3] at eD
    have hQ := eq_sub_of_add_eq eA.symm
    rw [hQ, eC, eB, eD]
    abel

/-- **Shapiro for `H¹_c` commutes with Frobenius**: for matching Frobenius data,
`shapiroH1c ∘ frobH1c(f_* M; ψ, τ, h) = frobH1c(M; ψ, τ', h') ∘ shapiroH1c`. -/
theorem shapiroH1c_frob (hJ : InertiaLift Γ H I J π xT) (ψ : H) (τ : S → S) (h : S → Γ)
    (hI : BdryCompat Γ I (ψ : G) τ h) (τ' : T → T) (h' : T → geoU Γ H)
    (hI' : BdryCompat (geoU Γ H) J ψ τ' h') (hM : FrobMatch Γ H I π xT ψ τ h τ' h')
    (x : H1c (pushRep H σ) Γ I) :
    shapiroH1c Γ H σ I J π xT hJ (frobH1c (pushRep H σ) Γ I (ψ : G) τ h hI x) =
      frobH1c σ (geoU Γ H) J ψ τ' h' hI' (shapiroH1c Γ H σ I J π xT hJ x) := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (H1c.mk σ (geoU Γ H) J)
    (Subtype.ext (resEvc_twistc Γ H σ I π xT hp ψ τ h τ' h' hM))

/-- Traces of all powers of the Frobenius agree through `shapiroH1cEquiv`. -/
theorem trace_frob_shapiro (hJ : InertiaLift Γ H I J π xT) (hT : DCover Γ H I π xT) (hD : DDisj Γ H I π xT)
    (R : CosetReps Γ H) (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ) (hHo : IsOpen (H : Set G))
    (ψ : H) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I (ψ : G) τ h) (τ' : T → T) (h' : T → geoU Γ H)
    (hI' : BdryCompat (geoU Γ H) J ψ τ' h') (hM : FrobMatch Γ H I π xT ψ τ h τ' h') (m : ℕ) :
    LinearMap.trace k _ (frobH1c (pushRep H σ) Γ I (ψ : G) τ h hI ^ m) =
      LinearMap.trace k _ (frobH1c σ (geoU Γ H) J ψ τ' h' hI' ^ m) :=
  trace_pow_eq_of_comm (shapiroH1cEquiv Γ H σ I J π xT hJ hT hD R hcov hHo) _ _
    (fun x => shapiroH1c_frob Γ H σ I J π xT hJ ψ τ h hI τ' h' hI' hM x) m

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

-- ===== S4.Def_RP_Lefschetz_AmbSub =====
section

/-!
# S4-Lefschetz, L4i part 1: Shapiro with Frobenius inside an ambient subgroup `G' ≤ G`

The cone Shapiro isomorphism `shapiroH1cEquiv` needs `G = H·Γ`. For a cover `E` whose constant field is `𝔽_{q^d}`
this holds only inside the ambient subgroup `G' = H·Γ` (the degree-divisible-by-`d` part of `G`). Here every piece
of Shapiro data for `(G, Γ, H, I, J, π, x)` is moved to `(G', Γ ∩ G', H ∩ G', I ∩ G', J, π, x)` (all by definitional
unfolding: the coercions are literal), and `Γ ∩ H` computed inside `G'` is identified with `Γ ∩ H` by `eGeoT`.

* `inertiaLift_sub`, `dCover_sub`, `dDisj_sub`, `cosetReps_sub`, `hcov_sub` (`hcov'_of_le_sup`), `isOpen_sub`,
  `bdryCompat_sub`, `bdryCompat_geo_sub`, `frobMatch_sub`;
* `eGeoT : (Γ ∩ G') ∩ (H ∩ G') ≃ₜ* Γ ∩ H`, `EH : H ∩ G' ≃* H`, `intw_sub`, `intwI_sub`, `trace_geo_sub`;
* **`trace_shapiro_sub`**: `Tr(F^m | H¹_c(G'; Ind_H^{G'} σ)) = Tr(F^m | H¹_c(Γ ∩ H; σ))` for `G' = H·Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Representation CupDuality

section AmbSub

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] {Γ H G' : Subgroup G}
  {S T : Type} {I : S → Subgroup G} {J : T → Subgroup H} {π : T → S} {xT : T → Γ}

/-- `Γ → Γ ∩ G'`. -/
def liftΓ (hΓ : Γ ≤ G') (x : Γ) : geoU Γ G' := ⟨⟨x, hΓ x.2⟩, x.2⟩

/-- `Γ ∩ G' → Γ`. -/
def downΓ (y : geoU Γ G') : Γ := ⟨((y : G') : G), y.2⟩

/-- `Γ ∩ H → (Γ ∩ G') ∩ (H ∩ G')`. -/
def upGeo (hH : H ≤ G') (h : geoU Γ H) : geoU (geoU Γ G') (H.subgroupOf G') := ⟨upH hH h, h.2⟩

/-- `(Γ ∩ G') ∩ (H ∩ G') → Γ ∩ H`. -/
def downGeo (h : geoU (geoU Γ G') (H.subgroupOf G')) : geoU Γ H := ⟨downH H G' h, h.2⟩

/-! ## Shapiro data inside `G'` -/

theorem inertiaLift_sub (hΓ : Γ ≤ G') (hJ : InertiaLift Γ H I J π xT) :
    InertiaLift (geoU Γ G') (H.subgroupOf G') (fun s => (I s).subgroupOf G') (fun t => (J t).comap (downH H G'))
      π (fun t => liftΓ hΓ (xT t)) := by
  intro t h
  exact hJ t (downGeo h)

theorem dCover_sub (hΓ : Γ ≤ G') (hH : H ≤ G') (hT : DCover Γ H I π xT) :
    DCover (geoU Γ G') (H.subgroupOf G') (fun s => (I s).subgroupOf G') π (fun t => liftΓ hΓ (xT t)) := by
  intro s y
  obtain ⟨t, ht, h, g, hg, hy⟩ := hT s (downΓ y)
  exact ⟨t, ht, upGeo hH h, liftΓ hΓ g, hg, Subtype.ext hy⟩

theorem dDisj_sub (hΓ : Γ ≤ G') (hD : DDisj Γ H I π xT) :
    DDisj (geoU Γ G') (H.subgroupOf G') (fun s => (I s).subgroupOf G') π (fun t => liftΓ hΓ (xT t)) := by
  intro t t' hπ h g hg he
  exact hD t t' hπ (downGeo h) (downΓ g) hg (congrArg Subtype.val he)

/-- Coset representatives of `Γ / (Γ ∩ H)` inside `G'`. -/
def cosetReps_sub (hΓ : Γ ≤ G') (R : CosetReps Γ H) : CosetReps (geoU Γ G') (H.subgroupOf G') where
  r y := liftΓ hΓ (R.r (downΓ y))
  mem y := R.mem (downΓ y)
  coset y y' hyy := congrArg (liftΓ hΓ) (R.coset (downΓ y) (downΓ y') hyy)
  one := by
    show liftΓ hΓ (R.r 1) = 1
    rw [R.one]
    rfl
  fin := (R.fin.image (liftΓ hΓ)).subset (by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, ⟨downΓ y, rfl⟩, rfl⟩)

theorem hcov_sub (hΓ : Γ ≤ G') (hH : H ≤ G') (hcov' : ∀ x ∈ G', ∃ a ∈ H, ∃ b ∈ Γ, x = a * b) :
    ∀ x : G', ∃ h : H.subgroupOf G', ∃ γ : geoU Γ G', x = (h : G') * γ := by
  intro x
  obtain ⟨a, ha, b, hb, hx⟩ := hcov' x x.2
  exact ⟨upH hH ⟨a, ha⟩, liftΓ hΓ ⟨b, hb⟩, Subtype.ext hx⟩

theorem bdryCompat_sub (hΓ : Γ ≤ G') (ψ : G') (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I (ψ : G) τ h) :
    BdryCompat (geoU Γ G') (fun s => (I s).subgroupOf G') ψ τ (fun s => liftΓ hΓ (h s)) := by
  intro s g hg
  exact hI s (downΓ g) hg

theorem bdryCompat_geo_sub (hH : H ≤ G') (ψ : H) (τ' : T → T) (h' : T → geoU Γ H)
    (hI' : BdryCompat (geoU Γ H) J ψ τ' h') :
    BdryCompat (geoU (geoU Γ G') (H.subgroupOf G')) (fun t => (J t).comap (downH H G')) (upH hH ψ) τ'
      (fun t => upGeo hH (h' t)) := by
  intro t g hg
  exact hI' t (downGeo g) hg

section Top

variable [IsTopologicalGroup G]

theorem frobMatch_sub (hΓ : Γ ≤ G') (hH : H ≤ G') (ψ : H) (τ : S → S) (h : S → Γ) (τ' : T → T)
    (h' : T → geoU Γ H) (hM : FrobMatch Γ H I π xT ψ τ h τ' h') :
    FrobMatch (geoU Γ G') (H.subgroupOf G') (fun s => (I s).subgroupOf G') π (fun t => liftΓ hΓ (xT t))
      (upH hH ψ) τ (fun s => liftΓ hΓ (h s)) τ' (fun t => upGeo hH (h' t)) := by
  intro t
  exact hM t

variable (Γ) in
/-- `Γ ∩ H` computed inside `G'` is `Γ ∩ H`. -/
def eGeoT (hH : H ≤ G') : geoU (geoU Γ G') (H.subgroupOf G') ≃ₜ* geoU Γ H where
  toFun := downGeo
  invFun := upGeo hH
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_induced_rng.2 (continuous_induced_rng.2
    (show Continuous fun x : geoU (geoU Γ G') (H.subgroupOf G') => (((x : H.subgroupOf G') : G') : G) from
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  continuous_invFun := continuous_induced_rng.2 (continuous_induced_rng.2 (continuous_induced_rng.2
    (show Continuous fun x : geoU Γ H => ((x : H) : G) from continuous_subtype_val.comp continuous_subtype_val)))

theorem downGeo_coe (x : geoU (geoU Γ G') (H.subgroupOf G')) :
    ((downGeo x : geoU Γ H) : H) = downH H G' (x : H.subgroupOf G') := rfl

variable (Γ) in
theorem eGeoT_apply (hH : H ≤ G') (x : geoU (geoU Γ G') (H.subgroupOf G')) : eGeoT Γ hH x = downGeo x := rfl

variable (Γ) in
theorem eGeoT_coe (hH : H ≤ G') (x : geoU (geoU Γ G') (H.subgroupOf G')) :
    ((eGeoT Γ hH x : geoU Γ H) : H) = downH H G' (x : H.subgroupOf G') := by
  rw [eGeoT_apply, downGeo_coe]

variable (Γ) in
theorem intw_sub (σ : Representation k H M) (hH : H ≤ G') :
    Intw (σ.comp (downH H G')) σ (eGeoT Γ hH) := fun g => by
  rw [eGeoT_coe]
  rfl

variable (Γ J) in
theorem intwI_sub (hH : H ≤ G') :
    IntwI (fun t => (J t).comap (downH H G')) J (eGeoT Γ hH) := fun t g => by
  rw [eGeoT_coe]
  rfl

variable (Γ) in
theorem eGeoT_EH (hH : H ≤ G') (g : geoU (geoU Γ G') (H.subgroupOf G')) :
    ((eGeoT Γ hH g : geoU Γ H) : H) = EH hH (g : H.subgroupOf G') := by
  rw [eGeoT_coe, EH_apply]

variable [Γ.Normal]

/-- Traces of Frobenius on `H¹_c(Γ ∩ H)` computed inside `G'` and inside `G` agree. -/
theorem trace_geo_sub (σ : Representation k H M) (hH : H ≤ G') (ψ : H) (τ' : T → T) (h' : T → geoU Γ H)
    (hI' : BdryCompat (geoU Γ H) J ψ τ' h') (m : ℕ) :
    LinearMap.trace k _ (frobH1c (σ.comp (downH H G')) (geoU (geoU Γ G') (H.subgroupOf G'))
        (fun t => (J t).comap (downH H G')) (upH hH ψ) τ' (fun t => upGeo hH (h' t))
        (bdryCompat_geo_sub hH ψ τ' h' hI') ^ m) =
      LinearMap.trace k _ (frobH1c σ (geoU Γ H) J ψ τ' h' hI' ^ m) :=
  have hψ : EH hH (upH hH ψ) = ψ := rfl
  have hh : (fun s => eGeoT Γ hH (upGeo hH (h' s))) = h' := rfl
  have hI₂ : BdryCompat (geoU Γ H) J (EH hH (upH hH ψ)) τ' (fun s => eGeoT Γ hH (upGeo hH (h' s))) := by
    rw [hψ, hh]
    exact hI'
  have key : ∀ x, h1cTr (intw_sub Γ σ hH) (intwI_sub Γ J hH) (frobH1c (σ.comp (downH H G'))
      (geoU (geoU Γ G') (H.subgroupOf G')) (fun t => (J t).comap (downH H G')) (upH hH ψ) τ'
      (fun t => upGeo hH (h' t)) (bdryCompat_geo_sub hH ψ τ' h' hI') x) =
      frobH1c σ (geoU Γ H) J ψ τ' h' hI' (h1cTr (intw_sub Γ σ hH) (intwI_sub Γ J hH) x) := fun x => by
    rw [h1cTr_frob (intw_sub Γ σ hH) (intwI_sub Γ J hH) (EH hH) (eGeoT_EH Γ hH) (upH hH ψ) rfl τ'
      (fun t => upGeo hH (h' t)) (bdryCompat_geo_sub hH ψ τ' h' hI') hI₂ x]
    exact congrFun (congrArg DFunLike.coe (frobH1c_congr σ (geoU Γ H) J hψ rfl hh hI₂ hI')) _
  trace_pow_eq_of_comm (h1cTr (intw_sub Γ σ hH) (intwI_sub Γ J hH)) _ _ key m

/-- **L4i1**: Shapiro with Frobenius inside an ambient subgroup `G' = H·Γ`:
`Tr(F^m | H¹_c(Γ ∩ G'; Ind_{H}^{G'} σ)) = Tr(F^m | H¹_c(Γ ∩ H; σ))`. -/
theorem trace_shapiro_sub (σ : Representation k H M) (hΓ : Γ ≤ G') (hH : H ≤ G')
    (hJ : InertiaLift Γ H I J π xT) (hT : DCover Γ H I π xT) (hD : DDisj Γ H I π xT) (R : CosetReps Γ H)
    (hcov' : ∀ x ∈ G', ∃ a ∈ H, ∃ b ∈ Γ, x = a * b) (hHo : IsOpen (H : Set G))
    (ψ : H) (τ : S → S) (h : S → Γ) (hI : BdryCompat Γ I (ψ : G) τ h) (τ' : T → T) (h' : T → geoU Γ H)
    (hI' : BdryCompat (geoU Γ H) J ψ τ' h') (hM : FrobMatch Γ H I π xT ψ τ h τ' h') (m : ℕ) :
    LinearMap.trace k _ (frobH1c (pushRep (H.subgroupOf G') (σ.comp (downH H G'))) (geoU Γ G')
        (fun s => (I s).subgroupOf G') ((upH hH ψ : H.subgroupOf G') : G') τ (fun s => liftΓ hΓ (h s))
        (bdryCompat_sub hΓ (upH hH ψ : G') τ h hI) ^ m) =
      LinearMap.trace k _ (frobH1c σ (geoU Γ H) J ψ τ' h' hI' ^ m) :=
  (trace_frob_shapiro (geoU Γ G') (H.subgroupOf G') (σ.comp (downH H G')) (fun s => (I s).subgroupOf G')
    (fun t => (J t).comap (downH H G')) π (fun t => liftΓ hΓ (xT t)) (inertiaLift_sub hΓ hJ)
    (dCover_sub hΓ hH hT) (dDisj_sub hΓ hD) (cosetReps_sub hΓ R) (hcov_sub hΓ hH hcov') (isOpen_sub hHo)
    (upH hH ψ) τ (fun s => liftΓ hΓ (h s)) (bdryCompat_sub hΓ (upH hH ψ : G') τ h hI) τ'
    (fun t => upGeo hH (h' t)) (bdryCompat_geo_sub hH ψ τ' h' hI')
    (frobMatch_sub hΓ hH ψ τ h τ' h' hM) m).trans (trace_geo_sub σ hH ψ τ' h' hI' m)

end Top

end AmbSub

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ConstExt =====
section

/-!
# S4-Lefschetz L4a: a function field over its full constant field

Let `E` be a function field over `𝔽_q` in the coordinates of S3-Places (`Algebra 𝔽_q[X] E`, `Algebra 𝔽_q(X) E`,
finite separable over `𝔽_q(X)`), but with an arbitrary constant field. Its full constant field
`k' = constField 𝔽_q E` is finite, `x = X_E` is transcendental over `k'`, and with `k'[X] → E`, `k'(X) → E` given by
`X ↦ X_E` the field `E` is a function field over `k'` (finite separable over `k'(X)`) whose full constant field is `k'`
itself (`constField_eq_bot`). So every covering curve of `U` satisfies the hypotheses of S4-CP4 over its own constant
field (`cp4_constExt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped nonZeroDivisors

namespace RamanujanPetersson
namespace Lefschetz

open Places CurveCoh GalCover CP4a

noncomputable section

section ConstExt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

instance finite_Kc : Finite (Kc Fq E) := Module.finite_of_finite Fq

instance fintype_Kc : Fintype (Kc Fq E) := Fintype.ofFinite _

/-- The coordinate `x` of `E`. -/
def xE : E := algebraMap (RatFunc Fq) E RatFunc.X

theorem xE_eq : xE Fq E = algebraMap Fq[X] E X := by
  rw [xE, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply]

theorem algebraMap_poly_eq_aeval (p : Fq[X]) : algebraMap Fq[X] E p = aeval (xE Fq E) p := by
  rw [xE_eq]
  have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom Fq Fq[X] E) (X : Fq[X]) p
  rw [Polynomial.aeval_X_left_apply] at h
  exact h.symm

theorem xE_transcendental_Fq : Transcendental Fq (xE Fq E) := by
  rw [xE, transcendental_algebraMap_iff (algebraMap (RatFunc Fq) E).injective]
  exact RatFunc.transcendental_X

theorem xE_transcendental : Transcendental (Kc Fq E) (xE Fq E) :=
  (xE_transcendental_Fq Fq E).extendScalars (Kc Fq E)

theorem aeval_xE_injective : Function.Injective (aeval (R := Kc Fq E) (xE Fq E)) :=
  transcendental_iff_injective.mp (xE_transcendental Fq E)

theorem aeval_xE_nonZeroDivisors :
    (Kc Fq E)[X]⁰ ≤ E⁰.comap (aeval (R := Kc Fq E) (xE Fq E)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_xE_injective Fq E)

/-- `k'[X] → E`, `X ↦ x`. -/
instance algPolyKc : Algebra (Kc Fq E)[X] E := (aeval (R := Kc Fq E) (xE Fq E)).toRingHom.toAlgebra

theorem algebraMap_polyKc (p : (Kc Fq E)[X]) : algebraMap (Kc Fq E)[X] E p = aeval (xE Fq E) p := rfl

instance isScalarTower_Kc_poly : IsScalarTower (Kc Fq E) (Kc Fq E)[X] E :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [algebraMap_polyKc, Polynomial.algebraMap_apply, aeval_C]
    rfl

/-- `k'(X) → E`, `X ↦ x`. -/
instance algRatKc : Algebra (RatFunc (Kc Fq E)) E :=
  (RatFunc.liftAlgHom (aeval (R := Kc Fq E) (xE Fq E)) (aeval_xE_nonZeroDivisors Fq E)).toRingHom.toAlgebra

theorem algebraMap_ratKc (f : RatFunc (Kc Fq E)) :
    algebraMap (RatFunc (Kc Fq E)) E f =
      RatFunc.liftAlgHom (aeval (R := Kc Fq E) (xE Fq E)) (aeval_xE_nonZeroDivisors Fq E) f := rfl

theorem liftAlgHom_algebraMap {K L : Type} [Field K] [Field L] [Algebra K L] (φ : K[X] →ₐ[K] L)
    (hφ : K[X]⁰ ≤ L⁰.comap φ) (p : K[X]) : RatFunc.liftAlgHom φ hφ (algebraMap K[X] (RatFunc K) p) = φ p := by
  have h := RatFunc.liftAlgHom_apply_div φ hφ p 1
  rwa [map_one, div_one, map_one, div_one] at h

instance isScalarTower_Kc_rat : IsScalarTower (Kc Fq E)[X] (RatFunc (Kc Fq E)) E :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_ratKc, liftAlgHom_algebraMap, algebraMap_polyKc]

theorem mapPoly_nonZeroDivisors : Fq[X]⁰ ≤ (Kc Fq E)[X]⁰.comap (mapPoly Fq E) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ (algebraMap Fq (Kc Fq E)).injective)

instance algRatRat : Algebra (RatFunc Fq) (RatFunc (Kc Fq E)) :=
  (RatFunc.mapRingHom (mapPoly Fq E) (mapPoly_nonZeroDivisors Fq E)).toAlgebra

theorem algebraMap_ratRat_poly (p : Fq[X]) :
    algebraMap (RatFunc Fq) (RatFunc (Kc Fq E)) (algebraMap Fq[X] (RatFunc Fq) p) =
      algebraMap (Kc Fq E)[X] (RatFunc (Kc Fq E)) (mapPoly Fq E p) := by
  show RatFunc.mapRingHom (mapPoly Fq E) (mapPoly_nonZeroDivisors Fq E) (algebraMap Fq[X] (RatFunc Fq) p) = _
  rw [RatFunc.coe_mapRingHom_eq_coe_map, ← div_one (algebraMap Fq[X] (RatFunc Fq) p), ← map_one (algebraMap Fq[X] (RatFunc Fq)),
    RatFunc.map_apply_div, map_one, map_one, div_one]

instance isScalarTower_rat_rat : IsScalarTower (RatFunc Fq) (RatFunc (Kc Fq E)) E := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine IsLocalization.ringHom_ext (nonZeroDivisors Fq[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [algebraMap_ratRat_poly, ← IsScalarTower.algebraMap_apply (Kc Fq E)[X] (RatFunc (Kc Fq E)) E,
    ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) E, algebraMap_polyKc, algebraMap_poly_eq_aeval, mapPoly,
    Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]

instance functionField_Kc : FunctionField (Kc Fq E) E :=
  Module.Finite.of_restrictScalars_finite (RatFunc Fq) (RatFunc (Kc Fq E)) E

instance isSeparable_Kc : Algebra.IsSeparable (RatFunc (Kc Fq E)) E :=
  Algebra.isSeparable_tower_top_of_isSeparable (RatFunc Fq) (RatFunc (Kc Fq E)) E

/-- **`k'` is the full constant field of `E` over `k'`.** -/
theorem constField_eq_bot : constField (Kc Fq E) E = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : IsAlgebraic (Kc Fq E) x := mem_algebraicClosure_iff.mp hx
  have h2 : IsAlgebraic Fq x := (Algebra.IsAlgebraic.isAlgebraic_iff (R := Fq) (S := Kc Fq E)).2 h1
  exact IntermediateField.mem_bot.2 ⟨⟨x, mem_algebraicClosure_iff.2 h2⟩, rfl⟩

theorem charP_Kc (p : ℕ) [CharP E p] : CharP (Kc Fq E) p :=
  (algebraMap (Kc Fq E) E).charP (algebraMap (Kc Fq E) E).injective p

/-- `#k'` is a positive power of the characteristic. -/
theorem card_Kc (p : ℕ) [Fact p.Prime] [CharP E p] : ∃ e : ℕ, 0 < e ∧ Fintype.card (Kc Fq E) = p ^ e := by
  have := charP_Kc Fq E p
  obtain ⟨n, hp, hn⟩ := FiniteField.card (Kc Fq E) p
  exact ⟨n, n.pos, hn⟩

end ConstExt

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrTower =====
section

/-!
# S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure

`IsUnramifiedSub A K L` asks that the inertia groups of `Gal(L/K)` on the integral closure of `A` in `L` vanish.
If `R → S → K` is a tower with `S` integral over `R`, the integral closures of `R` and `S` in `L` are the same
subring of `L` (as `Gal(L/K)`-rings), so `unramSet S K = unramSet R K` and `maxUnram S K = maxUnram R K`.
Applications: `maxUnram (Rfin 𝔽_q F) F = maxUnram 𝔽_q[X] F`, and for a covering function field `E` with full
constant field `k'` (L4a) `maxUnram (Rfin k' E) E = maxUnram 𝔽_q[X] E` (`k'[X]` is integral over `𝔽_q[X]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover

noncomputable section

/-! ### Inertia transport along an equivariant ring isomorphism -/

section InertiaTransport

variable {G B B' : Type} [Group G] [CommRing B] [CommRing B'] [MulSemiringAction G B]
  [MulSemiringAction G B']

end InertiaTransport

/-! ### Integral towers `R → S → K` give the same `K_U` -/

section Tower

variable (R S K : Type) [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] [Algebra.IsIntegral R S]

end Tower

/-! ### Applications: `Rfin`, and `k'[X]` over `𝔽_q[X]` -/

section Apps

variable (Fq : Type) [Field Fq] [Fintype Fq]

variable [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

theorem algPolyPoly_apply (p : Fq[X]) :
    @algebraMap Fq[X] (Kc Fq E)[X] _ _ (algPolyPoly Fq E) p = p.map (algebraMap Fq (Kc Fq E)) := rfl

theorem isScalarTower_polyPoly :
    @IsScalarTower Fq[X] (Kc Fq E)[X] E (algPolyPoly Fq E).toSMul _ _ := by
  letI := algPolyPoly Fq E
  refine IsScalarTower.of_algebraMap_eq fun p => ?_
  rw [algPolyPoly_apply, algebraMap_polyKc, algebraMap_poly_eq_aeval, aeval_map_algebraMap]

theorem isScalarTower_Fq_polyPoly :
    @IsScalarTower Fq Fq[X] (Kc Fq E)[X] _ (algPolyPoly Fq E).toSMul _ := by
  letI := algPolyPoly Fq E
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [algPolyPoly_apply, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Polynomial.map_C]
  rfl

theorem isIntegral_polyPoly :
    @Algebra.IsIntegral Fq[X] (Kc Fq E)[X] _ _ (algPolyPoly Fq E) := by
  letI := algPolyPoly Fq E
  have := isScalarTower_Fq_polyPoly Fq E
  refine ⟨fun q => ?_⟩
  induction q using Polynomial.induction_on' with
  | add p q hp hq => exact hp.add hq
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    refine IsIntegral.mul ?_ (IsIntegral.pow ?_ n)
    · have hc : IsIntegral Fq (algebraMap (Kc Fq E) (Kc Fq E)[X] c) :=
        (Algebra.IsIntegral.isIntegral (R := Fq) c).algebraMap
      rw [Polynomial.algebraMap_eq] at hc
      exact hc.tower_top
    · have hX : (X : (Kc Fq E)[X]) = algebraMap Fq[X] (Kc Fq E)[X] X := by
        rw [algPolyPoly_apply, Polynomial.map_X]
      rw [hX]
      exact isIntegral_algebraMap

/-- `K_U` of `E` over its full constant field equals `K_U` over `𝔽_q[X]`. -/
theorem maxUnram_rfin_Kc :
    maxUnram (FunctionField.ringOfIntegers (Kc Fq E) E) E = maxUnram Fq[X] E := by
  letI := algPolyPoly Fq E
  have := isScalarTower_polyPoly Fq E
  have := isIntegral_polyPoly Fq E
  have : Algebra.IsIntegral (Kc Fq E)[X] (FunctionField.ringOfIntegers (Kc Fq E) E) :=
    integralClosure.AlgebraIsIntegral
  rw [maxUnram_eq_tower (Kc Fq E)[X] (FunctionField.ringOfIntegers (Kc Fq E) E) E]
  exact maxUnram_eq_tower Fq[X] (Kc Fq E)[X] E

end Apps

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_RinfKc =====
section

/-!
# S4-Lefschetz L4b part 2: the rings `R_fin`, `R_∞` do not see the constant field

For a function field `E` over `𝔽_q` (S3-Places coordinates) with full constant field `k' = Kc 𝔽_q E`:
* `O_∞(𝔽_q) → O_∞(k')` is an integral ring extension (`algOinfOinf`, `isIntegral_Oinf_Oinf`), compatible with every
  `𝔽_q(X) → k'(X) → L` tower;
* hence `IsIntegral O_∞(k') x ↔ IsIntegral O_∞(𝔽_q) x` and `R_∞(k', E) = R_∞(𝔽_q, E)` as subrings of `E`
  (`rinfKcEquiv`, values `rfl`);
* likewise `IsIntegral k'[X] x ↔ IsIntegral 𝔽_q[X] x` and `R_fin(k', E) = R_fin(𝔽_q, E)` (`rfinKcEquiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped nonZeroDivisors

namespace RamanujanPetersson
namespace Lefschetz

open Places CurveCoh GalCover CP4a

noncomputable section

section RinfKc

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

theorem algebraMap_ratRat_poly' (p : Fq[X]) :
    algebraMap (RatFunc Fq) (RatFunc (Kc Fq E)) (algebraMap Fq[X] (RatFunc Fq) p) =
      algebraMap (Kc Fq E)[X] (RatFunc (Kc Fq E)) (p.map (algebraMap Fq (Kc Fq E))) := by
  rw [algebraMap_ratRat_poly, mapPoly, Polynomial.coe_mapRingHom]

theorem ratRat_num_denom (g : RatFunc Fq) :
    algebraMap (RatFunc Fq) (RatFunc (Kc Fq E)) g =
      algebraMap (Kc Fq E)[X] (RatFunc (Kc Fq E)) (g.num.map (algebraMap Fq (Kc Fq E))) /
        algebraMap (Kc Fq E)[X] (RatFunc (Kc Fq E)) (g.denom.map (algebraMap Fq (Kc Fq E))) := by
  conv_lhs => rw [← RatFunc.num_div_denom g]
  rw [map_div₀, algebraMap_ratRat_poly', algebraMap_ratRat_poly']

/-- `𝔽_q(X) → k'(X)` maps `O_∞(𝔽_q)` into `O_∞(k')` (degrees are preserved). -/
theorem map_mem_Oinf (g : RatFunc Fq) (hg : g ∈ Oinf Fq) :
    algebraMap (RatFunc Fq) (RatFunc (Kc Fq E)) g ∈ Oinf (Kc Fq E) := by
  by_cases h0 : g = 0
  · rw [h0, map_zero]
    exact zero_mem _
  have hn : g.num ≠ 0 := RatFunc.num_ne_zero h0
  have hd : g.denom ≠ 0 := g.denom_ne_zero
  have hinj : Function.Injective (algebraMap Fq (Kc Fq E)) := (algebraMap Fq (Kc Fq E)).injective
  have hn' : g.num.map (algebraMap Fq (Kc Fq E)) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hn
  have hd' : g.denom.map (algebraMap Fq (Kc Fq E)) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hd
  have hne : algebraMap (RatFunc Fq) (RatFunc (Kc Fq E)) g ≠ 0 := (_root_.map_ne_zero _).2 h0
  rw [mem_Oinf_iff' _ hne, ratRat_num_denom, intDegree_div_polys _ hn' hd',
    Polynomial.natDegree_map, Polynomial.natDegree_map]
  have h := (mem_Oinf_iff' Fq h0).1 hg
  rw [RatFunc.intDegree] at h
  exact h

/-- `O_∞(𝔽_q) → O_∞(k')`. -/
instance algOinfOinf : Algebra (Oinf Fq) (Oinf (Kc Fq E)) :=
  RingHom.toAlgebra (((algebraMap (RatFunc Fq) (RatFunc (Kc Fq E))).comp (Oinf Fq).subtype).codRestrict
    (Oinf (Kc Fq E)) (fun g => map_mem_Oinf Fq E g g.2))

theorem coe_algebraMap_OinfOinf (g : Oinf Fq) :
    ((algebraMap (Oinf Fq) (Oinf (Kc Fq E)) g : Oinf (Kc Fq E)) : RatFunc (Kc Fq E)) =
      algebraMap (RatFunc Fq) (RatFunc (Kc Fq E)) (g : RatFunc Fq) := rfl

/-- Every `𝔽_q(X) → k'(X) → L` tower restricts to `O_∞(𝔽_q) → O_∞(k') → L`. -/
theorem isScalarTower_Oinf_of (L : Type) [CommRing L] [Algebra (RatFunc Fq) L]
    [Algebra (RatFunc (Kc Fq E)) L] [IsScalarTower (RatFunc Fq) (RatFunc (Kc Fq E)) L] :
    IsScalarTower (Oinf Fq) (Oinf (Kc Fq E)) L :=
  IsScalarTower.of_algebraMap_eq fun g => by
    show algebraMap (RatFunc Fq) L (g : RatFunc Fq) =
      algebraMap (RatFunc (Kc Fq E)) L (algebraMap (RatFunc Fq) (RatFunc (Kc Fq E)) (g : RatFunc Fq))
    exact IsScalarTower.algebraMap_apply (RatFunc Fq) (RatFunc (Kc Fq E)) L _

instance isScalarTower_OinfOinf_E : IsScalarTower (Oinf Fq) (Oinf (Kc Fq E)) E :=
  isScalarTower_Oinf_of Fq E E

/-- The inclusion `O_∞(k') → k'(X)` as an `O_∞(𝔽_q)`-algebra map (stated by hand: synthesizing
`SMul O_∞(k') k'(X)` times out). -/
def oinfVal : Oinf (Kc Fq E) →ₐ[Oinf Fq] RatFunc (Kc Fq E) :=
  { (Oinf (Kc Fq E)).subtype with commutes' := fun _ => rfl }

theorem oinfVal_apply (y : Oinf (Kc Fq E)) : oinfVal Fq E y = (y : RatFunc (Kc Fq E)) := rfl

/-- **`O_∞(k')` is integral over `O_∞(𝔽_q)`.** -/
instance isIntegral_Oinf_Oinf : Algebra.IsIntegral (Oinf Fq) (Oinf (Kc Fq E)) := by
  constructor
  intro y
  have h : IsIntegral (Oinf Fq) (oinfVal Fq E y) :=
    isIntegral_of_mem_Oinf Fq (Kc Fq E) (algebraMap_ratRat_poly' Fq E) y y.2
  have hinj : Function.Injective (oinfVal Fq E) := Subtype.val_injective
  exact (isIntegral_algHom_iff _ hinj).1 h

/-- Integrality over `O_∞` does not see the constant field (any `𝔽_q(X) → k'(X) → L` tower). -/
theorem isIntegral_Oinf_iff_of (L : Type) [CommRing L] [Algebra (RatFunc Fq) L]
    [Algebra (RatFunc (Kc Fq E)) L] [IsScalarTower (RatFunc Fq) (RatFunc (Kc Fq E)) L] (x : L) :
    IsIntegral (Oinf (Kc Fq E)) x ↔ IsIntegral (Oinf Fq) x := by
  have := isScalarTower_Oinf_of Fq E L
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

theorem isIntegral_Oinf_iff (x : E) : IsIntegral (Oinf (Kc Fq E)) x ↔ IsIntegral (Oinf Fq) x :=
  isIntegral_Oinf_iff_of Fq E E x

/-- **`R_∞(k', E) = R_∞(𝔽_q, E)`** (same subring of `E`). -/
def rinfKcEquiv : Rinf (Kc Fq E) E ≃+* Rinf Fq E where
  toFun x := ⟨x.1, (isIntegral_Oinf_iff Fq E x.1).1 x.2⟩
  invFun x := ⟨x.1, (isIntegral_Oinf_iff Fq E x.1).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem rinfKcEquiv_val (x : Rinf (Kc Fq E) E) : ((rinfKcEquiv Fq E x : Rinf Fq E) : E) = (x : E) := rfl

theorem rinfKcEquiv_symm_val (x : Rinf Fq E) :
    (((rinfKcEquiv Fq E).symm x : Rinf (Kc Fq E) E) : E) = (x : E) := rfl

/-- Integrality over `k'[X]` does not see the constant field either. -/
theorem isIntegral_polyKc_iff (x : E) : IsIntegral (Kc Fq E)[X] x ↔ IsIntegral Fq[X] x := by
  let _ := algPolyPoly Fq E
  have := isScalarTower_polyPoly Fq E
  have := isIntegral_polyPoly Fq E
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

/-- **`R_fin(k', E) = R_fin(𝔽_q, E)`** (same subring of `E`). -/
def rfinKcEquiv : Rfin (Kc Fq E) E ≃+* Rfin Fq E where
  toFun x := ⟨x.1, (isIntegral_polyKc_iff Fq E x.1).1 x.2⟩
  invFun x := ⟨x.1, (isIntegral_polyKc_iff Fq E x.1).2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem rfinKcEquiv_val (x : Rfin (Kc Fq E) E) : ((rfinKcEquiv Fq E x : Rfin Fq E) : E) = (x : E) := rfl

theorem rfinKcEquiv_symm_val (x : Rfin Fq E) :
    (((rfinKcEquiv Fq E).symm x : Rfin (Kc Fq E) E) : E) = (x : E) := rfl

end RinfKc

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrExt =====
section

/-!
# S4-Lefschetz L4d (part 1): `K_U` is unramified over a finite subextension `E ⊆ K_U`

Easy direction of "`K_U` is the maximal unramified extension of `E` too": for `E ≤ M` with `M` unramified finite
Galois over `K`, `M` viewed over `E` (`IntermediateField.extendScalars h`) is unramified finite Galois over `E`
(`unrIn_extendScalars`): `Gal(M/E) → Gal(M/K)` is injective and maps inertia into inertia (`mem_inertia_comap`,
`inertia_eq_bot_of_injective`). Hence every point of `K_U` lies in an `E`-unramified finite Galois subextension
(`exists_unrIn_of_mem`), when `E ⊆ K_U` is finite over `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

section InertiaHom

variable {G G' B B' : Type} [Group G] [Group G'] [CommRing B] [CommRing B'] [MulSemiringAction G B]
  [MulSemiringAction G' B']

end InertiaHom

section Ext

variable (A : Type) {K Ω : Type} [CommRing A] [Field K] [Algebra A K] [Field Ω] [Algebra K Ω] [Algebra A Ω]
  [IsScalarTower A K Ω]

variable {E M : IntermediateField K Ω} (h : E ≤ M)

end Ext

section Mem

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- Every point of `K_U` lies in an `E`-unramified finite Galois subextension, for `E ⊆ K_U` finite over `K`. -/
theorem exists_unrIn_of_mem (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (hE : E ≤ maxUnram A K) (z : AlgebraicClosure K) (hz : z ∈ maxUnram A K) :
    ∃ L : IntermediateField E (AlgebraicClosure K), UnrIn A E (AlgebraicClosure K) L ∧ z ∈ L := by
  classical
  obtain ⟨M₁, hM₁, hz₁⟩ := (mem_maxUnram_iff A K z).1 hz
  let b := Module.finBasis K E
  let t : Finset (AlgebraicClosure K) := Finset.univ.image (fun i => ((b i : E) : AlgebraicClosure K))
  have hs : ∀ x ∈ t, x ∈ maxUnram A K := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hE (b i).2
  obtain ⟨N, hN, hadj⟩ := exists_unramSet_of_finite A K t hs
  have hEN : E ≤ N := by
    intro x hx
    apply hadj
    show ((⟨x, hx⟩ : E) : AlgebraicClosure K) ∈ IntermediateField.adjoin K (t : Set (AlgebraicClosure K))
    rw [← b.sum_repr ⟨x, hx⟩, IntermediateField.coe_sum]
    refine sum_mem (fun i _ => ?_)
    rw [IntermediateField.coe_smul]
    exact IntermediateField.smul_mem _ (IntermediateField.subset_adjoin K _
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  have hM := sup_mem_unramSet A K hM₁ hN
  exact ⟨IntermediateField.extendScalars (hEN.trans le_sup_right),
    unrIn_extendScalars A (hEN.trans le_sup_right) hM, (le_sup_left : M₁ ≤ M₁ ⊔ N) hz₁⟩

end Mem

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrFix =====
section

/-!
# S4-Lefschetz L4d (part 2a): helpers for "unramified over `E ⊆ K_U` implies inside `K_U`"

* `conj_mem_inertia`: inertia is stable under conjugation (translate the prime by the conjugating element).
* `mem_fixingSubgroup_iSup`: an automorphism fixes a compositum iff it fixes every piece.
* `exists_unramSet_ge`: a finite `E ⊆ K_U` lies in one unramified finite Galois `N`.
* `fix_of_unram`, `fix_of_unrIn`: an automorphism of `K̄` whose restriction to `M` is inertial fixes every unramified
  Galois `L ⊆ M` over `K`, and (if it fixes `E`) every unramified Galois `L' ⊆ M` over `E`.
* `le_sepCl_of_unrIn`: a Galois extension `L'` of `E ⊆ N` is separable over `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

section Conj

variable {G B : Type} [Group G] [CommRing B] [MulSemiringAction G B]

end Conj

section Fix

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- A finite `E ⊆ K_U` lies in one unramified finite Galois subextension. -/
theorem exists_unramSet_ge (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (hE : E ≤ maxUnram A K) : ∃ N ∈ unramSet A K, E ≤ N := by
  classical
  let b := Module.finBasis K E
  let t : Finset (AlgebraicClosure K) := Finset.univ.image (fun i => ((b i : E) : AlgebraicClosure K))
  have hs : ∀ x ∈ t, x ∈ maxUnram A K := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hE (b i).2
  obtain ⟨N, hN, hadj⟩ := exists_unramSet_of_finite A K t hs
  refine ⟨N, hN, fun x hx => hadj ?_⟩
  show ((⟨x, hx⟩ : E) : AlgebraicClosure K) ∈ IntermediateField.adjoin K (t : Set (AlgebraicClosure K))
  rw [← b.sum_repr ⟨x, hx⟩, IntermediateField.coe_sum]
  refine sum_mem (fun i _ => ?_)
  rw [IntermediateField.coe_smul]
  exact IntermediateField.smul_mem _ (IntermediateField.subset_adjoin K _
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i))))

end Fix

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrMax =====
section

/-!
# S4-Lefschetz L4c+d (part 2b): `K_U` is also the maximal unramified extension of a finite `E ⊆ K_U`

* `unram_normalClosure`: the normal closure `M` of `P` is unramified as soon as every automorphism of `K̄` with
  inertial restriction to `M` fixes `P` (conjugates of an inertia element are inertial at translated primes).
* `le_maxUnram_of_unrIn` (D2): for `E ⊆ K_U` finite over `K`, every finite Galois `L'/E` unramified over `A` lies in
  `K_U` (take `N ⊇ E` in `unramSet`, `M` = normal closure of `L' ⊔ N`).
* `mem_maxUnram_iff_of_sub`: `y ∈ maxUnram A E ↔ ι y ∈ maxUnram A K` for any `ι : Ē ≃ₐ[E] K̄` (D1 + D2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover

noncomputable section

section Max

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- (D2) For `E ⊆ K_U` finite over `K`, a finite Galois `L'/E` unramified over `A` lies in `K_U`. -/
theorem le_maxUnram_of_unrIn (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (hE : E ≤ maxUnram A K) (L' : IntermediateField E (AlgebraicClosure K))
    (hL' : UnrIn A E (AlgebraicClosure K) L') : ∀ z ∈ L', z ∈ maxUnram A K := by
  obtain ⟨N, hN, hEN⟩ := exists_unramSet_ge A K E hE
  have := hN.1
  have := hN.2.1
  have := hL'.1
  have := hL'.2.1
  have : FiniteDimensional K L' := Module.Finite.trans E L'
  have : FiniteDimensional K (L'.restrictScalars K) := inferInstanceAs (FiniteDimensional K L')
  have hsepP : L'.restrictScalars K ⊔ N ≤ separableClosure K (AlgebraicClosure K) :=
    sup_le (le_sepCl_of_unrIn A K hN hEN L') (le_separableClosure K _ N)
  have : Algebra.IsSeparable K (IntermediateField.normalClosure K ↥(L'.restrictScalars K ⊔ N) (AlgebraicClosure K)) := by
    rw [← le_separableClosure_iff]
    exact (IntermediateField.normalClosure_mono _ _ hsepP).trans
      (separableClosure.normalClosure_eq_self K _).le
  have hLM : ∀ x ∈ L', x ∈ IntermediateField.normalClosure K ↥(L'.restrictScalars K ⊔ N) (AlgebraicClosure K) := fun x hx =>
    IntermediateField.le_normalClosure _ ((le_sup_left : L'.restrictScalars K ≤ L'.restrictScalars K ⊔ N)
      ((IntermediateField.mem_restrictScalars K).2 hx))
  have hNM : N ≤ IntermediateField.normalClosure K ↥(L'.restrictScalars K ⊔ N) (AlgebraicClosure K) :=
    le_sup_right.trans (IntermediateField.le_normalClosure _)
  have hM : IntermediateField.normalClosure K ↥(L'.restrictScalars K ⊔ N) (AlgebraicClosure K) ∈ unramSet A K := by
    refine ⟨inferInstance, ⟨⟩, unram_normalClosure A K _ ?_⟩
    intro Q hQ ρ hρ
    have hfN := fix_of_unram A K hNM hN.2.2 Q ρ hρ
    have hfL := fix_of_unrIn A K L' hL' hLM Q ρ (fun x hx => hfN x (hEN hx)) hρ
    have hfix : ρ ∈ (L'.restrictScalars K ⊔ N).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
          hfL x ((IntermediateField.mem_restrictScalars K).1 hx),
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 hfN⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix
  intro z hz
  exact (mem_maxUnram_iff A K z).2 ⟨_, hM, hLM z hz⟩

/-- L4c+d: for `E ⊆ K_U` finite over `K` and any `ι : Ē ≃ₐ[E] K̄`, `y ∈ maxUnram A E ↔ ι y ∈ maxUnram A K`. -/
theorem mem_maxUnram_iff_of_sub (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    (hE : E ≤ maxUnram A K) (ι : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure K) (y : AlgebraicClosure E) :
    y ∈ maxUnram A E ↔ ι y ∈ maxUnram A K := by
  rw [mem_maxUnram_iff_of_equiv A E ι y]
  constructor
  · rintro ⟨L, hL, hy⟩
    exact le_maxUnram_of_unrIn A K E hE L hL _ hy
  · intro h
    exact exists_unrIn_of_mem A K E hE _ h

end Max

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Pi1Sub =====
section

/-!
# S4-Lefschetz L4e: `π₁` of a finite subextension `E ⊆ K_U` is the subgroup of `π₁(K)` fixing `E`

`ιE : Ē ≃ₐ[E] K̄`; `map_maxUnram`: `ιE` maps `K_U(E)` onto `K_U` (as `E`-field), giving `jE`; `theta`:
`π₁(E) → π₁(K)`, `σ ↦ jE σ jE⁻¹`, injective, continuous, with range the automorphisms fixing `E`; `thetaHomeo`:
`π₁(E) ≃ₜ* Δ` for `Δ` the fixing group of `E`; `exists_sub_of_isOpen`: every open `Δ` is such a fixing group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open GalCover CurveCoh Topology

noncomputable section

section Pi1Sub

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K)

instance isAlgClosure_sub : IsAlgClosure E (AlgebraicClosure K) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) E⟩

/-- A chosen `Ē ≃ₐ[E] K̄`. -/
def ιE : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure K :=
  IsAlgClosure.equiv E (AlgebraicClosure E) (AlgebraicClosure K)

theorem map_maxUnram [FiniteDimensional K E] :
    (maxUnram A E).map (ιE K E : AlgebraicClosure E →ₐ[E] AlgebraicClosure K) =
      IntermediateField.extendScalars hE := by
  ext y
  rw [IntermediateField.mem_map, IntermediateField.mem_extendScalars]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_maxUnram_iff_of_sub A K E hE (ιE K E) x).1 hx
  · intro hy
    refine ⟨(ιE K E).symm y, (mem_maxUnram_iff_of_sub A K E hE (ιE K E) _).2 ?_, ?_⟩
    · rwa [AlgEquiv.apply_symm_apply]
    · exact (ιE K E).apply_symm_apply y

/-- `K_U(E) ≃ₐ[E] K_U`. -/
def jE [FiniteDimensional K E] : maxUnram A E ≃ₐ[E] IntermediateField.extendScalars hE :=
  (IntermediateField.equivMap (maxUnram A E) (ιE K E : AlgebraicClosure E →ₐ[E] AlgebraicClosure K)).trans
    (IntermediateField.equivOfEq (map_maxUnram A K E hE))

/-- `π₁(E) → π₁(K)`, `σ ↦ jE σ jE⁻¹`. -/
def theta [FiniteDimensional K E] : Pi1 A E →* Pi1 A K :=
  (galExt hE).comp (jE A K E hE).autCongr.toMonoidHom

theorem theta_apply [FiniteDimensional K E] (σ : Pi1 A E) (x : maxUnram A K) :
    theta A K E hE σ x = (eExt hE).symm (jE A K E hE (σ ((jE A K E hE).symm (eExt hE x)))) := rfl

theorem theta_injective [FiniteDimensional K E] : Function.Injective (theta A K E hE) :=
  (galExt_injective hE).comp (jE A K E hE).autCongr.injective

theorem theta_fix [FiniteDimensional K E] (σ : Pi1 A E) {x : AlgebraicClosure K} (hx : x ∈ E) :
    theta A K E hE σ ⟨x, hE hx⟩ = ⟨x, hE hx⟩ := by
  have h1 : eExt hE ⟨x, hE hx⟩ = algebraMap E (IntermediateField.extendScalars hE) ⟨x, hx⟩ := Subtype.ext rfl
  rw [theta_apply, h1, AlgEquiv.commutes, AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

theorem mem_range_theta [FiniteDimensional K E] (τ : Pi1 A K) :
    τ ∈ (theta A K E hE).range ↔ ∀ x (hx : x ∈ E), τ ⟨x, hE hx⟩ = ⟨x, hE hx⟩ := by
  constructor
  · rintro ⟨σ, rfl⟩ x hx
    exact theta_fix A K E hE σ hx
  · intro h
    let τE : IntermediateField.extendScalars hE ≃ₐ[E] IntermediateField.extendScalars hE :=
      { ((eExt hE).symm.trans (τ.trans (eExt hE))).toRingEquiv with
        commutes' := fun e => by
          show eExt hE (τ ⟨(e : AlgebraicClosure K), hE e.2⟩) = _
          rw [h _ e.2]
          rfl }
    refine ⟨(jE A K E hE).autCongr.symm τE, ?_⟩
    show galExt hE ((jE A K E hE).autCongr ((jE A K E hE).autCongr.symm τE)) = τ
    rw [MulEquiv.apply_symm_apply]
    ext x
    rfl

theorem theta_continuous [FiniteDimensional K E] : Continuous (theta A K E hE) := by
  refine continuous_of_continuousAt_one (theta A K E hE) ?_
  intro s hs
  rw [map_one] at hs
  rw [Filter.mem_map]
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff K (maxUnram A K) s).1 hs
  have := hF
  let b := Module.finBasis K F
  let W : Set (Pi1 A E) :=
    ⋂ i, (fixElt A E ((jE A K E hE).symm (eExt hE (b i : maxUnram A K))) : Set (Pi1 A E))
  have hW : IsOpen W := isOpen_iInter_of_finite fun i => fixElt_isOpen A E _
  have h1 : (1 : Pi1 A E) ∈ W := Set.mem_iInter.2 fun i => (fixElt A E _).one_mem
  refine Filter.mem_of_superset (hW.mem_nhds h1) ?_
  intro σ hσ
  have hσ' : ∀ i, theta A K E hE σ (b i : maxUnram A K) = (b i : maxUnram A K) := by
    intro i
    have h : σ ((jE A K E hE).symm (eExt hE (b i : maxUnram A K))) =
        (jE A K E hE).symm (eExt hE (b i : maxUnram A K)) := Set.mem_iInter.1 hσ i
    rw [theta_apply, h, AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]
  apply hFs
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hlin : (theta A K E hE σ).toLinearMap ∘ₗ F.val.toLinearMap = F.val.toLinearMap :=
    b.ext fun i => hσ' i
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end Pi1Sub

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_Pi1Geo =====
section

/-!
# S4-Lefschetz L4f: geometric `π₁` and Frobenius lifts under `theta` and under a change of `A`

* `fixConst_iff_of_conj` / `frobConst_iff_of_conj`: "fixes the constants" and "acts as `x ↦ x^q` on the constants"
  are invariant under conjugation by a ring isomorphism.
* `kE : K_U ≃+* K_U(E)` with `theta σ = kE⁻¹ σ kE`; `theta_mem_pi1geo_iff`, `theta_isFrobLift_iff`.
* `isConst_pow_iff`, `pi1geo_pow`: the constants of level `q^d` are those of level `q` (`d ≥ 1`);
  `IsFrobLift.pow'`: `φ^d` is a `q^d`-Frobenius lift.
* `pi1Congr h : π₁(A) ≃ₜ* π₁(B)` for `h : K_U(A) = K_U(B)`, compatible with `pi1geo` and `IsFrobLift`.
* `pi1Kc : π₁(Rfin k' E) ≃ₜ* π₁(𝔽_q[X], E)` for the full constant field `k' = Kc 𝔽_q E`, with
  `pi1Kc_mem_pi1geo_iff` (level `#k'` on the left, `q` on the right) and `pi1Kc_isFrobLift_iff`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh Topology

noncomputable section

/-! ### Conjugation invariance -/

section Conj

variable {L₁ L₂ : Type} [Field L₁] [Field L₂] (k : L₁ ≃+* L₂) (q : ℕ)

end Conj

/-! ### Levels `q^d` versus `q` -/

section Pow

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

end Pow

/-! ### `theta` -/

section Theta

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K) [FiniteDimensional K E]

/-- `K_U ≃+* K_U(E)`, the identification underlying `theta`. -/
def kE : maxUnram A K ≃+* maxUnram A E :=
  (eExt hE).toRingEquiv.trans (jE A K E hE).symm.toRingEquiv

theorem theta_kE (σ : Pi1 A E) (x : maxUnram A K) :
    kE A K E hE (theta A K E hE σ x) = σ (kE A K E hE x) := by
  show (jE A K E hE).symm (eExt hE ((eExt hE).symm (jE A K E hE (σ ((jE A K E hE).symm (eExt hE x)))))) =
    σ ((jE A K E hE).symm (eExt hE x))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]

theorem theta_mem_pi1geo_iff (q : ℕ) (σ : Pi1 A E) :
    theta A K E hE σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A E q :=
  fixConst_iff_of_conj (kE A K E hE) q (fun x => theta A K E hE σ x) (fun y => σ y)
    (fun x => (theta_kE A K E hE σ x).symm)

theorem theta_isFrobLift_iff (q : ℕ) (σ : Pi1 A E) :
    IsFrobLift A K q (theta A K E hE σ) ↔ IsFrobLift A E q σ :=
  frobConst_iff_of_conj (kE A K E hE) q (fun x => theta A K E hE σ x) (fun y => σ y)
    (fun x => (theta_kE A K E hE σ x).symm)

variable (Δ : Subgroup (Pi1 A K))
  (hΔ : ∀ τ : Pi1 A K, τ ∈ Δ ↔ ∀ x (hx : x ∈ E), τ ⟨x, hE hx⟩ = ⟨x, hE hx⟩)

end Theta

/-! ### Changing `A` with the same `K_U` -/

section Congr

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

/-- `σ ↦ e σ e⁻¹` for `e = equivOfEq h`. -/
def pi1CongrEquiv (h : maxUnram A K = maxUnram B K) : Pi1 A K ≃* Pi1 B K :=
  (IntermediateField.equivOfEq h).autCongr

theorem pi1CongrEquiv_conj (h : maxUnram A K = maxUnram B K) (σ : Pi1 A K) (x : maxUnram A K) :
    pi1CongrEquiv h σ (IntermediateField.equivOfEq h x) = IntermediateField.equivOfEq h (σ x) := by
  rw [pi1CongrEquiv, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

theorem pi1CongrEquiv_continuous (h : maxUnram A K = maxUnram B K) : Continuous (pi1CongrEquiv h) :=
  autCongr_equivOfEq_continuous h

/-- `π₁(A) ≃ₜ* π₁(B)` when `K_U(A) = K_U(B)`. -/
def pi1Congr (h : maxUnram A K = maxUnram B K) : Pi1 A K ≃ₜ* Pi1 B K :=
  have hc : Continuous (pi1CongrEquiv h) := pi1CongrEquiv_continuous h
  have : T2Space (Pi1 B K) := krullTopology_t2
  { pi1CongrEquiv h with
    continuous_toFun := hc
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := (pi1CongrEquiv h).toEquiv) hc).symm.continuous }

theorem pi1Congr_apply (h : maxUnram A K = maxUnram B K) (σ : Pi1 A K) :
    pi1Congr h σ = pi1CongrEquiv h σ := rfl

theorem pi1Congr_mem_pi1geo_iff (h : maxUnram A K = maxUnram B K) (q : ℕ) (σ : Pi1 A K) :
    pi1Congr h σ ∈ pi1geo B K q ↔ σ ∈ pi1geo A K q :=
  (fixConst_iff_of_conj (IntermediateField.equivOfEq h).toRingEquiv q (fun x => σ x)
    (fun y => pi1CongrEquiv h σ y) (fun x => pi1CongrEquiv_conj h σ x)).symm

theorem pi1Congr_isFrobLift_iff (h : maxUnram A K = maxUnram B K) (q : ℕ) (σ : Pi1 A K) :
    IsFrobLift B K q (pi1Congr h σ) ↔ IsFrobLift A K q σ :=
  (frobConst_iff_of_conj (IntermediateField.equivOfEq h).toRingEquiv q (fun x => σ x)
    (fun y => pi1CongrEquiv h σ y) (fun x => pi1CongrEquiv_conj h σ x)).symm

end Congr

/-! ### The full constant field -/

section KcPi1

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

theorem card_Kc_eq_pow : Fintype.card (Kc Fq E) = Fintype.card Fq ^ Module.finrank Fq (Kc Fq E) :=
  Module.card_eq_pow_finrank

theorem finrank_Kc_pos : 0 < Module.finrank Fq (Kc Fq E) := Module.finrank_pos

/-- `π₁` of `E` over its full constant field `k'` is `π₁` over `𝔽_q[X]`. -/
def pi1Kc : Pi1 (Rfin (Kc Fq E) E) E ≃ₜ* Pi1 Fq[X] E := pi1Congr (maxUnram_rfin_Kc Fq E)

/-- `π₁^geo` at level `#k'` over `k'` is `π₁^geo` at level `q` over `𝔽_q[X]`. -/
theorem pi1Kc_mem_pi1geo_iff (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    pi1Kc Fq E σ ∈ pi1geo Fq[X] E (Fintype.card Fq) ↔
      σ ∈ pi1geo (Rfin (Kc Fq E) E) E (Fintype.card (Kc Fq E)) := by
  rw [card_Kc_eq_pow Fq E, pi1geo_pow (Rfin (Kc Fq E) E) E (Fintype.card Fq) (finrank_Kc_pos Fq E)]
  exact pi1Congr_mem_pi1geo_iff (maxUnram_rfin_Kc Fq E) (Fintype.card Fq) σ

theorem pi1Kc_isFrobLift_iff (q : ℕ) (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    IsFrobLift Fq[X] E q (pi1Kc Fq E σ) ↔ IsFrobLift (Rfin (Kc Fq E) E) E q σ :=
  pi1Congr_isFrobLift_iff (maxUnram_rfin_Kc Fq E) q σ

end KcPi1

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ChartE =====
section

/-!
# S4-Lefschetz L4g part 1: `K_U` of a finite subcover and the group map to `π₁(U)`

`K` is a function field over `𝔽_q` (S3-Places coordinates), `E ⊆ K_U` a finite subextension inside `K̄`,
`k' = Kc 𝔽_q E` its full constant field. CP4 for `E` lives on `K_U(E) = maxUnram (R_fin(k', E)) E` (inside `Ē`)
and `π₁(E) = Pi1 (R_fin(k', E)) E`; the base lives on `maxUnram (R_fin(𝔽_q, K)) K` (inside `K̄`).
* `uE : K_U(E) ≃+* K_U` with values `ι_E` (`uE_val`);
* `thetaE : π₁(E) →* π₁(U)` (= `pi1Congr ∘ theta ∘ pi1Kc`; equivariance `uE (σ y) = thetaE σ (uE y)` is part 2);
* the tower `O_∞ → R_∞(K) → K_U` and `IsIntegral R_∞(K) x ↔ IsIntegral O_∞ (x : K̄)` (`isIntegral_chartK_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh

noncomputable section

section ChartE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

include hE in
theorem mem_uE (y : maxUnram (Rfin (Kc Fq E) E) E) :
    ιE K E (y : AlgebraicClosure E) ∈ maxUnram (Rfin Fq K) K := by
  have key : ∀ z : AlgebraicClosure E, z ∈ maxUnram (Rfin (Kc Fq E) E) E → z ∈ maxUnram Fq[X] E := by
    intro z hz
    rwa [maxUnram_rfin_Kc Fq E] at hz
  have h1 : (y : AlgebraicClosure E) ∈ maxUnram Fq[X] E := key _ y.2
  rw [maxUnram_rfin Fq K]
  exact (mem_maxUnram_iff_of_sub Fq[X] K E hE (ιE K E) _).1 h1

include hE in
theorem mem_uE_symm (x : maxUnram (Rfin Fq K) K) :
    (ιE K E).symm (x : AlgebraicClosure K) ∈ maxUnram (Rfin (Kc Fq E) E) E := by
  rw [maxUnram_rfin_Kc Fq E, mem_maxUnram_iff_of_sub Fq[X] K E hE (ιE K E), AlgEquiv.apply_symm_apply,
    ← maxUnram_rfin Fq K]
  exact x.2

/-- `K_U(E) ≃+* K_U`, `y ↦ ι_E y` (built from values: composites of `equivOfEq` along `maxUnram` equalities hit
kernel deterministic timeouts). -/
def uE : maxUnram (Rfin (Kc Fq E) E) E ≃+* maxUnram (Rfin Fq K) K where
  toFun y := ⟨ιE K E y, mem_uE Fq K E hE y⟩
  invFun x := ⟨(ιE K E).symm x, mem_uE_symm Fq K E hE x⟩
  left_inv y := Subtype.ext ((ιE K E).symm_apply_apply _)
  right_inv x := Subtype.ext ((ιE K E).apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul (ιE K E) _ _)
  map_add' a b := Subtype.ext (map_add (ιE K E) _ _)

theorem uE_val (y : maxUnram (Rfin (Kc Fq E) E) E) :
    ((uE Fq K E hE y : maxUnram (Rfin Fq K) K) : AlgebraicClosure K) = ιE K E (y : AlgebraicClosure E) := rfl

theorem uE_symm_val (x : maxUnram (Rfin Fq K) K) :
    (((uE Fq K E hE).symm x : maxUnram (Rfin (Kc Fq E) E) E) : AlgebraicClosure E) =
      (ιE K E).symm (x : AlgebraicClosure K) := rfl

/-- `π₁(E) →* π₁(U)` over the CP4 charts of both sides. -/
def thetaE : Pi1 (Rfin (Kc Fq E) E) E →* Pi1 (Rfin Fq K) K :=
  (pi1Congr (maxUnram_rfin Fq K).symm).toMulEquiv.toMonoidHom.comp
    ((theta Fq[X] K E hE).comp (pi1Kc Fq E).toMulEquiv.toMonoidHom)

theorem thetaE_apply (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    thetaE Fq K E hE σ =
      pi1CongrEquiv (maxUnram_rfin Fq K).symm (theta Fq[X] K E hE (pi1CongrEquiv (maxUnram_rfin_Kc Fq E) σ)) :=
  rfl

/-! ### The chart of `K` over `∞` in terms of `O_∞(𝔽_q)` -/

instance towerChartK : IsScalarTower (Oinf Fq) (Rinf Fq K) (maxUnram (Rfin Fq K) K) :=
  IsScalarTower.of_algebraMap_eq fun g => Subtype.ext <| by
    show algebraMap (Oinf Fq) (AlgebraicClosure K) g =
      algebraMap (Rinf Fq K) (AlgebraicClosure K) (algebraMap (Oinf Fq) (Rinf Fq K) g)
    rw [IsScalarTower.algebraMap_apply (Oinf Fq) K (AlgebraicClosure K),
      IsScalarTower.algebraMap_apply (Rinf Fq K) K (AlgebraicClosure K)]
    rfl

/-- An element of `K_U` lies in the chart over `∞` iff it is integral over `O_∞(𝔽_q)` in `K̄`. -/
theorem isIntegral_chartK_iff (x : maxUnram (Rfin Fq K) K) :
    IsIntegral (Rinf Fq K) x ↔ IsIntegral (Oinf Fq) (x : AlgebraicClosure K) := by
  have : Algebra.IsIntegral (Oinf Fq) (Rinf Fq K) := ⟨fun r => integralClosure.isIntegral r⟩
  rw [IntermediateField.coe_isIntegral_iff]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

end ChartE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ChartE2 =====
section

/-!
# S4-Lefschetz L4g part 2: the chart over `∞` of a finite subcover

`E ⊆ K_U` a finite subextension of `K̄`, `k' = Kc 𝔽_q E`. Value lemmas for `jE`, `theta`, `pi1CongrEquiv`
(proved generically, never through `equivOfEq` composites), then:
* `thetaE_val`, `uE_smul`: `uE (σ y) = thetaE σ (uE y)`;
* `isIntegral_chartE_iff`: `IsIntegral R_∞(k', E) y ↔ IsIntegral O_∞(𝔽_q) (y : Ē)`; `isIntegral_iotaE_iff`;
* `chartE : proChart(E) ≃+* proChart(K)` (charts over `∞`), `chartE_smul`, `chartE_symm_smul`;
* boundary primes and inertia correspond: `chartQ`/`chartP`, `isBdryPrime_chartQ/P`, `mem_inertia_chartQ_iff`
  (generic forms `isBdryPrime_comap`, `mem_inertia_comap_iff` for any isomorphism of pro-charts).
Concrete `Ideal.inertia` statements on these charts need `(α := proChart ..)` explicitly (else `α` stays a
metavariable: the chart's `Subalgebra.toSemiring` does not unify with `Ring.toSemiring ?_`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh

noncomputable section

section ValGen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram A K) [FiniteDimensional K E]

theorem jE_val (y : maxUnram A E) :
    ((jE A K E hE y : IntermediateField.extendScalars hE) : AlgebraicClosure K) =
      ιE K E (y : AlgebraicClosure E) := rfl

theorem jE_symm_val (z : IntermediateField.extendScalars hE) :
    (((jE A K E hE).symm z : maxUnram A E) : AlgebraicClosure E) = (ιE K E).symm (z : AlgebraicClosure K) := by
  rw [AlgEquiv.eq_symm_apply, ← jE_val A K E hE, AlgEquiv.apply_symm_apply]

theorem theta_val (σ : Pi1 A E) (x : maxUnram A K) :
    ((theta A K E hE σ x : maxUnram A K) : AlgebraicClosure K) =
      ιE K E ((σ ((jE A K E hE).symm (eExt hE x)) : maxUnram A E) : AlgebraicClosure E) := by
  rw [theta_apply]
  exact jE_val A K E hE _

end ValGen

section EqVal

variable {F L : Type} [Field F] [Field L] [Algebra F L]

end EqVal

section CongrVal

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

theorem pi1CongrEquiv_val (h : maxUnram A K = maxUnram B K) (τ : Pi1 A K) (x : maxUnram B K) :
    ((pi1CongrEquiv h τ x : maxUnram B K) : AlgebraicClosure K) =
      ((τ ((IntermediateField.equivOfEq h).symm x) : maxUnram A K) : AlgebraicClosure K) :=
  autCongr_equivOfEq_coe h τ x

end CongrVal

section ChartGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

end ChartGen

section ChartE2

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

/-- Step 1 of `thetaE_val`: the outer `pi1CongrEquiv`. -/
theorem thetaE_val_o (σ : Pi1 (Rfin (Kc Fq E) E) E) (x : maxUnram (Rfin Fq K) K) :
    ((thetaE Fq K E hE σ x : maxUnram (Rfin Fq K) K) : AlgebraicClosure K) =
      ((theta Fq[X] K E hE (pi1CongrEquiv (maxUnram_rfin_Kc Fq E) σ)
        ((IntermediateField.equivOfEq (maxUnram_rfin Fq K).symm).symm x) : maxUnram Fq[X] K) :
          AlgebraicClosure K) := by
  rw [thetaE_apply]
  exact pi1CongrEquiv_val (maxUnram_rfin Fq K).symm _ x

/-- Step 2 of `thetaE_val`: the inner `pi1CongrEquiv`. -/
theorem thetaE_val_i (σ : Pi1 (Rfin (Kc Fq E) E) E) (w : maxUnram Fq[X] E) :
    ((pi1CongrEquiv (maxUnram_rfin_Kc Fq E) σ w : maxUnram Fq[X] E) : AlgebraicClosure E) =
      ((σ ((IntermediateField.equivOfEq (maxUnram_rfin_Kc Fq E)).symm w) : maxUnram (Rfin (Kc Fq E) E) E) :
        AlgebraicClosure E) :=
  pi1CongrEquiv_val (maxUnram_rfin_Kc Fq E) σ w

/-- Step 3 of `thetaE_val`: the argument is `uE⁻¹ x`. -/
theorem uE_symm_eq (x : maxUnram (Rfin Fq K) K) :
    (IntermediateField.equivOfEq (maxUnram_rfin_Kc Fq E)).symm
      ((jE Fq[X] K E hE).symm (eExt hE ((IntermediateField.equivOfEq (maxUnram_rfin Fq K).symm).symm x))) =
      (uE Fq K E hE).symm x := by
  apply Subtype.ext
  rw [equivOfEq_symm_val, jE_symm_val, eExt_val, equivOfEq_symm_val, uE_symm_val]

/-! ### The chart of `E` over `∞` -/

/-! ### Boundary primes and inertia -/

end ChartE2

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ShapData =====
section

/-!
# S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover

Generic part (`ShapGen`): two pro-charts with boundary data `D` (of `V`) and `D'` (of `U`), an isomorphism
`f : proChart(V) ≃+* proChart(U)` equivariant along an injective `r : π₁(U) →* π₁(V)` with `r⁻¹(Γ) = Γ_U`, and
"stabiliser in `Γ` ⇒ inertia" on `V`. Then `gπ`, `gxT` (from `D.cover`), `gJ` satisfy the three Shapiro
hypotheses `InertiaLift`, `DCover`, `DDisj` of `CurveCoh_ShapiroCone` for `H = range r`.

Concrete part (`ShapE`): `V = K`, `U = E ⊆ K_U` over `k' = Kc 𝔽_q E`, `f = chartE.symm`, `r = thetaE`:
`thetaE_mem_pi1geo_iff`, `thetaE_injective`, `stab_mem_inertia_K`, the objects `bdPiE`, `bdxE`, `bdJE` and
`shap_inertiaLift`, `shap_dCover`, `shap_dDisj`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh CP4a

noncomputable section

section ShapGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

variable {q q' : ℕ} {S T : Type} (D : BdryData A K q R0 S) (D' : BdryData A' K' q' R0' T)
  (f : proChart A K R0 ≃+* proChart A' K' R0')
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) (hD'B : ∀ Q, D'.B Q ↔ IsBdryPrime A' K' R0' Q)

variable (r : Pi1 A' K' →* Pi1 A K) (hf : ∀ σ x, f (r σ • x) = σ • f x) (hr : Function.Injective r)
  (hgeo : ∀ σ, r σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A' K' q')
  (hstab : ∀ Q, IsBdryPrime A K R0 Q → ∀ σ ∈ pi1geo A K q, σ • Q = Q → σ ∈ Q.inertia (Pi1 A K))

end ShapGen

section ShapE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

theorem thetaE_eq (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    thetaE Fq K E hE σ = pi1Congr (maxUnram_rfin Fq K).symm (theta Fq[X] K E hE (pi1Kc Fq E σ)) := rfl

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end ShapE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_BlockE =====
section

/-!
# S4-Lefschetz, L3d3b: the cover `E` of an open subgroup, in the `Rfin` chart

For an open `H ≤ π₁(U)` (`U = Spec Rfin`): `exists_E_of_open` gives a finite separable `E ⊆ K_U` with
`range thetaE = H`, every `τ ∈ H` fixing `E` and every point of `K_U` fixed by `H` lying in `E` (Galois
correspondence through `pi1Congr`). `thetaE_isFrobLift_iff` transports Frobenius lifts along `thetaE` at any level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open Places GalCover CurveCoh CP4a

section Val

variable {K : Type} [Field K]

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A K] [Algebra B K]

/-- `pi1Congr` acts on underlying points of `K̄` as the original automorphism. -/
theorem pi1Congr_val (h : maxUnram A K = maxUnram B K) (σ : Pi1 A K) (x : maxUnram A K) (y : maxUnram B K)
    (hxy : (x : AlgebraicClosure K) = y) :
    ((pi1Congr h σ y : maxUnram B K) : AlgebraicClosure K) = (σ x : AlgebraicClosure K) :=
  autCongr_val h σ x y hxy

end Val

section BlockE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

/-- `thetaE` matches Frobenius lifts (any level). -/
theorem thetaE_isFrobLift_iff (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (hE : E ≤ maxUnram Fq[X] K) (q : ℕ) (σ : Pi1 (Rfin (Kc Fq E) E) E) :
    IsFrobLift (Rfin Fq K) K q (thetaE Fq K E hE σ) ↔ IsFrobLift (Rfin (Kc Fq E) E) E q σ :=
  (pi1Congr_isFrobLift_iff (maxUnram_rfin Fq K).symm q (theta Fq[X] K E hE (pi1Kc Fq E σ))).trans
    ((theta_isFrobLift_iff Fq[X] K E hE q (pi1Kc Fq E σ)).trans (pi1Kc_isFrobLift_iff Fq E q σ))

/-- `range thetaE` is the `pi1Congr`-image of `range theta`. -/
theorem mem_range_thetaE_iff (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (hE : E ≤ maxUnram Fq[X] K) (τ : Pi1 (Rfin Fq K) K) :
    τ ∈ (thetaE Fq K E hE).range ↔ (pi1Congr (maxUnram_rfin Fq K).symm).symm τ ∈ (theta Fq[X] K E hE).range := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨pi1Kc Fq E σ, by rw [thetaE_eq, ContinuousMulEquiv.symm_apply_apply]⟩
  · rintro ⟨τ', hτ⟩
    refine ⟨(pi1Kc Fq E).symm τ', ?_⟩
    rw [thetaE_eq, ContinuousMulEquiv.apply_symm_apply, hτ, ContinuousMulEquiv.apply_symm_apply]

/-- A `τ'` fixing `E ⊆ K_U` (`Fq[X]` chart) fixes the points of `E` in the `Rfin` chart. -/
theorem pi1Congr_fix (E : IntermediateField K (AlgebraicClosure K)) (hE : E ≤ maxUnram Fq[X] K) (τ' : Pi1 Fq[X] K)
    (hτ : ∀ x (hx : x ∈ E), τ' ⟨x, hE hx⟩ = ⟨x, hE hx⟩) (y : maxUnram (Rfin Fq K) K)
    (hy : (y : AlgebraicClosure K) ∈ E) : pi1Congr (maxUnram_rfin Fq K).symm τ' y = y := by
  apply Subtype.ext
  exact (pi1Congr_val (maxUnram_rfin Fq K).symm τ' ⟨(y : AlgebraicClosure K), hE hy⟩ y (Subtype.coe_mk _ _)).trans
    ((congrArg Subtype.val (hτ _ hy)).trans (Subtype.coe_mk _ _))

end BlockE

section FixGen

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

end FixGen

section CongrGen

variable {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A K] [Algebra B K]

end CongrGen

section EOpen

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]

end EOpen

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_PtLift =====
section

/-!
# S4-Lefschetz, L5c4a: the block count through `π₁(U)` (generic), block subgroup lemmas, open fixers

* `liftHom r hr π hker : G →* Gf` (`π` through a surjection `r` with `ker r ≤ ker π`), `liftHom_apply`;
* `card_fixed_blk_lift`: `card_fixed_blk` with `Γ`, `F`, `π` given upstairs (in `P`, e.g. `π₁(U)`), through
  `r : P →* G`: the count is `#{p ∈ π(Γ) | (p a)⁻¹ π(F) (p a) = γ}`;
* `mem_blkH_of_fix_iff` (`x ζ = ζ`: `x ∈ H_ω ↔ π x = 1`), `mem_blkH_of_ginv_iff` (`x ζ = g⁻¹ ζ`:
  `x ∈ H_ω ↔ π x = π g⁻¹`);
* `mem_fixRestrict_iff`, `isOpen_fixRestrict`, `resPt_eq_one_of_fix`: the fixer of a finite level `L ≤ K_U` is open
  and is `ker resPt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open GalCover CurveCoh

section LiftHom

variable {P G Gf : Type} [Group P] [Group G] [Group Gf]

theorem eq_of_lift_eq (r : P →* G) (π : P →* Gf) (hker : ∀ σ, r σ = 1 → π σ = 1) {x y : P}
    (h : r x = r y) : π x = π y := by
  have h1 := hker (x⁻¹ * y) (by rw [map_mul, map_inv, h, inv_mul_cancel])
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

end LiftHom

section PtLift

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {G : Type} [Group G] [MulSemiringAction G B]
  {Ω : Type} [Field Ω]
variable [Finite G] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (H : Subgroup G) {C : Type} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [SMulCommClass H C B] [Algebra.IsInvariant C B H]

end PtLift

section BlkFix

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 A K →* Gf) (g : Pi1 A K) (ζ : maxUnram A K)

end BlkFix

section FixRestrict

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
variable {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)

end FixRestrict

end

end Lefschetz
end RamanujanPetersson


end


