-- Prove2me | Definitions.Def_RPLib_S4_LefPack11
-- name    : RPLib_S4_LefPack11
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T18:53:22.99226+00:00
-- url     : https://prove2.me/theorems/26fcba42-2d07-405e-98bb-1462822244f6
-- title:
--   Lefschetz trace formula library (Grothendieck–Lefschetz trace formula mod ℓⁿ on curves over finite fields), part 11 of 32
-- statement:
--   Part 11 of 32 of the Lefschetz trace formula library: the following library modules, in dependency order.
--
--   * `Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
--   * `Def_RP_Lefschetz_ConeComp`: S4-Lefschetz, L3a: composition law for the cone Frobenius
--   * `Def_RP_Lefschetz_Euler`: S4-Lefschetz L1: Euler characteristic of traces for a three-term complex
--   * `Def_RP_Lefschetz_ConeEuler`: S4-Lefschetz, L3e2a: Euler characteristic of the cone Frobenius
--   * `Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
--   * `Def_RP_Lefschetz_ResK`: S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist
--   * `Def_RP_Lefschetz_PtExt`: S4-Lefschetz, L5b (part 1): points extend along integral extensions
--   * `Def_RP_Lefschetz_Pow`: S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius
--   * `Def_RP_Lefschetz_Cancel`: S4-Lefschetz (L2): cancelling a non-unit factor by lifting the coefficient level
--   * `Def_RP_Lefschetz_ZFin1`: S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part
--
--   **Formalization note.** Library package of a formalization of the Grothendieck–Lefschetz trace formula modulo $\ell^n$ for a lisse sheaf of free $\mathbb Z/\ell^n$-modules on an affine curve over a finite field, on the compactly supported cochain complex of the geometric fundamental group. The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki, exposé 279 (1964/65); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Rapport sur la formule des traces »; J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §13

import Mathlib
import Definitions.Def_RPLib_S4_CurveCohPair
import Definitions.Def_RPLib_S4_CDPack05
import Definitions.Def_RPLib_S4_CDPack03
import Definitions.Def_RPLib_S4_CDPack18e
import Definitions.Def_RPLib_S4_CDPack06
import Definitions.Def_RPLib_S4_CDPack06b

/-!
# Lefschetz trace formula library package, part 11 of 32

Library modules of the formalization of the Grothendieck-Lefschetz trace formula mod `l^n` for lisse sheaves on an
affine curve over a finite field (`RamanujanPetersson.Lefschetz.lefschetz_main`). Each module below is copied
verbatim (import lines removed) inside its own `section` ... `end`:

* `Def_RP_Lefschetz_FrobCong`: S4-Lefschetz, L4h part 1: congruences for the Frobenius on `H¹_c` and `H²_c`
* `Def_RP_Lefschetz_ConeComp`: S4-Lefschetz, L3a: composition law for the cone Frobenius
* `Def_RP_Lefschetz_Euler`: S4-Lefschetz L1: Euler characteristic of traces for a three-term complex
* `Def_RP_Lefschetz_ConeEuler`: S4-Lefschetz, L3e2a: Euler characteristic of the cone Frobenius
* `Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
* `Def_RP_Lefschetz_ResK`: S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist
* `Def_RP_Lefschetz_PtExt`: S4-Lefschetz, L5b (part 1): points extend along integral extensions
* `Def_RP_Lefschetz_Pow`: S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius
* `Def_RP_Lefschetz_Cancel`: S4-Lefschetz (L2): cancelling a non-unit factor by lifting the coefficient level
* `Def_RP_Lefschetz_ZFin1`: S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part
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

theorem bdryCompat_inner (γ0 : Γ) : BdryCompat Γ I (γ0 : G) id (fun _ => γ0⁻¹) := by
  intro s g hg
  have e : ((γ0⁻¹ : Γ) : G)⁻¹ * ((γ0 : G)⁻¹ * g * γ0) * ((γ0⁻¹ : Γ) : G) = g := by
    simp only [Subgroup.coe_inv, inv_inv]
    group
  beta_reduce
  rw [e]
  exact hg

theorem frobH1c_inner (γ0 : Γ) :
    frobH1c ρ Γ I (γ0 : G) id (fun _ => γ0⁻¹) (bdryCompat_inner Γ I γ0) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun p => ?_)
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk p
  have hc : (p : (Γ → M) × (S → M)).1 ∈ Z1 ρ Γ := p.2.1
  refine (Submodule.Quotient.eq _).mpr (Submodule.mem_comap.mpr ((mem_B1c ρ Γ I _).mpr
    ⟨(Z1c ρ Γ I).sub_mem (twistc_mem_Z1c ρ Γ I _ _ _ (bdryCompat_inner Γ I γ0) p.2) p.2, (p : (Γ → M) × (S → M)).1 γ0, fun g => ?_, fun s => ?_⟩))
  · change (twistc ρ Γ (γ0 : G) id (fun _ => γ0⁻¹) (p : (Γ → M) × (S → M)) - (p : (Γ → M) × (S → M))).1 g = _
    simp only [Prod.fst_sub, Pi.sub_apply, twistc_fst, twist_apply]
    have e : (γ0 * conjΓ Γ (γ0 : G) g : Γ) = g * γ0 := by
      ext
      simp [mul_assoc]
    have h1 := hc.2 γ0 (conjΓ Γ (γ0 : G) g)
    rw [e, hc.2 g γ0, eq_comm, ← sub_eq_iff_eq_add'] at h1
    rw [← h1]
    abel
  · have h2 := hc.2 γ0 γ0⁻¹
    rw [mul_inv_cancel, Z1_one ρ Γ hc] at h2
    change (twistc ρ Γ (γ0 : G) id (fun _ => γ0⁻¹) (p : (Γ → M) × (S → M)) - (p : (Γ → M) × (S → M))).2 s = _
    simp only [Prod.snd_sub, Pi.sub_apply, twistc_snd, id_eq, map_sub, Subgroup.coe_inv,
      Representation.self_inv_apply]
    rw [eq_neg_of_add_eq_zero_right h2.symm]
    abel

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

/-- The correcting elements of `F(ψ, τ, h)^m`. -/
def hpow (ψ : G) (τ : S → S) (h : S → Γ) : ℕ → S → Γ
  | 0 => fun _ => 1
  | m + 1 => fun s => conjΓ Γ (ψ ^ m) (h s) * hpow ψ τ h m (τ s)

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

theorem frobH1c_pow {ψ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ τ h) (m : ℕ) :
    frobH1c ρ Γ I ψ τ h hI ^ m =
      frobH1c ρ Γ I (ψ ^ m) τ^[m] (hpow Γ ψ τ h m) (bdryCompat_pow Γ I hI m) := by
  induction m with
  | zero =>
    rw [pow_zero (frobH1c ρ Γ I ψ τ h hI)]
    refine Submodule.linearMap_qext _ (LinearMap.ext fun p => ?_)
    show H1c.mk ρ Γ I p = H1c.mk ρ Γ I _
    exact congrArg (H1c.mk ρ Γ I) (Subtype.ext (twistc_pow_zero ρ Γ ψ τ h p.2.1).symm)
  | succ m ih =>
    rw [pow_succ' (frobH1c ρ Γ I ψ τ h hI) m, ih, Module.End.mul_eq_comp, frobH1c_comp]
    exact frobH1c_congr ρ Γ I (pow_succ' ψ m).symm rfl rfl _ _

/-! ## Changing the correcting elements inside the inertia -/

theorem twistc_congr_h (ψ : G) (τ : S → S) (h h' : S → Γ) (hh : ∀ s, (((h s)⁻¹ * h' s : Γ) : G) ∈ I (τ s))
    {p : (Γ → M) × (S → M)} (hp : p ∈ Z1c ρ Γ I) : twistc ρ Γ ψ τ h' p = twistc ρ Γ ψ τ h p := by
  refine Prod.ext rfl (funext fun s => ?_)
  rw [twistc_snd, twistc_snd]
  congr 1
  rw [← mul_inv_cancel_left (h s) (h' s), hp.1.2, hp.2 (τ s) _ (hh s)]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
  abel

theorem frobH1c_congr_h (ψ : G) (τ : S → S) (h h' : S → Γ) (hh : ∀ s, (((h s)⁻¹ * h' s : Γ) : G) ∈ I (τ s))
    (hI : BdryCompat Γ I ψ τ h) (hI' : BdryCompat Γ I ψ τ h') :
    frobH1c ρ Γ I ψ τ h' hI' = frobH1c ρ Γ I ψ τ h hI := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun p => ?_)
  show H1c.mk ρ Γ I _ = H1c.mk ρ Γ I _
  exact congrArg (H1c.mk ρ Γ I) (Subtype.ext (twistc_congr_h ρ Γ I ψ τ h h' hh p.2))

/-! ## `H²_c` -/

theorem frobH2c_comp (ψ ψ' : G) (χ χ' : k) :
    frobH2c ρ Γ ψ χ ∘ₗ frobH2c ρ Γ ψ' χ' = frobH2c ρ Γ (ψ * ψ') (χ * χ') := by
  refine Representation.Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
  simp only [LinearMap.comp_apply, frobH2c_mk, map_smul, smul_smul, map_mul, Module.End.mul_apply]
  rw [mul_comm χ χ']

theorem frobH2c_geo (γ0 : Γ) : frobH2c ρ Γ (γ0 : G) 1 = LinearMap.id := by
  refine Representation.Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
  simp only [LinearMap.comp_apply, frobH2c_mk, one_smul, LinearMap.id_apply]
  exact Representation.Coinvariants.mk_self_apply (ρ.comp Γ.subtype) γ0 x

theorem frobH2c_mul_geo (ψ : G) (χ : k) (γ0 : Γ) : frobH2c ρ Γ (ψ * γ0) χ = frobH2c ρ Γ ψ χ := by
  calc frobH2c ρ Γ (ψ * γ0) χ = frobH2c ρ Γ (ψ * γ0) (χ * 1) := by rw [mul_one]
    _ = frobH2c ρ Γ ψ χ ∘ₗ frobH2c ρ Γ (γ0 : G) 1 := (frobH2c_comp ρ Γ ψ γ0 χ 1).symm
    _ = frobH2c ρ Γ ψ χ := by rw [frobH2c_geo, LinearMap.comp_id]

theorem frobH2c_pow (ψ : G) (χ : k) (m : ℕ) : frobH2c ρ Γ ψ χ ^ m = frobH2c ρ Γ (ψ ^ m) (χ ^ m) := by
  induction m with
  | zero =>
    refine Representation.Coinvariants.hom_ext (LinearMap.ext fun x => ?_)
    simp [frobH2c_mk]
  | succ m ih =>
    rw [pow_succ' (frobH2c ρ Γ ψ χ) m, ih, Module.End.mul_eq_comp, frobH2c_comp, ← pow_succ', ← pow_succ']

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

/-- The cone Frobenius on `K¹` is `twistc` on the underlying pairs. -/
theorem frob1_val (ψ : G) (t : S → S) (h : S → Γ) (p : Z1 ρ Γ × (S → M)) :
    ((((frob1 ρ Γ ψ t h p).1 : Z1 ρ Γ) : Γ → M), (frob1 ρ Γ ψ t h p).2) =
      twistc ρ Γ ψ t h (((p.1 : Z1 ρ Γ) : Γ → M), p.2) := rfl

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

-- ===== S4.Def_RP_Lefschetz_Euler =====
section

/-!
# S4-Lefschetz L1: Euler characteristic of traces for a three-term complex

Over a local ring, for a complex `K⁰ → K¹ → K²` of free finite modules with injective `d⁰` and free finite
cohomology `H¹ = ker d¹ / im d⁰`, `H² = coker d¹`, an endomorphism `(f⁰, f¹, f²)` of the complex satisfies
`Tr f⁰ - Tr f¹ + Tr f² = Tr(f | H²) - Tr(f | H¹)` (`euler3`). The tools: traces along a split short exact sequence
(`trace_split`), the splitting of `0 → Q → P → P ⧸ Q → 0` when `P ⧸ Q` is free (`trace_eq_restrict_add_quot`), and
freeness of such `Q` over a local ring (`sub_free_finite`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace Lefschetz

open LinearMap (trace)

noncomputable section

section Intw

variable {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Traces agree along a linear equivalence intertwining two endomorphisms. -/
theorem trace_intw (e : V ≃ₗ[R] W) {f : V →ₗ[R] V} {g : W →ₗ[R] W} (hfg : ∀ v, e (f v) = g (e v)) :
    trace R V f = trace R W g := by
  have hg : g = e.conj f := LinearMap.ext fun w => by
    rw [LinearEquiv.conj_apply_apply, hfg, LinearEquiv.apply_symm_apply]
  rw [hg, LinearMap.trace_conj']

end Intw

section Split

variable {R : Type*} [CommRing R] {P' P P'' : Type*} [AddCommGroup P'] [Module R P'] [AddCommGroup P] [Module R P]
  [AddCommGroup P''] [Module R P'']

/-- Additivity of traces along a split short exact sequence of free finite modules. -/
theorem trace_split [Module.Free R P'] [Module.Finite R P'] [Module.Free R P] [Module.Finite R P]
    [Module.Free R P''] [Module.Finite R P''] {i : P' →ₗ[R] P} {r : P →ₗ[R] P'} {π : P →ₗ[R] P''}
    {s : P'' →ₗ[R] P} (hri : r ∘ₗ i = LinearMap.id) (hπs : π ∘ₗ s = LinearMap.id)
    (hsum : i ∘ₗ r + s ∘ₗ π = LinearMap.id) {φ' : P' →ₗ[R] P'} {φ : P →ₗ[R] P} {φ'' : P'' →ₗ[R] P''}
    (h1 : φ ∘ₗ i = i ∘ₗ φ') (h2 : π ∘ₗ φ = φ'' ∘ₗ π) :
    trace R P φ = trace R P' φ' + trace R P'' φ'' := by
  have e : φ = (φ ∘ₗ i) ∘ₗ r + (φ ∘ₗ s) ∘ₗ π := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_add, hsum, LinearMap.comp_id]
  have t1 : trace R P ((φ ∘ₗ i) ∘ₗ r) = trace R P' φ' := by
    rw [LinearMap.trace_comp_comm', h1, ← LinearMap.comp_assoc, hri, LinearMap.id_comp]
  have t2 : trace R P ((φ ∘ₗ s) ∘ₗ π) = trace R P'' φ'' := by
    rw [LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, h2, LinearMap.comp_assoc, hπs, LinearMap.comp_id]
  rw [e, map_add, t1, t2]

end Split

section Quot

variable {R : Type*} [CommRing R] {P : Type*} [AddCommGroup P] [Module R P] (Q : Submodule R P)

theorem mem_of_sec {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) (x : P) : x - s (Q.mkQ x) ∈ Q := by
  rw [← Submodule.Quotient.mk_eq_zero Q, Submodule.Quotient.mk_sub]
  have := LinearMap.congr_fun hs (Q.mkQ x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply] at this ⊢
  rw [this, sub_self]

/-- The retraction `P → Q`, `x ↦ x - s (x mod Q)`, attached to a section `s` of `P → P ⧸ Q`. -/
def retr {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) : P →ₗ[R] Q :=
  LinearMap.codRestrict Q (LinearMap.id - s ∘ₗ Q.mkQ) fun x => mem_of_sec Q hs x

theorem retr_subtype {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) :
    retr Q hs ∘ₗ Q.subtype = LinearMap.id :=
  LinearMap.ext fun q => Subtype.ext (by
    simp [retr, (Submodule.Quotient.mk_eq_zero Q).2 q.2])

theorem subtype_retr_add {s : (P ⧸ Q) →ₗ[R] P} (hs : Q.mkQ ∘ₗ s = LinearMap.id) :
    Q.subtype ∘ₗ retr Q hs + s ∘ₗ Q.mkQ = LinearMap.id :=
  LinearMap.ext fun x => by simp [retr]

variable [Module.Free R (P ⧸ Q)]

theorem exists_sec : ∃ s : (P ⧸ Q) →ₗ[R] P, Q.mkQ ∘ₗ s = LinearMap.id :=
  Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective

/-- Over a local ring, a submodule of a free finite module with free quotient is free and finite. -/
theorem sub_free_finite [IsLocalRing R] [Module.Free R P] [Module.Finite R P] :
    Module.Free R Q ∧ Module.Finite R Q := by
  obtain ⟨s, hs⟩ := exists_sec Q
  have hri := retr_subtype Q hs
  have : Module.Projective R Q := Module.Projective.of_split Q.subtype (retr Q hs) hri
  have : Module.Finite R Q :=
    Module.Finite.of_surjective (retr Q hs) (fun v => ⟨Q.subtype v, LinearMap.congr_fun hri v⟩)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

/-- `Tr φ = Tr(φ | Q) + Tr(φ | P ⧸ Q)` for `Q` stable under `φ`, `P` free finite and `P ⧸ Q` free finite over a local
ring. -/
theorem trace_eq_restrict_add_quot [IsLocalRing R] [Module.Free R P] [Module.Finite R P] [Module.Finite R (P ⧸ Q)]
    (φ : P →ₗ[R] P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    trace R P φ = trace R Q (φ.restrict hQ) + trace R (P ⧸ Q) (Q.mapQ Q φ fun x hx => hQ x hx) := by
  obtain ⟨s, hs⟩ := exists_sec Q
  obtain ⟨_, _⟩ := sub_free_finite Q
  exact trace_split (retr_subtype Q hs) hs (subtype_retr_add Q hs) (LinearMap.ext fun q => rfl)
    (LinearMap.ext fun x => rfl)

end Quot

section Euler

variable {R : Type*} [CommRing R] {K0 K1 K2 : Type*} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
  [AddCommGroup K2] [Module R K2] (d0 : K0 →ₗ[R] K1) (d1 : K1 →ₗ[R] K2) (hd : ∀ x, d1 (d0 x) = 0)

/-- `d⁰` with values in the cocycles `ker d¹`. -/
def d0Z : K0 →ₗ[R] LinearMap.ker d1 :=
  LinearMap.codRestrict _ d0 fun x => LinearMap.mem_ker.2 (hd x)

/-- `H¹ = ker d¹ / im d⁰`. -/
abbrev Hc1 : Type _ := LinearMap.ker d1 ⧸ LinearMap.range (d0Z d0 d1 hd)

variable {d0 d1} {f0 : K0 →ₗ[R] K0} {f1 : K1 →ₗ[R] K1} {f2 : K2 →ₗ[R] K2}

theorem mem_ker_f1 (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : ∀ x ∈ LinearMap.ker d1, f1 x ∈ LinearMap.ker d1 :=
  fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← h1, hx, map_zero]

/-- `f¹` on the cocycles. -/
def fZ (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : LinearMap.ker d1 →ₗ[R] LinearMap.ker d1 :=
  f1.restrict (mem_ker_f1 h1)

theorem mem_range_d0Z (h0 : ∀ x, f1 (d0 x) = d0 (f0 x)) (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) :
    ∀ z ∈ LinearMap.range (d0Z d0 d1 hd), fZ h1 z ∈ LinearMap.range (d0Z d0 d1 hd) := by
  rintro z ⟨x, rfl⟩
  exact ⟨f0 x, Subtype.ext (h0 x).symm⟩

theorem mem_range_d1 (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : ∀ y ∈ LinearMap.range d1, f2 y ∈ LinearMap.range d1 := by
  rintro y ⟨x, rfl⟩
  exact ⟨f1 x, (h1 x).symm⟩

/-- The endomorphism of `H¹`. -/
def mapH1 (h0 : ∀ x, f1 (d0 x) = d0 (f0 x)) (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : Hc1 d0 d1 hd →ₗ[R] Hc1 d0 d1 hd :=
  Submodule.mapQ _ _ (fZ h1) fun z hz => mem_range_d0Z hd h0 h1 z hz

/-- The endomorphism of `H² = coker d¹`. -/
def mapH2 (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) : K2 ⧸ LinearMap.range d1 →ₗ[R] K2 ⧸ LinearMap.range d1 :=
  Submodule.mapQ _ _ f2 fun y hy => mem_range_d1 h1 y hy

/-- **Euler characteristic of traces** for a three-term complex of free finite modules over a local ring with
injective `d⁰` and free finite `H¹`, `H²`: `Tr f⁰ - Tr f¹ + Tr f² = Tr(f | H²) - Tr(f | H¹)`. -/
theorem euler3 [IsLocalRing R] [Module.Free R K0] [Module.Finite R K0] [Module.Free R K1] [Module.Finite R K1]
    [Module.Free R K2] [Module.Finite R K2] (hinj : Function.Injective d0)
    [Module.Free R (Hc1 d0 d1 hd)] [Module.Finite R (Hc1 d0 d1 hd)]
    [Module.Free R (K2 ⧸ LinearMap.range d1)] [Module.Finite R (K2 ⧸ LinearMap.range d1)]
    (h0 : ∀ x, f1 (d0 x) = d0 (f0 x)) (h1 : ∀ x, f2 (d1 x) = d1 (f1 x)) :
    trace R K0 f0 - trace R K1 f1 + trace R K2 f2 = trace R _ (mapH2 h1) - trace R _ (mapH1 hd h0 h1) := by
  -- `B = im d¹ ⊆ K²` with quotient `H²`
  obtain ⟨_, _⟩ := sub_free_finite (LinearMap.range d1)
  have T2 : trace R K2 f2 = trace R _ (f2.restrict (mem_range_d1 h1)) + trace R _ (mapH2 h1) :=
    trace_eq_restrict_add_quot _ f2 (mem_range_d1 h1)
  -- `K¹ ⧸ ker d¹ ≃ B`
  have : Module.Free R (K1 ⧸ LinearMap.ker d1) := Module.Free.of_equiv d1.quotKerEquivRange.symm
  have : Module.Finite R (K1 ⧸ LinearMap.ker d1) := Module.Finite.equiv d1.quotKerEquivRange.symm
  obtain ⟨_, _⟩ := sub_free_finite (LinearMap.ker d1)
  have T1 : trace R K1 f1 = trace R _ (fZ h1) +
      trace R _ (Submodule.mapQ _ _ f1 fun x hx => mem_ker_f1 h1 x hx) :=
    trace_eq_restrict_add_quot _ f1 (mem_ker_f1 h1)
  have TB : trace R (K1 ⧸ LinearMap.ker d1) (Submodule.mapQ _ _ f1 fun x hx => mem_ker_f1 h1 x hx) =
      trace R _ (f2.restrict (mem_range_d1 h1)) := by
    refine trace_intw d1.quotKerEquivRange fun v => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    apply Subtype.ext
    simp [h1]
  -- `im d⁰ ⊆ ker d¹` with quotient `H¹`, and `K⁰ ≃ im d⁰`
  have hinjZ : Function.Injective (d0Z d0 d1 hd) := fun a b h => hinj (congrArg Subtype.val h)
  have TZ : trace R _ (fZ h1) = trace R _ ((fZ h1).restrict (mem_range_d0Z hd h0 h1)) +
      trace R _ (mapH1 hd h0 h1) :=
    trace_eq_restrict_add_quot _ (fZ h1) (mem_range_d0Z hd h0 h1)
  have T0 : trace R K0 f0 = trace R _ ((fZ h1).restrict (mem_range_d0Z hd h0 h1)) :=
    trace_intw (LinearEquiv.ofInjective (d0Z d0 d1 hd) hinjZ) fun v => Subtype.ext (Subtype.ext (h0 v).symm)
  linear_combination T0 - T1 + T2 - TB - TZ

end Euler

end

end Lefschetz
end RamanujanPetersson

end

-- ===== S4.Def_RP_Lefschetz_ConeEuler =====
section

/-!
# S4-Lefschetz, L3e2a: Euler characteristic of the cone Frobenius

For the cone `K(M) = [M → Z¹(Γ; M) × M^S → Π_s Z¹(Γ ⊓ I s; M)]` (`cx0`, `cx1`) with its Frobenius
(`ρ ψ`, `frob1`, `frob2`): `H¹` of the cone in the form of `Def_RP_Lefschetz_Euler` is `H¹_c` (`hc1Equiv`), and over a
local ring with free finite terms, `H¹_c` and `H²(K)`:
* `cone_euler`: `Tr(F | K⁰) - Tr(F | K¹) + Tr(F | K²) = Tr(frobH2K) - Tr(frobH1c)`;
* `cone_euler_tri`: the same as `Σ_{i<3} (-1)^i Tr(triMap .. i)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) {S : Type}
  (I : S → Subgroup G) (hρ : IsOpen (ρ.ker : Set G))

theorem cx1_cx0 (m : M) : cx1 ρ Γ I hρ (cx0 ρ Γ S hρ m) = 0 :=
  LinearMap.congr_fun (cx1_comp_cx0 ρ Γ I hρ) m

/-- `H¹ = ker d¹ / im d⁰` of the cone is `H¹_c`. -/
def hc1Equiv : Hc1 (cx0 ρ Γ S hρ) (cx1 ρ Γ I hρ) (cx1_cx0 ρ Γ I hρ) ≃ₗ[k] H1c ρ Γ I :=
  (Submodule.Quotient.equiv _ _ (kerEquivZ1c ρ Γ I hρ) (by
    rw [cx0c, LinearMap.range_comp]
    rfl)).trans (h1Equiv ρ Γ I hρ)

variable [Γ.Normal] (ψ : G) (t : S → S) (h : S → Γ)

/-- **Euler characteristic of the cone Frobenius.** -/
theorem cone_euler [IsLocalRing k] [Nonempty S] [Module.Free k M] [Module.Finite k M]
    [Module.Free k (Z1 ρ Γ × (S → M))] [Module.Finite k (Z1 ρ Γ × (S → M))]
    [Module.Free k ((s : S) → Z1 ρ (Γ ⊓ I s))] [Module.Finite k ((s : S) → Z1 ρ (Γ ⊓ I s))]
    [Module.Free k (H1c ρ Γ I)] [Module.Finite k (H1c ρ Γ I)]
    [Module.Free k (H2K ρ Γ I hρ)] [Module.Finite k (H2K ρ Γ I hρ)] (hI : BdryCompat Γ I ψ t h) :
    LinearMap.trace k M (ρ ψ) - LinearMap.trace k _ (frob1 ρ Γ ψ t h) +
        LinearMap.trace k _ (frob2 ρ Γ I ψ t h hI) =
      LinearMap.trace k _ (frobH2K ρ Γ I ψ t h hρ hI) - LinearMap.trace k _ (frobH1c ρ Γ I ψ t h hI) := by
  have h0 : ∀ x, frob1 ρ Γ ψ t h (cx0 ρ Γ S hρ x) = cx0 ρ Γ S hρ (ρ ψ x) := fun x =>
    (LinearMap.congr_fun (cx0_frob ρ Γ ψ t h hρ) x).symm
  have h1 : ∀ x, frob2 ρ Γ I ψ t h hI (cx1 ρ Γ I hρ x) = cx1 ρ Γ I hρ (frob1 ρ Γ ψ t h x) := fun x =>
    (LinearMap.congr_fun (cx1_frob ρ Γ I ψ t h hρ hI) x).symm
  have : Module.Free k (Hc1 (cx0 ρ Γ S hρ) (cx1 ρ Γ I hρ) (cx1_cx0 ρ Γ I hρ)) :=
    Module.Free.of_equiv (hc1Equiv ρ Γ I hρ).symm
  have : Module.Finite k (Hc1 (cx0 ρ Γ S hρ) (cx1 ρ Γ I hρ) (cx1_cx0 ρ Γ I hρ)) :=
    Module.Finite.equiv (hc1Equiv ρ Γ I hρ).symm
  rw [euler3 (cx1_cx0 ρ Γ I hρ) (cx0_injective ρ Γ S hρ) h0 h1]
  exact congrArg₂ (· - ·) rfl
    (trace_intw (hc1Equiv ρ Γ I hρ) fun v => Submodule.Quotient.induction_on _ v fun _ => rfl)

/-- `cone_euler` as an alternating sum over the `Tri` family. -/
theorem cone_euler_tri [IsLocalRing k] [Nonempty S] [Module.Free k M] [Module.Finite k M]
    [Module.Free k (Z1 ρ Γ × (S → M))] [Module.Finite k (Z1 ρ Γ × (S → M))]
    [Module.Free k ((s : S) → Z1 ρ (Γ ⊓ I s))] [Module.Finite k ((s : S) → Z1 ρ (Γ ⊓ I s))]
    [Module.Free k (H1c ρ Γ I)] [Module.Finite k (H1c ρ Γ I)]
    [Module.Free k (H2K ρ Γ I hρ)] [Module.Finite k (H2K ρ Γ I hρ)] (hI : BdryCompat Γ I ψ t h) :
    ∑ i ∈ Finset.range (2 + 1), (-1 : k) ^ i *
        LinearMap.trace k _ (triMap (ρ ψ) (frob1 ρ Γ ψ t h) (frob2 ρ Γ I ψ t h hI) i) =
      LinearMap.trace k _ (frobH2K ρ Γ I ψ t h hρ hI) - LinearMap.trace k _ (frobH1c ρ Γ I ψ t h hI) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, one_mul,
    neg_one_mul, neg_one_sq, one_mul, ← sub_eq_add_neg]
  exact cone_euler ρ Γ I hρ ψ t h hI

end

end Lefschetz
end RamanujanPetersson

end

-- ===== S4.Def_RP_LisseDuality_Amb =====
section

/-!
# S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group

For subgroups `Δ₁ ≤ G₁`, `Δ₂ ≤ G₂`, a continuous isomorphism `e : Δ₁ ≃ₜ* Δ₂` intertwining `ρ₁` and `ρ₂`
(`Intw`) and matching the boundary subgroups (`IntwI`), the cocycle and cohomology groups are transported:
`z1Tr : Z¹(Δ₁, ρ₁) ≃ Z¹(Δ₂, ρ₂)`, `h1Tr`, `z1cTr`, `h1cTr` and (with `infTr` on `Δ ⊓ I s`) `h2kTr` on the cone `H²`.
Used for the ambient change `G ⇝ K·Γ` in the disconnected case of lisse duality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Tr

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] {M : Type} [AddCommGroup M] [Module k M]
  {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M} {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂}

/-- `e` intertwines `ρ₁` and `ρ₂`. -/
def Intw (ρ₁ : Representation k G₁ M) (ρ₂ : Representation k G₂ M) (e : Δ₁ ≃ₜ* Δ₂) : Prop :=
  ∀ g : Δ₁, ρ₁ g = ρ₂ (e g)

theorem Intw.symm {e : Δ₁ ≃ₜ* Δ₂} (h : Intw ρ₁ ρ₂ e) : Intw ρ₂ ρ₁ e.symm := fun g => by
  rw [h (e.symm g), ContinuousMulEquiv.apply_symm_apply]

variable {e : Δ₁ ≃ₜ* Δ₂}

theorem z1_comp (h : Intw ρ₁ ρ₂ e) {c : Δ₂ → M} (hc : c ∈ Z1 ρ₂ Δ₂) : c ∘ e ∈ Z1 ρ₁ Δ₁ := by
  obtain ⟨hl, hco⟩ := (mem_Z1 ρ₂ Δ₂ c).1 hc
  refine (mem_Z1 ρ₁ Δ₁ _).2 ⟨hl.comp_continuous (map_continuous e), fun a b => ?_⟩
  simp only [Function.comp_apply, map_mul, hco, h a]

theorem b1_comp (h : Intw ρ₁ ρ₂ e) {c : Δ₂ → M} (hc : c ∈ B1 ρ₂ Δ₂) : c ∘ e ∈ B1 ρ₁ Δ₁ := by
  obtain ⟨hz, m, hm⟩ := (mem_B1 ρ₂ Δ₂ c).1 hc
  exact (mem_B1 ρ₁ Δ₁ _).2 ⟨z1_comp h hz, m, fun g => by simp only [Function.comp_apply, hm, h g]⟩

theorem comp_symm_comp {X : Type} (c : Δ₂ → X) : (c ∘ e) ∘ e.symm = c :=
  funext fun g => by simp

theorem comp_comp_symm {X : Type} (c : Δ₁ → X) : (c ∘ e.symm) ∘ e = c :=
  funext fun g => by simp

/-- `Z¹` transported along `e`: `c ↦ c ∘ e⁻¹`. -/
def z1Tr (h : Intw ρ₁ ρ₂ e) : Z1 ρ₁ Δ₁ ≃ₗ[k] Z1 ρ₂ Δ₂ where
  toFun c := ⟨(c : Δ₁ → M) ∘ e.symm, z1_comp h.symm c.2⟩
  invFun c := ⟨(c : Δ₂ → M) ∘ e, z1_comp h c.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (comp_comp_symm (e := e) _)
  right_inv _ := Subtype.ext (comp_symm_comp (e := e) _)

theorem z1Tr_apply (h : Intw ρ₁ ρ₂ e) (c : Z1 ρ₁ Δ₁) (g : Δ₂) :
    (z1Tr h c : Δ₂ → M) g = (c : Δ₁ → M) (e.symm g) := rfl

theorem z1Tr_symm_apply (h : Intw ρ₁ ρ₂ e) (c : Z1 ρ₂ Δ₂) (g : Δ₁) :
    ((z1Tr h).symm c : Δ₁ → M) g = (c : Δ₂ → M) (e g) := rfl

/-- `H¹` transported along `e`. -/
def h1Tr (h : Intw ρ₁ ρ₂ e) : H1 ρ₁ Δ₁ ≃ₗ[k] H1 ρ₂ Δ₂ :=
  Submodule.Quotient.equiv _ _ (z1Tr h) (by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    constructor
    · intro hx
      have := b1_comp h.symm hx
      show (x : Δ₂ → M) ∈ B1 ρ₂ Δ₂
      rw [← comp_symm_comp (e := e) (x : Δ₂ → M)]
      exact this
    · exact b1_comp h)

theorem h1Tr_mk (h : Intw ρ₁ ρ₂ e) (c : Z1 ρ₁ Δ₁) :
    h1Tr h (Submodule.Quotient.mk c) = Submodule.Quotient.mk (z1Tr h c) := rfl

/-! ## The compactly supported part -/

variable {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

/-- `e` matches the boundary subgroups. -/
def IntwI (I₁ : S → Subgroup G₁) (I₂ : S → Subgroup G₂) (e : Δ₁ ≃ₜ* Δ₂) : Prop :=
  ∀ (s : S) (g : Δ₁), (g : G₁) ∈ I₁ s ↔ ((e g : Δ₂) : G₂) ∈ I₂ s

theorem IntwI.symm (hI : IntwI I₁ I₂ e) : IntwI I₂ I₁ e.symm := fun s g => by
  rw [hI s (e.symm g), ContinuousMulEquiv.apply_symm_apply]

theorem z1c_comp (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) {p : (Δ₂ → M) × (S → M)} (hp : p ∈ Z1c ρ₂ Δ₂ I₂) :
    (p.1 ∘ e, p.2) ∈ Z1c ρ₁ Δ₁ I₁ := by
  obtain ⟨hz, hb⟩ := (mem_Z1c ρ₂ Δ₂ I₂ p).1 hp
  refine (mem_Z1c ρ₁ Δ₁ I₁ _).2 ⟨z1_comp h hz, fun s g hg => ?_⟩
  simp only [Function.comp_apply, hb s (e g) ((hI s g).1 hg), h g]

theorem b1c_comp (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) {p : (Δ₂ → M) × (S → M)} (hp : p ∈ B1c ρ₂ Δ₂ I₂) :
    (p.1 ∘ e, p.2) ∈ B1c ρ₁ Δ₁ I₁ := by
  obtain ⟨hz, m, hm, hm'⟩ := hp
  exact ⟨z1c_comp h hI hz, m, fun g => by simp only [Function.comp_apply, hm, h g], hm'⟩

/-- `Z¹_c` transported along `e`: `(c, m) ↦ (c ∘ e⁻¹, m)`. -/
def z1cTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) : Z1c ρ₁ Δ₁ I₁ ≃ₗ[k] Z1c ρ₂ Δ₂ I₂ where
  toFun p := ⟨((p : (Δ₁ → M) × (S → M)).1 ∘ e.symm, (p : (Δ₁ → M) × (S → M)).2), z1c_comp h.symm hI.symm p.2⟩
  invFun p := ⟨((p : (Δ₂ → M) × (S → M)).1 ∘ e, (p : (Δ₂ → M) × (S → M)).2), z1c_comp h hI p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext (Prod.ext (comp_comp_symm (e := e) _) rfl)
  right_inv _ := Subtype.ext (Prod.ext (comp_symm_comp (e := e) _) rfl)

theorem z1cTr_apply (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (p : Z1c ρ₁ Δ₁ I₁) :
    (z1cTr h hI p : (Δ₂ → M) × (S → M)) =
      ((p : (Δ₁ → M) × (S → M)).1 ∘ e.symm, (p : (Δ₁ → M) × (S → M)).2) := rfl

/-- `H¹_c` transported along `e`. -/
def h1cTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) : H1c ρ₁ Δ₁ I₁ ≃ₗ[k] H1c ρ₂ Δ₂ I₂ :=
  Submodule.Quotient.equiv _ _ (z1cTr h hI) (by
    ext x
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
    constructor
    · intro hx
      have := b1c_comp h.symm hI.symm hx
      have key : (((x : (Δ₂ → M) × (S → M)).1 ∘ e) ∘ e.symm, (x : (Δ₂ → M) × (S → M)).2) =
          (x : (Δ₂ → M) × (S → M)) := Prod.ext (comp_symm_comp (e := e) _) rfl
      show (x : (Δ₂ → M) × (S → M)) ∈ B1c ρ₂ Δ₂ I₂
      rw [← key]
      exact this
    · exact b1c_comp h hI)

theorem h1cTr_mk (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (p : Z1c ρ₁ Δ₁ I₁) :
    h1cTr h hI (Submodule.Quotient.mk p) = Submodule.Quotient.mk (z1cTr h hI p) := rfl

/-! ## The boundary groups and the cone `H²` -/

/-- `e` restricted to `Δ ⊓ I s`. -/
def infTr (hI : IntwI I₁ I₂ e) (s : S) : ↥(Δ₁ ⊓ I₁ s) ≃ₜ* ↥(Δ₂ ⊓ I₂ s) where
  toFun g := ⟨e ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩,
    Subgroup.mem_inf.2 ⟨(e _).2, (hI s _).1 (Subgroup.mem_inf.1 g.2).2⟩⟩
  invFun g := ⟨e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩,
    Subgroup.mem_inf.2 ⟨(e.symm _).2, (hI.symm s _).1 (Subgroup.mem_inf.1 g.2).2⟩⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (show ((e ⟨(a : G₁) * b, (Subgroup.mem_inf.1 (a * b).2).1⟩ : Δ₂) : G₂) =
      (e ⟨a, (Subgroup.mem_inf.1 a.2).1⟩ : G₂) * (e ⟨b, (Subgroup.mem_inf.1 b.2).1⟩ : G₂) from
    congrArg Subtype.val
      (map_mul e ⟨(a : G₁), (Subgroup.mem_inf.1 a.2).1⟩ ⟨(b : G₁), (Subgroup.mem_inf.1 b.2).1⟩))
  continuous_toFun :=
    (continuous_subtype_val.comp ((map_continuous e).comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp ((map_continuous e.symm).comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

theorem infTr_coe (hI : IntwI I₁ I₂ e) (s : S) (g : ↥(Δ₁ ⊓ I₁ s)) :
    ((infTr hI s g : ↥(Δ₂ ⊓ I₂ s)) : G₂) = (e ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ : G₂) := rfl

theorem infTr_symm_coe (hI : IntwI I₁ I₂ e) (s : S) (g : ↥(Δ₂ ⊓ I₂ s)) :
    (((infTr hI s).symm g : ↥(Δ₁ ⊓ I₁ s)) : G₁) = (e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ : G₁) := rfl

theorem Intw.inf (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (s : S) : Intw ρ₁ ρ₂ (infTr hI s) :=
  fun g => h ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩

/-- The `Π_s Z¹(Δ ⊓ I s)` transport. -/
def piTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) :
    ((s : S) → Z1 ρ₁ (Δ₁ ⊓ I₁ s)) ≃ₗ[k] ((s : S) → Z1 ρ₂ (Δ₂ ⊓ I₂ s)) :=
  LinearEquiv.piCongrRight fun s => z1Tr (h.inf hI s)

variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

theorem piTr_cx1 (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁))
    (hρ₂ : IsOpen (ρ₂.ker : Set G₂)) (p : Z1 ρ₁ Δ₁ × (S → M)) :
    piTr h hI (cx1 ρ₁ Δ₁ I₁ hρ₁ p) = cx1 ρ₂ Δ₂ I₂ hρ₂ (z1Tr h p.1, p.2) :=
  funext fun s => Subtype.ext (funext fun g => by
    show (cx1 ρ₁ Δ₁ I₁ hρ₁ p s : ↥(Δ₁ ⊓ I₁ s) → M) ((infTr hI s).symm g) =
      (cx1 ρ₂ Δ₂ I₂ hρ₂ (z1Tr h p.1, p.2) s : ↥(Δ₂ ⊓ I₂ s) → M) g
    rw [cx1_apply, cx1_apply, (h.inf hI s).symm g]
    rfl)

/-- The cone `H²` transported along `e`. -/
def h2kTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁))
    (hρ₂ : IsOpen (ρ₂.ker : Set G₂)) : H2K ρ₁ Δ₁ I₁ hρ₁ ≃ₗ[k] H2K ρ₂ Δ₂ I₂ hρ₂ :=
  Submodule.Quotient.equiv _ _ (piTr h hI) (by
    have hc : (piTr h hI : _ →ₗ[k] _) ∘ₗ cx1 ρ₁ Δ₁ I₁ hρ₁ =
        cx1 ρ₂ Δ₂ I₂ hρ₂ ∘ₗ ((z1Tr h).prodCongr (LinearEquiv.refl k (S → M)) : _ →ₗ[k] _) :=
      LinearMap.ext fun p => piTr_cx1 h hI hρ₁ hρ₂ p
    rw [← LinearMap.range_comp, hc, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])

theorem h2kTr_mk (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁))
    (hρ₂ : IsOpen (ρ₂.ker : Set G₂)) (x : (s : S) → Z1 ρ₁ (Δ₁ ⊓ I₁ s)) :
    h2kTr h hI hρ₁ hρ₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (piTr h hI x) := rfl

end Tr

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_Lefschetz_ResK =====
section

/-!
# S4-Lefschetz, L3 (i): the residue hypothesis of the total cone, with its Frobenius twist

For `π` cut out by a finite unramified `M` (S3 chart, true boundary permutation): `exists_resHyp_tw` gives a
`ResHyp Λ π π₁^geo I` together with the twist clause `hTW` of `h2Equiv_frob` / `trace_h2_tot` at `ψ = φ⁻¹`,
`t = trueTau`, `h = trueH`, `c = q`, for every Frobenius lift `φ` (the first half of `h2Equiv_S3`'s proof).
`trueTw_hD` and `trueTw_ht` are the other two side conditions (`hD`, `ht`), for every `ψ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

set_option maxHeartbeats 800000 in
/-- The side condition `hD` of `h2Equiv_frob` for the true boundary permutation of any `ψ`. -/
theorem trueTw_hD {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (ψ : Pi1 (Places.Rfin Fq F) F) (s : S) (d : Gf) :
    d ∈ (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D ψ s)).map π ↔
      π (ψ * (trueH D ψ s : Pi1 (Places.Rfin Fq F) F)) * d * (π (ψ * (trueH D ψ s : Pi1 (Places.Rfin Fq F) F)))⁻¹ ∈
        (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π :=
  map_inf_conj_iff (I1 := D.inertia (trueTau D ψ s)) (I2 := D.inertia s) π _ _
    (fun y => inert_conj_iff (trueTau_smul D ψ s) y) d

set_option maxHeartbeats 800000 in
/-- The side condition `ht` of `h2Equiv_frob`: the true boundary permutation is a bijection. -/
theorem trueTw_ht {S : Type} [Finite S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S) (ψ : Pi1 (Places.Rfin Fq F) F) :
    Function.Bijective (trueTau D ψ) :=
  tt_bijective D.P _ D.disj ψ (trueTau D ψ) (trueH D ψ) (trueTau_spec D ψ)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **The total cone's residue hypothesis with the Frobenius twist** (S3 chart, `π` cut out by `M`): a `ResHyp` whose
generators satisfy `hTW` of `h2Equiv_frob` at `ψ = φ⁻¹`, `trueTau`, `trueH`, `c = q` for every Frobenius lift `φ`. -/
theorem exists_resHyp_tw {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n))
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] [Fintype Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hπ : IsOpen (π.ker : Set (Pi1 (Places.Rfin Fq F) F)))
    {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    {Λ : Type} [CommRing Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    [Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)).map π)]
    [∀ s, Fintype ((pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s).map π)] :
    ∃ H : ResHyp Λ π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia,
      ∀ φ : Pi1 (Places.Rfin Fq F) F, IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ →
        ∀ s (e : Z1 (regRep Λ π) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D φ⁻¹ s))),
          (e : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D φ⁻¹ s)) →
              MonoidAlgebra Λ Gf)
            (conjSub (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))
              (bdry_mem (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia φ⁻¹ (trueTau D φ⁻¹)
                (trueH D φ⁻¹) (trueCompat D φ⁻¹) s) (H.sg s)) =
            (Fintype.card Fq : Λ) •
              (e : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia (trueTau D φ⁻¹ s)) →
                MonoidAlgebra Λ Gf) (H.sg (trueTau D φ⁻¹ s)) := by
  let _ : Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Fintype.ofFinite _
  let _ : DecidableEq (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) D.inertia) := Classical.decEq _
  have hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (D.P s) := fun s => (hDB _).1 (D.mem s)
  have hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • D.P s :=
    fun Q hQ => D.cover Q ((hDB Q).2 hQ)
  have hNF : ((l ^ n : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨D', hTWD⟩ := exists_resDat_tw hq he hNF hPic hM hMU π hπM D.P hP hcov D.disj D.inertia (fun _ => rfl)
  have hMo : ∀ m : MonoidAlgebra Λ Gf, (l ^ n) • m = 0 := fun m => by
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  refine ⟨D'.toResHyp hΛ hπ, fun φ hφ s e => ?_⟩
  have hu := fun s => trueTau_smul D φ⁻¹ s
  have hg : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq)
      (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))⁻¹ := by
    rw [mul_inv_rev, inv_inv]
    exact isFrobLift_geo_mul (inv_mem (trueH D φ⁻¹ s).2) hφ
  have hc : (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F))⁻¹ * D'.σ s *
      (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F)) ∈ D'.J (trueTau D φ⁻¹ s) :=
    (D'.hJ _ _).2 ⟨bdry_mem _ D.inertia φ⁻¹ (trueTau D φ⁻¹) (trueH D φ⁻¹) (trueCompat D φ⁻¹) s _ (D'.hσ s),
      by rw [map_mul, map_mul, D'.hσπ s, mul_one, map_inv, inv_mul_cancel]⟩
  have h1 := hTWD s (trueTau D φ⁻¹ s) (φ⁻¹ * (trueH D φ⁻¹ s : Pi1 (Places.Rfin Fq F) F)) hg (hu s)
    (MonoidAlgebra Λ Gf) hMo (resK π _ (D'.J (trueTau D φ⁻¹ s)) (D'.hJ (trueTau D φ⁻¹ s)) e)
    (resK_lc π _ _ _ e) (resK_add π _ _ _ e) hc
  exact h1.trans (Nat.cast_smul_eq_nsmul Λ _ _).symm

end S3

end

end Lefschetz
end RamanujanPetersson

end

-- ===== S4.Def_RP_Lefschetz_PtExt =====
section

/-!
# S4-Lefschetz, L5b (part 1): points extend along integral extensions

`exists_hom_extend`: for an injective integral `C → B` and an algebraically closed field `Ω`, every ring hom
`v : C → Ω` extends to `w : B → Ω` (lying over + `IsAlgClosed.lift` on the residue rings).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

section PtExt

/-- **Extension of points** along an injective integral extension, into an algebraically closed field. -/
theorem exists_hom_extend {C B Ω : Type} [CommRing C] [CommRing B] [Algebra C B] [Algebra.IsIntegral C B]
    [FaithfulSMul C B] [Field Ω] [IsAlgClosed Ω] (v : C →+* Ω) :
    ∃ w : B →+* Ω, w.comp (algebraMap C B) = v := by
  classical
  have hP : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker v) (⊥ : Ideal B)
    (Ideal.comap_bot_le_of_injective _ (FaithfulSMul.algebraMap_injective C B))
  have : Q.LiesOver (RingHom.ker v) := ⟨hQP.symm⟩
  have : IsDomain (C ⧸ RingHom.ker v) := Ideal.Quotient.isDomain _
  have : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  let vb : C ⧸ RingHom.ker v →+* Ω := Ideal.Quotient.lift _ v fun c hc => RingHom.mem_ker.1 hc
  have hvb : Function.Injective vb := by
    refine (injective_iff_map_eq_zero vb).2 fun x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 hx)
  letI : Algebra (C ⧸ RingHom.ker v) Ω := vb.toAlgebra
  have : Module.IsTorsionFree (C ⧸ RingHom.ker v) Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hvb
  have hinj : Function.Injective (algebraMap (C ⧸ RingHom.ker v) (B ⧸ Q)) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk Q (algebraMap C B c) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [← hQP]
    exact hx
  have : Module.IsTorsionFree (C ⧸ RingHom.ker v) (B ⧸ Q) := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  have : Algebra.IsIntegral (C ⧸ RingHom.ker v) (B ⧸ Q) := inferInstance
  have : Algebra.IsAlgebraic (C ⧸ RingHom.ker v) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (B ⧸ Q) →ₐ[C ⧸ RingHom.ker v] Ω := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun c => ?_⟩
  show ψ (algebraMap (C ⧸ RingHom.ker v) (B ⧸ Q) (Ideal.Quotient.mk _ c)) = v c
  rw [ψ.commutes]
  rfl

end PtExt

end

end Lefschetz
end RamanujanPetersson

end

-- ===== S4.Def_RP_Lefschetz_Pow =====
section

/-!
# S4-Lefschetz L0: the Lefschetz trace formula for the powers of the Frobenius

`lefschetz_frob` (S4-PD) is the twisted trace formula for the Frobenius `F` itself. Here it is extended to every power
`F^m`: equivariance is stable under powers (`isEquivariant_pow`), intertwinings iterate (`intertwine_pow`), the map
induced on coinvariants by `φ^m ⊗ id` is the `m`-th power of the map induced by `φ ⊗ id` (`coinvMap_tensor_pow`), so
`Tr(F^m | M) - Tr(F^m | K¹(M)) + Tr(F^m | K²(M)) = Σ_c L(frobPC^m)[c] · Tr(τ(c)⁻¹ | M)` (`lefschetz_frob_pow`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct PerfectCx

noncomputable section

section Gen

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G] {P : Type*} [AddCommGroup P] [Module R P]

/-- Equivariant endomorphisms are stable under powers. -/
theorem isEquivariant_pow {ρ : Representation R G P} {f : P →ₗ[R] P} (hf : IsEquivariant ρ ρ f) :
    ∀ m : ℕ, IsEquivariant ρ ρ (f ^ m)
  | 0 => by rw [pow_zero, Module.End.one_eq_id]; exact isEquivariant_id
  | m + 1 => fun g => by
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc, isEquivariant_pow hf m g,
      ← LinearMap.comp_assoc, hf g, LinearMap.comp_assoc]

/-- An intertwining `e ∘ f = g ∘ e` iterates: `e ∘ f^m = g^m ∘ e`. -/
theorem intertwine_pow {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] (e : V → W)
    {f : V →ₗ[R] V} {g : W →ₗ[R] W} (hfg : ∀ v, e (f v) = g (e v)) : ∀ (m : ℕ) (v : V), e ((f ^ m) v) = (g ^ m) (e v)
  | 0, v => by simp only [pow_zero, Module.End.one_apply]
  | m + 1, v => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, intertwine_pow e hfg m, hfg]

variable {V : Type*} [AddCommGroup V] [Module R V]

theorem coinvMap_congr (θ : Representation R G V) {F F' : V →ₗ[R] V} (hF : IsEquivariant θ θ F)
    (hF' : IsEquivariant θ θ F') (e : F = F') : coinvMap θ F hF = coinvMap θ F' hF' := by
  subst e; rfl

/-- The map induced on coinvariants by `F^m` is the `m`-th power of the map induced by `F`. -/
theorem coinvMap_pow (θ : Representation R G V) {F : V →ₗ[R] V} (hF : IsEquivariant θ θ F) (m : ℕ)
    (hFm : IsEquivariant θ θ (F ^ m)) : coinvMap θ (F ^ m) hFm = coinvMap θ F hF ^ m := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective θ u
  rw [coinvMap_mk]
  exact intertwine_pow (⇑(Coinvariants.mk θ)) (fun v => (coinvMap_mk θ F hF v).symm) m x

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- `(φ^m ⊗ id)_G = ((φ ⊗ id)_G)^m` on the coinvariants of `P ⊗ M`. -/
theorem coinvMap_tensor_pow (ρ : Representation R G P) (τ : Representation R G M) {φ : P →ₗ[R] P}
    (hφ : IsEquivariant ρ ρ φ) (m : ℕ)
    (h : IsEquivariant (ρ.tprod τ) (ρ.tprod τ) (TensorProduct.map (φ ^ m) LinearMap.id)) :
    coinvMap (ρ.tprod τ) (TensorProduct.map (φ ^ m) LinearMap.id) h =
      coinvMap (ρ.tprod τ) (TensorProduct.map φ LinearMap.id) (isEquivariant_tensorMap hφ isEquivariant_id) ^ m := by
  rw [← coinvMap_pow (ρ.tprod τ) (isEquivariant_tensorMap hφ isEquivariant_id) m
    (isEquivariant_pow (isEquivariant_tensorMap hφ isEquivariant_id) m)]
  exact coinvMap_congr _ _ _ (by rw [TensorProduct.map_pow, Module.End.id_pow])

end Gen

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)
  [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

variable (m : ℕ)

theorem trace_pow0 :
    LinearMap.trace Λ _ (coinvMap ((ρPC Λ π Γ I 0).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 0 ^ m)
      LinearMap.id) (isEquivariant_tensorMap (isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI 0) m)
        isEquivariant_id)) = LinearMap.trace Λ M (τ (π ψ) ^ m) := by
  rw [coinvMap_tensor_pow _ τ (frobPC_equiv π Γ I ψ t h hI 0) m]
  exact trace_eq_of_intertwine _ _ _ (intertwine_pow _ (pcIso0_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t)
    (h := h) (hI := hI) (τ := τ)) m)

include hΛ hall hπ in
theorem trace_pow1 [Fintype S] [DecidableEq S] :
    LinearMap.trace Λ _ (coinvMap ((ρPC Λ π Γ I 1).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 1 ^ m)
      LinearMap.id) (isEquivariant_tensorMap (isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI 1) m)
        isEquivariant_id)) = LinearMap.trace Λ _ (frob1 (τ.comp π) Γ ψ t h ^ m) := by
  rw [coinvMap_tensor_pow _ τ (frobPC_equiv π Γ I ψ t h hI 1) m]
  exact trace_eq_of_intertwine _ _ _ (intertwine_pow _ (pcIso1_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t)
    (h := h) (hI := hI) (τ := τ) (hΛ := hΛ) (hall := hall) (hπ := hπ)) m)

include hΛ hallI hπ in
theorem trace_pow2 [Fintype S] [DecidableEq S] :
    LinearMap.trace Λ _ (coinvMap ((ρPC Λ π Γ I 2).tprod τ) (TensorProduct.map (frobPC Λ π Γ I ψ t h hI 2 ^ m)
      LinearMap.id) (isEquivariant_tensorMap (isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI 2) m)
        isEquivariant_id)) = LinearMap.trace Λ _ (frob2 (τ.comp π) Γ I ψ t h hI ^ m) := by
  rw [coinvMap_tensor_pow _ τ (frobPC_equiv π Γ I ψ t h hI 2) m]
  exact trace_eq_of_intertwine _ _ _ (intertwine_pow _ (pcIso2_frob (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t)
    (h := h) (hI := hI) (τ := τ) (hΛ := hΛ) (hallI := hallI) (hπ := hπ)) m)

include hΛ hall hallI hπ in
/-- **Lefschetz trace formula for the powers of the Frobenius** on the cone complex:
`Tr(F^m | M) - Tr(F^m | K¹(M)) + Tr(F^m | K²(M)) = Σ_c L(frobPC^m)[c] · Tr(τ(c)⁻¹ | M)`. -/
theorem lefschetz_frob_pow [IsLocalRing Λ] [Fintype (ConjClasses Gf)] [Fintype S] [DecidableEq S]
    [∀ i, Module.Free Λ (PC Λ π Γ I i)] [∀ i, Module.Finite Λ (PC Λ π Γ I i)]
    (hρ : ∀ i, IsProj (ρPC Λ π Γ I i)) [Module.Free Λ M] [Module.Finite Λ M] :
    LinearMap.trace Λ M (τ (π ψ) ^ m) - LinearMap.trace Λ _ (frob1 (τ.comp π) Γ ψ t h ^ m) +
      LinearMap.trace Λ _ (frob2 (τ.comp π) Γ I ψ t h hI ^ m) =
      ∑ c : ConjClasses Gf, lefschetz (ρPC Λ π Γ I) 2 (fun i => frobPC Λ π Γ I ψ t h hI i ^ m) c *
        twChar τ LinearMap.id c := by
  have H := lefschetz_PC π Γ I hρ (M := M) (τ := τ) (φ := fun i => frobPC Λ π Γ I ψ t h hI i ^ m)
    (fun i => isEquivariant_pow (frobPC_equiv π Γ I ψ t h hI i) m) (ψ := LinearMap.id) (isEquivariant_id (ρ := τ))
  beta_reduce at H
  rw [trace_pow0 π Γ I ψ t h hI τ m, trace_pow1 π Γ I ψ t h hI τ hΛ hall hπ m,
    trace_pow2 π Γ I ψ t h hI τ hΛ hallI hπ m] at H
  exact H

end Model

end

end Lefschetz
end RamanujanPetersson

end

-- ===== S4.Def_RP_Lefschetz_Cancel =====
section

/-!
# S4-Lefschetz (L2): cancelling a non-unit factor by lifting the coefficient level

The Hattori-Stallings centraliser formula only gives `|Z(γ)| * τ_[γ] = |Z(γ)| * N_γ` in `ℤ/lᵐ`, and `|Z(γ)|` need not
be a unit. The cure: compute at the higher level `ℤ/l^(n+k)` with `|Z(γ)| ∣ l^k`-part absorbed, then reduce to `ℤ/lⁿ`.
* `cast_eq_of_mul_eq`: if `a * x = a * y` in `ZMod (l ^ (n + k))` and `a ∣ l ^ k`, then `x` and `y` have the same image
  in `ZMod (l ^ n)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.Lefschetz

/-- The level divisibility `l ^ n ∣ l ^ (n + k)`. -/
theorem lvl_dvd (l n k : ℕ) : l ^ n ∣ l ^ (n + k) := pow_dvd_pow l (Nat.le_add_right n k)

/-- **Cancellation by lifting the level.** If `a * x = a * y` in `ℤ/l^(n+k)` and `a ∣ l^k`, then `x ≡ y` in `ℤ/lⁿ`. -/
theorem cast_eq_of_mul_eq {l : ℕ} (hl : 0 < l) (n k a : ℕ) (ha : a ∣ l ^ k)
    (x y : ZMod (l ^ (n + k))) (h : (a : ZMod (l ^ (n + k))) * x = a * y) :
    ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) x = ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) y := by
  have : NeZero (l ^ (n + k)) := ⟨pow_ne_zero _ hl.ne'⟩
  rw [← sub_eq_zero, ← map_sub]
  have h0 : (a : ZMod (l ^ (n + k))) * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  rw [← ZMod.natCast_zmod_val (x - y), ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨b, hb⟩ := ha
  have hapos : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb
    exact pow_ne_zero _ hl.ne' hb
  have hdvd : l ^ n ∣ (x - y).val := by
    have h1 : a * (l ^ n * b) ∣ a * (x - y).val := by
      have he : a * (l ^ n * b) = l ^ (n + k) := by rw [pow_add, hb]; ring
      rw [he]
      exact h0
    exact dvd_trans (dvd_mul_right _ b) ((mul_dvd_mul_iff_left hapos).1 h1)
  rw [← ZMod.natCast_zmod_val (x - y), map_natCast, ZMod.natCast_eq_zero_iff]
  exact hdvd

/-- The same with the factor written as a cast of a natural number dividing `l ^ k` on both sides as a scalar. -/
theorem cast_eq_of_nsmul_eq {l : ℕ} (hl : 0 < l) (n k a : ℕ) (ha : a ∣ l ^ k)
    (x y : ZMod (l ^ (n + k))) (h : a • x = a • y) :
    ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) x = ZMod.castHom (lvl_dvd l n k) (ZMod (l ^ n)) y :=
  cast_eq_of_mul_eq hl n k a ha x y (by rw [← nsmul_eq_mul, ← nsmul_eq_mul, h])

end RamanujanPetersson.Lefschetz

end

-- ===== S4.Def_RP_Lefschetz_ZFin1 =====
section

/-!
# S4-Lefschetz, L6z (1): finiteness of cocycle modules, the group-theoretic part

* `HomLC D A`: locally constant homomorphisms `D → A`.
* `z1_eq_of_reps`: a cocycle on `Δ` is determined by its values on `Δ ∩ ker π` and on representatives of `π(Δ)`.
* `finite_Z1_regRep`: `Z¹(Δ, Λ[Gf])` is finite once `Hom_lc(Δ ∩ ker π, Λ)` is (`Λ`, `Gf` finite).
* `finite_Z1_inertia`: from a residue hypothesis (`Ldet`), every `Z¹(Γ ⊓ I_s, Λ[Gf])` is finite.
* `finite_Z1_triv`: `Z¹(Γ, Λ)` (trivial action) is finite once `H¹_c(Γ, {I_s}; Λ)` and all `Z¹(Γ ⊓ I_s, Λ)` are.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Lefschetz

noncomputable section

open CurveCoh PerfectCx

/-- Locally constant homomorphisms `D → A`. -/
abbrev HomLC (D A : Type) [Mul D] [TopologicalSpace D] [Add A] : Type :=
  {f : D → A // IsLocallyConstant f ∧ ∀ a b, f (a * b) = f a + f b}

section Gen

theorem finite_of_ker_range {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (f : X →+ Y) [Finite Y]
    (hk : Finite f.ker) : Finite X := by
  have : Finite (X ⧸ f.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange f).symm.toEquiv
  exact Finite.of_addSubgroup_quotient f.ker

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G]
  {A : Type} [AddCommGroup A] [Module Λ A] (ρ : Representation Λ G A)

/-- A cocycle on `Δ` is determined by its values on `Δ ∩ ker π` and on representatives of `π(Δ)`. -/
theorem z1_eq_of_reps {Gf : Type} [Group Gf] (π : G →* Gf) (Δ : Subgroup G) (R : Gf → Δ)
    (hR : ∀ g : Δ, π (R (π g) : G) = π g) (c1 c2 : Z1 ρ Δ)
    (hK : ∀ g : Δ, π g = 1 → (c1 : Δ → A) g = (c2 : Δ → A) g)
    (hRc : ∀ y, (c1 : Δ → A) (R y) = (c2 : Δ → A) (R y)) : c1 = c2 := by
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨r, hr⟩ : ∃ r, r = R (π g) := ⟨_, rfl⟩
  have hg : g = r * (r⁻¹ * g) := by group
  have hh : π ((r⁻¹ * g : Δ) : G) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hr, hR g, inv_mul_cancel]
  have e1 := ((mem_Z1 _ _ _).1 c1.2).2 r (r⁻¹ * g)
  have e2 := ((mem_Z1 _ _ _).1 c2.2).2 r (r⁻¹ * g)
  rw [← hg] at e1 e2
  rw [e1, e2, hK _ hh, hr, hRc]

/-- Representatives of `π(Δ)` in `Δ`. -/
theorem exists_reps {Gf : Type} [Group Gf] (π : G →* Gf) (Δ : Subgroup G) :
    ∃ R : Gf → Δ, ∀ g : Δ, π (R (π g) : G) = π g := by
  classical
  refine ⟨fun y => if h : ∃ g : Δ, π g = y then h.choose else 1, fun g => ?_⟩
  have h : ∃ g' : Δ, π g' = π g := ⟨g, rfl⟩
  show π ((if h : ∃ g' : Δ, π g' = π g then h.choose else 1 : Δ) : G) = π g
  rw [dif_pos h]
  exact h.choose_spec

variable [Finite Λ] [IsTopologicalGroup G] {Gf : Type} [Group Gf] [Finite Gf]

/-- `Z¹(Δ, Λ[Gf])` is finite once `Hom_lc(Δ ∩ ker π, Λ)` is. -/
theorem finite_Z1_regRep (π : G →* Gf) (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1)
    (hfin : Finite (HomLC K Λ)) : Finite (Z1 (regRep Λ π) Δ) := by
  classical
  haveI := hfin
  haveI := finite_A Λ Gf
  obtain ⟨R, hR⟩ := exists_reps π Δ
  let Φ : Z1 (regRep Λ π) Δ → (Gf → HomLC K Λ) × (Gf → MonoidAlgebra Λ Gf) := fun c =>
    (fun y => ⟨fun k => (resK π Δ K hK c k).coeff y,
      (resK_lc π Δ K hK c).comp (fun a : MonoidAlgebra Λ Gf => a.coeff y),
      fun a b => by beta_reduce; rw [resK_add, MonoidAlgebra.coeff_add, Finsupp.add_apply]⟩,
      fun y => (c : Δ → MonoidAlgebra Λ Gf) (R y))
  refine Finite.of_injective Φ fun c1 c2 h => ?_
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine z1_eq_of_reps (regRep Λ π) π Δ R hR c1 c2 (fun g hg => ?_) (fun y => congrFun h2 y)
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun y => ?_)
  exact congrArg (fun f : HomLC K Λ => f.1 ⟨g, (hK g).2 ⟨g.2, hg⟩⟩) (congrFun h1 y)

variable (π : G →* Gf) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]

/-- From a residue hypothesis, `Z¹(Γ ⊓ I_s, Λ[Gf])` is finite (`Ldet`: a cocycle is determined on the kernel of `π`
by its value at the generator `σ_s`). -/
theorem finite_Z1_inertia (Hr : ResHyp Λ π Γ I) (s : S) : Finite (Z1 (regRep Λ π) (Γ ⊓ I s)) := by
  classical
  haveI := finite_A Λ Gf
  obtain ⟨R, hR⟩ := exists_reps π (Γ ⊓ I s)
  let Φ : Z1 (regRep Λ π) (Γ ⊓ I s) → MonoidAlgebra Λ Gf × (Gf → MonoidAlgebra Λ Gf) := fun c =>
    ((c : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) ⟨Hr.σ s, Hr.hσ s⟩, fun y => (c : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (R y))
  refine Finite.of_injective Φ fun c1 c2 h => ?_
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine z1_eq_of_reps (regRep Λ π) π (Γ ⊓ I s) R hR c1 c2 (fun g hg => ?_) (fun y => congrFun h2 y)
  have h0 : ((c1 - c2 : Z1 (regRep Λ π) (Γ ⊓ I s)) : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) ⟨Hr.σ s, Hr.hσ s⟩ = 0 := by
    rw [Submodule.coe_sub, Pi.sub_apply, sub_eq_zero]
    exact h1
  have h3 := Hr.Ldet s (c1 - c2) h0 g hg
  rw [Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at h3
  exact h3

end Gen

section Triv

variable {Λ : Type} [CommRing Λ] [Finite Λ] {G : Type} [Group G] [TopologicalSpace G]

/-- `Z¹(Γ, Λ)` (trivial action) is finite once `H¹_c(Γ, {I_s}; Λ)` and all `Z¹(Γ ⊓ I_s, Λ)` are. -/
theorem finite_Z1_triv {S : Type} [Finite S] (Γ : Subgroup G) (I : S → Subgroup G)
    (hH : Finite (H1c (Representation.trivial Λ G Λ) Γ I))
    (hI : ∀ s, Finite (Z1 (Representation.trivial Λ G Λ) (Γ ⊓ I s))) :
    Finite (Z1 (Representation.trivial Λ G Λ) Γ) := by
  haveI := hI
  let res : Z1 (Representation.trivial Λ G Λ) Γ →+
      ((s : S) → Z1 (Representation.trivial Λ G Λ) (Γ ⊓ I s)) :=
    { toFun := fun c s => ⟨fun g => (c : Γ → Λ) ⟨(g : G), (Subgroup.mem_inf.1 g.2).1⟩,
        ((mem_Z1 _ _ _).1 c.2).1.comp_continuous (continuous_subtype_val.subtype_mk _),
        fun g h => by
          beta_reduce
          exact ((mem_Z1 _ _ _).1 c.2).2 ⟨(g : G), (Subgroup.mem_inf.1 g.2).1⟩ ⟨(h : G), (Subgroup.mem_inf.1 h.2).1⟩⟩
      map_zero' := funext fun s => Subtype.ext (funext fun g => rfl)
      map_add' := fun _ _ => funext fun s => Subtype.ext (funext fun g => rfl) }
  have hker : ∀ c : Z1 (Representation.trivial Λ G Λ) Γ, c ∈ res.ker →
      ∀ s (g : Γ), (g : G) ∈ I s → (c : Γ → Λ) g = 0 := by
    intro c hc s g hg
    exact congrArg (fun f => ((f s : Z1 (Representation.trivial Λ G Λ) (Γ ⊓ I s)) : ↥(Γ ⊓ I s) → Λ)
      ⟨g, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩) ((AddMonoidHom.mem_ker).1 hc)
  let ψ : res.ker → H1c (Representation.trivial Λ G Λ) Γ I := fun c =>
    Submodule.Quotient.mk ⟨(((c : Z1 (Representation.trivial Λ G Λ) Γ) : Γ → Λ), (0 : S → Λ)),
      (mem_Z1c _ _ _ _).2 ⟨(c : Z1 (Representation.trivial Λ G Λ) Γ).2, fun s g hg => by
        first
          | (dsimp only; rw [hker _ c.2 s g hg]; simp)
          | simp [hker _ c.2 s g hg]⟩⟩
  have hψ : Function.Injective ψ := by
    intro c1 c2 h
    have h' := (Submodule.Quotient.eq _).1 h
    obtain ⟨-, m, hm, -⟩ := (mem_B1c _ _ _ _).1 (Submodule.mem_comap.1 h')
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have := hm g
    simp only [Submodule.coe_subtype, Submodule.coe_sub, Prod.fst_sub, Pi.sub_apply,
      Representation.trivial_apply, sub_self, sub_eq_zero] at this
    exact this
  have : Finite res.ker := Finite.of_injective ψ hψ
  exact finite_of_ker_range res inferInstance

end Triv

end

end Lefschetz
end RamanujanPetersson

end


