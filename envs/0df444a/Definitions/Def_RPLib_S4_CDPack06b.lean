-- Prove2me | Definitions.Def_RPLib_S4_CDPack06b
-- name    : RPLib_S4_CDPack06b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:04:56.402783+00:00
-- url     : https://prove2.me/theorems/ab510589-a308-4767-b913-153beb01c609
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 6b of 71
-- statement:
--   Part 6b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_E4SEq`: S4-PD E4S, part 3: the top term of the cone is `A_Γ`
--   * `Def_RP_Cone_E4SInd`: S4-PD E4S, part 4: sections and induction cocycles
--   * `Def_RP_Cone_E4SLoc`: S4-PD E4S, part 5a: local residue hypotheses from normalised generators
--   * `Def_RP_Cone_E4SDat`: S4-PD E4S, part 5b: the residue hypotheses from local and cover-level data
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack06
import Definitions.Def_RPLib_S4_TameInertiaCoef

/-!
# Curve-duality library package, part 6b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_E4SEq`: S4-PD E4S, part 3: the top term of the cone is `A_Γ`
* `Def_RP_Cone_E4SInd`: S4-PD E4S, part 4: sections and induction cocycles
* `Def_RP_Cone_E4SLoc`: S4-PD E4S, part 5a: local residue hypotheses from normalised generators
* `Def_RP_Cone_E4SDat`: S4-PD E4S, part 5b: the residue hypotheses from local and cover-level data
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_E4SEq =====
section

/-!
# S4-PD E4S, part 3: the top term of the cone is `A_Γ`

From `ResHyp` (E4SRes): `R̄ : C = coker d¹ → A` is injective, `Ψ : A_Γ → C`, `[w] ↦ [ε_{s0} · w]` at `s0`, satisfies
`R̄ (Ψ [w]) = N_P · w`, and is a `Gf`-equivariant bijection.
* `cokResEquiv H hπ : C ≃ₗ[Λ] A_Γ`, `cokResEquiv_equiv`: it intertwines `cokRep (d1I ..)` and `rRepΓ π Γ`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra Representation

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (hπ : IsOpen (π.ker : Set G))

namespace ResHyp

variable (H : ResHyp Λ π Γ I)

/-- `R̄ : C → A`. -/
def resQ : (((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸ LinearMap.range (d1I Λ π Γ I hπ).toLinearMap) →ₗ[Λ]
    MonoidAlgebra Λ Gf :=
  Submodule.liftQ _ H.resL (by
    rintro _ ⟨p, rfl⟩
    exact LinearMap.mem_ker.2 (H.resL_d1 hπ p))

omit [Fintype Gf] in
theorem resQ_mk (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    H.resQ hπ (Submodule.Quotient.mk e) = H.resL e := rfl

theorem resQ_injective : Function.Injective (H.resQ hπ) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).2 (H.mem_range_of_resL_eq_zero hπ e hx)

omit [Fintype Gf] in
/-- `R e = N_P · U` for some `U`. -/
theorem exists_resL_eq (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    ∃ U : MonoidAlgebra Λ Gf, H.resL e = nrmS Λ (Γ.map π) * U := by
  have hu : ∀ s, ∃ u, (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) = nrmS Λ ((Γ ⊓ I s).map π) * u := fun s =>
    exists_eq_nrmS_mul_of_inv ((Γ ⊓ I s).map π) _ (fun d hd => H.inv_sg s (e s) d hd)
  choose u hu using hu
  refine ⟨∑ s, u s, ?_⟩
  rw [resL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hu s, ← mul_assoc, H.hNs s]

/-- `w ↦ ε_{s0} · w`. -/
def epsL : MonoidAlgebra Λ Gf →ₗ[Λ] Z1 (regRep Λ π) (Γ ⊓ I H.s0) where
  toFun w := eMul π (Γ ⊓ I H.s0) w (H.Lex' H.s0).choose
  map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _)
  map_smul' r a := Subtype.ext (funext fun _ => mul_smul_comm r _ a)

omit [Fintype Gf] in
theorem epsL_apply (w : MonoidAlgebra Λ Gf) (g : ↥(Γ ⊓ I H.s0)) :
    (H.epsL w : ↥(Γ ⊓ I H.s0) → MonoidAlgebra Λ Gf) g =
      ((H.Lex' H.s0).choose : ↥(Γ ⊓ I H.s0) → MonoidAlgebra Λ Gf) g * w := rfl

/-- `Ψ' w = [ε_{s0} · w]` (placed at `s0`). -/
def psiL : MonoidAlgebra Λ Gf →ₗ[Λ]
    (((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸ LinearMap.range (d1I Λ π Γ I hπ).toLinearMap) :=
  (LinearMap.range (d1I Λ π Γ I hπ).toLinearMap).mkQ ∘ₗ
    LinearMap.single Λ (fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0 ∘ₗ H.epsL

omit [Fintype Gf] in
theorem psiL_apply (w : MonoidAlgebra Λ Gf) :
    H.psiL hπ w = Submodule.Quotient.mk (Pi.single (M := fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0 (H.epsL w)) :=
  rfl

theorem resQ_psiL (w : MonoidAlgebra Λ Gf) : H.resQ hπ (H.psiL hπ w) = nrmS Λ (Γ.map π) * w := by
  rw [psiL_apply, resQ_mk, resL_apply, Finset.sum_eq_single H.s0]
  · rw [Pi.single_eq_same, epsL_apply, (H.Lex' H.s0).choose_spec, ← mul_assoc, H.hNs]
  · intro s _ hs
    rw [Pi.single_eq_of_ne hs, Submodule.coe_zero, Pi.zero_apply, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem psiL_regRep (γ : Γ) (w : MonoidAlgebra Λ Gf) :
    H.psiL hπ (((regRep Λ π).comp Γ.subtype) γ w) = H.psiL hπ w := by
  rw [← sub_eq_zero, ← map_sub]
  apply H.resQ_injective hπ
  rw [resQ_psiL, map_zero, regRepΓ_apply, mul_sub, ← mul_assoc,
    nrmS_mul_single (Γ.map π) _ (Subgroup.mem_map_of_mem π γ.2), sub_self]

/-- `Ψ : A_Γ → C`. -/
def Psi : AΓ (Λ := Λ) π Γ →ₗ[Λ]
    (((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸ LinearMap.range (d1I Λ π Γ I hπ).toLinearMap) :=
  Coinvariants.lift _ (H.psiL hπ) fun γ => LinearMap.ext fun w => H.psiL_regRep hπ γ w

theorem Psi_mk (w : MonoidAlgebra Λ Gf) : H.Psi hπ (Coinvariants.mk _ w) = H.psiL hπ w := rfl

theorem Psi_injective : Function.Injective (H.Psi hπ) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨w, rfl⟩ := Coinvariants.mk_surjective _ x
  have h := congrArg (H.resQ hπ) hx
  rw [map_zero, Psi_mk, resQ_psiL] at h
  exact (Submodule.Quotient.mk_eq_zero _).2 (mem_ker_of_nrmS_mul π Γ w h)

theorem Psi_surjective : Function.Surjective (H.Psi hπ) := by
  intro y
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨U, hU⟩ := H.exists_resL_eq e
  refine ⟨Coinvariants.mk _ U, H.resQ_injective hπ ?_⟩
  rw [Psi_mk, resQ_psiL, resQ_mk, hU]

theorem Psi_equiv (h : Gf) (x : AΓ (Λ := Λ) π Γ) :
    H.Psi hπ (rRepΓ π Γ h x) = cokRep (d1I Λ π Γ I hπ) h (H.Psi hπ x) := by
  refine Coinvariants.induction_on x fun w => ?_
  rw [rRepΓ_mk, Psi_mk, Psi_mk, psiL_apply, psiL_apply]
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk (rho2 Λ π Γ I h (Pi.single H.s0 (H.epsL w)))
  congr 1
  funext s
  by_cases hs : s = H.s0
  · subst hs
    show Pi.single (M := fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0 (H.epsL (w * single h⁻¹ 1)) H.s0 =
      eRep π (Γ ⊓ I H.s0) h (Pi.single (M := fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0 (H.epsL w) H.s0)
    rw [Pi.single_eq_same, Pi.single_eq_same]
    refine Subtype.ext (funext fun g => ?_)
    show _ * (w * single h⁻¹ 1) = _ * w * single h⁻¹ 1
    rw [mul_assoc]
  · show Pi.single (M := fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0 (H.epsL (w * single h⁻¹ 1)) s =
      eRep π (Γ ⊓ I s) h (Pi.single (M := fun s => Z1 (regRep Λ π) (Γ ⊓ I s)) H.s0 (H.epsL w) s)
    rw [Pi.single_eq_of_ne hs, Pi.single_eq_of_ne hs, map_zero]

/-- **E4S**: the top term `C = coker (d¹ : P¹ → P²)` of the cone is `A_Γ = Λ[Gf]_Γ`. -/
def cokResEquiv :
    (((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸ LinearMap.range (d1I Λ π Γ I hπ).toLinearMap) ≃ₗ[Λ]
      AΓ (Λ := Λ) π Γ :=
  (LinearEquiv.ofBijective (H.Psi hπ) ⟨H.Psi_injective hπ, H.Psi_surjective hπ⟩).symm

theorem cokResEquiv_symm_apply (x : AΓ (Λ := Λ) π Γ) : (H.cokResEquiv hπ).symm x = H.Psi hπ x := rfl

/-- `cokResEquiv` intertwines `cokRep (d1I ..)` and `rRepΓ π Γ`. -/
theorem cokResEquiv_equiv (h : Gf)
    (y : ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸ LinearMap.range (d1I Λ π Γ I hπ).toLinearMap) :
    H.cokResEquiv hπ (cokRep (d1I Λ π Γ I hπ) h y) = rRepΓ π Γ h (H.cokResEquiv hπ y) := by
  apply (H.cokResEquiv hπ).symm.injective
  rw [LinearEquiv.symm_apply_apply, cokResEquiv_symm_apply, Psi_equiv, ← cokResEquiv_symm_apply,
    LinearEquiv.symm_apply_apply]

end ResHyp

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_E4SInd =====
section

/-!
# S4-PD E4S, part 4: sections and induction cocycles

* `secOf π Δ p`: a section of `π` over `π(Δ)` with values in `Δ`.
* `lc_of_cocycle`: a cocycle vanishing on an open neighbourhood of `1` is locally constant.
* `indCoc`: the induction cocycle `g ↦ Σ_p p · χ((sec p)⁻¹ g sec((π g)⁻¹ p))` of a locally constant homomorphism
  `χ : Δ ∩ ker π → Λ`, a locally constant cocycle of `Δ` with values in `Λ[Gf]`.
* `coeff_nrmS`, `sum_single_ind`: norm elements through indicator coefficients.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra

section Sec

variable {Gf : Type} [Group Gf] {G : Type} [Group G] (π : G →* Gf) (Δ : Subgroup G)

open Classical in
/-- A section of `π` over `π(Δ)` with values in `Δ`. -/
def secOf (p : Gf) : G := if h : p ∈ Δ.map π then (Subgroup.mem_map.1 h).choose else 1

theorem secOf_mem (p : Gf) : secOf π Δ p ∈ Δ := by
  unfold secOf
  split_ifs with h
  · exact (Subgroup.mem_map.1 h).choose_spec.1
  · exact Δ.one_mem

theorem secOf_map {p : Gf} (hp : p ∈ Δ.map π) : π (secOf π Δ p) = p := by
  unfold secOf
  rw [dif_pos hp]
  exact (Subgroup.mem_map.1 hp).choose_spec.2

/-- `π g` as an element of `π(Δ)`. -/
def gP (g : Δ) : Δ.map π := ⟨π g, Subgroup.mem_map_of_mem π g.2⟩

end Sec

section LC

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Δ : Subgroup G)

omit [IsTopologicalGroup G] in
/-- A cocycle vanishing on an open neighbourhood of `1` is locally constant. -/
theorem lc_of_cocycle [IsTopologicalGroup G] {c : Δ → M} (hc : ∀ g h : Δ, c (g * h) = c g + ρ g (c h))
    {W : Set Δ} (hW : IsOpen W) (h1 : (1 : Δ) ∈ W) (hW0 : ∀ w ∈ W, c w = 0) : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(g * ·) '' W, isOpenMap_mul_left g W hW, ⟨1, h1, mul_one g⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  show c (g * w) = c g
  rw [hc, hW0 w hw, map_zero, add_zero]

end LC

section Ind

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Δ : Subgroup G) (K : Subgroup G)
  (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
include hK in
theorem indK_mem (p : Δ.map π) (g : Δ) :
    (secOf π Δ p)⁻¹ * (g : G) * secOf π Δ ((π (g : G))⁻¹ * p) ∈ K := by
  have hq : (π (g : G))⁻¹ * (p : Gf) ∈ Δ.map π :=
    (Δ.map π).mul_mem ((Δ.map π).inv_mem (Subgroup.mem_map_of_mem π g.2)) p.2
  refine (hK _).2 ⟨Δ.mul_mem (Δ.mul_mem (Δ.inv_mem (secOf_mem π Δ _)) g.2) (secOf_mem π Δ _), ?_⟩
  rw [map_mul, map_mul, map_inv, secOf_map π Δ p.2, secOf_map π Δ hq]
  group

/-- `(sec p)⁻¹ g sec((π g)⁻¹ p) ∈ Δ ∩ ker π`. -/
def indK (p : Δ.map π) (g : Δ) : K := ⟨_, indK_mem π Δ K hK p g⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indK_mul (p : Δ.map π) (g h : Δ) :
    indK π Δ K hK p (g * h) = indK π Δ K hK p g * indK π Δ K hK ((gP π Δ g)⁻¹ * p) h := by
  have e : (π ((g : G) * h))⁻¹ * (p : Gf) = (π (h : G))⁻¹ * ((π (g : G))⁻¹ * p) := by
    rw [map_mul, mul_inv_rev, mul_assoc]
  apply Subtype.ext
  show (secOf π Δ p)⁻¹ * ((g * h : Δ) : G) * secOf π Δ ((π ((g * h : Δ) : G))⁻¹ * p) =
    (secOf π Δ p)⁻¹ * (g : G) * secOf π Δ ((π (g : G))⁻¹ * p) *
      ((secOf π Δ ((π (g : G))⁻¹ * p))⁻¹ * (h : G) * secOf π Δ ((π (h : G))⁻¹ * ((π (g : G))⁻¹ * p)))
  rw [Subgroup.coe_mul, e]
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem indK_coe_of_ker (p : Δ.map π) (w : Δ) (hw : π (w : G) = 1) :
    (indK π Δ K hK p w : G) = (secOf π Δ p)⁻¹ * w * secOf π Δ p := by
  show (secOf π Δ p)⁻¹ * (w : G) * secOf π Δ ((π (w : G))⁻¹ * p) = _
  rw [hw, inv_one, one_mul]

variable [Fintype (Δ.map π)]

/-- The induction cochain of `χ : Δ ∩ ker π → Λ`. -/
def indFun (χ : K → Λ) (g : Δ) : MonoidAlgebra Λ Gf :=
  ∑ p : Δ.map π, single (p : Gf) (χ (indK π Δ K hK p g))

theorem indFun_mul (χ : K → Λ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g h : Δ) :
    indFun π Δ K hK χ (g * h) = indFun π Δ K hK χ g + regRep Λ π (g : G) (indFun π Δ K hK χ h) := by
  have e1 : regRep Λ π (g : G) (indFun π Δ K hK χ h) =
      ∑ p : Δ.map π, single (p : Gf) (χ (indK π Δ K hK ((gP π Δ g)⁻¹ * p) h)) := by
    rw [regRep_apply]
    unfold indFun
    rw [Finset.mul_sum]
    simp only [single_mul_single, one_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft (gP π Δ g)) _ _ (fun p => by
      rw [Equiv.coe_mulLeft, inv_mul_cancel_left]
      rfl)
  rw [e1]
  unfold indFun
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← single_add, ← hχ, ← indK_mul]

theorem indFun_lc (hπ : IsOpen (π.ker : Set G)) (χ : K → Λ) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) : IsLocallyConstant (indFun π Δ K hK χ) := by
  have h10 : χ 1 = 0 := by
    have h := hχ 1 1
    rw [mul_one] at h
    simpa using h
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (hχc {0})
  have hO0 : ∀ k : K, (k : G) ∈ O → χ k = 0 := fun k hk => by
    have h : k ∈ χ ⁻¹' {0} := by rw [← hOeq]; exact hk
    exact h
  have h1O : (1 : G) ∈ O := by
    have h : (1 : K) ∈ χ ⁻¹' {0} := h10
    rw [← hOeq] at h
    exact h
  refine lc_of_cocycle (regRep Λ π) Δ (indFun_mul π Δ K hK χ hχ)
    (W := ⋂ p : Δ.map π, (fun w : Δ => (secOf π Δ p)⁻¹ * (w : G) * secOf π Δ p) ⁻¹' (O ∩ π.ker)) ?_ ?_ ?_
  · exact isOpen_iInter_of_finite fun p => (hO.inter hπ).preimage (by fun_prop)
  · simp only [Set.mem_iInter, Set.mem_preimage, OneMemClass.coe_one, mul_one, inv_mul_cancel]
    exact fun _ => ⟨h1O, π.ker.one_mem⟩
  · intro w hw
    have hw' := Set.mem_iInter.1 hw
    have hw1 : π (w : G) = 1 := by
      have h := (hw' 1).2
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
        secOf_map π Δ (1 : Δ.map π).2] at h
      simpa using h
    unfold indFun
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [hO0 _ ?_, single_zero]
    rw [indK_coe_of_ker π Δ K hK p w hw1]
    exact (hw' p).1

/-- The induction cocycle of a locally constant homomorphism `χ : Δ ∩ ker π → Λ`. -/
def indCoc (hπ : IsOpen (π.ker : Set G)) (χ : K → Λ) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) : Z1 (regRep Λ π) Δ :=
  ⟨indFun π Δ K hK χ, (mem_Z1 _ _ _).2 ⟨indFun_lc π Δ K hK hπ χ hχc hχ, indFun_mul π Δ K hK χ hχ⟩⟩

theorem indCoc_apply (hπ : IsOpen (π.ker : Set G)) (χ : K → Λ) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g : Δ) :
    (indCoc π Δ K hK hπ χ hχc hχ : Δ → MonoidAlgebra Λ Gf) g = indFun π Δ K hK χ g := rfl

end Ind

section Norm

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf]

open Classical in
theorem coeff_nrmS (D : Subgroup Gf) [Fintype D] (z : Gf) :
    (nrmS Λ D).coeff z = if z ∈ D then 1 else 0 := by
  unfold nrmS
  rw [coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_single, Finsupp.single_apply]
  split_ifs with hz
  · rw [Finset.sum_eq_single ⟨z, hz⟩ (fun d _ hd => if_neg fun h => hd (Subtype.ext h))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  · exact Finset.sum_eq_zero fun d _ => if_neg fun h : (d : Gf) = z => hz (h ▸ d.2)

open Classical in
/-- `Σ_{p ∈ P} [p q ∈ D] p = N_D · q⁻¹` for `D ≤ P`, `q ∈ P`. -/
theorem sum_single_ind (P D : Subgroup Gf) [Fintype P] [Fintype D] (hDP : D ≤ P) (q : Gf) (hq : q ∈ P) :
    ∑ p : P, single (p : Gf) (if (p : Gf) * q ∈ D then (1 : Λ) else 0) = nrmS Λ D * single q⁻¹ 1 := by
  ext y
  rw [coeff_mul_single_apply, coeff_nrmS, inv_inv, mul_one, coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_single, Finsupp.single_apply]
  by_cases hy : y ∈ P
  · rw [Finset.sum_eq_single ⟨y, hy⟩ (fun p _ hp => if_neg fun h => hp (Subtype.ext h))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  · have hyq : ¬ y * q ∈ D := fun h => hy (by simpa using P.mul_mem (hDP h) (P.inv_mem hq))
    rw [Finset.sum_eq_zero fun (p : P) _ => if_neg fun h : (p : Gf) = y => hy (h ▸ p.2), if_neg hyq]

end Norm

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_E4SLoc =====
section

/-!
# S4-PD E4S, part 5a: local residue hypotheses from normalised generators

* `LocGen J I' N τ`: the body of `Residue.TauProp` with the inertia group as a parameter `I'`.
* `LocGen.eq_zero`, `LocGen.conj`: locally constant homomorphisms `J → M` (`N M = 0`) are determined by the
  value at `τ`, which is invariant under conjugation by `I'`.
* `hom_conj`, `sum_eq_zero_of_zmod` (transfer of a `ℤ/N`-valued vanishing statement to `N`-torsion groups).
* `zlift : ℤ/N →+ Λ` (`N = 0` in `Λ`), `resK` (restriction of a cocycle to `Δ ∩ ker π`).
* `ldet_of_locGen`, `linv_of_locGen`, `lex_of_locGen`: the hypotheses `Ldet`, `Linv`, `Lex` of `ResHyp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra TameInertia

section Gen

/-- A normalised generator `τ` of `J` with its character `θ` (the shape of `Residue.TauProp`, with the
inertia group `I'` as a parameter). -/
abbrev LocGen {G : Type} [Group G] [TopologicalSpace G] (J I' : Subgroup G) (N : ℕ) (τ : J) : Prop :=
  ∃ θ : J → ZMod N, IsLocallyConstant θ ∧ (∀ σ σ', θ (σ * σ') = θ σ + θ σ') ∧ θ τ = 1 ∧
    (∀ g ∈ I', ∀ σ (hσ : σ ∈ J) (hσ' : g⁻¹ * σ * g ∈ J), θ ⟨g⁻¹ * σ * g, hσ'⟩ = θ ⟨σ, hσ⟩) ∧
    (∀ χ : J → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') → ∀ σ, χ σ = χ τ * θ σ)

variable {G : Type} [Group G] [TopologicalSpace G] {J I' : Subgroup G} {N : ℕ} [NeZero N] {τ : J}
  {M : Type*} [AddCommGroup M]

theorem LocGen.eq_zero (h : LocGen J I' N τ) (hM : ∀ m : M, N • m = 0) (ψ : J → M) (hψc : IsLocallyConstant ψ)
    (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) (h0 : ψ τ = 0) (j : J) : ψ j = 0 := by
  obtain ⟨θ, -, -, hθ1, -, hgen⟩ := h
  rw [eq_val_nsmul_of_gen hM hθ1 (fun χ hχc hχ => ⟨χ τ, hgen χ hχc hχ⟩) ψ hψc hψ j, h0, nsmul_zero]

theorem LocGen.conj (h : LocGen J I' N τ) (hM : ∀ m : M, N • m = 0) (ψ : J → M) (hψc : IsLocallyConstant ψ)
    (hψ : ∀ a b, ψ (a * b) = ψ a + ψ b) (g : G) (hg : g ∈ I') (hj : g * τ * g⁻¹ ∈ J) :
    ψ ⟨g * τ * g⁻¹, hj⟩ = ψ τ := by
  obtain ⟨θ, -, -, hθ1, hθc, hgen⟩ := h
  have hj' : g⁻¹⁻¹ * (τ : G) * g⁻¹ ∈ J := by rwa [inv_inv]
  have e : (⟨g * τ * g⁻¹, hj⟩ : J) = ⟨g⁻¹⁻¹ * τ * g⁻¹, hj'⟩ :=
    Subtype.ext (by show g * (τ : G) * g⁻¹ = g⁻¹⁻¹ * τ * g⁻¹; rw [inv_inv])
  have hθ : θ ⟨g * τ * g⁻¹, hj⟩ = 1 := by
    rw [e]
    exact (hθc g⁻¹ (I'.inv_mem hg) τ τ.2 hj').trans hθ1
  rw [eq_val_nsmul_of_gen hM hθ1 (fun χ hχc hχ => ⟨χ τ, hgen χ hχc hχ⟩) ψ hψc hψ ⟨g * τ * g⁻¹, hj⟩, hθ,
    one_val_nsmul hM]

/-- A homomorphism to an abelian group is conjugation invariant. -/
theorem hom_conj {H : Type*} [Group H] (χ : H → M) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (h z : H) :
    χ (h * z * h⁻¹) = χ z := by
  have h1 : χ 1 = 0 := by
    have e := hχ 1 1
    rw [mul_one] at e
    simpa using e
  have h2 : χ h + χ h⁻¹ = 0 := by rw [← hχ, mul_inv_cancel, h1]
  rw [hχ, hχ, add_right_comm, h2, zero_add]

/-- Transfer of a `ℤ/N`-valued vanishing statement to every abelian group killed by `N`
(characters `M → ℚ/ℤ`, as in `TameInertia.eq_val_nsmul_of_gen`). -/
theorem sum_eq_zero_of_zmod {H : Type*} [Mul H] [TopologicalSpace H] {T : Type*} [Fintype T] (y : T → H)
    (hR : ∀ χ : H → ZMod N, IsLocallyConstant χ → (∀ a b, χ (a * b) = χ a + χ b) → ∑ t, χ (y t) = 0)
    (hM : ∀ m : M, N • m = 0) (χ : H → M) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) : ∑ t, χ (y t) = 0 := by
  classical
  refine CharacterModule.eq_zero_of_character_apply fun c => ?_
  have hex : ∀ σ, ∃ k : ZMod N, toQCircle N k = c (χ σ) := fun σ =>
    exists_toQCircle_eq N (by rw [← map_nsmul, hM, map_zero])
  let g : AddCircle (1 : ℚ) → ZMod N := fun z => if h : ∃ k, toQCircle N k = z then h.choose else 0
  have hg : ∀ σ, toQCircle N (g (c (χ σ))) = c (χ σ) := fun σ => by
    simp only [g, dif_pos (hex σ)]
    exact (hex σ).choose_spec
  have hgc : IsLocallyConstant (fun σ => g (c (χ σ))) := hχc.comp (fun m => g (c m))
  have hgm : ∀ σ τ, g (c (χ (σ * τ))) = g (c (χ σ)) + g (c (χ τ)) := fun σ τ =>
    toQCircle_injective N (by rw [map_add, hg, hg, hg, hχ, map_add])
  have h0 : ∑ t, g (c (χ (y t))) = 0 := hR _ hgc hgm
  rw [map_sum]
  calc ∑ t, c (χ (y t)) = ∑ t, toQCircle N (g (c (χ (y t)))) :=
        Finset.sum_congr rfl fun t _ => (hg (y t)).symm
    _ = toQCircle N (∑ t, g (c (χ (y t)))) := (map_sum _ _ _).symm
    _ = 0 := by rw [h0, map_zero]

end Gen

section Loc

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf)

theorem nsmul_alg {N : ℕ} (hN : (N : Λ) = 0) (a : MonoidAlgebra Λ Gf) : N • a = 0 := by
  rw [← Nat.cast_smul_eq_nsmul Λ, hN, zero_smul]

variable (Λ) in
/-- `ℤ/N → Λ` for `N = 0` in `Λ`. -/
def zlift (N : ℕ) (hN : (N : Λ) = 0) : ZMod N →+ Λ :=
  ZMod.lift N ⟨Int.castAddHom Λ, by simp [hN]⟩

theorem zlift_one {N : ℕ} (hN : (N : Λ) = 0) : zlift Λ N hN 1 = 1 := by
  have h : ((1 : ℤ) : ZMod N) = 1 := Int.cast_one
  rw [← h, zlift, ZMod.lift_coe]
  simp

theorem zlift_ite {N : ℕ} (hN : (N : Λ) = 0) (P : Prop) [Decidable P] :
    zlift Λ N hN (if P then 1 else 0) = if P then 1 else 0 := by
  split_ifs
  · exact zlift_one hN
  · exact map_zero _

/-- Restriction of a cocycle on `Δ` to `K = Δ ∩ ker π`. -/
def resK (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (e : Z1 (regRep Λ π) Δ) (k : K) :
    MonoidAlgebra Λ Gf :=
  (e : Δ → MonoidAlgebra Λ Gf) ⟨k, ((hK k).1 k.2).1⟩

theorem resK_lc (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (e : Z1 (regRep Λ π) Δ) :
    IsLocallyConstant (resK π Δ K hK e) :=
  ((mem_Z1 _ _ _).1 e.2).1.comp_continuous (continuous_subtype_val.subtype_mk _)

theorem resK_add (Δ K : Subgroup G) (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (e : Z1 (regRep Λ π) Δ)
    (a b : K) : resK π Δ K hK e (a * b) = resK π Δ K hK e a + resK π Δ K hK e b := by
  have hc := ((mem_Z1 _ _ _).1 e.2).2 ⟨a, ((hK a).1 a.2).1⟩ ⟨b, ((hK b).1 b.2).1⟩
  have ha : ∀ x, regRep Λ π (a : G) x = x := fun x => by
    rw [regRep_apply, ((hK a).1 a.2).2, ← one_def, one_mul]
  exact hc.trans (congrArg (fun z => (e : Δ → MonoidAlgebra Λ Gf) ⟨a, ((hK a).1 a.2).1⟩ + z) (ha _))

variable {N : ℕ} [NeZero N]

/-- (Ldet) from `LocGen`. -/
theorem ldet_of_locGen {Δ K I' : Subgroup G} (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) {τ : K}
    (h : LocGen K I' N τ) (hN : (N : Λ) = 0) (e : Z1 (regRep Λ π) Δ)
    (h0 : (e : Δ → MonoidAlgebra Λ Gf) ⟨τ, ((hK τ).1 τ.2).1⟩ = 0) (j : Δ) (hj : π j = 1) :
    (e : Δ → MonoidAlgebra Λ Gf) j = 0 :=
  h.eq_zero (nsmul_alg hN) _ (resK_lc π Δ K hK e) (resK_add π Δ K hK e) h0 ⟨j, (hK j).2 ⟨j.2, hj⟩⟩

/-- (Linv) from `LocGen`. -/
theorem linv_of_locGen {Δ K I' : Subgroup G} (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1) (hΔ : Δ ≤ I') {τ : K}
    (h : LocGen K I' N τ) (hN : (N : Λ) = 0) (e : Z1 (regRep Λ π) Δ) (g : Δ) :
    (e : Δ → MonoidAlgebra Λ Gf) (g * ⟨τ, ((hK τ).1 τ.2).1⟩ * g⁻¹) =
      (e : Δ → MonoidAlgebra Λ Gf) ⟨τ, ((hK τ).1 τ.2).1⟩ := by
  have hτ := (hK τ).1 τ.2
  have hj : (g : G) * τ * (g : G)⁻¹ ∈ K := (hK _).2 ⟨Δ.mul_mem (Δ.mul_mem g.2 hτ.1) (Δ.inv_mem g.2), by
    rw [map_mul, map_mul, map_inv, hτ.2, mul_one, mul_inv_cancel]⟩
  exact h.conj (nsmul_alg hN) _ (resK_lc π Δ K hK e) (resK_add π Δ K hK e) g (hΔ g.2) hj

/-- (Lex) from `LocGen`: the induction cocycle of `θ` takes the value `N_{π Δ}` at `τ`. -/
theorem lex_of_locGen {Δ K I' : Subgroup G} [Fintype (Δ.map π)] (hK : ∀ g, g ∈ K ↔ g ∈ Δ ∧ π g = 1)
    (hΔ : Δ ≤ I') {τ : K} (h : LocGen K I' N τ) (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) :
    ∃ ε : Z1 (regRep Λ π) Δ, (ε : Δ → MonoidAlgebra Λ Gf) ⟨τ, ((hK τ).1 τ.2).1⟩ = nrmS Λ (Δ.map π) := by
  obtain ⟨θ, hθc, hθ, hθ1, hθconj, -⟩ := h
  refine ⟨indCoc π Δ K hK hπ (fun k => zlift Λ N hN (θ k)) (hθc.comp fun z => zlift Λ N hN z)
    (fun a b => by simp only [hθ, map_add]), ?_⟩
  rw [indCoc_apply]
  unfold indFun nrmS
  refine Finset.sum_congr rfl fun p _ => ?_
  have hw : π ((⟨τ, ((hK τ).1 τ.2).1⟩ : Δ) : G) = 1 := ((hK τ).1 τ.2).2
  have hc := indK_coe_of_ker π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩ hw
  have hj : (secOf π Δ p)⁻¹ * (τ : G) * secOf π Δ p ∈ K :=
    (congrArg (· ∈ K) hc).mp (indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩).2
  have e : indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩ = ⟨_, hj⟩ := Subtype.ext hc
  have key : θ (indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩) = 1 :=
    (congrArg θ e).trans ((hθconj _ (hΔ (secOf_mem π Δ p)) τ τ.2 hj).trans hθ1)
  show single (p : Gf) (zlift Λ N hN (θ (indK π Δ K hK p ⟨τ, ((hK τ).1 τ.2).1⟩))) = single (p : Gf) 1
  rw [key, zlift_one]

end Loc

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_E4SDat =====
section

/-!
# S4-PD E4S, part 5b: the residue hypotheses from local and cover-level data

`ResDat` collects data in the shape the arithmetic side produces: normalised generators `σ s` with `LocGen`,
cover points `t : T` over `sh t : S` with conjugators `x t ∈ Γ` and `y t = x t σ (sh t) (x t)⁻¹ ∈ Γ_H = Γ ∩ ker π`,
the coset condition `hrep`, the residue theorem `hR` and the existence statement `hE` (both `ℤ/N`-valued).
`ResDat.toResHyp` builds the `ResHyp` of part 2 over any `Λ` with `N = 0` in `Λ`
(`GR` via `conj_x`, `GE1`/`GE2` via the global induction cocycle `exists_glob` and `conj_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra TameInertia

section Dat

variable {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (π : G →* Gf) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S] (I : S → Subgroup G)
  (N : ℕ) (T : Type) [Fintype T]

/-- Local and cover-level input for `ResHyp`: generators `σ s` with `LocGen`, cover points `t` over `sh t` with
`y t = x t σ (sh t) (x t)⁻¹ ∈ Γ_H`, the coset condition `hrep`, the residue theorem `hR`, existence `hE`. -/
structure ResDat where
  σ : S → G
  hσ : ∀ s, σ s ∈ Γ ⊓ I s
  hσπ : ∀ s, π (σ s) = 1
  J : S → Subgroup G
  hJ : ∀ s g, g ∈ J s ↔ g ∈ Γ ⊓ I s ∧ π g = 1
  hloc : ∀ s, LocGen (J s) (I s) N ⟨σ s, (hJ s (σ s)).2 ⟨hσ s, hσπ s⟩⟩
  ΓH : Subgroup G
  hΓH : ∀ g, g ∈ ΓH ↔ g ∈ Γ ∧ π g = 1
  sh : T → S
  x : T → G
  hx : ∀ t, x t ∈ Γ
  y : T → ΓH
  hy : ∀ t, (y t : G) = x t * σ (sh t) * (x t)⁻¹
  hrep : ∀ s, ∀ p ∈ Γ.map π, ∃! t, sh t = s ∧ (π (x t))⁻¹ * p ∈ (Γ ⊓ I s).map π
  hR : ∀ χ : ΓH → ZMod N, IsLocallyConstant χ → (∀ a b, χ (a * b) = χ a + χ b) → ∑ t, χ (y t) = 0
  hE : ∀ c : T → ZMod N, ∑ t, c t = 0 → ∃ χ : ΓH → ZMod N, IsLocallyConstant χ ∧
    (∀ a b, χ (a * b) = χ a + χ b) ∧ ∀ t, χ (y t) = c t
  s0 : S

variable {π Γ I N T}

namespace ResDat

variable (D : ResDat π Γ I N T) {Λ : Type} [CommRing Λ] [Fintype (Γ.map π)]
  [∀ s, Fintype ((Γ ⊓ I s).map π)]

theorem hσJ (s : S) : D.σ s ∈ D.J s := (D.hJ s _).2 ⟨D.hσ s, D.hσπ s⟩

/-- `σ s` in `Γ`. -/
def sG (s : S) : Γ := ⟨D.σ s, (Subgroup.mem_inf.1 (D.hσ s)).1⟩

variable (Λ) in
/-- `N_s = Σ_{t over s} π(x_t)`. -/
def Ns (s : S) : MonoidAlgebra Λ Gf :=
  ∑ t ∈ Finset.univ.filter (fun t => D.sh t = s), single (π (D.x t)) (1 : Λ)

theorem hNs (s : S) : D.Ns Λ s * nrmS Λ ((Γ ⊓ I s).map π) = nrmS Λ (Γ.map π) := by
  ext z
  rw [coeff_nrmS (Γ.map π) z, Ns, Finset.sum_mul, coeff_sum, Finsupp.finsetSum_apply]
  simp only [coeff_single_mul_apply, one_mul, coeff_nrmS]
  by_cases hz : z ∈ Γ.map π
  · obtain ⟨t0, ht0, hu⟩ := D.hrep s z hz
    rw [if_pos hz, Finset.sum_eq_single t0
      (fun t ht htne => if_neg fun h => htne (hu t ⟨(Finset.mem_filter.1 ht).2, h⟩))
      (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht0.1⟩)).elim), if_pos ht0.2]
  · rw [if_neg hz]
    exact Finset.sum_eq_zero fun t _ => if_neg fun h => hz (by
      have := (Γ.map π).mul_mem (Subgroup.mem_map_of_mem π (D.hx t)) (Subgroup.map_mono inf_le_left h)
      rwa [mul_inv_cancel_left] at this)

theorem conj_x (c : Z1 (regRep Λ π) Γ) (t : T) :
    single (π (D.x t)) (1 : Λ) * (c : Γ → MonoidAlgebra Λ Gf) (D.sG (D.sh t)) =
      resK π Γ D.ΓH D.hΓH c (D.y t) :=
  calc single (π (D.x t)) (1 : Λ) * (c : Γ → MonoidAlgebra Λ Gf) (D.sG (D.sh t))
      = (c : Γ → MonoidAlgebra Λ Gf) (⟨D.x t, D.hx t⟩ * D.sG (D.sh t) * ⟨D.x t, D.hx t⟩⁻¹) :=
        (cocycle_conj π c ⟨D.x t, D.hx t⟩ (D.sG (D.sh t)) (D.hσπ _)).symm
    _ = resK π Γ D.ΓH D.hΓH c (D.y t) :=
        congrArg (c : Γ → MonoidAlgebra Λ Gf) (Subtype.ext (D.hy t).symm)

/-- (GR) from the residue theorem `hR`. -/
theorem GR [NeZero N] (hN : (N : Λ) = 0) (c : Z1 (regRep Λ π) Γ) :
    ∑ s, D.Ns Λ s * (c : Γ → MonoidAlgebra Λ Gf) (D.sG s) = 0 := by
  have e1 : ∀ s, D.Ns Λ s * (c : Γ → MonoidAlgebra Λ Gf) (D.sG s) =
      ∑ t ∈ Finset.univ.filter (fun t => D.sh t = s), resK π Γ D.ΓH D.hΓH c (D.y t) := fun s => by
    rw [Ns, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← (Finset.mem_filter.1 ht).2]
    exact D.conj_x c t
  rw [Finset.sum_congr rfl fun s _ => e1 s, Finset.sum_fiberwise]
  exact sum_eq_zero_of_zmod D.y D.hR (nsmul_alg hN) _ (resK_lc π Γ D.ΓH D.hΓH c) (resK_add π Γ D.ΓH D.hΓH c)

theorem cmem (t : T) (s : S) (j : G) (hj : j ∈ D.J s) : D.x t * j * (D.x t)⁻¹ ∈ D.ΓH := by
  obtain ⟨hjΔ, hjπ⟩ := (D.hJ s j).1 hj
  exact (D.hΓH _).2 ⟨Γ.mul_mem (Γ.mul_mem (D.hx t) (Subgroup.mem_inf.1 hjΔ).1) (Γ.inv_mem (D.hx t)), by
    rw [map_mul, map_mul, map_inv, hjπ, mul_one, mul_inv_cancel]⟩

/-- `j ↦ χ(x_t j x_t⁻¹)` on `J s`. -/
def cfun {M : Type*} (χ : D.ΓH → M) (t : T) (s : S) (j : D.J s) : M :=
  χ ⟨D.x t * j * (D.x t)⁻¹, D.cmem t s j j.2⟩

theorem cfun_lc {M : Type*} (χ : D.ΓH → M) (hχc : IsLocallyConstant χ) (t : T) (s : S) :
    IsLocallyConstant (D.cfun χ t s) :=
  hχc.comp_continuous (((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _)

theorem cfun_add {M : Type*} [AddCommGroup M] (χ : D.ΓH → M) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (t : T)
    (s : S) (a b : D.J s) : D.cfun χ t s (a * b) = D.cfun χ t s a + D.cfun χ t s b := by
  simp only [cfun]
  rw [← hχ]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  group

/-- KEY conjugation lemma: `χ(g⁻¹ σ_s g) = χ(y_t)` when `t` is the cover point over `s` of the coset of `π g⁻¹`. -/
theorem conj_eq [NeZero N] {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0) (χ : D.ΓH → M)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g : G) (hg : g ∈ Γ) (s : S) (t : T)
    (hts : D.sh t = s) (hgt : (π (D.x t))⁻¹ * (π g)⁻¹ ∈ (Γ ⊓ I s).map π) (hgs : g⁻¹ * D.σ s * g ∈ D.ΓH) :
    χ ⟨g⁻¹ * D.σ s * g, hgs⟩ = χ (D.y t) := by
  subst hts
  obtain ⟨δ, hδ, hδπ⟩ := Subgroup.mem_map.1 hgt
  have hxt := D.hx t
  have hδΓ : δ ∈ Γ := (Subgroup.mem_inf.1 hδ).1
  have hh : g⁻¹ * δ⁻¹ * (D.x t)⁻¹ ∈ D.ΓH := (D.hΓH _).2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (Γ.inv_mem hδΓ))
    (Γ.inv_mem hxt), by simp only [map_mul, map_inv, hδπ]; group⟩
  have hjδ : δ * D.σ (D.sh t) * δ⁻¹ ∈ D.J (D.sh t) := (D.hJ _ _).2 ⟨(Γ ⊓ I (D.sh t)).mul_mem
    ((Γ ⊓ I (D.sh t)).mul_mem hδ (D.hσ _)) ((Γ ⊓ I (D.sh t)).inv_mem hδ), by
    rw [map_mul, map_mul, map_inv, D.hσπ, mul_one, mul_inv_cancel]⟩
  have key := (D.hloc (D.sh t)).conj hM (D.cfun χ t (D.sh t)) (D.cfun_lc χ hχc t _) (D.cfun_add χ hχ t _) δ
    (Subgroup.mem_inf.1 hδ).2 hjδ
  have e1 : g⁻¹ * D.σ (D.sh t) * g = (g⁻¹ * δ⁻¹ * (D.x t)⁻¹) * (D.x t * (δ * D.σ (D.sh t) * δ⁻¹) * (D.x t)⁻¹) *
      (g⁻¹ * δ⁻¹ * (D.x t)⁻¹)⁻¹ := by group
  calc χ ⟨g⁻¹ * D.σ (D.sh t) * g, hgs⟩
      = χ (⟨_, hh⟩ * ⟨_, D.cmem t _ _ hjδ⟩ * (⟨_, hh⟩ : D.ΓH)⁻¹) := congrArg χ (Subtype.ext e1)
    _ = D.cfun χ t (D.sh t) ⟨δ * D.σ (D.sh t) * δ⁻¹, hjδ⟩ := hom_conj χ hχ _ _
    _ = D.cfun χ t (D.sh t) ⟨D.σ (D.sh t), D.hσJ _⟩ := key
    _ = χ (D.y t) := congrArg χ (Subtype.ext (D.hy t).symm)

/-- The cover point over `s` of the coset of `q`. -/
def tOf (s : S) (q : Γ.map π) : T := (D.hrep s q q.2).exists.choose

theorem tOf_spec (s : S) (q : Γ.map π) :
    D.sh (D.tOf s q) = s ∧ (π (D.x (D.tOf s q)))⁻¹ * (q : Gf) ∈ (Γ ⊓ I s).map π :=
  (D.hrep s q q.2).exists.choose_spec

theorem tOf_unique (s : S) (q : Γ.map π) (t : T) (ht : D.sh t = s)
    (htq : (π (D.x t))⁻¹ * (q : Gf) ∈ (Γ ⊓ I s).map π) : D.tOf s q = t :=
  (D.hrep s q q.2).unique (D.tOf_spec s q) ⟨ht, htq⟩

theorem tOf_eq_iff (s' s : S) (p q : Γ.map π) :
    D.tOf s' p = D.tOf s q ↔ s' = s ∧ (q : Gf)⁻¹ * p ∈ (Γ ⊓ I s).map π := by
  constructor
  · intro h
    have h1 := D.tOf_spec s' p
    have h2 := D.tOf_spec s q
    rw [h] at h1
    have hs : s' = s := h1.1.symm.trans h2.1
    refine ⟨hs, ?_⟩
    rw [hs] at h1
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2.2) h1.2
    rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
  · rintro ⟨rfl, h⟩
    refine D.tOf_unique s' p _ (D.tOf_spec s' q).1 ?_
    have := Subgroup.mul_mem _ (D.tOf_spec s' q).2 h
    rwa [mul_assoc, mul_inv_cancel_left] at this

theorem tOf_inv_eq_iff (s' s : S) (p q : Γ.map π) :
    D.tOf s' p⁻¹ = D.tOf s q ↔ s' = s ∧ (p : Gf) * q ∈ (Γ ⊓ I s).map π := by
  rw [D.tOf_eq_iff]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (q : Gf)⁻¹ * (p : Gf)⁻¹ ∈ (Γ ⊓ I s).map π := h
    have := Subgroup.inv_mem _ h'
    rwa [mul_inv_rev, inv_inv, inv_inv] at this
  · show (q : Gf)⁻¹ * (p : Gf)⁻¹ ∈ (Γ ⊓ I s).map π
    have := Subgroup.inv_mem _ h
    rwa [mul_inv_rev] at this

variable [DecidableEq T]

theorem sum_glob (s' s : S) (q : Γ.map π) :
    ∑ p : Γ.map π, single (p : Gf) (if D.tOf s' p⁻¹ = D.tOf s q then (1 : Λ) else 0) =
      if s' = s then nrmS Λ ((Γ ⊓ I s).map π) * single (q : Gf)⁻¹ 1 else 0 := by
  split_ifs with hs
  · rw [← sum_single_ind (Γ.map π) ((Γ ⊓ I s).map π) (Subgroup.map_mono inf_le_left) q q.2]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    classical
    exact if_congr ((D.tOf_inv_eq_iff s' s p q).trans (and_iff_right hs)) rfl rfl
  · exact Finset.sum_eq_zero fun (p : Γ.map π) _ => by
      rw [if_neg fun h => hs ((D.tOf_inv_eq_iff s' s p q).1 h).1, single_zero]

/-- The global induction cocycle of a `χ` with prescribed values `c` on the `y t`. -/
theorem exists_glob [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) (c : T → ZMod N)
    (hc : ∑ t, c t = 0) : ∃ e : Z1 (regRep Λ π) Γ, ∀ s', (e : Γ → MonoidAlgebra Λ Gf) (D.sG s') =
      ∑ p : Γ.map π, single (p : Gf) (zlift Λ N hN (c (D.tOf s' p⁻¹))) := by
  obtain ⟨χ, hχc, hχ, hχy⟩ := D.hE c hc
  have hMz : ∀ m : ZMod N, N • m = 0 := fun m => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine ⟨indCoc π Γ D.ΓH D.hΓH hπ (fun k => zlift Λ N hN (χ k)) (hχc.comp fun z => zlift Λ N hN z)
    (fun a b => by simp only [hχ, map_add]), fun s' => ?_⟩
  rw [indCoc_apply]
  unfold indFun
  refine Finset.sum_congr rfl fun p _ => ?_
  have hw : π ((D.sG s' : Γ) : G) = 1 := D.hσπ s'
  have hc' := indK_coe_of_ker π Γ D.ΓH D.hΓH p (D.sG s') hw
  have hgs : (secOf π Γ p)⁻¹ * D.σ s' * secOf π Γ p ∈ D.ΓH :=
    (congrArg (· ∈ D.ΓH) hc').mp (indK π Γ D.ΓH D.hΓH p (D.sG s')).2
  have hgt : (π (D.x (D.tOf s' p⁻¹)))⁻¹ * (π (secOf π Γ p))⁻¹ ∈ (Γ ⊓ I s').map π := by
    rw [secOf_map π Γ p.2]
    exact (D.tOf_spec s' p⁻¹).2
  have e : indK π Γ D.ΓH D.hΓH p (D.sG s') = ⟨_, hgs⟩ := Subtype.ext hc'
  have key : χ (indK π Γ D.ΓH D.hΓH p (D.sG s')) = c (D.tOf s' p⁻¹) :=
    ((congrArg χ e).trans
      (D.conj_eq hMz χ hχc hχ _ (secOf_mem π Γ p) s' _ (D.tOf_spec s' p⁻¹).1 hgt hgs)).trans (hχy _)
  show single (p : Gf) (zlift Λ N hN (χ (indK π Γ D.ΓH D.hΓH p (D.sG s')))) = _
  rw [key]

/-- (GE1) from `hE`. -/
theorem GE1 [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) (s : S) :
    ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (D.sG s') =
      (if s' = s then nrmS Λ ((Γ ⊓ I s).map π) else 0) -
        (if s' = D.s0 then nrmS Λ ((Γ ⊓ I D.s0).map π) else 0) := by
  obtain ⟨e, he⟩ := D.exists_glob hN hπ
    (fun t => (if t = D.tOf s 1 then 1 else 0) - (if t = D.tOf D.s0 1 then 1 else 0))
    (by simp [Finset.sum_sub_distrib])
  refine ⟨e, fun s' => (he s').trans ?_⟩
  have h1 : single (((1 : Γ.map π) : Gf))⁻¹ (1 : Λ) = 1 := by
    show single (1 : Gf)⁻¹ (1 : Λ) = 1
    rw [inv_one, one_def]
  simp only [map_sub, zlift_ite, single_sub, Finset.sum_sub_distrib, D.sum_glob, h1, mul_one]

/-- (GE2) from `hE`. -/
theorem GE2 [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) (γ : Γ) :
    ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (D.sG s') =
      if s' = D.s0 then nrmS Λ ((Γ ⊓ I D.s0).map π) * (single (π γ) 1 - 1) else 0 := by
  obtain ⟨e, he⟩ := D.exists_glob hN hπ
    (fun t => (if t = D.tOf D.s0 (gP π Γ γ)⁻¹ then 1 else 0) - (if t = D.tOf D.s0 1 then 1 else 0))
    (by simp [Finset.sum_sub_distrib])
  refine ⟨e, fun s' => (he s').trans ?_⟩
  have h1 : single (((1 : Γ.map π) : Gf))⁻¹ (1 : Λ) = 1 := by
    show single (1 : Gf)⁻¹ (1 : Λ) = 1
    rw [inv_one, one_def]
  have h2 : single ((((gP π Γ γ)⁻¹ : Γ.map π) : Gf))⁻¹ (1 : Λ) = single (π (γ : G)) 1 := by
    show single ((π (γ : G))⁻¹)⁻¹ (1 : Λ) = _
    rw [inv_inv]
  simp only [map_sub, zlift_ite, single_sub, Finset.sum_sub_distrib, D.sum_glob, h1, h2, mul_one]
  split_ifs
  · rw [mul_sub, mul_one]
  · rw [sub_zero]

/-- The `ResHyp` of the data. -/
def toResHyp [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) : ResHyp Λ π Γ I where
  σ := D.σ
  hσ := D.hσ
  hσπ := D.hσπ
  Ns := D.Ns Λ
  hNs := D.hNs
  s0 := D.s0
  Ldet s e h0 j hj := ldet_of_locGen π (D.hJ s) (D.hloc s) hN e h0 j hj
  Linv s e g := linv_of_locGen π (D.hJ s) inf_le_right (D.hloc s) hN e g
  Lex s := lex_of_locGen π (D.hJ s) inf_le_right (D.hloc s) hN hπ
  GR := D.GR hN
  GE1 := D.GE1 hN hπ
  GE2 := D.GE2 hN hπ

theorem toResHyp_σ [NeZero N] (hN : (N : Λ) = 0) (hπ : IsOpen (π.ker : Set G)) :
    (D.toResHyp hN hπ).σ = D.σ := rfl

end ResDat

end Dat

end

end PerfectCx
end RamanujanPetersson

end


