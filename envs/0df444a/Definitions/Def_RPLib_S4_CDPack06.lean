-- Prove2me | Definitions.Def_RPLib_S4_CDPack06
-- name    : RPLib_S4_CDPack06
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:52:33.485959+00:00
-- url     : https://prove2.me/theorems/8936d604-2dbb-4e61-af32-152f6a6260c0
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 6 of 71
-- statement:
--   Part 6 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_Cone_E4SFree`: S4-PD E4S, part 1: a finite subgroup acting on `Λ[Gf]` by left multiplication
--   * `Def_RP_Cone_E4SRes`: S4-PD E4S, part 2: the residue map on the top term of the cone
--   * `Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
--   * `Def_RP_PerfectCx_Top`: S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack03
import Definitions.Def_RPLib_S4_CDPack01

/-!
# Curve-duality library package, part 6 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_Cone_E4SFree`: S4-PD E4S, part 1: a finite subgroup acting on `Λ[Gf]` by left multiplication
* `Def_RP_Cone_E4SRes`: S4-PD E4S, part 2: the residue map on the top term of the cone
* `Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
* `Def_RP_PerfectCx_Top`: S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Cone_E4SFree =====
section

/-!
# S4-PD E4S, part 1: a finite subgroup acting on `Λ[Gf]` by left multiplication

`rcRep D x` is a representative of the right coset `D x`; `nrmS Λ D = Σ_{d ∈ D} d`.
* `eq_nrmS_mul_of_inv` (F1): `D`-invariants are norms.
* `mem_ker_of_nrmS_mul` (F2): `N_P U = 0` puts `U` in the coinvariant kernel (`P = π(Γ)`).
* `cocycle_conj`: `e(g σ g⁻¹) = g · e(σ)` when `π σ = 1`.
* `exists_cob_of_ker` (F3): a cocycle vanishing on `Δ ∩ ker π` is a coboundary.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra Representation

section Free

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] (D : Subgroup Gf)

/-- A representative of the right coset `D x`. -/
def rcRep (x : Gf) : Gf := (Quotient.mk (QuotientGroup.rightRel D) x).out

theorem rcRep_mul_inv_mem (x : Gf) : rcRep D x * x⁻¹ ∈ D := by
  have h := @Quotient.exact _ (QuotientGroup.rightRel D) _ _
    (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel D) x))
  have h' : x * (rcRep D x)⁻¹ ∈ D := QuotientGroup.rightRel_apply.mp h
  simpa [mul_inv_rev] using D.inv_mem h'

theorem rcRep_mul (d x : Gf) (hd : d ∈ D) : rcRep D (d * x) = rcRep D x := by
  unfold rcRep
  congr 1
  exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simpa [mul_inv_rev] using D.inv_mem hd))

theorem rcRep_eq_of_mem {x y : Gf} (h : y * x⁻¹ ∈ D) : rcRep D y = rcRep D x := by
  have := rcRep_mul D (y * x⁻¹) x h
  rwa [inv_mul_cancel_right] at this

theorem rcRep_rcRep (x : Gf) : rcRep D (rcRep D x) = rcRep D x :=
  rcRep_eq_of_mem D (rcRep_mul_inv_mem D x)

variable [Fintype D]

variable (Λ) in
/-- The norm element `N_D = Σ_{d ∈ D} d` of `Λ[Gf]`. -/
def nrmS : MonoidAlgebra Λ Gf := ∑ d : D, single (d : Gf) (1 : Λ)

theorem coeff_nrmS_mul (a : MonoidAlgebra Λ Gf) (y : Gf) :
    (nrmS Λ D * a).coeff y = ∑ d : D, a.coeff ((d : Gf)⁻¹ * y) := by
  simp only [nrmS, Finset.sum_mul, coeff_sum, Finsupp.finsetSum_apply, coeff_single_mul_apply, one_mul]

theorem nrmS_mul_single (p : Gf) (hp : p ∈ D) : nrmS Λ D * single p (1 : Λ) = nrmS Λ D := by
  simp only [nrmS, Finset.sum_mul, single_mul_single, one_mul]
  exact Fintype.sum_equiv (Equiv.mulRight ⟨p, hp⟩) _ _ (fun d => rfl)

/-- (F1) `D`-invariants of `Λ[Gf]` are norms. -/
theorem eq_nrmS_mul_of_inv [DecidableEq Gf] (a : MonoidAlgebra Λ Gf) (ha : ∀ d ∈ D, single d (1 : Λ) * a = a) :
    a = nrmS Λ D * ofCoeff (a.coeff.filter fun x => rcRep D x = x) := by
  ext y
  rw [coeff_nrmS_mul]
  have hy : y * (rcRep D y)⁻¹ ∈ D := by simpa [mul_inv_rev] using D.inv_mem (rcRep_mul_inv_mem D y)
  rw [Finset.sum_eq_single ⟨y * (rcRep D y)⁻¹, hy⟩]
  · have hc := rcRep_mul_inv_mem D y
    have h := congrArg (fun b : MonoidAlgebra Λ Gf => b.coeff (rcRep D y)) (ha _ hc)
    simp only [coeff_single_mul_apply, one_mul, mul_inv_rev, inv_inv, inv_mul_cancel_right] at h
    simp only [Finsupp.filter_apply, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    rw [if_pos (rcRep_rcRep D y)]
    exact h
  · intro d _ hd
    simp only [Finsupp.filter_apply]
    split_ifs with h
    · exfalso
      rw [rcRep_mul D _ y (D.inv_mem d.2)] at h
      exact hd (Subtype.ext (by show (d : Gf) = y * (rcRep D y)⁻¹; rw [h]; group))
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- (F1) in existence form. -/
theorem exists_eq_nrmS_mul_of_inv (a : MonoidAlgebra Λ Gf) (ha : ∀ d ∈ D, single d (1 : Λ) * a = a) :
    ∃ u : MonoidAlgebra Λ Gf, a = nrmS Λ D * u := by
  classical
  exact ⟨_, eq_nrmS_mul_of_inv D a ha⟩

theorem mapDomain_rcRep_eq [DecidableEq Gf] (U : MonoidAlgebra Λ Gf) :
    mapDomain (rcRep D) U = ofCoeff ((nrmS Λ D * U).coeff.filter fun x => rcRep D x = x) := by
  induction U using MonoidAlgebra.induction_linear with
  | zero => ext; simp [mapDomain_zero, Finsupp.filter_zero]
  | add a b ha hb => rw [mapDomain_add, ha, hb, mul_add, coeff_add, Finsupp.filter_add, ofCoeff_add]
  | single x r =>
    rw [mapDomain_single]
    ext y
    simp only [Finsupp.filter_apply, coeff_nrmS_mul, coeff_single, Finsupp.single_apply]
    by_cases hy : rcRep D y = y
    · by_cases hxy : y * x⁻¹ ∈ D
      · have hx : rcRep D x = y := by rw [← hy]; exact (rcRep_eq_of_mem D hxy).symm
        rw [if_pos hx, if_pos hy, Finset.sum_eq_single ⟨y * x⁻¹, hxy⟩]
        · rw [if_pos (by simp)]
        · intro d _ hd
          rw [if_neg]
          intro h
          exact hd (Subtype.ext (by show (d : Gf) = y * x⁻¹; rw [h]; group))
        · intro h
          exact absurd (Finset.mem_univ _) h
      · have hx : rcRep D x ≠ y := fun h => hxy (by rw [← h]; exact rcRep_mul_inv_mem D x)
        rw [if_neg hx, if_pos hy]
        refine (Finset.sum_eq_zero fun d _ => if_neg fun h => hxy ?_).symm
        rw [h]
        simp [mul_inv_rev]
    · have hx : rcRep D x ≠ y := fun h => hy (by rw [← h]; exact rcRep_rcRep D x)
      rw [if_neg hx, if_neg hy]

end Free

section Coinv

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem sub_mapDomain_mem_ker (U : MonoidAlgebra Λ Gf) :
    U - mapDomain (rcRep (Γ.map π)) U ∈ Coinvariants.ker ((regRep Λ π).comp Γ.subtype) := by
  induction U using MonoidAlgebra.induction_linear with
  | zero => rw [mapDomain_zero, sub_zero]; exact Submodule.zero_mem _
  | add a b ha hb =>
    rw [mapDomain_add, add_sub_add_comm]
    exact Submodule.add_mem _ ha hb
  | single x r =>
    rw [mapDomain_single]
    obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 (rcRep_mul_inv_mem (Γ.map π) x)
    have h := Coinvariants.sub_mem_ker (ρ := (regRep Λ π).comp Γ.subtype) ⟨γ, hγ⟩ (single x r)
    have he : ((regRep Λ π).comp Γ.subtype) ⟨γ, hγ⟩ (single x r) = single (rcRep (Γ.map π) x) r := by
      show single (π γ) (1 : Λ) * single x r = _
      rw [single_mul_single, one_mul, hγx, inv_mul_cancel_right]
    rw [he] at h
    rw [← neg_sub]
    exact Submodule.neg_mem _ h

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- (F2) `N_P U = 0`, `P = π(Γ)`, puts `U` in the kernel of `Λ[Gf] → Λ[Gf]_Γ`. -/
theorem mem_ker_of_nrmS_mul [Fintype (Γ.map π)] (U : MonoidAlgebra Λ Gf) (hU : nrmS Λ (Γ.map π) * U = 0) :
    U ∈ Coinvariants.ker ((regRep Λ π).comp Γ.subtype) := by
  classical
  have h := sub_mapDomain_mem_ker π Γ U
  rwa [mapDomain_rcRep_eq, hU, coeff_zero, Finsupp.filter_zero, ofCoeff_zero, sub_zero] at h

/-- `e(g σ g⁻¹) = g · e(σ)` for a cocycle `e` and `π σ = 1`. -/
theorem cocycle_conj {Δ : Subgroup G} (e : Z1 (regRep Λ π) Δ) (g σ : Δ) (hσ : π σ = 1) :
    (e : Δ → MonoidAlgebra Λ Gf) (g * σ * g⁻¹) = regRep Λ π (g : G) ((e : Δ → MonoidAlgebra Λ Gf) σ) := by
  have hc := ((mem_Z1 _ _ _).1 e.2).2
  have h1 : (e : Δ → MonoidAlgebra Λ Gf) 1 = 0 := Z1_one (regRep Λ π) Δ e.2
  have hσa : ∀ a, regRep Λ π (σ : G) a = a := fun a => by rw [regRep_apply, hσ, ← one_def, one_mul]
  have h2 := hc g g⁻¹
  rw [mul_inv_cancel, h1] at h2
  rw [hc (g * σ) g⁻¹, hc g σ]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hσa]
  rw [add_right_comm, ← h2, zero_add]

end Coinv

section Cob

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf)

omit [Fintype Gf] [IsTopologicalGroup G] in
/-- A cocycle vanishing on `Δ ∩ ker π` is constant on the fibres of `π`. -/
theorem cocycle_eq_of_map_eq {Δ : Subgroup G} {e : Δ → MonoidAlgebra Λ Gf} (he : e ∈ Z1 (regRep Λ π) Δ)
    (hker : ∀ j : Δ, π j = 1 → e j = 0) {g h : Δ} (hgh : π g = π h) : e g = e h := by
  have hk : π ((g⁻¹ * h : Δ) : G) = 1 := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hgh, inv_mul_cancel]
  have h1 := he.2 g (g⁻¹ * h)
  rw [mul_inv_cancel_left, hker _ hk, map_zero, add_zero] at h1
  exact h1.symm

/-- (F3) A cocycle of `Δ` with values in `Λ[Gf]` vanishing on `Δ ∩ ker π` is a coboundary. -/
theorem exists_cob_of_ker {Δ : Subgroup G} {e : Δ → MonoidAlgebra Λ Gf} (he : e ∈ Z1 (regRep Λ π) Δ)
    (hker : ∀ j : Δ, π j = 1 → e j = 0) :
    ∃ b : MonoidAlgebra Λ Gf, ∀ g : Δ, e g = regRep Λ π (g : G) b - b := by
  classical
  have hD : ∀ x : Gf, x * (rcRep (Δ.map π) x)⁻¹ ∈ Δ.map π := fun x => by
    simpa [mul_inv_rev] using (Δ.map π).inv_mem (rcRep_mul_inv_mem (Δ.map π) x)
  choose j hjΔ hj using fun x => Subgroup.mem_map.1 (hD x)
  obtain ⟨T, hb⟩ : ∃ T : MonoidAlgebra Λ Gf, ∀ z, T.coeff z = (e ⟨j z, hjΔ z⟩).coeff z :=
    ⟨∑ x : Gf, single x ((e ⟨j x, hjΔ x⟩).coeff x), fun z => by
      rw [coeff_sum, Finsupp.finsetSum_apply]
      simp [coeff_single, Finsupp.single_apply]⟩
  refine ⟨-T, fun g => ?_⟩
  ext y
  have hmem : (π g)⁻¹ ∈ Δ.map π := (Δ.map π).inv_mem (Subgroup.mem_map_of_mem π g.2)
  have hc : e ⟨j ((π g)⁻¹ * y), hjΔ _⟩ = e (g⁻¹ * ⟨j y, hjΔ y⟩) := by
    apply cocycle_eq_of_map_eq π he hker
    show π (j ((π g)⁻¹ * y)) = π ((g : G)⁻¹ * j y)
    rw [map_mul, map_inv, hj, hj, rcRep_mul _ _ _ hmem, mul_assoc]
  have h2 := he.2 g⁻¹ ⟨j y, hjΔ y⟩
  have h3 := Z1_inv (regRep Λ π) Δ he g
  simp only [regRep_apply, coeff_sub, coeff_neg, Finsupp.sub_apply, Finsupp.neg_apply, coeff_single_mul_apply,
    one_mul, hb]
  rw [hc, h2, h3]
  simp only [regRep_apply, coeff_add, coeff_neg, Finsupp.add_apply, Finsupp.neg_apply, coeff_single_mul_apply,
    one_mul, Subgroup.coe_inv, map_inv, inv_inv, mul_inv_cancel_left]
  abel

end Cob

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_E4SRes =====
section

/-!
# S4-PD E4S, part 2: the residue map on the top term of the cone

`ResHyp` collects the base-level input (normalised inertia generators `σ s ∈ Γ ⊓ I s` with `π (σ s) = 1`,
`N_s · N_{D_s} = N_P`, the local statements `Ldet`, `Linv`, `Lex`, the residue theorem `GR` and the
existence statements `GE1`, `GE2`).
* `resL H e = Σ_s N_s · e_s(σ_s)`; `resL_d1`: it kills the image of `d¹`.
* `exists_cocycle_of_family`: a family `(N_{D_s} u_s)_s` with `Σ_s u_s` in the coinvariant kernel is realised by
  a global cocycle at the `σ_s`.
* `mem_range_of_resL_eq_zero`: `resL H e = 0` puts `e` in the image of `d¹`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra Representation

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]

variable (Λ) in
/-- Base-level input of the top-degree computation. -/
structure ResHyp where
  σ : S → G
  hσ : ∀ s, σ s ∈ Γ ⊓ I s
  hσπ : ∀ s, π (σ s) = 1
  Ns : S → MonoidAlgebra Λ Gf
  hNs : ∀ s, Ns s * nrmS Λ ((Γ ⊓ I s).map π) = nrmS Λ (Γ.map π)
  s0 : S
  Ldet : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I s)), (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) ⟨σ s, hσ s⟩ = 0 →
    ∀ j : ↥(Γ ⊓ I s), π j = 1 → (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) j = 0
  Linv : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I s)) (g : ↥(Γ ⊓ I s)),
    (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (g * ⟨σ s, hσ s⟩ * g⁻¹) = (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) ⟨σ s, hσ s⟩
  Lex : ∀ s, ∃ ε : Z1 (regRep Λ π) (Γ ⊓ I s),
    (ε : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) ⟨σ s, hσ s⟩ = nrmS Λ ((Γ ⊓ I s).map π)
  GR : ∀ c : Z1 (regRep Λ π) Γ,
    ∑ s, Ns s * (c : Γ → MonoidAlgebra Λ Gf) ⟨σ s, (Subgroup.mem_inf.1 (hσ s)).1⟩ = 0
  GE1 : ∀ s, ∃ c : Z1 (regRep Λ π) Γ, ∀ s',
    (c : Γ → MonoidAlgebra Λ Gf) ⟨σ s', (Subgroup.mem_inf.1 (hσ s')).1⟩ =
      (if s' = s then nrmS Λ ((Γ ⊓ I s).map π) else 0) - (if s' = s0 then nrmS Λ ((Γ ⊓ I s0).map π) else 0)
  GE2 : ∀ γ : Γ, ∃ c : Z1 (regRep Λ π) Γ, ∀ s',
    (c : Γ → MonoidAlgebra Λ Gf) ⟨σ s', (Subgroup.mem_inf.1 (hσ s')).1⟩ =
      if s' = s0 then nrmS Λ ((Γ ⊓ I s0).map π) * (single (π γ) 1 - 1) else 0

variable {π Γ I}

namespace ResHyp

variable (H : ResHyp Λ π Γ I)

/-- `σ s` in `Γ ⊓ I s`. -/
def sg (s : S) : ↥(Γ ⊓ I s) := ⟨H.σ s, H.hσ s⟩

/-- `σ s` in `Γ`. -/
def sG (s : S) : Γ := ⟨H.σ s, (Subgroup.mem_inf.1 (H.hσ s)).1⟩

omit [IsTopologicalGroup G] in
theorem Ldet' (s : S) (e : Z1 (regRep Λ π) (Γ ⊓ I s)) (h : (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) = 0)
    (j : ↥(Γ ⊓ I s)) (hj : π j = 1) : (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) j = 0 :=
  H.Ldet s e h j hj

omit [IsTopologicalGroup G] in
theorem Linv' (s : S) (e : Z1 (regRep Λ π) (Γ ⊓ I s)) (g : ↥(Γ ⊓ I s)) :
    (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (g * H.sg s * g⁻¹) = (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) :=
  H.Linv s e g

omit [IsTopologicalGroup G] in
theorem Lex' (s : S) : ∃ ε : Z1 (regRep Λ π) (Γ ⊓ I s),
    (ε : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) = nrmS Λ ((Γ ⊓ I s).map π) :=
  H.Lex s

omit [IsTopologicalGroup G] in
theorem GR' (c : Z1 (regRep Λ π) Γ) : ∑ s, H.Ns s * (c : Γ → MonoidAlgebra Λ Gf) (H.sG s) = 0 :=
  H.GR c

omit [IsTopologicalGroup G] in
theorem GE1' (s : S) : ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (H.sG s') =
    (if s' = s then nrmS Λ ((Γ ⊓ I s).map π) else 0) - (if s' = H.s0 then nrmS Λ ((Γ ⊓ I H.s0).map π) else 0) :=
  H.GE1 s

omit [IsTopologicalGroup G] in
theorem GE2' (γ : Γ) : ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (H.sG s') =
    if s' = H.s0 then nrmS Λ ((Γ ⊓ I H.s0).map π) * (single (π γ) 1 - 1) else 0 :=
  H.GE2 γ

/-- The values `e(σ_s)` of a cocycle of `Γ ⊓ I s` are `D_s`-invariant. -/
theorem inv_sg (s : S) (e : Z1 (regRep Λ π) (Γ ⊓ I s)) (d : Gf) (hd : d ∈ (Γ ⊓ I s).map π) :
    single d (1 : Λ) * (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) = (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hd
  have h := cocycle_conj π e ⟨g, hg⟩ (H.sg s) (H.hσπ s)
  calc single (π g) (1 : Λ) * (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s)
      = regRep Λ π ((⟨g, hg⟩ : ↥(Γ ⊓ I s)) : G) ((e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s)) := rfl
    _ = (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (⟨g, hg⟩ * H.sg s * ⟨g, hg⟩⁻¹) := h.symm
    _ = (e : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) := H.Linv' s e ⟨g, hg⟩

/-- `R e = Σ_s N_s · e_s(σ_s)`. -/
def resL : ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) →ₗ[Λ] MonoidAlgebra Λ Gf where
  toFun e := ∑ s, H.Ns s * (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s)
  map_add' e f := by
    simp only [Pi.add_apply, Submodule.coe_add, mul_add, Finset.sum_add_distrib]
  map_smul' r e := by
    simp only [Pi.smul_apply, Submodule.coe_smul, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]

omit [IsTopologicalGroup G] in
theorem resL_apply (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    H.resL e = ∑ s, H.Ns s * (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) := rfl

/-- `R ∘ d¹ = 0` (the residue theorem `GR`). -/
theorem resL_d1 (hπ : IsOpen (π.ker : Set G)) (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :
    H.resL (d1 Λ π Γ I hπ p) = 0 := by
  rw [resL_apply]
  have h : ∀ s, ((d1 Λ π Γ I hπ p s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s)) =
      (p.1 : Γ → MonoidAlgebra Λ Gf) (H.sG s) := fun s => by
    show (p.1 : Γ → MonoidAlgebra Λ Gf) (H.sG s) - (regRep Λ π (H.σ s) (p.2 s) - p.2 s) =
      (p.1 : Γ → MonoidAlgebra Λ Gf) (H.sG s)
    rw [regRep_apply, H.hσπ s, ← one_def, one_mul, sub_self, sub_zero]
  simp only [h]
  exact H.GR' p.1

/-- Elements of the coinvariant kernel are realised at `σ_{s0}` by global cocycles (from `GE2`). -/
theorem exists_cocycle_of_ker {U : MonoidAlgebra Λ Gf} (hU : U ∈ Coinvariants.ker ((regRep Λ π).comp Γ.subtype)) :
    ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (H.sG s') =
      if s' = H.s0 then nrmS Λ ((Γ ⊓ I H.s0).map π) * U else 0 := by
  have hU' : U ∈ Submodule.span Λ (Set.range fun (gv : Γ × MonoidAlgebra Λ Gf) =>
      ((regRep Λ π).comp Γ.subtype) gv.1 gv.2 - gv.2) := hU
  clear hU
  induction hU' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨γ, y⟩, rfl⟩ := hx
    obtain ⟨c, hc⟩ := H.GE2' γ
    refine ⟨eMul π Γ y c, fun s' => ?_⟩
    have hρ : ((regRep Λ π).comp Γ.subtype) γ y = single (π (γ : G)) (1 : Λ) * y := rfl
    simp only [hρ]
    rw [eMul_apply, hc s']
    split_ifs <;> simp [mul_sub, sub_mul, mul_assoc]
  | zero => exact ⟨0, fun s' => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, fun s' => ?_⟩
    rw [Submodule.coe_add, Pi.add_apply, hc, hd]
    split_ifs <;> simp [mul_add]
  | smul r x _ hx =>
    obtain ⟨c, hc⟩ := hx
    refine ⟨r • c, fun s' => ?_⟩
    rw [Submodule.coe_smul, Pi.smul_apply, hc]
    split_ifs <;> simp

/-- A family `(N_{D_s} u_s)_s` with `Σ_s u_s` in the coinvariant kernel is the family of values at the `σ_s` of a
global cocycle (from `GE1`, `GE2`). -/
theorem exists_cocycle_of_family (u : S → MonoidAlgebra Λ Gf)
    (hu : ∑ s, u s ∈ Coinvariants.ker ((regRep Λ π).comp Γ.subtype)) :
    ∃ c : Z1 (regRep Λ π) Γ, ∀ s', (c : Γ → MonoidAlgebra Λ Gf) (H.sG s') = nrmS Λ ((Γ ⊓ I s').map π) * u s' := by
  choose c1 hc1 using H.GE1'
  obtain ⟨c2, hc2⟩ := H.exists_cocycle_of_ker hu
  refine ⟨∑ s, eMul π Γ (u s) (c1 s) + c2, fun s' => ?_⟩
  have e1 : ∀ s, (eMul π Γ (u s) (c1 s) : Γ → MonoidAlgebra Λ Gf) (H.sG s') =
      (if s' = s then nrmS Λ ((Γ ⊓ I s).map π) * u s else 0) -
        (if s' = H.s0 then nrmS Λ ((Γ ⊓ I H.s0).map π) * u s else 0) := fun s => by
    rw [eMul_apply, hc1 s s', sub_mul]
    simp only [ite_mul, zero_mul]
  rw [Submodule.coe_add, Pi.add_apply, Submodule.coe_sum, Finset.sum_apply, hc2]
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : s' = H.s0
  · subst h
    simp only [if_true]
    rw [Finset.mul_sum]
    abel
  · simp [h]

/-- (Injectivity) `R e = 0` puts `e` in the image of `d¹`. -/
theorem mem_range_of_resL_eq_zero [Fintype Gf] (hπ : IsOpen (π.ker : Set G))
    (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (he : H.resL e = 0) :
    e ∈ LinearMap.range (d1 Λ π Γ I hπ) := by
  have hu : ∀ s, ∃ u, (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) = nrmS Λ ((Γ ⊓ I s).map π) * u := fun s =>
    exists_eq_nrmS_mul_of_inv ((Γ ⊓ I s).map π) _ (fun d hd => H.inv_sg s (e s) d hd)
  choose u hu using hu
  have hU : nrmS Λ (Γ.map π) * ∑ s, u s = 0 := by
    calc nrmS Λ (Γ.map π) * ∑ s, u s = H.resL e := by
          rw [resL_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hu s, ← mul_assoc, H.hNs s]
      _ = 0 := he
  obtain ⟨c, hc⟩ := H.exists_cocycle_of_family u (mem_ker_of_nrmS_mul π Γ _ hU)
  have hf : ∀ s, ∃ b : MonoidAlgebra Λ Gf, ∀ g : ↥(Γ ⊓ I s), (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) g -
      (c : Γ → MonoidAlgebra Λ Gf) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ = regRep Λ π (g : G) b - b := by
    intro s
    let f : Z1 (regRep Λ π) (Γ ⊓ I s) := e s - res (regRep Λ π) Γ inf_le_left c
    have h0 : (f : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) = 0 := by
      show (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s) - (c : Γ → MonoidAlgebra Λ Gf) (H.sG s) = 0
      rw [hu s, hc s, sub_self]
    exact exists_cob_of_ker π f.2 (H.Ldet' s f h0)
  choose b hb using hf
  refine ⟨(c, -b), funext fun s => Subtype.ext (funext fun g => ?_)⟩
  show (c : Γ → MonoidAlgebra Λ Gf) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ - (regRep Λ π (g : G) (-b s) - -b s) =
    (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) g
  have h1 := hb s g
  rw [sub_eq_iff_eq_add] at h1
  rw [map_neg, h1]
  abel

end ResHyp

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_CoinvG =====
section

/-!
# S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`

* `AΓ π Γ := Λ[Gf]_Γ`, the coinvariants of `Γ` acting on `Λ[Gf]` by left multiplication through `π`.
* `rRepΓ π Γ`: `Gf` acting on `AΓ` by right multiplication by `h⁻¹` (it descends: left and right multiplication commute).
* `coinvG π Γ τ : (AΓ ⊗ M)_{Gf} ≃ M_Γ`, `⟦⟦a⟧ ⊗ m⟧ ↦ ⟦a · m⟧`, inverse `⟦m⟧ ↦ ⟦⟦1⟧ ⊗ m⟧`
  (`M_Γ = Coinvariants ((τ.comp π).comp Γ.subtype)`, which is `CurveCoh.H2c (τ.comp π) Γ` by definition).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra Representation TensorProduct

noncomputable section

section CoinvG

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

/-- `A_Γ := Λ[Gf]_Γ`. -/
abbrev AΓ : Type := Coinvariants ((regRep Λ π).comp Γ.subtype)

/-- Right multiplication by `h⁻¹` commutes with the left `Γ`-action. -/
def rInt (h : Gf) : IntertwiningMap ((regRep Λ π).comp Γ.subtype) ((regRep Λ π).comp Γ.subtype) :=
  ⟨rRep Λ Gf h, fun g => LinearMap.ext fun a => by
    show single (π (g : G)) 1 * a * single h⁻¹ 1 = single (π (g : G)) 1 * (a * single h⁻¹ 1)
    rw [mul_assoc]⟩

/-- `Gf` acting on `A_Γ` by right multiplication by `h⁻¹`. -/
def rRepΓ : Representation Λ Gf (AΓ (Λ := Λ) π Γ) where
  toFun h := Coinvariants.map _ _ (rInt π Γ h)
  map_one' := Coinvariants.hom_ext (LinearMap.ext fun a => by
    show Coinvariants.mk _ (a * single 1⁻¹ 1) = Coinvariants.mk _ a
    rw [inv_one, ← one_def, mul_one])
  map_mul' x y := Coinvariants.hom_ext (LinearMap.ext fun a => by
    show Coinvariants.mk _ (a * single (x * y)⁻¹ 1) = Coinvariants.mk _ (a * single y⁻¹ 1 * single x⁻¹ 1)
    rw [mul_assoc, single_mul_single, mul_inv_rev, one_mul])

theorem rRepΓ_mk (h : Gf) (a : MonoidAlgebra Λ Gf) :
    rRepΓ π Γ h (Coinvariants.mk _ a) = Coinvariants.mk _ (a * single h⁻¹ 1) := rfl

theorem regRepΓ_apply (g : Γ) (a : MonoidAlgebra Λ Gf) :
    ((regRep Λ π).comp Γ.subtype) g a = single (π (g : G)) 1 * a := rfl

variable {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

/-- `a ↦ (m ↦ ⟦a · m⟧)` on `Λ[Gf]`. -/
def gB0 : MonoidAlgebra Λ Gf →ₗ[Λ] M →ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  (τ.asAlgebraHom.toLinearMap : MonoidAlgebra Λ Gf →ₗ[Λ] M →ₗ[Λ] M).compr₂
    (Coinvariants.mk ((τ.comp π).comp Γ.subtype))

theorem gB0_apply (a : MonoidAlgebra Λ Gf) (m : M) :
    gB0 π Γ τ a m = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

theorem gB0_inv (g : Γ) : gB0 π Γ τ ∘ₗ ((regRep Λ π).comp Γ.subtype) g = gB0 π Γ τ := by
  refine LinearMap.ext fun a => LinearMap.ext fun m => ?_
  rw [LinearMap.comp_apply, regRepΓ_apply, gB0_apply, gB0_apply, map_mul, Module.End.mul_apply,
    Representation.asAlgebraHom_single_one]
  exact Coinvariants.mk_self_apply ((τ.comp π).comp Γ.subtype) g _

/-- `⟦a⟧ ⊗ m ↦ ⟦a · m⟧`. -/
def gF : AΓ (Λ := Λ) π Γ ⊗[Λ] M →ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  TensorProduct.lift (Coinvariants.lift _ (gB0 π Γ τ) (gB0_inv π Γ τ))

theorem gF_mk_tmul (a : MonoidAlgebra Λ Gf) (m : M) :
    gF π Γ τ (Coinvariants.mk _ a ⊗ₜ m) = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

theorem gF_inv (h : Gf) : gF π Γ τ ∘ₗ ((rRepΓ π Γ).tprod τ) h = gF π Γ τ := by
  refine TensorProduct.ext' fun x m => ?_
  induction x using Coinvariants.induction_on with
  | h a =>
    have hinv : τ h⁻¹ (τ h m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, rRepΓ_mk, gF_mk_tmul,
      gF_mk_tmul, map_mul, Module.End.mul_apply, Representation.asAlgebraHom_single_one, hinv]

/-- Forward map `(A_Γ ⊗ M)_{Gf} → M_Γ`. -/
def gFwd : Coinvariants ((rRepΓ π Γ).tprod τ) →ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  Coinvariants.lift _ (gF π Γ τ) (gF_inv π Γ τ)

theorem gFwd_mk (a : MonoidAlgebra Λ Gf) (m : M) :
    gFwd π Γ τ (Coinvariants.mk _ (Coinvariants.mk _ a ⊗ₜ m)) = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

/-- Balancedness: `⟦⟦b a⟧ ⊗ m⟧ = ⟦⟦b⟧ ⊗ a · m⟧`. -/
theorem gmk_mul_tmul (b a : MonoidAlgebra Λ Gf) (m : M) :
    Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ (b * a) ⊗ₜ m) =
      Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ b ⊗ₜ τ.asAlgebraHom a m) := by
  induction a using MonoidAlgebra.induction_on with
  | of x =>
    rw [Representation.asAlgebraHom_of, of_apply]
    have hb : (Coinvariants.mk ((regRep Λ π).comp Γ.subtype) (b * single x 1) : AΓ (Λ := Λ) π Γ) =
        rRepΓ π Γ x⁻¹ (Coinvariants.mk _ b) := by rw [rRepΓ_mk, inv_inv]
    rw [hb, Coinvariants.mk_inv_tmul]
  | add a a' ha ha' => simp only [mul_add, map_add, add_tmul, ha, ha', LinearMap.add_apply, tmul_add]
  | smul r a ha => simp only [mul_smul_comm, map_smul, ← smul_tmul', ha, LinearMap.smul_apply, tmul_smul]

theorem gBk_inv (g : Γ) :
    (Coinvariants.mk ((rRepΓ π Γ).tprod τ) ∘ₗ TensorProduct.mk Λ (AΓ (Λ := Λ) π Γ) M (Coinvariants.mk _ 1)) ∘ₗ
        ((τ.comp π).comp Γ.subtype) g =
      Coinvariants.mk ((rRepΓ π Γ).tprod τ) ∘ₗ TensorProduct.mk Λ (AΓ (Λ := Λ) π Γ) M (Coinvariants.mk _ 1) := by
  refine LinearMap.ext fun m => ?_
  show Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ 1 ⊗ₜ τ (π (g : G)) m) =
    Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ 1 ⊗ₜ m)
  rw [← Coinvariants.mk_inv_tmul (rRepΓ π Γ) τ, rRepΓ_mk, inv_inv, one_mul]
  have h1 : (Coinvariants.mk ((regRep Λ π).comp Γ.subtype) (single (π (g : G)) 1) : AΓ (Λ := Λ) π Γ) =
      Coinvariants.mk _ 1 := by
    have := Coinvariants.mk_self_apply ((regRep Λ π).comp Γ.subtype) g (1 : MonoidAlgebra Λ Gf)
    rw [← this]
    show _ = Coinvariants.mk _ (single (π (g : G)) 1 * 1)
    rw [mul_one]
  rw [h1]

/-- Backward map `M_Γ → (A_Γ ⊗ M)_{Gf}`, `⟦m⟧ ↦ ⟦⟦1⟧ ⊗ m⟧`. -/
def gBwd : Coinvariants ((τ.comp π).comp Γ.subtype) →ₗ[Λ] Coinvariants ((rRepΓ π Γ).tprod τ) :=
  Coinvariants.lift _ _ (gBk_inv π Γ τ)

theorem gBwd_mk (m : M) :
    gBwd π Γ τ (Coinvariants.mk _ m) = Coinvariants.mk _ (Coinvariants.mk _ 1 ⊗ₜ m) := rfl

/-- **`(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`** (`= H²_c` of `CurveCoh`). -/
def coinvG : Coinvariants ((rRepΓ π Γ).tprod τ) ≃ₗ[Λ] Coinvariants ((τ.comp π).comp Γ.subtype) :=
  LinearEquiv.ofLinearMap (gFwd π Γ τ) (gBwd π Γ τ)
    (Coinvariants.hom_ext (LinearMap.ext fun m => by
      show Coinvariants.mk _ (τ.asAlgebraHom 1 m) = Coinvariants.mk _ m
      rw [map_one, Module.End.one_apply]))
    (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
      induction x using Coinvariants.induction_on with
      | h a =>
        show Coinvariants.mk _ (Coinvariants.mk _ 1 ⊗ₜ τ.asAlgebraHom a m) =
          Coinvariants.mk ((rRepΓ π Γ).tprod τ) (Coinvariants.mk _ a ⊗ₜ m)
        rw [← gmk_mul_tmul, one_mul]))

theorem coinvG_mk (a : MonoidAlgebra Λ Gf) (m : M) :
    coinvG π Γ τ (Coinvariants.mk _ (Coinvariants.mk _ a ⊗ₜ m)) = Coinvariants.mk _ (τ.asAlgebraHom a m) := rfl

theorem coinvG_symm_mk (m : M) :
    (coinvG π Γ τ).symm (Coinvariants.mk _ m) = Coinvariants.mk _ (Coinvariants.mk _ 1 ⊗ₜ m) := rfl

end CoinvG

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_Top =====
section

/-!
# S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact

* `cokRep f`, `cokMk f`: the representation on `coker f` for an intertwining map `f`, and `W → coker f`.
* `coinvCokEquiv`: `((W ⊗ M)_G) / im (V ⊗ M)_G ≃ (coker f ⊗ M)_G` (right exactness of `(· ⊗ M)_G`).
* `topEquiv`: for the perfect complex, `H²(K(M)) = coker d¹_K ≃ (C ⊗ M)_{Gf}` with `C := coker d¹` on `P`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra Representation TensorProduct

noncomputable section

section RExact

variable {k G : Type} [CommRing k] [Group G] {V W M : Type} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] [AddCommGroup M] [Module k M] {σ : Representation k G V} {ρ : Representation k G W}
  (f : IntertwiningMap σ ρ) (τ : Representation k G M)

theorem range_le_comap_of_intertwining (g : G) :
    LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (ρ g) := by
  intro x hx
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hx
  exact Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨σ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩)

/-- The representation on `coker f`. -/
abbrev cokRep : Representation k G (W ⧸ LinearMap.range f.toLinearMap) :=
  ρ.quotient _ (range_le_comap_of_intertwining f)

/-- `W → coker f` as an intertwining map. -/
def cokMk : IntertwiningMap ρ (cokRep f) :=
  ⟨(LinearMap.range f.toLinearMap).mkQ, fun _ => LinearMap.ext fun _ => rfl⟩

theorem cokMk_apply (w : W) : cokMk f w = Submodule.Quotient.mk w := rfl

theorem cokMk_map (u : Coinvariants (σ.tprod τ)) :
    Coinvariants.map _ _ ((cokMk f).rTensor τ) (Coinvariants.map _ _ (f.rTensor τ) u) = 0 := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v m =>
    rw [Coinvariants.map_mk, Coinvariants.map_mk, IntertwiningMap.rTensor_apply, IntertwiningMap.rTensor_apply]
    have h0 : cokMk f (f v) = 0 := (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨v, rfl⟩)
    rw [h0, zero_tmul, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- `(W ⊗ M)_G / im (V ⊗ M)_G → (coker f ⊗ M)_G`. -/
def cokFwd : (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) →ₗ[k]
    Coinvariants ((cokRep f).tprod τ) :=
  Submodule.liftQ _ (Coinvariants.map _ _ ((cokMk f).rTensor τ)) (by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (cokMk_map f τ u))

/-- The bilinear map `W × M → (W ⊗ M)_G / im`, `(w, m) ↦ [w ⊗ m]`. -/
def cokB : W →ₗ[k] M →ₗ[k] (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) :=
  (TensorProduct.mk k W M).compr₂ ((Submodule.mkQ _) ∘ₗ Coinvariants.mk (ρ.tprod τ))

theorem cokB_apply (w : W) (m : M) :
    cokB f τ w m = Submodule.Quotient.mk (Coinvariants.mk (ρ.tprod τ) (w ⊗ₜ m)) := rfl

theorem range_le_ker_cokB : LinearMap.range f.toLinearMap ≤ LinearMap.ker (cokB f τ) := by
  intro x hx
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hx
  refine LinearMap.mem_ker.2 (LinearMap.ext fun m => ?_)
  rw [cokB_apply, LinearMap.zero_apply]
  exact (Submodule.Quotient.mk_eq_zero _).2
    (LinearMap.mem_range.2 ⟨Coinvariants.mk _ (v ⊗ₜ m), rfl⟩)

/-- `coker f ⊗ M → (W ⊗ M)_G / im`. -/
def cokT : (W ⧸ LinearMap.range f.toLinearMap) ⊗[k] M →ₗ[k]
    (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) :=
  TensorProduct.lift (Submodule.liftQ _ (cokB f τ) (range_le_ker_cokB f τ))

theorem cokT_mk_tmul (w : W) (m : M) :
    cokT f τ (Submodule.Quotient.mk w ⊗ₜ m) = Submodule.Quotient.mk (Coinvariants.mk (ρ.tprod τ) (w ⊗ₜ m)) := rfl

theorem cokT_inv (g : G) : cokT f τ ∘ₗ ((cokRep f).tprod τ) g = cokT f τ := by
  refine TensorProduct.ext' fun x m => ?_
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, quotient_apply, Submodule.mapQ_apply,
    cokT_mk_tmul, cokT_mk_tmul]
  congr 1
  have := Coinvariants.mk_self_apply (ρ.tprod τ) g (w ⊗ₜ m)
  rw [Representation.tprod_apply, TensorProduct.map_tmul] at this
  exact this

/-- `(coker f ⊗ M)_G → (W ⊗ M)_G / im`. -/
def cokBwd : Coinvariants ((cokRep f).tprod τ) →ₗ[k]
    (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) :=
  Coinvariants.lift _ (cokT f τ) (cokT_inv f τ)

/-- **Right exactness of `(· ⊗ M)_G`**: `(W ⊗ M)_G / im (V ⊗ M)_G ≃ (coker f ⊗ M)_G`. -/
def coinvCokEquiv : (Coinvariants (ρ.tprod τ) ⧸ LinearMap.range (Coinvariants.map _ _ (f.rTensor τ))) ≃ₗ[k]
    Coinvariants ((cokRep f).tprod τ) :=
  LinearEquiv.ofLinearMap (cokFwd f τ) (cokBwd f τ)
    (Coinvariants.hom_ext (TensorProduct.ext' fun x m => by
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl))
    (Submodule.linearMap_qext _ (Coinvariants.hom_ext (TensorProduct.ext' fun w m => rfl)))

theorem coinvCokEquiv_mk (w : W) (m : M) :
    coinvCokEquiv f τ (Submodule.Quotient.mk (Coinvariants.mk _ (w ⊗ₜ m))) =
      Coinvariants.mk _ (Submodule.Quotient.mk w ⊗ₜ m) := rfl

end RExact

section Top

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G)) {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)
  [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

include hall in
theorem map_iso2_range_d1 [Fintype S] [DecidableEq S] :
    (LinearMap.range (Coinvariants.map _ _ ((d1I Λ π Γ I hπ).rTensor τ))).map
        (iso2 π Γ I hπ τ hΛ hallI).toLinearMap =
      LinearMap.range (cx1 (τ.comp π) Γ I (isOpen_comp_ker π τ hπ)) := by
  rw [← LinearMap.range_comp, iso2_comp_d1 π Γ I hπ τ hΛ hall hallI,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

include hall in
/-- **Top degree of the perfect complex**: `H²(K(M)) ≃ (C ⊗ M)_{Gf}`, `C = coker (d¹ : P¹ → P²)`. -/
def topEquiv [Fintype S] [DecidableEq S] :
    H2K (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) ≃ₗ[Λ] Coinvariants ((cokRep (d1I Λ π Γ I hπ)).tprod τ) :=
  (Submodule.Quotient.equiv _ _ (iso2 π Γ I hπ τ hΛ hallI) (map_iso2_range_d1 π Γ I hπ τ hΛ hall hallI)).symm ≪≫ₗ
    coinvCokEquiv (d1I Λ π Γ I hπ) τ

include hall in
theorem topEquiv_mk [Fintype S] [DecidableEq S] (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) :
    topEquiv π Γ I hπ τ hΛ hall hallI (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m)))) =
      Coinvariants.mk _ (Submodule.Quotient.mk e ⊗ₜ m) := by
  simp only [topEquiv, LinearEquiv.trans_apply, Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

end Top

end

end PerfectCx
end RamanujanPetersson

end


