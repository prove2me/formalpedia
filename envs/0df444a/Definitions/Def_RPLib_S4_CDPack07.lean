-- Prove2me | Definitions.Def_RPLib_S4_CDPack07
-- name    : RPLib_S4_CDPack07
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:20:52.35068+00:00
-- url     : https://prove2.me/theorems/19f431e1-4d9a-46bc-8e5c-29b02c1e5d75
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 7 of 71
-- statement:
--   Part 7 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ConeDuality_ConstRes`: S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses
--   * `Def_RP_Cone_E4SFrob`: S4-PD E4frob (generic): the Frobenius on the top term of the cone
--   * `Def_RP_Cone_H2`: S4-PD (4): the cone's `H²` is `H²_c = M_Γ`, with Frobenius
--   * `Def_RP_CupDuality_GysC`: S4-CurveDuality O4G-3: coinducing a unipotent character
--   * `Def_RP_CupDuality_GysE`: S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack05
import Definitions.Def_RPLib_S4_CDPack06
import Definitions.Def_RPLib_S4_CDPack06b

/-!
# Curve-duality library package, part 7 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ConeDuality_ConstRes`: S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses
* `Def_RP_Cone_E4SFrob`: S4-PD E4frob (generic): the Frobenius on the top term of the cone
* `Def_RP_Cone_H2`: S4-PD (4): the cone's `H²` is `H²_c = M_Γ`, with Frobenius
* `Def_RP_CupDuality_GysC`: S4-CurveDuality O4G-3: coinducing a unipotent character
* `Def_RP_CupDuality_GysE`: S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ConeDuality_ConstRes =====
section

/-!
# S4-CurveDuality O6a: constant-coefficient data from S4-PD's residue hypotheses

`constData_of_resHyp`: the residue input `ResHyp` of S4-PD, taken for the trivial quotient `π : G → PUnit`
(so `Λ[Gf] = k`), gives `ConstData σ Γ I H.sg` for any `σ` that is trivial on `Γ`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `Λ[PUnit] ≅ Λ`. -/
abbrev unitE (k : Type) [CommRing k] : MonoidAlgebra k PUnit ≃+* k :=
  MonoidAlgebra.uniqueRingEquiv (R := k) (M := PUnit)

theorem regRep_one_apply (g : G) (a : MonoidAlgebra k PUnit) :
    regRep k (1 : G →* PUnit) g a = a := by
  rw [regRep_apply, MonoidHom.one_apply, ← MonoidAlgebra.one_def, one_mul]

theorem nrmS_punit (D : Subgroup PUnit) [Fintype D] : nrmS k D = 1 := by
  unfold nrmS
  rw [Fintype.sum_subsingleton _ (1 : D)]
  rfl

/-- Transport `Z¹(Γ', k(1)) → Z¹(Γ', k[PUnit])` when `σ` is trivial on `Γ'`. -/
theorem up_mem (σ : Representation k G k) (Γ' : Subgroup G) (h : ∀ (g : Γ') (x : k), σ g x = x)
    (e : Z1 σ Γ') : (fun g => (unitE k).symm ((e : Γ' → k) g)) ∈ Z1 (regRep k (1 : G →* PUnit)) Γ' := by
  obtain ⟨he1, he2⟩ := (mem_Z1 σ Γ' _).1 e.2
  refine (mem_Z1 _ Γ' _).2 ⟨he1.comp _, fun g g' => ?_⟩
  simp only [he2 g g', h, map_add, regRep_one_apply]

/-- Transport `Z¹(Γ', k[PUnit]) → Z¹(Γ', k(1))` when `σ` is trivial on `Γ'`. -/
theorem down_mem (σ : Representation k G k) (Γ' : Subgroup G) (h : ∀ (g : Γ') (x : k), σ g x = x)
    (e : Z1 (regRep k (1 : G →* PUnit)) Γ') :
    (fun g => unitE k ((e : Γ' → MonoidAlgebra k PUnit) g)) ∈ Z1 σ Γ' := by
  obtain ⟨he1, he2⟩ := (mem_Z1 _ Γ' _).1 e.2
  refine (mem_Z1 σ Γ' _).2 ⟨he1.comp _, fun g g' => ?_⟩
  simp only [he2 g g', h, map_add, regRep_one_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `σ` trivial on `Γ` is trivial on `Γ ⊓ I s`. -/
theorem triv_inf {σ : Representation k G k} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}
    (htriv : ∀ (g : Γ) (x : k), σ g x = x) (s : S) : ∀ (g : ↥(Γ ⊓ I s)) (x : k), σ g x = x :=
  fun g x => htriv ⟨g, (Subgroup.mem_inf.1 g.2).1⟩ x

variable (σ : Representation k G k) (Γ : Subgroup G) {S : Type} [Fintype S] [DecidableEq S]
  (I : S → Subgroup G) [Fintype (Γ.map (1 : G →* PUnit))] [∀ s, Fintype ((Γ ⊓ I s).map (1 : G →* PUnit))]

variable {σ Γ I} in
/-- **O6a.** S4-PD's residue hypotheses for the trivial quotient give the constant-coefficient data. -/
theorem constData_of_resHyp (H : ResHyp k (1 : G →* PUnit) Γ I) (htriv : ∀ (g : Γ) (x : k), σ g x = x) :
    ConstData σ Γ I H.sg := by
  have hN : ∀ s, H.Ns s = 1 := fun s => by
    have h := H.hNs s
    rwa [nrmS_punit, nrmS_punit, mul_one] at h
  have htG : ∀ s, tG H.sg s = H.sG s := fun s => rfl
  refine ⟨htriv, fun s e he => ?_, fun s a => ?_, fun d => ?_, fun r hr => ?_⟩
  · -- inj
    let e' : Z1 (regRep k (1 : G →* PUnit)) (Γ ⊓ I s) := ⟨_, up_mem σ _ (triv_inf htriv s) e⟩
    have h0 : (e' : ↥(Γ ⊓ I s) → MonoidAlgebra k PUnit) (H.sg s) = 0 := by
      show (unitE k).symm ((e : ↥(Γ ⊓ I s) → k) (H.sg s)) = 0
      rw [he, map_zero]
    apply Subtype.ext
    funext j
    have hj := H.Ldet' s e' h0 j (Subsingleton.elim _ _)
    have hj' : (unitE k).symm ((e : ↥(Γ ⊓ I s) → k) j) = 0 := hj
    exact (unitE k).symm.injective (hj'.trans (map_zero _).symm)
  · -- surj
    obtain ⟨ε, hε⟩ := H.Lex' s
    refine ⟨a • ⟨_, down_mem σ _ (triv_inf htriv s) ε⟩, ?_⟩
    show a • unitE k ((ε : ↥(Γ ⊓ I s) → MonoidAlgebra k PUnit) (H.sg s)) = a
    rw [hε, nrmS_punit, map_one, smul_eq_mul, mul_one]
  · -- resSum
    have h := congrArg (unitE k) (H.GR ⟨_, up_mem σ Γ htriv d⟩)
    simp only [hN, one_mul, map_sum, map_zero, RingEquiv.apply_symm_apply] at h
    exact h
  · -- resOnto
    choose c hc using H.GE1
    have hc' : ∀ s s', (c s : Γ → MonoidAlgebra k PUnit) (H.sG s') =
        (if s' = s then 1 else 0) - (if s' = H.s0 then 1 else 0) := fun s s' => by
      have h := hc s s'
      rw [nrmS_punit, nrmS_punit] at h
      exact h
    refine ⟨∑ s, r s • ⟨_, down_mem σ Γ htriv (c s)⟩, fun s' => ?_⟩
    rw [htG]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc',
      map_sub, apply_ite (unitE k), map_one, map_zero, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases h : s' = H.s0
    · simp [h, hr]
    · simp [h]

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_E4SFrob =====
section

/-!
# S4-PD E4frob (generic): the Frobenius on the top term of the cone

For `ψ` with boundary data `(t, h)` (`BdryCompat`), bijective `t`, conjugate decomposition images `hD` and the twist
`hTW : e(φ_s⁻¹ σ_s φ_s) = c • e(σ_{t s})` (`φ_s = ψ h_s`), the residue carries the cone Frobenius `frob2` to
`c • (π ψ) ·` (`resL_frob2`), so `cokResEquiv` carries it to `c • lftΓ ψ` (`cokResEquiv_frob`).
* `single_mul_nrmS`: `x · N_{D'} = N_D · x` for `D = x D' x⁻¹`; `map_conj_mem`: `π ψ` normalises `π(Γ)`.
* `lftΓ ψ : A_Γ → A_Γ`, `[a] ↦ [π(ψ) a]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra Representation

section Nrm

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf]

/-- `x · N_{D'} = N_D · x` when `D = x D' x⁻¹`. -/
theorem single_mul_nrmS (D D' : Subgroup Gf) [Fintype D] [Fintype D'] (x : Gf)
    (hD : ∀ d, d ∈ D' ↔ x * d * x⁻¹ ∈ D) :
    single x (1 : Λ) * nrmS Λ D' = nrmS Λ D * single x (1 : Λ) := by
  let e : D' ≃ D :=
    { toFun := fun d => ⟨x * d * x⁻¹, (hD d).1 d.2⟩
      invFun := fun d => ⟨x⁻¹ * d * x, (hD _).2 (by simp [mul_assoc])⟩
      left_inv := fun d => Subtype.ext (by simp [mul_assoc])
      right_inv := fun d => Subtype.ext (by simp [mul_assoc]) }
  simp only [nrmS, Finset.mul_sum, Finset.sum_mul, single_mul_single, mul_one]
  exact Fintype.sum_equiv e _ _ (fun d => by simp [e, mul_assoc])

/-- `π ψ` normalises `π(Γ)` for normal `Γ`. -/
theorem map_conj_mem {G : Type} [Group G] (π : G →* Gf) (Γ : Subgroup G) [hΓ : Γ.Normal] (ψ : G) (d : Gf) :
    d ∈ Γ.map π ↔ π ψ * d * (π ψ)⁻¹ ∈ Γ.map π := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨ψ * g * ψ⁻¹, hΓ.conj_mem g hg ψ, by simp only [map_mul, map_inv]⟩
  · rintro ⟨g, hg, hgd⟩
    refine ⟨ψ⁻¹ * g * ψ, by simpa using hΓ.conj_mem g hg ψ⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hgd]
    group

end Nrm

section Lft

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [hΓ : Γ.Normal]

/-- Left multiplication by `π ψ` on `A_Γ`. -/
def lftΓ (ψ : G) : AΓ (Λ := Λ) π Γ →ₗ[Λ] AΓ (Λ := Λ) π Γ :=
  Coinvariants.lift _ (Coinvariants.mk _ ∘ₗ LinearMap.mulLeft Λ (single (π ψ) (1 : Λ))) fun g =>
    LinearMap.ext fun a => by
      have hg : ψ * (g : G) * ψ⁻¹ ∈ Γ := hΓ.conj_mem _ g.2 ψ
      have h := Coinvariants.mk_self_apply ((regRep Λ π).comp Γ.subtype) ⟨_, hg⟩ (single (π ψ) (1 : Λ) * a)
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [← h]
      congr 1
      show single (π ψ) (1 : Λ) * (single (π g) 1 * a) = single (π (ψ * g * ψ⁻¹)) 1 * (single (π ψ) 1 * a)
      simp only [← mul_assoc, single_mul_single, one_mul, map_mul, map_inv, inv_mul_cancel_right]

theorem lftΓ_mk (ψ : G) (a : MonoidAlgebra Λ Gf) :
    lftΓ π Γ ψ (Coinvariants.mk _ a) = Coinvariants.mk _ (single (π ψ) (1 : Λ) * a) := rfl

end Lft

section Frob

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (hπ : IsOpen (π.ker : Set G)) (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

namespace ResHyp

variable (H : ResHyp Λ π Γ I) (c : Λ)

omit [Fintype Gf] in
/-- `N_s · π(ψ h_s) · a = π(ψ) · N_{t s} · a` for `a` invariant under `π(Γ ⊓ I (t s))`. -/
theorem Ns_mul_frob (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
    (s : S) (a : MonoidAlgebra Λ Gf) (ha : ∀ d ∈ (Γ ⊓ I (t s)).map π, single d (1 : Λ) * a = a) :
    H.Ns s * (single (π (ψ * h s)) (1 : Λ) * a) = single (π ψ) (1 : Λ) * (H.Ns (t s) * a) := by
  obtain ⟨u, rfl⟩ := exists_eq_nrmS_mul_of_inv _ a ha
  have e1 : single (π ψ * π (h s)) (1 : Λ) = single (π ψ) 1 * single (π (h s)) 1 := by
    rw [single_mul_single, one_mul]
  calc H.Ns s * (single (π (ψ * h s)) (1 : Λ) * (nrmS Λ ((Γ ⊓ I (t s)).map π) * u))
      = H.Ns s * (single (π (ψ * h s)) (1 : Λ) * nrmS Λ ((Γ ⊓ I (t s)).map π)) * u := by
        simp only [mul_assoc]
    _ = H.Ns s * nrmS Λ ((Γ ⊓ I s).map π) * single (π (ψ * h s)) (1 : Λ) * u := by
        rw [single_mul_nrmS _ _ _ (hD s), ← mul_assoc]
    _ = nrmS Λ (Γ.map π) * single (π ψ) 1 * single (π (h s)) 1 * u := by
        rw [H.hNs s, map_mul, e1, ← mul_assoc]
    _ = single (π ψ) 1 * (nrmS Λ (Γ.map π) * single (π (h s)) 1) * u := by
        rw [← single_mul_nrmS (Γ.map π) (Γ.map π) (π ψ) (map_conj_mem π Γ ψ), mul_assoc (single _ _)]
    _ = single (π ψ) (1 : Λ) * (H.Ns (t s) * (nrmS Λ ((Γ ⊓ I (t s)).map π) * u)) := by
        rw [nrmS_mul_single (Γ.map π) _ (Subgroup.mem_map_of_mem π (h s).2), ← mul_assoc (H.Ns (t s)),
          H.hNs (t s), mul_assoc]

omit [Fintype Gf] in
/-- **Frobenius and the residue**: `R(F e) = c • π(ψ) · R(e)`. -/
theorem resL_frob2 (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
    (ht : Function.Bijective t)
    (hTW : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I (t s))),
      (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (H.sg s)) =
        c • (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (H.sg (t s)))
    (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    H.resL (frob2 (regRep Λ π) Γ I ψ t h hI e) = c • (single (π ψ) (1 : Λ) * H.resL e) := by
  rw [resL_apply, resL_apply, Finset.mul_sum, Finset.smul_sum,
    ← Equiv.sum_comp (Equiv.ofBijective t ht)
      (fun s => c • (single (π ψ) (1 : Λ) * (H.Ns s * (e s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf) (H.sg s))))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [frob2_apply, regRep_apply, hTW s (e (t s)), mul_smul_comm, mul_smul_comm,
    H.Ns_mul_frob ψ t h hD s _ (fun d hd => H.inv_sg (t s) (e (t s)) d hd), Equiv.ofBijective_apply]

/-- **`cokResEquiv` carries the cone Frobenius to `c • lftΓ ψ`.** -/
theorem cokResEquiv_frob
    (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
    (ht : Function.Bijective t)
    (hTW : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I (t s))),
      (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (H.sg s)) =
        c • (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (H.sg (t s)))
    (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :
    H.cokResEquiv hπ (Submodule.Quotient.mk (frob2 (regRep Λ π) Γ I ψ t h hI e)) =
      c • lftΓ π Γ ψ (H.cokResEquiv hπ (Submodule.Quotient.mk e)) := by
  obtain ⟨a, ha⟩ := Coinvariants.mk_surjective _ (H.cokResEquiv hπ (Submodule.Quotient.mk e))
  have he : H.resL e = nrmS Λ (Γ.map π) * a := by
    have h1 : (Submodule.Quotient.mk e : ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸
        LinearMap.range (d1I Λ π Γ I hπ).toLinearMap) = H.Psi hπ (Coinvariants.mk _ a) := by
      rw [ha, ← cokResEquiv_symm_apply, LinearEquiv.symm_apply_apply]
    rw [← H.resQ_mk hπ, h1, Psi_mk, resQ_psiL]
  rw [← ha, lftΓ_mk]
  apply (H.cokResEquiv hπ).symm.injective
  rw [LinearEquiv.symm_apply_apply, map_smul, cokResEquiv_symm_apply, Psi_mk]
  apply H.resQ_injective hπ
  rw [resQ_mk, map_smul, resQ_psiL, H.resL_frob2 ψ t h hI c hD ht hTW, he, ← mul_assoc, ← mul_assoc,
    single_mul_nrmS (Γ.map π) (Γ.map π) (π ψ) (map_conj_mem π Γ ψ)]

end ResHyp

end Frob

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_Cone_H2 =====
section

/-!
# S4-PD (4): the cone's `H²` is `H²_c = M_Γ`, with Frobenius

From a `ResHyp` (E4S): `h2Equiv : H²(K(M)) ≃ M_Γ` (`topEquiv`, then `coinvRes` = `(cokResEquiv ⊗ 1)_{Gf}`, then
`coinvG`), and `h2Equiv_frob`: it carries the cone Frobenius `frobH2K` to `frobH2c ψ c` (`c • ρ(ψ)` on `M_Γ`) under
the twist hypothesis `hTW` of `cokResEquiv_frob`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh MonoidAlgebra Representation TensorProduct

section H2

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] [Fintype Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (hπ : IsOpen (π.ker : Set G)) {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

namespace ResHyp

variable (H : ResHyp Λ π Γ I)

/-- `cokResEquiv` as an intertwining map. -/
def resI : IntertwiningMap (cokRep (d1I Λ π Γ I hπ)) (rRepΓ π Γ) :=
  ⟨(H.cokResEquiv hπ).toLinearMap, fun g => LinearMap.ext fun y => H.cokResEquiv_equiv hπ g y⟩

/-- Its inverse as an intertwining map. -/
def resIinv : IntertwiningMap (rRepΓ π Γ) (cokRep (d1I Λ π Γ I hπ)) :=
  ⟨(H.cokResEquiv hπ).symm.toLinearMap, fun g => LinearMap.ext fun y => by
    apply (H.cokResEquiv hπ).injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [H.cokResEquiv_equiv hπ g, LinearEquiv.apply_symm_apply]⟩

/-- `(C ⊗ M)_{Gf} ≃ (A_Γ ⊗ M)_{Gf}`. -/
def coinvRes : Coinvariants ((cokRep (d1I Λ π Γ I hπ)).tprod τ) ≃ₗ[Λ] Coinvariants ((rRepΓ π Γ).tprod τ) :=
  LinearEquiv.ofLinearMap (Coinvariants.map _ _ ((H.resI hπ).rTensor τ))
    (Coinvariants.map _ _ ((H.resIinv hπ).rTensor τ))
    (Coinvariants.hom_ext (TensorProduct.ext' fun y m => by
      show Coinvariants.mk _ ((H.cokResEquiv hπ) ((H.cokResEquiv hπ).symm y) ⊗ₜ m) = Coinvariants.mk _ (y ⊗ₜ m)
      rw [LinearEquiv.apply_symm_apply]))
    (Coinvariants.hom_ext (TensorProduct.ext' fun y m => by
      show Coinvariants.mk _ ((H.cokResEquiv hπ).symm ((H.cokResEquiv hπ) y) ⊗ₜ m) = Coinvariants.mk _ (y ⊗ₜ m)
      rw [LinearEquiv.symm_apply_apply]))

theorem coinvRes_mk (y : ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⧸ LinearMap.range (d1I Λ π Γ I hπ).toLinearMap)
    (m : M) : H.coinvRes hπ τ (Coinvariants.mk _ (y ⊗ₜ m)) = Coinvariants.mk _ (H.cokResEquiv hπ y ⊗ₜ m) := rfl

variable [Finite Λ] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

include hall in
/-- **The cone's `H²` is `H²_c = M_Γ`** (S4-PD item (4)). -/
def h2Equiv : H2K (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) ≃ₗ[Λ] H2c (τ.comp π) Γ :=
  topEquiv π Γ I hπ τ hΛ hall hallI ≪≫ₗ H.coinvRes hπ τ ≪≫ₗ coinvG π Γ τ

include hall in
theorem h2Equiv_mk (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) :
    H.h2Equiv hπ τ hΛ hall hallI
        (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m)))) =
      coinvG π Γ τ (Coinvariants.mk _ (H.cokResEquiv hπ (Submodule.Quotient.mk e) ⊗ₜ m)) := by
  simp only [h2Equiv, LinearEquiv.trans_apply, topEquiv_mk]
  rfl

include hall in
/-- **Frobenius on the cone's `H²` is `c • ρ(ψ)` on `M_Γ`** (for the geometric Frobenius `c = q`: `M_Γ(-1)`). -/
theorem h2Equiv_frob (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h) (c : Λ)
    (hD : ∀ s d, d ∈ (Γ ⊓ I (t s)).map π ↔ π (ψ * h s) * d * (π (ψ * h s))⁻¹ ∈ (Γ ⊓ I s).map π)
    (ht : Function.Bijective t)
    (hTW : ∀ s (e : Z1 (regRep Λ π) (Γ ⊓ I (t s))),
      (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (conjSub (ψ * h s) (bdry_mem Γ I ψ t h hI s) (H.sg s)) =
        c • (e : ↥(Γ ⊓ I (t s)) → MonoidAlgebra Λ Gf) (H.sg (t s)))
    (x : H2K (τ.comp π) Γ I (isOpen_comp_ker π τ hπ)) :
    H.h2Equiv hπ τ hΛ hall hallI (frobH2K (τ.comp π) Γ I ψ t h (isOpen_comp_ker π τ hπ) hI x) =
      frobH2c (τ.comp π) Γ ψ c (H.h2Equiv hπ τ hΛ hall hallI x) := by
  have key : ∀ (e : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M),
      H.h2Equiv hπ τ hΛ hall hallI (frobH2K (τ.comp π) Γ I ψ t h (isOpen_comp_ker π τ hπ) hI
        (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m))))) =
      frobH2c (τ.comp π) Γ ψ c (H.h2Equiv hπ τ hΛ hall hallI
        (Submodule.Quotient.mk (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (e ⊗ₜ m))))) := by
    intro e m
    rw [frobH2K_mk, ← iso2_frob_mk (π := π) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hI := hI) (p := e) (m := m),
      H.h2Equiv_mk, H.h2Equiv_mk, H.cokResEquiv_frob hπ ψ t h hI c hD ht hTW e]
    obtain ⟨a, ha⟩ := Coinvariants.mk_surjective _ (H.cokResEquiv hπ (Submodule.Quotient.mk e))
    rw [← ha, lftΓ_mk, ← TensorProduct.smul_tmul', map_smul, map_smul, coinvG_mk, coinvG_mk, frobH2c_mk,
      map_mul τ.asAlgebraHom, Module.End.mul_apply, asAlgebraHom_single_one]
    rfl
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z, rfl⟩ := (iso2 π Γ I hπ τ hΛ hallI).surjective y
  induction z using Coinvariants.induction_on with
  | h w =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero, Submodule.Quotient.mk_zero]
    | tmul e m => exact key e m
    | add w w' hw hw' =>
      simp only [map_add, Submodule.Quotient.mk_add] at hw hw' ⊢
      rw [hw, hw']

end ResHyp

end H2

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_CupDuality_GysC =====
section

/-!
# S4-CurveDuality O4G-3: coinducing a unipotent character

Route G (session 44). Let `Γ ⊴ G` and `d : Γ → k` additive, zero on `Γ ∩ N` for an open normal `N` of finite index.
Coinduce the unipotent representation `v ↦ (v.1 + d g * v.2, v.2)` of `Γ` along `Γ → G ⧸ N` (Mathlib's
`Representation.coind`) and pull it back to `G`. In the coordinates `f ↦ (f(r_i))_i` at representatives `r_i` of
`(G ⧸ N) ⧸ Γ̄` this is a representation on `(ι → k) × (ι → k)` with open kernel on which `Γ` acts unipotently through
the conjugates `g ↦ d(r_i g r_i⁻¹)` (`exists_coind`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

section Uni

variable {k : Type} [CommRing k] {G : Type} [Group G] {Γ : Subgroup G}

theorem d_one {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) : d 1 = 0 := by
  have := hd 1 1
  rw [mul_one] at this
  linear_combination -this

theorem d_inv {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) (a : Γ) : d a⁻¹ = -d a := by
  have := hd a⁻¹ a
  rw [inv_mul_cancel, d_one hd] at this
  linear_combination -this

/-- The unipotent representation `v ↦ (v.1 + d g * v.2, v.2)` of `Γ` attached to an additive `d`. -/
def uni2 (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) : Representation k Γ (k × k) where
  toFun g :=
    { toFun := fun v => (v.1 + d g * v.2, v.2)
      map_add' := fun v w => by
        refine Prod.ext ?_ rfl
        simp only [Prod.fst_add, Prod.snd_add]
        ring
      map_smul' := fun c v => by
        refine Prod.ext ?_ rfl
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
        ring }
  map_one' := LinearMap.ext fun v => by
    refine Prod.ext ?_ rfl
    simp [d_one hd]
  map_mul' g h := LinearMap.ext fun v => by
    refine Prod.ext ?_ rfl
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, hd]
    ring

theorem uni2_apply (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) (g : Γ) (v : k × k) :
    uni2 d hd g v = (v.1 + d g * v.2, v.2) := rfl

theorem uni2_congr {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) {g h : Γ} (e : d g = d h) :
    uni2 d hd g = uni2 d hd h :=
  LinearMap.ext fun v => by rw [uni2_apply, uni2_apply, e]

end Uni

section Coind

variable {k : Type} [CommRing k] {G : Type} [Group G] (Γ N : Subgroup G) [N.Normal]

/-- `Γ → G ⧸ N`. -/
abbrev phiN : Γ →* G ⧸ N := (QuotientGroup.mk' N).comp Γ.subtype

/-- The index set: `(G ⧸ N) ⧸ Γ̄`. -/
abbrev Cos : Type := (G ⧸ N) ⧸ Γ.map (QuotientGroup.mk' N)

/-- A representative in `G` of a coset `i`. -/
def repG (i : Cos Γ N) : G := Quotient.out (Quotient.out i : G ⧸ N)

theorem repG_spec (i : Cos Γ N) :
    (QuotientGroup.mk (QuotientGroup.mk (repG Γ N i) : G ⧸ N) : Cos Γ N) = i := by
  unfold repG
  rw [QuotientGroup.out_eq', QuotientGroup.out_eq']

theorem phi_mem (γ : Γ) : phiN Γ N γ ∈ Γ.map (QuotientGroup.mk' N) := Subgroup.mem_map_of_mem _ γ.2

variable {Γ N} in
theorem d_eq_of_phi {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) {a b : Γ} (h : phiN Γ N a = phiN Γ N b) : d a = d b := by
  have h' : (QuotientGroup.mk (a : G) : G ⧸ N) = QuotientGroup.mk (b : G) := h
  have hm : ((a⁻¹ * b : Γ) : G) ∈ N := QuotientGroup.eq.1 h'
  have h0 := hdN _ hm
  rw [hd, d_inv hd] at h0
  linear_combination -h0

theorem exists_gam [hΓ : Γ.Normal] (x : G ⧸ N) :
    ∃ γ : Γ, phiN Γ N γ * (QuotientGroup.mk (repG Γ N (QuotientGroup.mk x)) : G ⧸ N) = x := by
  have hn : (Γ.map (QuotientGroup.mk' N)).Normal := hΓ.map _ (QuotientGroup.mk'_surjective N)
  have h := repG_spec Γ N (QuotientGroup.mk x)
  have h2 := hn.mem_comm (QuotientGroup.eq.1 h)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h2
  refine ⟨⟨y, hy⟩, ?_⟩
  rw [show phiN Γ N ⟨y, hy⟩ = _ from hyx, inv_mul_cancel_right]

/-- The `Γ`-part of `x = γ̄ · r_{[x]}`. -/
def gam [Γ.Normal] (x : G ⧸ N) : Γ := Classical.choose (exists_gam Γ N x)

theorem gam_spec [Γ.Normal] (x : G ⧸ N) :
    phiN Γ N (gam Γ N x) * (QuotientGroup.mk (repG Γ N (QuotientGroup.mk x)) : G ⧸ N) = x :=
  Classical.choose_spec (exists_gam Γ N x)

/-- The coinduced function with prescribed values `v` at the representatives. -/
def extF [Γ.Normal] (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b)
    (v : (Cos Γ N → k) × (Cos Γ N → k)) (x : G ⧸ N) : k × k :=
  uni2 d hd (gam Γ N x) (v.1 (QuotientGroup.mk x), v.2 (QuotientGroup.mk x))

theorem extF_mem [hΓ : Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (v : (Cos Γ N → k) × (Cos Γ N → k)) :
    extF Γ N d hd v ∈ Representation.coindV (phiN Γ N) (uni2 d hd) := by
  have hn : (Γ.map (QuotientGroup.mk' N)).Normal := hΓ.map _ (QuotientGroup.mk'_surjective N)
  rw [Representation.mem_coindV]
  intro γ0 x
  have hc : (QuotientGroup.mk (phiN Γ N γ0 * x) : Cos Γ N) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    have := hn.conj_mem _ (inv_mem (phi_mem Γ N γ0)) x⁻¹
    convert this using 1
    group
  have hy := gam_spec Γ N (phiN Γ N γ0 * x)
  have hx := gam_spec Γ N x
  rw [hc] at hy
  have hφ : phiN Γ N (gam Γ N (phiN Γ N γ0 * x)) = phiN Γ N (γ0 * gam Γ N x) := by
    apply mul_right_cancel (b := (QuotientGroup.mk (repG Γ N (QuotientGroup.mk x)) : G ⧸ N))
    rw [hy, map_mul, mul_assoc, hx]
  simp only [extF]
  rw [hc, uni2_congr hd (d_eq_of_phi hd hdN hφ), map_mul, Module.End.mul_apply]

theorem extF_rep [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (v : (Cos Γ N → k) × (Cos Γ N → k)) (i : Cos Γ N) :
    extF Γ N d hd v (QuotientGroup.mk (repG Γ N i)) = (v.1 i, v.2 i) := by
  have hi := repG_spec Γ N i
  have hy := gam_spec Γ N (QuotientGroup.mk (repG Γ N i))
  rw [hi] at hy
  have h1 : phiN Γ N (gam Γ N (QuotientGroup.mk (repG Γ N i))) = phiN Γ N 1 := by
    rw [map_one]
    exact mul_right_cancel (hy.trans (one_mul _).symm)
  simp only [extF]
  rw [hi, uni2_congr hd (d_eq_of_phi hd hdN h1), map_one]
  rfl

/-- Evaluation at the representatives. -/
def evalW [Γ.Normal] (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) :
    Representation.coindV (phiN Γ N) (uni2 d hd) →ₗ[k] (Cos Γ N → k) × (Cos Γ N → k) where
  toFun f := (fun i => ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).1,
    fun i => ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalW_inj [Γ.Normal] (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) :
    Function.Injective (evalW Γ N d hd) := by
  intro f g hfg
  have hr : ∀ i, (f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i)) =
      (g : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i)) := fun i =>
    Prod.ext (congrFun (congrArg Prod.fst hfg) i) (congrFun (congrArg Prod.snd hfg) i)
  apply Subtype.ext
  funext x
  have hx := gam_spec Γ N x
  rw [← hx, (Representation.mem_coindV _ _ _).1 f.2, (Representation.mem_coindV _ _ _).1 g.2, hr]

theorem evalW_surj [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) : Function.Surjective (evalW Γ N d hd) := by
  intro v
  refine ⟨⟨extF Γ N d hd v, extF_mem Γ N hd hdN v⟩, ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrArg Prod.fst (extF_rep Γ N hd hdN v i)
  · exact congrArg Prod.snd (extF_rep Γ N hd hdN v i)

/-- The coordinate equivalence. -/
def eW [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) :
    Representation.coindV (phiN Γ N) (uni2 d hd) ≃ₗ[k] (Cos Γ N → k) × (Cos Γ N → k) :=
  LinearEquiv.ofBijective (evalW Γ N d hd) ⟨evalW_inj Γ N d hd, evalW_surj Γ N hd hdN⟩

theorem eW_fst [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (f : Representation.coindV (phiN Γ N) (uni2 d hd))
    (i : Cos Γ N) : (eW Γ N hd hdN f).1 i = ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).1 := rfl

theorem eW_snd [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (f : Representation.coindV (phiN Γ N) (uni2 d hd))
    (i : Cos Γ N) : (eW Γ N hd hdN f).2 i = ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))).2 := rfl

/-- The coinduced representation, pulled back to `G`. -/
def rhoW (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) :
    Representation k G (Representation.coindV (phiN Γ N) (uni2 d hd)) :=
  (Representation.coind (phiN Γ N) (uni2 d hd)).comp (QuotientGroup.mk' N)

theorem rhoW_apply (d : Γ → k) (hd : ∀ a b, d (a * b) = d a + d b) (g : G)
    (f : Representation.coindV (phiN Γ N) (uni2 d hd)) (x : G ⧸ N) :
    ((rhoW Γ N d hd g f : Representation.coindV (phiN Γ N) (uni2 d hd)) : G ⧸ N → k × k) x =
      (f : G ⧸ N → k × k) (x * QuotientGroup.mk g) := rfl

/-- The coinduced representation in coordinates. -/
def rhoV [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) : Representation k G ((Cos Γ N → k) × (Cos Γ N → k)) where
  toFun g := (eW Γ N hd hdN).toLinearMap ∘ₗ rhoW Γ N d hd g ∘ₗ (eW Γ N hd hdN).symm.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' g h := LinearMap.ext fun v => by simp

theorem rhoV_apply [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (g : G) (v : (Cos Γ N → k) × (Cos Γ N → k)) :
    rhoV Γ N hd hdN g v = eW Γ N hd hdN (rhoW Γ N d hd g ((eW Γ N hd hdN).symm v)) := rfl

theorem le_ker_rhoV [Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) : N ≤ (rhoV Γ N hd hdN).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  have h1 : rhoW Γ N d hd n = 1 := by
    have : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    simp only [rhoW, MonoidHom.comp_apply, this, map_one]
  refine LinearMap.ext fun v => ?_
  rw [rhoV_apply, h1, Module.End.one_apply, LinearEquiv.apply_symm_apply, Module.End.one_apply]

theorem rhoW_conj [hΓ : Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b) (g : Γ)
    (f : Representation.coindV (phiN Γ N) (uni2 d hd)) (i : Cos Γ N) :
    ((rhoW Γ N d hd g f : Representation.coindV (phiN Γ N) (uni2 d hd)) : G ⧸ N → k × k)
        (QuotientGroup.mk (repG Γ N i)) =
      uni2 d hd ⟨repG Γ N i * g * (repG Γ N i)⁻¹, hΓ.conj_mem _ g.2 _⟩
        ((f : G ⧸ N → k × k) (QuotientGroup.mk (repG Γ N i))) := by
  rw [rhoW_apply]
  have : (QuotientGroup.mk (repG Γ N i) : G ⧸ N) * QuotientGroup.mk (g : G) =
      phiN Γ N ⟨repG Γ N i * g * (repG Γ N i)⁻¹, hΓ.conj_mem _ g.2 _⟩ *
        QuotientGroup.mk (repG Γ N i) := by
    show _ = (QuotientGroup.mk (repG Γ N i * g * (repG Γ N i)⁻¹) : G ⧸ N) * _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, inv_mul_cancel_right]
  rw [this, (Representation.mem_coindV _ _ _).1 f.2]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isUniFam_rhoV [hΓ : Γ.Normal] {d : Γ → k} (hd : ∀ a b, d (a * b) = d a + d b)
    (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) [Fintype (Cos Γ N)] :
    IsUniFam (rhoV Γ N hd hdN) (fun i (g : Γ) => d ⟨repG Γ N i * g * (repG Γ N i)⁻¹, hΓ.conj_mem _ g.2 _⟩) := by
  intro g v
  obtain ⟨f, rfl⟩ := (eW Γ N hd hdN).surjective v
  rw [rhoV_apply, LinearEquiv.symm_apply_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrArg Prod.fst (rhoW_conj Γ N hd g f i)
  · have h := congrArg Prod.snd (rhoW_conj Γ N hd g f i)
    exact h

/-- **O4G-3.** Coinduction: a unipotent family with open kernel whose parameters are the conjugates of `d`. -/
theorem exists_coind [hΓ : Γ.Normal] (hN : IsOpen (N : Set G)) [Finite (G ⧸ N)] (d : Γ → k)
    (hd : ∀ a b, d (a * b) = d a + d b) (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (σs : ι → G) (ρ : Representation k G ((ι → k) × (ι → k))),
      IsOpen (ρ.ker : Set G) ∧
        IsUniFam ρ (fun i (g : Γ) => d ⟨σs i * g * (σs i)⁻¹, hΓ.conj_mem _ g.2 _⟩) := by
  have : Finite (Cos Γ N) := Finite.of_surjective _ QuotientGroup.mk_surjective
  let _ : Fintype (Cos Γ N) := Fintype.ofFinite _
  exact ⟨Cos Γ N, inferInstance, repG Γ N, rhoV Γ N hd hdN,
    Subgroup.isOpen_mono (le_ker_rhoV Γ N hd hdN) hN, isUniFam_rhoV Γ N hd hdN⟩

end Coind

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_CupDuality_GysE =====
section

/-!
# S4-CurveDuality O4G-5: the right kernel of `constPair` is stable under Frobenius conjugation

Route G (session 44). `InR H DD d`: `d` is a parabolic cocycle (a hom, `σ` trivial on `Γ`) in the right kernel of
`constPair`. If `⟨F x, F y⟩ = c ⟨x, y⟩` with `c` a unit (`F` = Frobenius of `φ⁻¹`), then `InR d` implies
`InR (d ∘ conjΓ φ)` (`inR_conj`): `F [d ∘ conjΓ φ] = σ(φ⁻¹)(1) · [d]`, so `c ⟨x, [d ∘ conjΓ φ]⟩ = 0`; parabolicity
uses a boundary compatibility of `φ`. Iterating gives `d ∘ conjΓ φ^j` (`inR_conj_pow`). Conjugation by `Γ · N`
(`N ∩ Γ ⊆ ker d`, `N` normal) does not change `d` (`d_conj_mul`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh

noncomputable section

/-- `σ(g)(1)` is a unit for a representation on the ring itself. -/
theorem isUnit_rep_one {k : Type} [CommRing k] {G : Type} [Group G] (σ : Representation k G k) (g : G) :
    IsUnit (σ g 1) := by
  refine IsUnit.of_mul_eq_one (σ g⁻¹ 1) ?_
  have h : σ g (σ g⁻¹ 1) = 1 := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one σ, Module.End.one_apply]
  calc σ g 1 * σ g⁻¹ 1 = σ g⁻¹ 1 • σ g 1 := by rw [smul_eq_mul, mul_comm]
    _ = σ g (σ g⁻¹ 1 • 1) := (map_smul _ _ _).symm
    _ = 1 := by rw [smul_eq_mul, mul_one, h]

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S]
  {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- `d` is a parabolic cocycle in the right kernel of `constPair`. -/
def InR (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ) (DD : ConstData σ Γ I t)
    (d : Γ → k) : Prop :=
  ∃ hd : d ∈ Z1 σ Γ, (∀ s (g : Γ), (g : G) ∈ I s → d g = 0) ∧
    ∀ z : H1c (Representation.trivial k G k) Γ I, constPair H DD z (H1.mk σ Γ ⟨d, hd⟩) = 0

theorem add_of_Z1 (htriv : ∀ (g : Γ) (x : k), σ g x = x) {d : Γ → k} (hd : d ∈ Z1 σ Γ) (a b : Γ) :
    d (a * b) = d a + d b := by
  rw [hd.2, htriv]

theorem conj_conj_inv (φ : G) (g : Γ) : conjΓ Γ φ (conjΓ Γ φ⁻¹ g) = g :=
  Subtype.ext (by simp only [conjΓ_val]; group)

/-- **O4G-5a.** Stability of the right kernel under `d ↦ d ∘ conjΓ φ`. -/
theorem inR_conj (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ) (DD : ConstData σ Γ I t)
    (htriv : ∀ (g : Γ) (x : k), σ g x = x) {φ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I φ⁻¹ τ h)
    {τ2 : S → S} {h2 : S → Γ} (hI2 : BdryCompat Γ I φ τ2 h2) {c : k} (hc : IsUnit c)
    (hF : ∀ x y, constPair H DD (frobH1c (Representation.trivial k G k) Γ I φ⁻¹ τ h hI x) (frobH1 σ Γ φ⁻¹ y) =
      c * constPair H DD x y) {d : Γ → k} (hR : InR H DD d) : InR H DD (fun g => d (conjΓ Γ φ g)) := by
  obtain ⟨hd, hpar, hker⟩ := hR
  have hadd := add_of_Z1 htriv hd
  have hd' : (fun g => d (conjΓ Γ φ g)) ∈ Z1 σ Γ :=
    ⟨hd.1.comp_continuous (continuous_conjΓ Γ φ), fun g g' => by
      simp only [conjΓ_mul, hadd, htriv]⟩
  refine ⟨hd', fun s g hg => ?_, fun z => ?_⟩
  · have hm := bdryCompat_mem Γ I hI2 s g hg
    have e : conjΓ Γ φ g = h2 s * ((h2 s)⁻¹ * conjΓ Γ φ g * h2 s) * (h2 s)⁻¹ := by group
    show d (conjΓ Γ φ g) = 0
    rw [e, hadd, hadd, hpar _ _ hm, d_inv hadd]
    ring
  · have key : frobH1 σ Γ φ⁻¹ (H1.mk σ Γ ⟨_, hd'⟩) = σ φ⁻¹ 1 • H1.mk σ Γ ⟨d, hd⟩ := by
      rw [← map_smul]
      refine congrArg (H1.mk σ Γ) (Subtype.ext (funext fun g => ?_))
      show σ φ⁻¹ (d (conjΓ Γ φ (conjΓ Γ φ⁻¹ g))) = σ φ⁻¹ 1 * d g
      rw [conj_conj_inv]
      calc σ φ⁻¹ (d g) = σ φ⁻¹ (d g • (1 : k)) := by rw [smul_eq_mul, mul_one]
        _ = d g • σ φ⁻¹ 1 := map_smul _ _ _
        _ = σ φ⁻¹ 1 * d g := by rw [smul_eq_mul, mul_comm]
    have h1 := hF z (H1.mk σ Γ ⟨_, hd'⟩)
    rw [key, map_smul, hker, smul_zero] at h1
    exact hc.mul_right_eq_zero.1 h1.symm

/-- **O4G-5b.** Iteration: `InR d → InR (d ∘ conjΓ φ^j)`. -/
theorem inR_conj_pow (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (DD : ConstData σ Γ I t) (htriv : ∀ (g : Γ) (x : k), σ g x = x) {φ : G} {τ : S → S} {h : S → Γ}
    (hI : BdryCompat Γ I φ⁻¹ τ h) {τ2 : S → S} {h2 : S → Γ} (hI2 : BdryCompat Γ I φ τ2 h2) {c : k}
    (hc : IsUnit c)
    (hF : ∀ x y, constPair H DD (frobH1c (Representation.trivial k G k) Γ I φ⁻¹ τ h hI x) (frobH1 σ Γ φ⁻¹ y) =
      c * constPair H DD x y) (j : ℕ) :
    ∀ {d : Γ → k}, InR H DD d → InR H DD (fun g => d (conjΓ Γ (φ ^ j) g)) := by
  induction j with
  | zero =>
    intro d hR
    have e : (fun g => d (conjΓ Γ (φ ^ 0) g)) = d := funext fun g => congrArg d (Subtype.ext (by simp))
    rw [e]
    exact hR
  | succ j ih =>
    intro d hR
    have e : (fun g => d (conjΓ Γ (φ ^ (j + 1)) g)) =
        fun g => (fun g' => d (conjΓ Γ φ g')) (conjΓ Γ (φ ^ j) g) :=
      funext fun g => congrArg d (Subtype.ext (by simp only [conjΓ_val, pow_succ]; group))
    rw [e]
    exact ih (inR_conj H DD htriv hI hI2 hc hF hR)

/-- **O4G-5c.** Conjugation by `γ n` (`γ ∈ Γ`, `n ∈ N`, `N ∩ Γ ⊆ ker d`) does not change `d`. -/
theorem d_conj_mul (htriv : ∀ (g : Γ) (x : k), σ g x = x) {d : Γ → k} (hd : d ∈ Z1 σ Γ) (N : Subgroup G)
    [hN : N.Normal] (hdN : ∀ g : Γ, (g : G) ∈ N → d g = 0) (ψ : G) {γ : G} (hγ : γ ∈ Γ) {n : G}
    (hn : n ∈ N) (g : Γ) : d (conjΓ Γ (ψ * γ * n) g) = d (conjΓ Γ ψ g) := by
  have hadd := add_of_Z1 htriv hd
  have hγ' : ((⟨γ, hγ⟩ : Γ) : G) = γ := rfl
  have h1 : d ((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩) = d (conjΓ Γ ψ g) := by
    rw [hadd, hadd, d_inv hadd]
    ring
  have hw : ((conjΓ Γ (ψ * γ * n) g * ((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩)⁻¹ : Γ) : G) ∈ N := by
    have e : ((conjΓ Γ (ψ * γ * n) g * ((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩)⁻¹ : Γ) : G) =
        n⁻¹ * ((((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩ : Γ) : G) * n *
          ((((⟨γ, hγ⟩ : Γ)⁻¹ * conjΓ Γ ψ g * ⟨γ, hγ⟩ : Γ) : G))⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjΓ_val]
      group
    rw [e]
    exact N.mul_mem (N.inv_mem hn) (hN.conj_mem n hn _)
  have h2 := hdN _ hw
  rw [hadd, d_inv hadd] at h2
  linear_combination h2 + h1

end Gen

end

end CupDuality
end RamanujanPetersson

end


