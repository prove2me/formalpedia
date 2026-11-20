-- Prove2me | Definitions.Def_RPLib_F2_022
-- name    : RPLib_F2_022
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T10:32:40.873693+00:00
-- url     : https://prove2.me/theorems/f4b84d4e-599d-4c3a-981d-36bfe8f78dd3
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 022 of 70
-- statement:
--   File 022 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PerfectCx_TensorIso`: S4-PD (5), E2(c) part 2: `(E ⊗ M)_{Gf} ≃ Z¹(Γ; M)`
--   * `S4.Def_RP_PerfectCx_Cx`: S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model
--   * `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
--   * `S4.Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
--   * `S4.Def_RP_PerfectCx_CxH`: S4-PD (5), E3: the cohomology of the cone complex
--   * `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
--   * `S4.Def_RP_Cone_E4SFree`: S4-PD E4S, part 1: a finite subgroup acting on `Λ[Gf]` by left multiplication
--   * `S4.Def_RP_Cone_E4SRes`: S4-PD E4S, part 2: the residue map on the top term of the cone
--   * `S4.Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
--   * `S4.Def_RP_PerfectCx_Top`: S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact
--   * `S4.Def_RP_Cone_E4SEq`: S4-PD E4S, part 3: the top term of the cone is `A_Γ`
--   * `S4.Def_RP_Cone_E4SFrob`: S4-PD E4frob (generic): the Frobenius on the top term of the cone
--   * `S4.Def_RP_TameInertia_Unr`: Tame inertia, part Unr: the unit-derivative criterion (S4-PD item (2), T5)
--   * `S4.Def_RP_TameInertia_Newton`: Tame inertia, part Newton: the Abhyankar trinomial has exactly one small root (S4-PD item (2), T6)
--   * `S4.Def_RP_TameInertia_LL`: Tame inertia, part LL: inertia fixes constants and the local Kummer lemma (S4-PD item (2), T0 + T1)
--   * `S4.Def_RP_TameInertia_Up`: Tame inertia, part Up: the upper bound `#Hom(I, ℤ/N) ≤ N` (S4-PD item (2), T2 + T3)
--   * `S4.Def_RP_TameInertia_Fix`: Tame inertia, part Fix: the Abhyankar polynomial and the inertia-fixed small root (S4-PD item (2), T5 applied + T7)
--   * `S4.Def_RP_Swan_GlobV`: S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group
--   * `S4.Def_RP_Swan_GlobE`: S4-Swan (K2), part 14: ramification index = order of the inertia group, for adic valuations
--   * `S4.Def_RP_Swan_GlobF`: S4-Swan (K2), part 15: fixed rings of Dedekind domains, and fixed fractions
--   * `S4.Def_RP_Swan_GlobVal`: S4-Swan (K2), part 16: the valuation condition for subgroups of an inertia group
--   * `S4.Def_RP_TameInertia_Count`: Tame inertia, part Count: the inertia orbit of an `N`-th root of the small root is full (S4-PD item (2), T8 count)
--   * `S4.Def_RP_TameInertia_Pole`: Tame inertia, part Pole: a pole element of order `≡ 1 mod N` (S4-PD item (2), T4)
--   * `S4.Def_RP_TameInertia_Lift`: Tame inertia, part Lift: inertia at a GIVEN prime of the pro-chart surjects onto finite-level inertia (S4-PD (2), T8 lift)
--   * `S4.Def_RP_TameInertia_Stab`: Tame inertia, part Stab: the decomposition group fixes the small root (S4-PD item (2), T10a)
--   * `S4.Def_RP_TameInertia_Main`: Tame inertia, part Main: `Hom(I_x, ℤ/N) = ℤ/N(-1)` (S4-PD item (2))
--   * `S4.Def_RP_Cone_KumAll`: S4-PD (4)/(5), E1 part K: the Kummer-closure property over every `E₀' ⊇ constFieldU`
--   * `S4.Def_RP_Cone_CdSub`: S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)
--   * `S4.Def_RP_TameInertia_Coef`: Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_021

/-!
# Ramanujan-Petersson curve library (flat edition), file 022 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PerfectCx_TensorIso`: S4-PD (5), E2(c) part 2: `(E ⊗ M)_{Gf} ≃ Z¹(Γ; M)`
* `S4.Def_RP_PerfectCx_Cx`: S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model
* `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
* `S4.Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
* `S4.Def_RP_PerfectCx_CxH`: S4-PD (5), E3: the cohomology of the cone complex
* `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
* `S4.Def_RP_Cone_E4SFree`: S4-PD E4S, part 1: a finite subgroup acting on `Λ[Gf]` by left multiplication
* `S4.Def_RP_Cone_E4SRes`: S4-PD E4S, part 2: the residue map on the top term of the cone
* `S4.Def_RP_PerfectCx_CoinvG`: S4-PD (4), E4 part 2: `(Λ[Gf]_Γ ⊗ M)_{Gf} ≃ M_Γ`
* `S4.Def_RP_PerfectCx_Top`: S4-PD (4), E4 part 1: the top degree of the perfect complex is right exact
* `S4.Def_RP_Cone_E4SEq`: S4-PD E4S, part 3: the top term of the cone is `A_Γ`
* `S4.Def_RP_Cone_E4SFrob`: S4-PD E4frob (generic): the Frobenius on the top term of the cone
* `S4.Def_RP_TameInertia_Unr`: Tame inertia, part Unr: the unit-derivative criterion (S4-PD item (2), T5)
* `S4.Def_RP_TameInertia_Newton`: Tame inertia, part Newton: the Abhyankar trinomial has exactly one small root (S4-PD item (2), T6)
* `S4.Def_RP_TameInertia_LL`: Tame inertia, part LL: inertia fixes constants and the local Kummer lemma (S4-PD item (2), T0 + T1)
* `S4.Def_RP_TameInertia_Up`: Tame inertia, part Up: the upper bound `#Hom(I, ℤ/N) ≤ N` (S4-PD item (2), T2 + T3)
* `S4.Def_RP_TameInertia_Fix`: Tame inertia, part Fix: the Abhyankar polynomial and the inertia-fixed small root (S4-PD item (2), T5 applied + T7)
* `S4.Def_RP_Swan_GlobV`: S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group
* `S4.Def_RP_Swan_GlobE`: S4-Swan (K2), part 14: ramification index = order of the inertia group, for adic valuations
* `S4.Def_RP_Swan_GlobF`: S4-Swan (K2), part 15: fixed rings of Dedekind domains, and fixed fractions
* `S4.Def_RP_Swan_GlobVal`: S4-Swan (K2), part 16: the valuation condition for subgroups of an inertia group
* `S4.Def_RP_TameInertia_Count`: Tame inertia, part Count: the inertia orbit of an `N`-th root of the small root is full (S4-PD item (2), T8 count)
* `S4.Def_RP_TameInertia_Pole`: Tame inertia, part Pole: a pole element of order `≡ 1 mod N` (S4-PD item (2), T4)
* `S4.Def_RP_TameInertia_Lift`: Tame inertia, part Lift: inertia at a GIVEN prime of the pro-chart surjects onto finite-level inertia (S4-PD (2), T8 lift)
* `S4.Def_RP_TameInertia_Stab`: Tame inertia, part Stab: the decomposition group fixes the small root (S4-PD item (2), T10a)
* `S4.Def_RP_TameInertia_Main`: Tame inertia, part Main: `Hom(I_x, ℤ/N) = ℤ/N(-1)` (S4-PD item (2))
* `S4.Def_RP_Cone_KumAll`: S4-PD (4)/(5), E1 part K: the Kummer-closure property over every `E₀' ⊇ constFieldU`
* `S4.Def_RP_Cone_CdSub`: S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)
* `S4.Def_RP_TameInertia_Coef`: Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PerfectCx_TensorIso =====
section

/-!
# S4-PD (5), E2(c) part 2: `(E ⊗ M)_{Gf} ≃ Z¹(Γ; M)`

Under `H2All` (exactness of `Z¹(Γ; -)` on finite `lᴺ`-torsion modules), the evaluation map `Phi` of part 1 is
bijective (`tensorEquiv`) and natural in `M` (`Phi_natural`).
* surjective: lift a cocycle along `qMap : (M → Λ[Gf]) → M`, `(a_m) ↦ Σ_m a_m · m`;
* injective: a family `(c_m)` killed by `Phi` assembles to a cocycle with values in `K = ker qMap`; it lifts along
  `combMap : (K → Λ[Gf]) → K`, `(d_k) ↦ Σ_k d_k k`, and balancedness (`mk_eMul_tmul`) kills `⟦Σ_m c_m ⊗ m⟧`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra TensorProduct

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

section Pi

variable (ι : Type)

end Pi

section QMap

variable {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

end QMap

section Comb

variable {ι ι' : Type} [Fintype ι]

end Comb

section Iso

variable {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

/-- **E2(c), injectivity** of `Phi`. -/
theorem Phi_injective [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G)) : Function.Injective (Phi π Γ τ) := by
  classical
  haveI := Fintype.ofFinite M
  have := finite_A Λ Gf
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
  obtain ⟨c, rfl⟩ := Theta_surjective π Γ x
  have hCK : ∀ g, (assemble π Γ M c : Γ → M → MonoidAlgebra Λ Gf) g ∈ (qKer π τ).toSubmodule := fun g => by
    rw [mem_qKer]
    have h1 : (Phi π Γ τ (Representation.Coinvariants.mk _ (Theta Λ π Γ M c)) : Γ → M) g = 0 := by
      rw [hu]
      rfl
    rw [Phi_mk_Theta] at h1
    have h2 : (assemble π Γ M c : Γ → M → MonoidAlgebra Λ Gf) g = fun m => (c m : Γ → MonoidAlgebra Λ Gf) g :=
      funext fun m => assemble_apply π Γ M c g m
    rw [h2]
    exact h1
  haveI : Fintype (qKer π τ).toSubmodule := Fintype.ofFinite _
  obtain ⟨D, hD⟩ := lift_of_values (piRep Λ π (qKer π τ).toSubmodule) (piRep Λ π M) Γ hall
    (nsmul_eq_zero_of_cast hΛ) (isOpen_piRep_ker π _ hπ)
    (combMap fun k : (qKer π τ).toSubmodule => (k : M → MonoidAlgebra Λ Gf))
    (combMap_equiv π fun k : (qKer π τ).toSubmodule => (k : M → MonoidAlgebra Λ Gf)) (qKer π τ)
    (fun d => (mem_qKer π τ _).2 (by
      rw [qMap_combMap]
      exact Finset.sum_eq_zero fun k _ => by rw [(mem_qKer π τ _).1 k.2, map_zero]))
    (fun w hw => ⟨Pi.single ⟨w, hw⟩ 1, combMap_single _ _⟩) (assemble π Γ M c) hCK
  have hc : ∀ m, c m = ∑ k : (qKer π τ).toSubmodule,
      eMul π Γ ((k : M → MonoidAlgebra Λ Gf) m) (projZ1 π Γ (qKer π τ).toSubmodule k D) :=
    fun m => Subtype.ext (funext fun g => by
      rw [← assemble_apply π Γ M c g m, ← hD g, combMap_apply, Submodule.coe_sum, Finset.sum_apply]
      rfl)
  rw [Theta_apply]
  simp_rw [hc, sum_tmul, map_sum, mk_eMul_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := mk_sum_tmul π Γ τ (projZ1 π Γ (qKer π τ).toSubmodule k D) (k : M → MonoidAlgebra Λ Gf)
  rw [(mem_qKer π τ _).1 k.2, tmul_zero, map_zero] at hk
  exact hk

/-- **E2(c) headline**: `(E ⊗_Λ M)_{Gf} ≃ Z¹(Γ; M)` for finite `M` (`E = Z¹(Γ; Λ[Gf])`), given `H² = 0` on `Γ`. -/
def tensorEquiv [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G)) :
    Representation.Coinvariants ((eRep (Λ := Λ) π Γ).tprod τ) ≃ₗ[Λ] Z1 (τ.comp π) Γ :=
  LinearEquiv.ofBijective (Phi π Γ τ) ⟨Phi_injective π Γ τ hΛ hall hπ, Phi_surjective π Γ τ hΛ hall hπ⟩

theorem tensorEquiv_apply [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G))
    (u : Representation.Coinvariants ((eRep (Λ := Λ) π Γ).tprod τ)) :
    tensorEquiv π Γ τ hΛ hall hπ u = Phi π Γ τ u := rfl

end Iso

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

/-- Restriction of cocycles along `Γ' ≤ Γ`. -/
def res {Γ' : Subgroup G} (h : Γ' ≤ Γ) : Z1 ρ Γ →ₗ[k] Z1 ρ Γ' where
  toFun c := ⟨fun g => (c : Γ → M) ⟨g.1, h g.2⟩, (mem_Z1 ρ Γ' _).2
    ⟨((mem_Z1 ρ Γ _).1 c.2).1.comp_continuous (continuous_subtype_val.subtype_mk _),
      fun g g' => ((mem_Z1 ρ Γ _).1 c.2).2 ⟨g.1, h g.2⟩ ⟨g'.1, h g'.2⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_apply {Γ' : Subgroup G} (h : Γ' ≤ Γ) (c : Z1 ρ Γ) (g : Γ') :
    (res ρ Γ h c : Γ' → M) g = (c : Γ → M) ⟨g.1, h g.2⟩ := rfl

variable (hρ : IsOpen (ρ.ker : Set G)) (hσ : IsOpen (σ.ker : Set G))

/-- `d¹ (c, b) = (c|_{Γ ⊓ I s} - d b_s)_s`. -/
def cx1 : Z1 ρ Γ × (S → M) →ₗ[k] ((s : S) → Z1 ρ (Γ ⊓ I s)) :=
  LinearMap.pi fun s => res ρ Γ inf_le_left ∘ₗ LinearMap.fst k _ _ -
    cob ρ hρ (Γ ⊓ I s) ∘ₗ LinearMap.proj s ∘ₗ LinearMap.snd k _ _

theorem cx1_apply (p : Z1 ρ Γ × (S → M)) (s : S) (g : ↥(Γ ⊓ I s)) :
    (cx1 ρ Γ I hρ p s : ↥(Γ ⊓ I s) → M) g = (p.1 : Γ → M) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ - (ρ g (p.2 s) - p.2 s) := rfl

theorem cx1_comp_cx0 : cx1 ρ Γ I hρ ∘ₗ cx0 ρ Γ S hρ = 0 :=
  LinearMap.ext fun _ => funext fun _ => Subtype.ext (funext fun _ => sub_self _)

variable (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m))

/-- The degree-1 term of `K` is functorial in the coefficients. -/
def K1map : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ × (S → N) :=
  (z1Map ρ σ Γ q hq).prodMap (LinearMap.piMap fun _ => q)

/-- The degree-2 term of `K` is functorial in the coefficients. -/
def K2map : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ ⊓ I s)) :=
  LinearMap.piMap fun s => z1Map ρ σ (Γ ⊓ I s) q hq

theorem cx1_natural : cx1 σ Γ I hσ ∘ₗ K1map ρ σ Γ q hq = K2map ρ σ Γ I q hq ∘ₗ cx1 ρ Γ I hρ :=
  LinearMap.ext fun p => funext fun s => Subtype.ext (funext fun g => by
    show q ((p.1 : Γ → M) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) - (σ g (q (p.2 s)) - q (p.2 s)) =
      q ((p.1 : Γ → M) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ - (ρ g (p.2 s) - p.2 s))
    rw [map_sub, map_sub, hq])

end Generic

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))

variable (Λ S) in
/-- `Gf` on `P¹ = E_Γ × A^S` (right multiplication by `h⁻¹`). -/
def rho1 : Representation Λ Gf (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :=
  (eRep π Γ).prod (repPi fun _ : S => rRep Λ Gf)

variable (Λ) in
/-- `Gf` on `P² = Π_s E_s`, `E_s = Z¹(Γ ⊓ I s; A)`. -/
def rho2 : Representation Λ Gf ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :=
  repPi fun s => eRep π (Γ ⊓ I s)

variable (Λ) in
/-- `d¹ : P¹ → P²`. -/
def d1 : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf) →ₗ[Λ] ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :=
  cx1 (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)

theorem d1_equiv : IsEquivariant (rho1 Λ π Γ S) (rho2 Λ π Γ I) (d1 Λ π Γ I hπ) := fun h =>
  (cx1_natural (regRep Λ π) (regRep Λ π) Γ I (isOpen_regRep_ker π hπ) (isOpen_regRep_ker π hπ)
    (LinearMap.mulRight Λ (single h⁻¹ 1)) (mulRight_regRep π _))

end Model

end

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

end Frob

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ)

end Model

section TriMap

variable {R : Type} [CommRing R] {G : Type} [Group G] {V0 V1 V2 : Type} [AddCommGroup V0] [AddCommGroup V1]
  [AddCommGroup V2] [Module R V0] [Module R V1] [Module R V2]

end TriMap

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_CxIso =====
section

/-!
# S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`

For a finite `Gf`-representation `τ` on `M` (pulled back to `G` along `π`), the coinvariants of the free model
`P = [A → E_Γ × A^S → Π_s E_s]` tensored with `M` are identified termwise with the cone complex
`K(M) = [M → Z¹(Γ; M) × M^S → Π_s Z¹(Γ ⊓ I s; M)]` (`coinvA`, `iso1`, `iso2`), and the identifications commute with
the differentials (`iso1_map_d0`, `iso2_map_d1`).
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

variable (Λ) in
/-- `d¹` as an intertwining map. -/
def d1I : IntertwiningMap (rho1 Λ π Γ S) (rho2 Λ π Γ I) := ⟨d1 Λ π Γ I hπ, d1_equiv π Γ I hπ⟩

theorem d1I_apply (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) : d1I Λ π Γ I hπ p = d1 Λ π Γ I hπ p := rfl

theorem d1I_val_apply (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (s : S) (g : ↥(Γ ⊓ I s)) :
    ((d1I Λ π Γ I hπ p s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf)) g =
      (p.1 : Γ → MonoidAlgebra Λ Gf) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ - (single (π g) 1 * p.2 s - p.2 s) := rfl

theorem cx0_fst_apply' {ρ : Representation Λ G M} (hρ : IsOpen (ρ.ker : Set G)) (m : M) (g : Γ) :
    ((cx0 ρ Γ S hρ m).1 : Γ → M) g = ρ g m - m := rfl

theorem cx0_snd_apply' {ρ : Representation Λ G M} (hρ : IsOpen (ρ.ker : Set G)) (m : M) (s : S) :
    (cx0 ρ Γ S hρ m).2 s = m := rfl

/-- `P¹` contains a submodule factor: fix the `AddCommGroup` of `P¹ ⊗ M`. -/
instance instAddCommGroupTensorP1 : AddCommGroup ((Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) ⊗[Λ] M) :=
  TensorProduct.addCommGroup

/-- `P²` is a product of submodules: fix the `AddCommGroup` of `P² ⊗ M`. -/
instance instAddCommGroupTensorP2 : AddCommGroup (((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⊗[Λ] M) :=
  TensorProduct.addCommGroup

variable [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

variable (S) in
/-- `(P¹ ⊗ M)_{Gf} ≃ Z¹(Γ; M) × M^S`. -/
def iso1 [Fintype S] [DecidableEq S] :
    Coinvariants ((rho1 Λ π Γ S).tprod τ) ≃ₗ[Λ] Z1 (τ.comp π) Γ × (S → M) :=
  coinvProd τ (eRep π Γ) (repPi fun _ : S => rRep Λ Gf) ≪≫ₗ
    (tensorEquiv π Γ τ hΛ hall hπ).prodCongr
      (coinvPi τ (fun _ : S => rRep Λ Gf) ≪≫ₗ LinearEquiv.piCongrRight fun _ => coinvA τ)

/-- `(P² ⊗ M)_{Gf} ≃ Π_s Z¹(Γ ⊓ I s; M)`. -/
def iso2 [Fintype S] [DecidableEq S] :
    Coinvariants ((rho2 Λ π Γ I).tprod τ) ≃ₗ[Λ] ((s : S) → Z1 (τ.comp π) (Γ ⊓ I s)) :=
  coinvPi τ (fun s => eRep (Λ := Λ) π (Γ ⊓ I s)) ≪≫ₗ
    LinearEquiv.piCongrRight fun s => tensorEquiv π (Γ ⊓ I s) τ hΛ (hallI s) hπ

variable (S) in
theorem iso1_mk_tmul [Fintype S] [DecidableEq S] (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (m : M) :
    iso1 π Γ S hπ τ hΛ hall (Coinvariants.mk _ (p ⊗ₜ m)) =
      (Phi π Γ τ (Coinvariants.mk _ (p.1 ⊗ₜ m)), fun s => τ.asAlgebraHom (p.2 s) m) := rfl

theorem iso2_mk_tmul [Fintype S] [DecidableEq S] (p : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) (s : S) :
    iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (p ⊗ₜ m)) s = Phi π (Γ ⊓ I s) τ (Coinvariants.mk _ (p s ⊗ₜ m)) := rfl

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

/-- `ker d¹ → Z1c`, `(c, b) ↦ (c, b)`. -/
def kerToZ1c : LinearMap.ker (cx1 ρ Γ I hρ) →ₗ[k] Z1c ρ Γ I where
  toFun p := ⟨((p.1.1 : Γ → M), p.1.2), (mem_Z1c ρ Γ I _).2 ⟨p.1.1.2, fun s g hg => by
    have h : ((cx1 ρ Γ I hρ p.1 s : ↥(Γ ⊓ I s) → M)) ⟨g.1, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩ = 0 := by
      rw [LinearMap.mem_ker.1 p.2]
      rfl
    rw [cx1_apply] at h
    exact sub_eq_zero.1 h⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `Z1c → ker d¹`, `(c, b) ↦ (c, b)`. -/
def z1cToKer : Z1c ρ Γ I →ₗ[k] LinearMap.ker (cx1 ρ Γ I hρ) where
  toFun p := ⟨(⟨p.1.1, ((mem_Z1c ρ Γ I _).1 p.2).1⟩, p.1.2), LinearMap.mem_ker.2 (funext fun s =>
    Subtype.ext (funext fun g => by
      rw [cx1_apply]
      exact sub_eq_zero.2 (((mem_Z1c ρ Γ I _).1 p.2).2 s ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩
        (Subgroup.mem_inf.1 g.2).2)))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `ker d¹ ≃ Z1c`. -/
def kerEquivZ1c : LinearMap.ker (cx1 ρ Γ I hρ) ≃ₗ[k] Z1c ρ Γ I :=
  LinearEquiv.ofLinearMap (kerToZ1c ρ Γ I hρ) (z1cToKer ρ Γ I hρ) (LinearMap.ext fun _ => rfl)
    (LinearMap.ext fun _ => rfl)

theorem kerEquivZ1c_apply (p : LinearMap.ker (cx1 ρ Γ I hρ)) :
    ((kerEquivZ1c ρ Γ I hρ p : Z1c ρ Γ I) : (Γ → M) × (S → M)) = ((p.1.1 : Γ → M), p.1.2) := rfl

/-- `im d⁰` corresponds to the relative coboundaries `B1c`. -/
theorem map_range_cx0 :
    ((LinearMap.range (cx0 ρ Γ S hρ)).comap (LinearMap.ker (cx1 ρ Γ I hρ)).subtype).map
      (kerEquivZ1c ρ Γ I hρ : LinearMap.ker (cx1 ρ Γ I hρ) →ₗ[k] Z1c ρ Γ I) =
      (B1c ρ Γ I).comap (Z1c ρ Γ I).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [Submodule.mem_comap, LinearMap.mem_range, Submodule.subtype_apply,
    LinearEquiv.coe_coe, mem_B1c]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨x.2, m, fun g => ?_, fun s => ?_⟩
    · exact (congrArg (fun p : Z1 ρ Γ × (S → M) => (p.1 : Γ → M) g) hm).symm
    · exact (congrArg (fun p : Z1 ρ Γ × (S → M) => p.2 s) hm).symm
  · rintro ⟨-, m, hm, hm'⟩
    exact ⟨m, Prod.ext (Subtype.ext (funext fun g => (hm g).symm)) (funext fun s => (hm' s).symm)⟩

theorem cx0_mem_ker (m : M) : cx0 ρ Γ S hρ m ∈ LinearMap.ker (cx1 ρ Γ I hρ) := by
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, cx1_comp_cx0, LinearMap.zero_apply]

/-- `d⁰` landing in `Z1c ≃ ker d¹`: `m ↦ (dm, (m)_s)`. -/
def cx0c : M →ₗ[k] Z1c ρ Γ I :=
  (kerEquivZ1c ρ Γ I hρ).toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.ker (cx1 ρ Γ I hρ)) (cx0 ρ Γ S hρ) (cx0_mem_ker ρ Γ I hρ)

theorem cx0c_apply (m : M) :
    ((cx0c ρ Γ I hρ m : Z1c ρ Γ I) : (Γ → M) × (S → M)) = (fun g : Γ => ρ g m - m, fun _ => m) := rfl

/-- **Exactness at `H¹`**: the image of `d⁰` in `Z1c ≃ ker d¹` is exactly `B1c`. -/
theorem range_cx0c : LinearMap.range (cx0c ρ Γ I hρ) = (B1c ρ Γ I).comap (Z1c ρ Γ I).subtype := by
  rw [cx0c, LinearMap.range_comp, LinearMap.range_codRestrict]
  exact map_range_cx0 ρ Γ I hρ

/-- **`H¹` of the cone complex is `H¹_c`**: `H¹(K(M)) = ker d¹ / im d⁰ ≃ Z1c / im d⁰ ≃ H1c ρ Γ I`. -/
def h1Equiv : (Z1c ρ Γ I ⧸ LinearMap.range (cx0c ρ Γ I hρ)) ≃ₗ[k] H1c ρ Γ I :=
  Submodule.quotEquivOfEq _ _ (range_cx0c ρ Γ I hρ)

theorem h1Equiv_mk (p : Z1c ρ Γ I) :
    h1Equiv ρ Γ I hρ (Submodule.Quotient.mk p) = H1c.mk ρ Γ I p := rfl

/-- `H²(K(M)) = coker d¹`. -/
abbrev H2K : Type := ((s : S) → Z1 ρ (Γ ⊓ I s)) ⧸ LinearMap.range (cx1 ρ Γ I hρ)

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

/-- The Frobenius on `H²(K) = coker d¹`. -/
def frobH2K (hI : BdryCompat Γ I ψ t h) : H2K ρ Γ I hρ →ₗ[k] H2K ρ Γ I hρ :=
  Submodule.mapQ _ _ (frob2 ρ Γ I ψ t h hI) fun x hx => by
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
    exact Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨frob1 ρ Γ ψ t h p,
      LinearMap.congr_fun (cx1_frob (ρ := ρ) (Γ := Γ) (I := I) (ψ := ψ) (t := t) (h := h) (hρ := hρ) (hI := hI)) p⟩)

end H

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

variable [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M)
  {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)
  (hπ : IsOpen (π.ker : Set G))

theorem iso2_frob_mk [Fintype S] [DecidableEq S] (p : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) :
    iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (frob2 (regRep Λ π) Γ I ψ t h hI p ⊗ₜ m)) =
      frob2 (τ.comp π) Γ I ψ t h hI (iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (p ⊗ₜ m))) := by
  refine funext fun s => Subtype.ext (funext fun g => ?_)
  simp only [iso2_mk_tmul, Phi_mk_tmul, frob2_apply, regRep_apply, act_single_mul, MonoidHom.comp_apply]

end Model

end

end PerfectCx
end RamanujanPetersson


end

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

end RExact

section Top

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G)) {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)
  [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

end Top

end

end PerfectCx
end RamanujanPetersson


end

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

-- ===== S4.Def_RP_TameInertia_Unr =====
section

/-!
# Tame inertia, part Unr: the unit-derivative criterion (S4-PD item (2), T5)

If `G ∈ A[X]` is monic and every root `y ∈ K̄` of `G` satisfies `y · G'(y) = u` for one unit `u` of `A`, then
the field generated over `K` by the roots of `G` is unramified over `A` (`udField_mem_unramSet`), so every root
lies in `K_U` (`mem_maxUnram_of_ud`). Proof: two distinct roots `a ≠ b` of `G` in the integral closure `S`
give `G = (X - a)(X - b) G₂` over `S`, so `a · G'(a) = (a - b) · a · G₂(a)` and `a - b` is a unit of `S`;
an inertia element moving `a` would put `a - σ a` in a prime.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Unr

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- The field generated over `K` by the roots of `G ∈ A[X]` in `K̄`. -/
abbrev udField (G : A[X]) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K ((G.map (algebraMap A K)).rootSet (AlgebraicClosure K))

instance udField_isSplittingField (G : A[X]) :
    (G.map (algebraMap A K)).IsSplittingField K (udField A K G) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance udField_finiteDimensional (G : A[X]) : FiniteDimensional K (udField A K G) :=
  IsSplittingField.finiteDimensional _ (G.map (algebraMap A K))

variable {A K}

/-- The unit-derivative hypothesis makes `G` separable over `K`. -/
theorem ud_separable {G : A[X]} (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A)) :
    (G.map (algebraMap A K)).Separable := by
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2 fun y => ?_
  by_cases hy : aeval y (G.map (algebraMap A K)) = 0
  · right
    rw [aeval_map_algebraMap] at hy
    rw [derivative_map, aeval_map_algebraMap]
    intro h0
    have h := hu y hy
    rw [h0, mul_zero] at h
    exact (u.isUnit.map (algebraMap A (AlgebraicClosure K))).ne_zero h.symm
  · exact Or.inl hy

/-- **T5.** The unit-derivative criterion: `K(roots of G)` is a finite Galois extension unramified over `A`. -/
theorem udField_mem_unramSet {G : A[X]} (hG : G.Monic) (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A)) :
    udField A K G ∈ unramSet A K := by
  have : IsGalois K (udField A K G) := IsGalois.of_separable_splitting_field (ud_separable u hu)
  refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  let L := udField A K G
  let S := integralClosure A L
  let ι : L →ₐ[A] AlgebraicClosure K := (IntermediateField.val L).restrictScalars A
  let φ : S →ₐ[A] AlgebraicClosure K := ι.comp (integralClosure A L).val
  have hι : Function.Injective ι := fun x y h => Subtype.ext h
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (Subtype.ext h)
  have hrootS : ∀ s : S, aeval (φ s) G = 0 → aeval s G = 0 := fun s hs =>
    hφ (by rw [← aeval_algHom_apply, map_zero]; exact hs)
  have hunitS : ∀ s : S, aeval (φ s) G = 0 → s * aeval s (derivative G) = algebraMap A S (u : A) :=
    fun s hs => hφ (by rw [map_mul, ← aeval_algHom_apply, AlgHom.commutes]; exact hu _ hs)
  -- every root `z ∈ L` is fixed by `τ`
  have hfixL : ∀ z : L, aeval (ι z) G = 0 → τ z = z := by
    intro z hz'
    have hz : aeval z G = 0 := hι (by rw [← aeval_algHom_apply, map_zero]; exact hz')
    have hτz : aeval (τ z) G = 0 := by
      have h := aeval_algHom_apply (((τ : L →ₐ[K] L)).restrictScalars A) z G
      rw [hz, map_zero] at h
      exact h
    have hint : IsIntegral A z := ⟨G, hG, by rw [← aeval_def]; exact hz⟩
    let a : S := ⟨z, hint⟩
    obtain ⟨b, hbdef⟩ : ∃ b : S, b = τ • a := ⟨_, rfl⟩
    have ha : aeval (φ a) G = 0 := hz'
    have hb : aeval (φ b) G = 0 := by
      rw [hbdef]
      show aeval (ι (τ z)) G = 0
      rw [aeval_algHom_apply, hτz, map_zero]
    by_contra hne
    have hba : b ≠ a := by
      intro h
      rw [hbdef] at h
      exact hne (congrArg Subtype.val h)
    have hra : (G.map (algebraMap A S)).IsRoot a := by
      rw [IsRoot.def, eval_map_algebraMap]; exact hrootS a ha
    have hrb : (G.map (algebraMap A S)).IsRoot b := by
      rw [IsRoot.def, eval_map_algebraMap]; exact hrootS b hb
    obtain ⟨G1, hG1⟩ := dvd_iff_isRoot.2 hra
    have hrb1 : G1.IsRoot b := by
      have h := hrb
      rw [IsRoot.def, hG1, eval_mul, eval_sub, eval_X, eval_C] at h
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hba)
    obtain ⟨G2, hG2⟩ := dvd_iff_isRoot.2 hrb1
    have hder : eval a (derivative (G.map (algebraMap A S))) = (a - b) * eval a G2 := by
      rw [hG1, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, hG2,
        eval_mul, eval_sub, eval_X, eval_C]
    have hd : eval a (derivative (G.map (algebraMap A S))) = aeval a (derivative G) := by
      rw [derivative_map, eval_map_algebraMap]
    have hkey : (a - b) * (a * eval a G2) = algebraMap A S (u : A) := by
      rw [← hunitS a ha, ← hd, hder]; ring
    have hunit : IsUnit (a - b) := by
      have h : IsUnit (algebraMap A S (u : A)) := u.isUnit.map _
      rw [← hkey] at h
      exact isUnit_of_mul_isUnit_left h
    have hmem : a - b ∈ Q := by
      have h : τ • a - a ∈ Q := AddSubgroup.mem_inertia.1 hτ a
      rw [← hbdef] at h
      rw [← neg_sub]
      exact Q.neg_mem h
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hmem hunit)
  refine AlgEquiv.ext fun z => AlgHom.congr_fun (IntermediateField.adjoin_algHom_ext (F := K)
    (φ₁ := (τ : L →ₐ[K] L)) (φ₂ := AlgHom.id K L) fun y hy => ?_) z
  have h := (mem_rootSet.1 hy).2
  rw [aeval_map_algebraMap] at h
  exact hfixL ⟨y, IntermediateField.subset_adjoin K _ hy⟩ h

theorem udField_le_maxUnram {G : A[X]} (hG : G.Monic) (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A)) :
    udField A K G ≤ maxUnram A K := by
  rw [maxUnram_eq_sSup]
  exact le_sSup (udField_mem_unramSet hG u hu)

/-- Every root of a unit-derivative polynomial lies in `K_U`. -/
theorem mem_maxUnram_of_ud {G : A[X]} (hG : G.Monic) (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A))
    {y : AlgebraicClosure K} (hy : aeval y G = 0) : y ∈ maxUnram A K := by
  refine udField_le_maxUnram hG u hu (IntermediateField.subset_adjoin K _ ?_)
  rw [mem_rootSet]
  refine ⟨(hG.map (algebraMap A K)).ne_zero, ?_⟩
  rw [aeval_map_algebraMap]
  exact hy

end Unr

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Newton =====
section

/-!
# Tame inertia, part Newton: the Abhyankar trinomial has exactly one small root (S4-PD item (2), T6)

For a valuation `v : L → ℤᵐ⁰` and `F` with `1 < v F` (a pole), every root `w` of `X^(p+1) - F X + 1` has
`log v w = -log v F` (small root) or `p · log v w = log v F` (big root) (`trin_val_cases`, three-term
ultrametric). If the trinomial splits, the product of the roots is `±1`, so the logs sum to `0` and exactly one
root is small (`trin_existsUnique_small`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Trin

variable {L : Type*} [Field L]

theorem trin_isRoot_iff (p : ℕ) (F w : L) : (trin p F).IsRoot w ↔ w ^ (p + 1) - F * w + 1 = 0 := by
  simp [trin, IsRoot.def]

theorem trin_eq (p : ℕ) (F : L) : trin p F = X ^ (p + 1) + (C (-F) * X + C 1) := by
  rw [trin, C_neg, C_1]
  ring

theorem trin_degree_lt {p : ℕ} (hp : 0 < p) (F : L) :
    degree (C (-F) * X + C 1 : L[X]) < ((p + 1 : ℕ) : WithBot ℕ) :=
  degree_linear_le.trans_lt (by exact_mod_cast (by omega : 1 < p + 1))

theorem trin_monic {p : ℕ} (hp : 0 < p) (F : L) : (trin p F).Monic := by
  rw [trin_eq]
  exact monic_X_pow_add (trin_degree_lt hp F)

theorem trin_natDegree {p : ℕ} (hp : 0 < p) (F : L) : (trin p F).natDegree = p + 1 := by
  rw [trin_eq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact trin_degree_lt hp F

theorem trin_coeff_zero (p : ℕ) (F : L) : (trin p F).coeff 0 = 1 := by
  simp [trin]

/-- The three-term ultrametric case split for a root `w` of the trinomial. -/
theorem trin_val_cases (v : Valuation L (WithZero (Multiplicative ℤ))) {p : ℕ} {F w : L}
    (hw : w ^ (p + 1) - F * w + 1 = 0) {a c : ℤ} (ha : v w = WithZero.exp a) (hc : v F = WithZero.exp c)
    (hc0 : 0 < c) : a = -c ∨ (p : ℤ) * a = c := by
  have he : v (w ^ (p + 1) + 1) = WithZero.exp (c + a) := by
    rw [show w ^ (p + 1) + 1 = F * w by linear_combination hw, map_mul, hc, ha, ← WithZero.exp_add]
  have hp1 : v (w ^ (p + 1)) = WithZero.exp ((p + 1 : ℕ) • a) := by
    rw [map_pow, ha, ← WithZero.exp_nsmul]
  have h1 : v (1 : L) = WithZero.exp 0 := by rw [map_one, WithZero.exp_zero]
  rcases lt_trichotomy a 0 with h | h | h
  · left
    have hlt : v (w ^ (p + 1)) < v 1 := by
      rw [hp1, h1, WithZero.exp_lt_exp, nsmul_eq_mul]
      push_cast
      nlinarith
    rw [Valuation.map_add_eq_of_lt_right v hlt, h1] at he
    have := WithZero.exp_injective he
    omega
  · exfalso
    subst h
    have hle := Valuation.map_add v (w ^ (p + 1)) 1
    rw [he, hp1, h1, smul_zero, max_self, WithZero.exp_le_exp] at hle
    omega
  · right
    have hlt : v (1 : L) < v (w ^ (p + 1)) := by
      rw [hp1, h1, WithZero.exp_lt_exp, nsmul_eq_mul]
      push_cast
      nlinarith
    rw [Valuation.map_add_eq_of_lt_left v hlt, hp1] at he
    have := WithZero.exp_injective he
    rw [nsmul_eq_mul] at this
    push_cast at this
    linarith

/-- Counting identity: `p · Σ ℓ = c · #s - (p + 1) c · #{ℓ < 0}` when every `ℓ x` is `-c` or `c / p`. -/
theorem count_small {X : Type*} (s : Multiset X) (ℓ : X → ℤ) {c : ℤ} (hc : 0 < c) (p : ℕ)
    (h : ∀ x ∈ s, ℓ x = -c ∨ (p : ℤ) * ℓ x = c) :
    (p : ℤ) * (s.map ℓ).sum = c * Multiset.card s - (p + 1) * c * Multiset.countP (fun x => ℓ x < 0) s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    have ih' := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    rcases h x (Multiset.mem_cons_self x s) with hx | hx
    · have hlt : ℓ x < 0 := by omega
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Multiset.countP_cons, hlt,
        if_true]
      push_cast
      linear_combination ih' + (p : ℤ) * hx
    · have hpos : ¬ ℓ x < 0 := by
        intro hneg
        have : (p : ℤ) * ℓ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg p) hneg.le
        omega
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Multiset.countP_cons, hpos,
        if_false, add_zero]
      push_cast
      linear_combination ih' + hx

theorem val_prod_eq_exp (v : Valuation L (WithZero (Multiplicative ℤ))) (s : Multiset L)
    (hs : ∀ x ∈ s, x ≠ 0) : v s.prod = WithZero.exp ((s.map fun x => WithZero.log (v x)).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.prod_cons, map_mul, ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy)),
      Multiset.map_cons, Multiset.sum_cons, WithZero.exp_add,
      WithZero.exp_log ((Valuation.ne_zero_iff v).2 (hs x (Multiset.mem_cons_self x s)))]

/-- **T6.** A split Abhyankar trinomial with `1 < v F` has exactly one root `w` with `v w < 1`. -/
theorem trin_existsUnique_small (v : Valuation L (WithZero (Multiplicative ℤ))) {p : ℕ} (hp : 0 < p) {F : L}
    (hF : 1 < v F) (hs : (trin p F).Splits) : ∃! w, (trin p F).IsRoot w ∧ v w < 1 := by
  classical
  have hF0 : F ≠ 0 := by
    intro h
    rw [h, map_zero] at hF
    exact not_lt_of_ge zero_le' hF
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = WithZero.log (v F) := ⟨_, rfl⟩
  have hcF : v F = WithZero.exp c := by rw [hc, WithZero.exp_log ((Valuation.ne_zero_iff v).2 hF0)]
  have hc0 : 0 < c := by
    rw [hcF, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hF
    exact hF
  have hne : trin p F ≠ 0 := (trin_monic hp F).ne_zero
  obtain ⟨s, hsdef⟩ : ∃ s : Multiset L, s = (trin p F).roots := ⟨_, rfl⟩
  have hcard : Multiset.card s = p + 1 := by
    rw [hsdef, ← hs.natDegree_eq_card_roots, trin_natDegree hp F]
  have hmemr : ∀ w, w ∈ s ↔ (trin p F).IsRoot w := fun w => by rw [hsdef, mem_roots hne]
  have hroot : ∀ w ∈ s, w ^ (p + 1) - F * w + 1 = 0 := fun w hw =>
    (trin_isRoot_iff p F w).1 ((hmemr w).1 hw)
  have hw0 : ∀ w ∈ s, w ≠ 0 := by
    intro w hw h
    have h' := hroot w hw
    rw [h] at h'
    simp at h'
  let ℓ : L → ℤ := fun x => WithZero.log (v x)
  have hexp : ∀ w ∈ s, v w = WithZero.exp (ℓ w) := fun w hw =>
    (WithZero.exp_log ((Valuation.ne_zero_iff v).2 (hw0 w hw))).symm
  have hcases : ∀ w ∈ s, ℓ w = -c ∨ (p : ℤ) * ℓ w = c := fun w hw =>
    trin_val_cases v (hroot w hw) (hexp w hw) hcF hc0
  have hsum : (s.map ℓ).sum = 0 := by
    have h1 := hs.coeff_zero_eq_prod_roots_of_monic (trin_monic hp F)
    rw [trin_coeff_zero, ← hsdef] at h1
    have h3 := congrArg v h1
    rw [map_one, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul,
      val_prod_eq_exp v s hw0, ← WithZero.exp_zero] at h3
    exact (WithZero.exp_injective h3).symm
  have hcnt := count_small s ℓ hc0 p hcases
  rw [hsum, mul_zero, hcard] at hcnt
  have hr : Multiset.countP (fun x => ℓ x < 0) s = 1 := by
    have h : ((p : ℤ) + 1) * c * (1 - (Multiset.countP (fun x => ℓ x < 0) s : ℤ)) = 0 := by
      push_cast at hcnt
      linear_combination -hcnt
    rcases mul_eq_zero.1 h with h | h
    · exfalso
      have : (0 : ℤ) < ((p : ℤ) + 1) * c := mul_pos (by positivity) hc0
      omega
    · omega
  rw [Multiset.countP_eq_card_filter] at hr
  obtain ⟨w₀, hw₀⟩ := Multiset.card_eq_one.1 hr
  have hmem : ∀ w, w ∈ s.filter (fun x => ℓ x < 0) ↔ w = w₀ := fun w => by
    rw [hw₀, Multiset.mem_singleton]
  have hsmall : ∀ w ∈ s, v w < 1 ↔ ℓ w < 0 := fun w hw => by
    rw [hexp w hw, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  refine ⟨w₀, ?_, ?_⟩
  · have h0 := (hmem w₀).2 rfl
    rw [Multiset.mem_filter] at h0
    exact ⟨(hmemr w₀).1 h0.1, (hsmall w₀ h0.1).2 h0.2⟩
  · rintro w ⟨hw, hwv⟩
    have hws : w ∈ s := (hmemr w).2 hw
    exact (hmem w).1 (Multiset.mem_filter.2 ⟨hws, (hsmall w hws).1 hwv⟩)

end Trin

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_LL =====
section

/-!
# Tame inertia, part LL: inertia fixes constants and the local Kummer lemma (S4-PD item (2), T0 + T1)

* `inertia_le_pi1geo`: the inertia group of a prime of the pro-chart fixes every constant, so `I ≤ π₁^geo`.
* `fix_of_inertia_local`: if `γ^N = c^N b / s` with `σ` in the inertia of `Q` fixing `c, b, s` and `b, s ∉ Q`,
  then `σ γ = γ` (a Kummer radical whose `Q`-adic valuation is divisible by `N` is not moved by inertia).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)]

theorem coe_smul (σ : Pi1 A K) (x : proChart A K R0) :
    ((σ • x : proChart A K R0) : maxUnram A K) = σ (x : maxUnram A K) := rfl

/-- T1 (local Kummer lemma): `γ^N · s = c^N · b` with `b, s ∉ Q`, `σ ∈ I(Q)` fixing `c, b, s` ⇒ `σ γ = γ`. -/
theorem fix_of_inertia_local {Q : Ideal (proChart A K R0)} [hQ : Q.IsPrime] {N : ℕ}
    (hN : IsUnit (N : proChart A K R0)) {σ : Pi1 A K} (hσ : σ ∈ Q.inertia (Pi1 A K))
    {γ c : maxUnram A K} {b s : proChart A K R0} (hc : c ≠ 0) (hb : b ∉ Q) (hs : s ∉ Q)
    (hcf : σ c = c) (hbf : σ (b : maxUnram A K) = b) (hsf : σ (s : maxUnram A K) = s)
    (hγ : γ ^ N * (s : maxUnram A K) = c ^ N * (b : maxUnram A K)) : σ γ = γ := by
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hN
    · exact h
  have hb0 : (b : maxUnram A K) ≠ 0 := by
    intro h; apply hb
    have : b = 0 := Subtype.ext h
    rw [this]; exact Q.zero_mem
  have hs0 : (s : maxUnram A K) ≠ 0 := by
    intro h; apply hs
    have : s = 0 := Subtype.ext h
    rw [this]; exact Q.zero_mem
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne', zero_mul] at hγ
    exact mul_ne_zero (pow_ne_zero _ hc) hb0 hγ.symm
  obtain ⟨g', hg'⟩ : ∃ g' : maxUnram A K, g' = (s : maxUnram A K) * γ / c := ⟨_, rfl⟩
  have hg'pow : g' ^ N = (s : maxUnram A K) ^ (N - 1) * b := by
    rw [hg', div_pow, mul_pow, div_eq_iff (pow_ne_zero _ hc)]
    have h4 : (s : maxUnram A K) ^ N = (s : maxUnram A K) ^ (N - 1) * s := by
      rw [← pow_succ]; congr 1; omega
    rw [h4, mul_assoc, mul_comm (s : maxUnram A K) (γ ^ N), hγ]
    ring
  have hg'int : IsIntegral R0 g' := by
    have h1 : IsIntegral R0 (g' ^ N) := by
      rw [hg'pow]
      exact (((mem_integralClosure_iff _ _).1 s.2).pow _).mul ((mem_integralClosure_iff _ _).1 b.2)
    exact IsIntegral.of_pow hN0 h1
  let gI : proChart A K R0 := ⟨g', (mem_integralClosure_iff _ _).2 hg'int⟩
  have hgQ : gI ∉ Q := by
    intro h
    have hpow : gI ^ N ∈ Q := Q.pow_mem_of_mem h N hN0
    have heq : gI ^ N = s ^ (N - 1) * b := by
      apply Subtype.ext
      show g' ^ N = (s : maxUnram A K) ^ (N - 1) * b
      exact hg'pow
    rw [heq] at hpow
    rcases hQ.mem_or_mem hpow with h1 | h1
    · exact hs (hQ.mem_of_pow_mem _ h1)
    · exact hb h1
  obtain ⟨z, hz⟩ : ∃ z : maxUnram A K, z = σ γ / γ := ⟨_, rfl⟩
  have hfix : σ (γ ^ N) = γ ^ N := by
    have h2 : γ ^ N = c ^ N * b / s := by rw [eq_div_iff hs0]; exact hγ
    rw [h2, map_div₀, map_mul, map_pow, hcf, hbf, hsf]
  have hzN : z ^ N = 1 := by
    rw [hz, div_pow, ← map_pow, hfix, div_self (pow_ne_zero _ hγ0)]
  have hzint : IsIntegral R0 z := IsIntegral.of_pow hN0 (by rw [hzN]; exact isIntegral_one)
  let zI : proChart A K R0 := ⟨z, (mem_integralClosure_iff _ _).2 hzint⟩
  have hmem : σ • gI - gI ∈ Q := AddSubgroup.mem_inertia.1 hσ gI
  have hfac : σ • gI - gI = (zI - 1) * gI := by
    apply Subtype.ext
    show σ g' - g' = (z - 1) * g'
    rw [hg', map_div₀, map_mul, hsf, hcf, hz]
    field_simp
  rw [hfac] at hmem
  have hz1 : zI - 1 ∈ Q := (hQ.mem_or_mem hmem).resolve_right hgQ
  have hzI : zI ^ N = 1 := by
    apply Subtype.ext
    show z ^ N = 1
    exact hzN
  have h5 : zI = 1 := Kummer.eq_one_of_sub_mem hN hzI hz1
  have hz' : z = 1 := congrArg Subtype.val h5
  rw [hz, div_eq_one_iff_eq hγ0] at hz'
  exact hz'

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Up =====
section

/-!
# Tame inertia, part Up: the upper bound `#Hom(I, ℤ/N) ≤ N` (S4-PD item (2), T2 + T3)

* `exists_pow_mul_of_dvd` (T2): in a Dedekind domain, `N ∣ v(x)` gives `x · s = c^N · b` with `b, s ∉ v`.
* `fixed_of_mem_adjoin`: elements of `K_U` lying in the field generated by `Γ`-fixed elements are `Γ`-fixed.
* `exists_ne_eq_of_family` (T3, pigeonhole): among `N + 1` locally constant characters `I → ℤ/N` of the inertia
  group of a nonzero prime of the pro-chart, two coincide (Kummer theory + the `v`-adic valuation mod `N` of the
  radicands at the prime under `Q` + the local Kummer lemma `fix_of_inertia_local`).
* `exists_eq_mul_of_surj`: if one character `θ` is onto, every character is a multiple of `θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh IsDedekindDomain Kummer

noncomputable section

section Val

variable {B F : Type*} [CommRing B] [IsDedekindDomain B] [Field F] [Algebra B F] [IsFractionRing B F]

/-- T2: `N ∣ log v(x)` ⇒ `x · s = c^N · b` with `b, s ∉ v`. -/
theorem exists_pow_mul_of_dvd (v : HeightOneSpectrum B) {N : ℕ} {x : F} (hx : x ≠ 0)
    (hN : (N : ℤ) ∣ WithZero.log (v.valuation F x)) :
    ∃ (c : F) (b s : B), c ≠ 0 ∧ b ∉ v.asIdeal ∧ s ∉ v.asIdeal ∧
      x * algebraMap B F s = c ^ N * algebraMap B F b := by
  obtain ⟨k, hk⟩ := hN
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hvx : v.valuation F x = WithZero.exp ((N : ℤ) * k) := by
    rw [← hk, WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)]
  obtain ⟨u, hu⟩ : ∃ u : F, u = x * π ^ ((N : ℤ) * k) := ⟨_, rfl⟩
  have hvu : v.valuation F u = 1 := by
    rw [hu, map_mul, map_zpow₀, hvx, hπ, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one]
    simp
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer u hvu.le
  have hn : n ∉ v.asIdeal := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, hvu, one_mul]
    exact (v.valuation_eq_one_iff_notMem (K := F)).2 d.2
  refine ⟨π ^ (-k), n, d, zpow_ne_zero _ hπ0, hn, d.2, ?_⟩
  rw [← hnd, hu]
  have hpow : (π ^ (-k)) ^ N * π ^ ((N : ℤ) * k) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hπ0]
    rw [show -k * (N : ℤ) + (N : ℤ) * k = 0 by ring, zpow_zero]
  calc x * algebraMap B F d = ((π ^ (-k)) ^ N * π ^ ((N : ℤ) * k)) * (x * algebraMap B F d) := by
        rw [hpow, one_mul]
    _ = (π ^ (-k)) ^ N * (x * π ^ ((N : ℤ) * k) * algebraMap B F d) := by ring

end Val

section Up

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- Elements of `K_U` in the field generated by `Γ`-fixed elements are `Γ`-fixed. -/
theorem fixed_of_mem_adjoin {Γ : Subgroup (Pi1 A K)} {s : Set (AlgebraicClosure K)}
    (hs : ∀ y ∈ s, ∃ x : maxUnram A K, (x : AlgebraicClosure K) = y ∧ ∀ σ ∈ Γ, σ x = x)
    {x : maxUnram A K} (hx : (x : AlgebraicClosure K) ∈ IntermediateField.adjoin K s)
    (σ : Pi1 A K) (hσ : σ ∈ Γ) : σ x = x := by
  have hle : IntermediateField.adjoin K s ≤ (IntermediateField.fixedField Γ).map (maxUnram A K).val := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    obtain ⟨x', rfl, hx'⟩ := hs y hy
    rw [IntermediateField.coe_map]
    exact ⟨x', (IntermediateField.mem_fixedField_iff _ _).2 hx', rfl⟩
  have h := hle hx
  rw [← SetLike.mem_coe, IntermediateField.coe_map] at h
  obtain ⟨y, hy, hyx⟩ := h
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  exact (IntermediateField.mem_fixedField_iff _ _).1 hy σ hσ

variable {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- T3 (pigeonhole): among `N + 1` locally constant characters of the inertia group of a nonzero prime `Q` of the
pro-chart, two coincide. -/
theorem exists_ne_eq_of_family {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q) {N : ℕ} [NeZero N]
    (hN : IsUnit (N : R0)) {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
    (hζI : ∀ σ ∈ Q.inertia (Pi1 A K), σ ζ = ζ)
    (χ : Fin (N + 1) → Q.inertia (Pi1 A K) → ZMod N) (hχc : ∀ i, IsLocallyConstant (χ i))
    (hχ : ∀ i σ τ, χ i (σ * τ) = χ i σ + χ i τ) : ∃ i j, i ≠ j ∧ χ i = χ j := by
  classical
  haveI := hQ.1
  choose α hαr hαχ using fun i => exists_kchar_eq hζ hζI (χ i) (hχc i) (hχ i)
  -- the finite level `M = K(α_i ^ N)`
  obtain ⟨s, hs⟩ : ∃ s : Finset (AlgebraicClosure K), s = Finset.univ.image
      (fun i => ((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K)) := ⟨_, rfl⟩
  have hsmem : ∀ i, ((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K) ∈
      (s : Set (AlgebraicClosure K)) := fun i => by
    rw [hs, Finset.coe_image]
    exact ⟨i, by simp, rfl⟩
  obtain ⟨L, hL, hML⟩ := exists_unramSet_of_finite A K s (by
    intro x hx
    rw [hs, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact SetLike.coe_mem _)
  obtain ⟨M, hMdef⟩ : ∃ M : IntermediateField K (AlgebraicClosure K),
      M = IntermediateField.adjoin K (s : Set (AlgebraicClosure K)) := ⟨_, rfl⟩
  rw [← hMdef] at hML
  haveI : FiniteDimensional K L := hL.1
  haveI : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  have hMU : M ≤ maxUnram A K := hML.trans hLU
  haveI : FiniteDimensional K M := FiniteDimensional.of_injective
    (IntermediateField.inclusion hML).toLinearMap (IntermediateField.inclusion hML).injective
  haveI : Algebra.IsSeparable K M :=
    Algebra.IsSeparable.of_algHom (F := K) (E' := L) (IntermediateField.inclusion hML)
  haveI : IsFractionRing (integralClosure R0 M) M :=
    integralClosure.isFractionRing_of_finite_extension (A := R0) K M
  haveI : IsDedekindDomain (integralClosure R0 M) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := M)
  -- `M` is fixed by the inertia group
  have hfixM : ∀ x : maxUnram A K, (x : AlgebraicClosure K) ∈ M → ∀ σ ∈ Q.inertia (Pi1 A K), σ x = x := by
    intro x hx σ hσ
    rw [hMdef] at hx
    refine fixed_of_mem_adjoin (Γ := Q.inertia (Pi1 A K)) ?_ hx σ hσ
    intro y hy
    rw [hs, Finset.coe_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact ⟨_, rfl, fun τ hτ => hαr i τ hτ⟩
  -- the prime `P` of `B_M` under `Q`
  obtain ⟨P, hPdef⟩ : ∃ P : Ideal (integralClosure R0 M), P = Q.comap (inclU R0 hMU) := ⟨_, rfl⟩
  have hPp : P.IsPrime := by rw [hPdef]; exact Ideal.IsPrime.comap _
  have hP0 : P ≠ ⊥ := by
    haveI : Nontrivial R0 := (algebraMap R0 K).domain_nontrivial
    obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    have h1 : Q.comap (algebraMap R0 (proChart A K R0)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hx0 hxQ (Algebra.IsIntegral.isIntegral x)
    obtain ⟨r, hrQ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    refine (Submodule.ne_bot_iff _).2 ⟨algebraMap R0 (integralClosure R0 M) r, ?_, ?_⟩
    · rw [hPdef, Ideal.mem_comap, AlgHom.commutes]
      exact hrQ
    · intro h
      have h3 : algebraMap R0 M r = 0 := by
        rw [IsScalarTower.algebraMap_apply R0 (integralClosure R0 M) M, h, map_zero]
      rw [IsScalarTower.algebraMap_apply R0 K M] at h3
      have h4 : algebraMap R0 K r = 0 := (map_eq_zero_iff _ (algebraMap K M).injective).1 h3
      exact hr0 (IsFractionRing.injective R0 K (h4.trans (map_zero _).symm))
  let v : HeightOneSpectrum (integralClosure R0 M) := ⟨P, hPp, hP0⟩
  -- the radicands as elements of `M`
  let aM : Fin (N + 1) → M := fun i =>
    ⟨((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K), by
      rw [hMdef]; exact IntermediateField.subset_adjoin K _ (hsmem i)⟩
  have haM0 : ∀ i, aM i ≠ 0 := by
    intro i h
    have h1 : ((((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K) = 0 :=
      congrArg Subtype.val h
    have h2 : (((α i : (maxUnram A K)ˣ) : maxUnram A K) ^ N : maxUnram A K) = 0 := Subtype.ext h1
    exact pow_ne_zero _ (α i).ne_zero h2
  -- pigeonhole on `log v(aM i) mod N`
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => ((WithZero.log (v.valuation M (aM i)) : ℤ) : ZMod N)) (by rw [ZMod.card, Fintype.card_fin]; omega)
  refine ⟨i, j, hij, ?_⟩
  have hdvd : (N : ℤ) ∣ WithZero.log (v.valuation M (aM i / aM j)) := by
    rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (haM0 i)) ((Valuation.ne_zero_iff _).2 (haM0 j))]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).1 hfij.symm
  obtain ⟨c, b, s', hc0, hb, hs', hcbs⟩ := exists_pow_mul_of_dvd v (div_ne_zero (haM0 i) (haM0 j)) hdvd
  have hNp : IsUnit (N : proChart A K R0) := by
    simpa using hN.map (algebraMap R0 (proChart A K R0))
  have hγ : ((α i : maxUnram A K) / (α j : maxUnram A K)) ^ N *
      ((inclU R0 hMU s' : proChart A K R0) : maxUnram A K) =
      (IntermediateField.inclusion hMU c) ^ N * ((inclU R0 hMU b : proChart A K R0) : maxUnram A K) := by
    have h1 := congrArg (IntermediateField.inclusion hMU) hcbs
    simp only [map_mul, map_div₀, map_pow] at h1
    have e1 : ∀ k, IntermediateField.inclusion hMU (aM k) = ((α k : (maxUnram A K)ˣ) : maxUnram A K) ^ N :=
      fun k => Subtype.ext rfl
    have e2 : ∀ y : integralClosure R0 M, IntermediateField.inclusion hMU (algebraMap _ M y) =
        ((inclU R0 hMU y : proChart A K R0) : maxUnram A K) := fun y => rfl
    rw [e1, e1, e2, e2] at h1
    rw [div_pow]
    exact h1
  have hbQ : inclU R0 hMU b ∉ Q := fun h => hb (by
    show b ∈ P
    rw [hPdef]
    exact h)
  have hsQ : inclU R0 hMU s' ∉ Q := fun h => hs' (by
    show s' ∈ P
    rw [hPdef]
    exact h)
  funext σ
  have hfix := fix_of_inertia_local A K R0 hNp σ.2
    ((map_ne_zero (IntermediateField.inclusion hMU)).2 hc0) hbQ hsQ
    (hfixM _ c.2 σ σ.2) (hfixM _ (b : M).2 σ σ.2) (hfixM _ (s' : M).2 σ σ.2) hγ
  have hi := kchar_spec hζ (hαr i) σ
  have hj := kchar_spec hζ (hαr j) σ
  rw [hαχ i σ] at hi
  rw [hαχ j σ] at hj
  have hαi0 : ((α i : (maxUnram A K)ˣ) : maxUnram A K) ≠ 0 := (α i).ne_zero
  have hαj0 : ((α j : (maxUnram A K)ˣ) : maxUnram A K) ≠ 0 := (α j).ne_zero
  have hb0 := epow_ne_zero hζ (χ j σ)
  rw [map_div₀, hi, hj, div_eq_div_iff (mul_ne_zero hb0 hαj0) hαj0] at hfix
  apply epow_injective hζ
  have h5 : (epow ζ (χ i σ) - epow ζ (χ j σ)) *
      (((α i : (maxUnram A K)ˣ) : maxUnram A K) * ((α j : (maxUnram A K)ˣ) : maxUnram A K)) = 0 := by
    linear_combination hfix
  rcases mul_eq_zero.1 h5 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (mul_ne_zero hαi0 hαj0)

end Up

section Cyc

variable {G : Type} [Group G] [TopologicalSpace G] {N : ℕ} [NeZero N]

/-- If the pigeonhole bound holds for `G` and `θ : G → ℤ/N` is an onto locally constant character, every locally
constant character is a multiple of `θ`. -/
theorem exists_eq_mul_of_surj
    (hpig : ∀ χ : Fin (N + 1) → G → ZMod N, (∀ i, IsLocallyConstant (χ i)) →
      (∀ i σ τ, χ i (σ * τ) = χ i σ + χ i τ) → ∃ i j, i ≠ j ∧ χ i = χ j)
    {θ : G → ZMod N} (hθc : IsLocallyConstant θ) (hθ : ∀ σ τ, θ (σ * τ) = θ σ + θ τ) {σ₀ : G} (hσ₀ : θ σ₀ = 1)
    {χ : G → ZMod N} (hχc : IsLocallyConstant χ) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ) :
    ∃ k : ZMod N, ∀ σ, χ σ = k * θ σ := by
  classical
  let f : Fin (N + 1) → G → ZMod N := fun i => if (i : ℕ) = N then χ else fun σ => ((i : ℕ) : ZMod N) * θ σ
  have hfc : ∀ i, IsLocallyConstant (f i) := by
    intro i
    by_cases h : (i : ℕ) = N
    · simp only [f, h, if_true]; exact hχc
    · simp only [f, h, if_false]; exact hθc.comp (fun x => ((i : ℕ) : ZMod N) * x)
  have hf : ∀ i σ τ, f i (σ * τ) = f i σ + f i τ := by
    intro i σ τ
    by_cases h : (i : ℕ) = N
    · simp only [f, h, if_true]; exact hχ σ τ
    · simp only [f, h, if_false]; rw [hθ, mul_add]
  obtain ⟨i, j, hij, hfij⟩ := hpig f hfc hf
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hilt := i.isLt
  have hjlt := j.isLt
  by_cases hi : (i : ℕ) = N
  · have hj : (j : ℕ) ≠ N := fun h => hne (hi.trans h.symm)
    refine ⟨((j : ℕ) : ZMod N), fun σ => ?_⟩
    have := congrFun hfij σ
    simp only [f, hi, hj, if_true, if_false] at this
    exact this
  · by_cases hj : (j : ℕ) = N
    · refine ⟨((i : ℕ) : ZMod N), fun σ => ?_⟩
      have := congrFun hfij σ
      simp only [f, hi, hj, if_true, if_false] at this
      exact this.symm
    · exfalso
      have := congrFun hfij σ₀
      simp only [f, hi, hj, if_false, hσ₀, mul_one] at this
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact hne this

end Cyc

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Fix =====
section

/-!
# Tame inertia, part Fix: the Abhyankar polynomial and the inertia-fixed small root (S4-PD item (2), T5 applied + T7)

* `abhy p N f = X^(N(p+1)) - f X^N + 1 ∈ A[X]`; in characteristic `p`, `z · G'(z) = -N` at every root
  (`abhy_ud`), so every root lies in `K_U` when `N` is a unit of `A` (`mem_maxUnram_abhy`).
* `valuation_smul_lt_one`: an inertia element preserves `v_P(w) < 1`.
* `fix_small_root`: an inertia element fixes the unique root `w` with `v_P(w) < 1` of a split trinomial
  `X^(p+1) - F X + 1` with `1 < v_P(F)` and `F` fixed (Newton uniqueness, `trin_existsUnique_small`).
* `one_lt_valuation_level`: a pole of `a ∈ K` at `x = Q ∩ R0` is a pole at the prime `Q ∩ B_L` of every level.
* `fix_of_inertia_small`: pro-chart inertia elements fix the small root at a finite Galois level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

section Abhy

variable {A : Type} [CommRing A]

/-- The Abhyankar polynomial `X^(N(p+1)) - f X^N + 1`. -/
def abhy (p N : ℕ) (f : A) : A[X] := X ^ (N * (p + 1)) - C f * X ^ N + 1

theorem aeval_abhy {R : Type*} [CommRing R] [Algebra A R] (p N : ℕ) (f : A) (y : R) :
    aeval y (abhy p N f) = (y ^ N) ^ (p + 1) - algebraMap A R f * y ^ N + 1 := by
  simp [abhy, pow_mul]

theorem abhy_monic [Nontrivial A] {p N : ℕ} (hp : 0 < p) (hN : 0 < N) (f : A) : (abhy p N f).Monic := by
  have h : abhy p N f = X ^ (N * (p + 1)) + (C (-f) * X ^ N + C 1) := by
    rw [abhy, C_neg, C_1]; ring
  rw [h]
  refine monic_X_pow_add ?_
  calc degree (C (-f) * X ^ N + C 1) ≤ (N : WithBot ℕ) :=
        (degree_add_le _ _).trans (max_le (degree_C_mul_X_pow_le _ _)
          (degree_C_le.trans (by exact_mod_cast Nat.zero_le N)))
    _ < ((N * (p + 1) : ℕ) : WithBot ℕ) := by exact_mod_cast (show N < N * (p + 1) by nlinarith)

theorem aeval_derivative_abhy {R : Type*} [CommRing R] [Algebra A R] (p : ℕ) {N : ℕ} (hN : N ≠ 0)
    (f : A) (y : R) :
    y * aeval y (derivative (abhy p N f)) =
      ((N * (p + 1) : ℕ) : R) * y ^ (N * (p + 1)) - (N : R) * (algebraMap A R f * y ^ N) := by
  have h1 : N * (p + 1) ≠ 0 := Nat.mul_ne_zero hN (Nat.succ_ne_zero p)
  rw [abhy, derivative_add, derivative_sub, derivative_C_mul, derivative_X_pow, derivative_X_pow,
    derivative_one, add_zero]
  simp only [map_sub, map_mul, aeval_C, aeval_X_pow, map_natCast]
  rw [← mul_pow_sub_one h1 y, ← mul_pow_sub_one hN y]
  ring

/-- In characteristic `p`, the Abhyankar polynomial has the unit-derivative property `z · G'(z) = -N`. -/
theorem abhy_ud_of_cast {R : Type*} [CommRing R] [Algebra A R] {p : ℕ} (hp : (p : R) = 0) {N : ℕ}
    (hN : N ≠ 0) (f : A) {y : R} (hy : aeval y (abhy p N f) = 0) :
    y * aeval y (derivative (abhy p N f)) = -(N : R) := by
  rw [aeval_derivative_abhy p hN f y, pow_mul]
  rw [aeval_abhy] at hy
  push_cast
  linear_combination (N : R) * hy + ((N : R) * (y ^ N) ^ (p + 1)) * hp

variable {K : Type} [Field K] [Algebra A K]

theorem abhy_ud {p : ℕ} [CharP K p] {N : ℕ} (hN : IsUnit (N : A)) (f : A) :
    ∀ y : AlgebraicClosure K, aeval y (abhy p N f) = 0 →
      y * aeval y (derivative (abhy p N f)) = algebraMap A (AlgebraicClosure K) ((-hN.unit : Aˣ) : A) := by
  intro y hy
  have : Nontrivial A := (algebraMap A (AlgebraicClosure K)).domain_nontrivial
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hN
    exact not_isUnit_zero hN
  have hp : (p : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), CharP.cast_eq_zero, map_zero]
  rw [abhy_ud_of_cast hp hN0 f hy, Units.val_neg, IsUnit.unit_spec, map_neg, map_natCast]

/-- **T5 applied.** Every root of the Abhyankar polynomial lies in `K_U`. -/
theorem mem_maxUnram_abhy {p : ℕ} [CharP K p] (hp : 0 < p) {N : ℕ} (hN : IsUnit (N : A)) (f : A)
    {y : AlgebraicClosure K} (hy : aeval y (abhy p N f) = 0) : y ∈ maxUnram A K := by
  have : Nontrivial A := (algebraMap A (AlgebraicClosure K)).domain_nontrivial
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by
    rintro rfl
    rw [Nat.cast_zero] at hN
    exact not_isUnit_zero hN)
  exact mem_maxUnram_of_ud (abhy_monic hp hN0 f) _ (abhy_ud hN f) hy

theorem map_abhy_one {L : Type*} [Field L] [Algebra K L] (p : ℕ) (f : A) :
    ((abhy p 1 f).map (algebraMap A K)).map (algebraMap K L) = trin p (algebraMap K L (algebraMap A K f)) := by
  simp [abhy, trin, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- The roots of `g = abhy p 1 f` are `N`-th powers of roots of `abhy p N f`. -/
theorem udField_abhy_one_le [Nontrivial A] {p : ℕ} (hp : 0 < p) {N : ℕ} (hN : 0 < N) (f : A) :
    udField A K (abhy p 1 f) ≤ udField A K (abhy p N f) := by
  rw [IntermediateField.adjoin_le_iff]
  intro y hy
  have hy0 := (mem_rootSet.1 hy).2
  rw [aeval_map_algebraMap, aeval_abhy, pow_one] at hy0
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y hN
  have hzr : z ∈ ((abhy p N f).map (algebraMap A K)).rootSet (AlgebraicClosure K) := by
    rw [mem_rootSet]
    refine ⟨((abhy_monic hp hN f).map (algebraMap A K)).ne_zero, ?_⟩
    rw [aeval_map_algebraMap, aeval_abhy, hz]
    exact hy0
  rw [← hz]
  exact pow_mem (IntermediateField.subset_adjoin K _ hzr) N

end Abhy

section Gen

variable {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
  {G : Type*} [Group G] [MulSemiringAction G B] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : B), σ • algebraMap B L s = algebraMap B L (σ • s))

include hc in
/-- Inertia elements preserve `v_P(w) < 1`. -/
theorem valuation_smul_lt_one (P : HeightOneSpectrum B) {σ : G} (hσ : σ ∈ P.asIdeal.inertia G) {w : L}
    (hw : P.valuation L w < 1) : P.valuation L (σ • w) < 1 := by
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer w hw.le
  have hd1 : P.valuation L (algebraMap B L d) = 1 := (P.valuation_eq_one_iff_notMem (K := L)).2 d.2
  have hn : n ∈ P.asIdeal := by
    refine (P.valuation_lt_one_iff_mem (K := L) n).1 ?_
    show P.valuation L (algebraMap B L n) < 1
    rw [← hnd, map_mul, hd1, mul_one]
    exact hw
  have hσn : σ • n ∈ P.asIdeal := by
    have h := P.asIdeal.add_mem (AddSubgroup.mem_inertia.1 hσ n) hn
    rwa [sub_add_cancel] at h
  have hσd : σ • (d : B) ∉ P.asIdeal := fun h => d.2 (by
    have h' := P.asIdeal.sub_mem h (AddSubgroup.mem_inertia.1 hσ (d : B))
    rwa [sub_sub_cancel] at h')
  have hmul : σ • w * algebraMap B L (σ • (d : B)) = algebraMap B L (σ • n) := by
    rw [← hc, ← hc, ← smul_mul', hnd]
  have h1 : P.valuation L (algebraMap B L (σ • (d : B))) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := L)).2 hσd
  have h2 : P.valuation L (algebraMap B L (σ • n)) < 1 := (P.valuation_lt_one_iff_mem (K := L) _).2 hσn
  rw [← hmul, map_mul, h1, mul_one] at h2
  exact h2

include hc in
/-- **T7 (level form).** An inertia element fixing `F` fixes the unique small root of the split trinomial. -/
theorem fix_small_root (P : HeightOneSpectrum B) {p : ℕ} (hp : 0 < p) {F : L} (hF : 1 < P.valuation L F)
    (hs : (trin p F).Splits) {σ : G} (hσ : σ ∈ P.asIdeal.inertia G) (hσF : σ • F = F) {w : L}
    (hw : (trin p F).IsRoot w) (hwv : P.valuation L w < 1) : σ • w = w := by
  obtain ⟨w₀, -, huniq⟩ := trin_existsUnique_small (P.valuation L) hp hF hs
  have hr : (trin p F).IsRoot (σ • w) := by
    have h := congrArg (fun t => σ • t) ((trin_isRoot_iff p F w).1 hw)
    simp only [smul_add, smul_sub, smul_mul', smul_pow', smul_one, smul_zero, hσF] at h
    exact (trin_isRoot_iff p F _).2 h
  exact (huniq (σ • w) ⟨hr, valuation_smul_lt_one hc P hσ hwv⟩).trans (huniq w ⟨hw, hwv⟩).symm

end Gen

section Level

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

/-- A pole at `x = Q ∩ R0` is a pole at the prime `Q ∩ B_L` of every finite level. -/
theorem one_lt_valuation_level {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [IsDedekindDomain (integralClosure R0 L)] [IsFractionRing (integralClosure R0 L) L]
    {Q : Ideal (proChart A K R0)} (x : HeightOneSpectrum R0)
    (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    (P : HeightOneSpectrum (integralClosure R0 L)) (hP : P.asIdeal = Q.comap (inclU R0 hLU))
    {a : K} (ha : 1 < x.valuation K a) : 1 < P.valuation L (algebraMap K L a) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact not_lt_of_ge zero_le' ha
  have hinv : x.valuation K a⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ ha
  obtain ⟨n, d, hnd⟩ := x.exists_primeCompl_mul_eq_of_integer a⁻¹ hinv.le
  have hn : n ∈ x.asIdeal := by
    refine (x.valuation_lt_one_iff_mem (K := K) n).1 ?_
    show x.valuation K (algebraMap R0 K n) < 1
    rw [← hnd, map_mul, (x.valuation_eq_one_iff_notMem (K := K)).2 d.2, mul_one]
    exact hinv
  have hmem : ∀ r : R0, algebraMap R0 (integralClosure R0 L) r ∈ P.asIdeal ↔ r ∈ x.asIdeal := by
    intro r
    rw [hP, hx, Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  have h1 : P.valuation L (algebraMap _ L (algebraMap R0 (integralClosure R0 L) (d : R0))) = 1 :=
    (P.valuation_eq_one_iff_notMem (K := L)).2 fun h => d.2 ((hmem d).1 h)
  have h2 : P.valuation L (algebraMap _ L (algebraMap R0 (integralClosure R0 L) n)) < 1 :=
    (P.valuation_lt_one_iff_mem (K := L) _).2 ((hmem n).2 hn)
  have hL : (algebraMap K L a)⁻¹ * algebraMap _ L (algebraMap R0 (integralClosure R0 L) (d : R0)) =
      algebraMap _ L (algebraMap R0 (integralClosure R0 L) n) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R0 K L, IsScalarTower.algebraMap_apply R0 K L n, ← map_inv₀, ← map_mul, hnd]
  rw [← hL, map_mul, h1, mul_one, map_inv₀] at h2
  have hpos : 0 < P.valuation L (algebraMap K L a) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 ha0))
  exact (inv_lt_one₀ hpos).1 h2

end Level

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Swan_GlobV =====
section

/-!
# S4-Swan (K2), part 13: the `P`-adic additive valuation and the local data of an inertia group

For a Dedekind domain `S` with fraction field `L` and a height-one prime `P`, `adicAdd P` is the `P`-adic
valuation of `L` as an `AddValuation L (WithTop ℤ)` (`-log` of Mathlib's multiplicative `P.valuation L`).
It has a uniformizer, integral elements are approximated by elements of `S` modulo `P`, and it is invariant
under every automorphism of `S` (compatibly extended to `L`) that stabilizes `P`.

If a finite group `G` is a Galois group for `S / R` (`IsGaloisGroup G R S`) and `S ⧸ P` is finite, every element
of `S` is congruent mod `P` to an element fixed by the inertia group `I = P.inertia G` (the residue field
extension of `S` over `S^I` is trivial: `card_stabilizer_eq_card_inertia_mul_finrank` with stabilizer = inertia
= `I`). Hence `(I, L, adicAdd P)` is local data (`inertiaLocData`), so `Swan.LocData.ramFn` applies.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero
open scoped Pointwise

namespace RamanujanPetersson.Swan

section AdicAdd

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)

open Classical in
/-- `-log` of the `P`-adic valuation, with `⊤` at `0`. -/
def negLogV (x : L) : WithTop ℤ :=
  if x = 0 then ⊤ else ((-log (P.valuation L x) : ℤ) : WithTop ℤ)

theorem negLogV_of_ne {x : L} (hx : x ≠ 0) :
    negLogV P x = ((-log (P.valuation L x) : ℤ) : WithTop ℤ) := if_neg hx

theorem negLogV_zero : negLogV P (0 : L) = ⊤ := if_pos rfl

theorem negLogV_mul (x y : L) : negLogV P (x * y) = negLogV P x + negLogV P y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, negLogV_zero, WithTop.top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, negLogV_zero, WithTop.add_top]
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h2 : P.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [negLogV_of_ne P (mul_ne_zero hx hy), negLogV_of_ne P hx, negLogV_of_ne P hy, map_mul,
    log_mul h1 h2, neg_add, WithTop.coe_add]

theorem negLogV_add (x y : L) : min (negLogV P x) (negLogV P y) ≤ negLogV P (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add]; exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero]; exact min_le_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, negLogV_zero]; exact le_top
  have h := Valuation.map_add (P.valuation L) x y
  have h1 : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h2 : P.valuation L y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have h3 : P.valuation L (x + y) ≠ 0 := (Valuation.ne_zero_iff _).2 hxy
  rw [← exp_log h1, ← exp_log h2, ← exp_log h3, le_max_iff, exp_le_exp, exp_le_exp] at h
  rw [negLogV_of_ne P hx, negLogV_of_ne P hy, negLogV_of_ne P hxy, ← WithTop.coe_min,
    WithTop.coe_le_coe]
  rcases h with h | h
  · exact min_le_of_left_le (by omega)
  · exact min_le_of_right_le (by omega)

/-- The `P`-adic valuation of `L = Frac S` as an additive valuation with values in `ℤ ∪ {⊤}`. -/
def adicAdd : AddValuation L (WithTop ℤ) :=
  AddValuation.of (negLogV P) (negLogV_zero P)
    (by rw [negLogV_of_ne P one_ne_zero, map_one, log_one, neg_zero, WithTop.coe_zero])
    (negLogV_add P) (negLogV_mul P)

theorem adicAdd_apply (x : L) : adicAdd P x = negLogV P x := rfl

section Smul

variable {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
include hc

end Smul

end AdicAdd

section Residue

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

end Residue

section Inertia

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

end Inertia

end RamanujanPetersson.Swan

end

end

-- ===== S4.Def_RP_Swan_GlobE =====
section

/-!
# S4-Swan (K2), part 14: ramification index = order of the inertia group, for adic valuations

Let `S / A` be a finite torsion-free extension of Dedekind domains with Galois group `H` (`IsGaloisGroup H A S`),
`Q` a height-one prime of `S` with finite residue field and `p = Q ∩ A`. Then the ramification index of `Q`
over `p` is `|Q.inertia H|` (`card_inertia_eq_ramificationIdxIn`), so the `Q`-adic valuation restricts to
`|Q.inertia H|` times the `p`-adic one (`intValuation_liesOver`, `valuation_liesOver`). We record this for the
additive valuations `adicAdd` of `GlobV`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero

namespace RamanujanPetersson.Swan

section Core

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  (H : Type*) [Group H] [Finite H] [MulSemiringAction H S] [IsGaloisGroup H A S]
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

omit [Module.IsTorsionFree A S] [Finite (S ⧸ Q.asIdeal)] in
theorem liesOver_under : Q.asIdeal.LiesOver (Q.under A).asIdeal := ⟨rfl⟩

attribute [local instance] Ideal.Quotient.field in
/-- The ramification index of `Q` over `Q ∩ A` is the order of the inertia group of `Q` in `H`. -/
theorem ramificationIdx'_under_eq_card :
    (Q.under A).asIdeal.ramificationIdx' Q.asIdeal = Nat.card (Q.asIdeal.inertia H) := by
  have := liesOver_under (A := A) Q
  have : (Q.under A).asIdeal.IsMaximal := (Q.under A).isMaximal
  have : Finite (A ⧸ (Q.under A).asIdeal) :=
    Finite.of_injective (algebraMap (A ⧸ (Q.under A).asIdeal) (S ⧸ Q.asIdeal)) (RingHom.injective _)
  have : Finite (Q.under A).asIdeal.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField (Q.under A).asIdeal).2
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) (Q.under A).asIdeal Q.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under A).asIdeal Q.asIdeal H,
    Ideal.ramificationIdx'_eq_ramificationIdx (Q.under A).asIdeal Q.asIdeal (Q.under A).ne_bot]

theorem intValuation_algebraMap_eq_pow (c : A) :
    Q.intValuation (algebraMap A S c) =
      (Q.under A).intValuation c ^ Nat.card (Q.asIdeal.inertia H) := by
  have := liesOver_under (A := A) Q
  rw [← ramificationIdx'_under_eq_card (A := A) H Q]
  exact (HeightOneSpectrum.intValuation_liesOver (Q.under A) Q c).symm

variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]

/-- Additive form on `A`: `v_Q(c) = |I| · k` for a nonzero `c ∈ A`. -/
theorem exists_adicAdd_algebraMap_eq (c : A) (hc : c ≠ 0) :
    ∃ k : ℤ, adicAdd Q (algebraMap S L (algebraMap A S c)) =
      (((Nat.card (Q.asIdeal.inertia H) : ℤ) * k : ℤ) : WithTop ℤ) := by
  have hc' : algebraMap S L (algebraMap A S c) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective S L)]
    exact (FaithfulSMul.algebraMap_injective A S).ne_iff' (map_zero _) |>.2 hc
  refine ⟨-log ((Q.under A).intValuation c), ?_⟩
  rw [adicAdd_apply, negLogV_of_ne Q hc', HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_algebraMap_eq_pow H Q c, log_pow, nsmul_eq_mul]
  congr 1
  ring

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A S L]

/-- Additive form on `K = Frac A`: `v_Q(x) = |I| · v_p(x)`. -/
theorem adicAdd_algebraMap_eq (x : K) (m : ℤ) (hm : adicAdd (Q.under A) x = m) :
    adicAdd Q (algebraMap K L x) =
      (((Nat.card (Q.asIdeal.inertia H) : ℤ) * m : ℤ) : WithTop ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hm
    exact WithTop.top_ne_coe hm
  have hx' : algebraMap K L x ≠ 0 := (map_ne_zero _).2 hx
  have := liesOver_under (A := A) Q
  rw [adicAdd_apply, negLogV_of_ne (L := K) _ hx] at hm
  have hm' : -log ((Q.under A).valuation K x) = m := WithTop.coe_inj.1 hm
  rw [adicAdd_apply, negLogV_of_ne Q hx', ← HeightOneSpectrum.valuation_liesOver L (Q.under A) Q x,
    ramificationIdx'_under_eq_card (A := A) H Q, log_pow, nsmul_eq_mul, ← hm']
  congr 1
  ring

end Core

end RamanujanPetersson.Swan

end

end

-- ===== S4.Def_RP_Swan_GlobF =====
section

/-!
# S4-Swan (K2), part 15: fixed rings of Dedekind domains, and fixed fractions

* `isDedekindDomain_fixed`: if `S` is a Dedekind domain, finite and torsion-free over a Dedekind domain `R`, and
  `H` is a group of `R`-automorphisms of `S`, then the fixed ring `S^H = FixedPoints.subalgebra R S H` is a
  Dedekind domain (Noetherian as an `R`-submodule of `S`, dimension one as an integral extension of `R`,
  integrally closed because `S` is and `H` fixes the integral closure inside `Frac (S^H)`), and `S` is finite
  over it.
* `exists_fixed_mul_eq`: for a finite group `H` acting compatibly on `S` and `L = Frac S`, every `H`-fixed
  `x ∈ L` is a quotient of `H`-fixed elements of `S` (multiply by the norm `∏_h h b` of a denominator `b`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Swan

section FixedRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (H : Subgroup G)

theorem mem_fixedSubalgebra_iff (s : S) :
    s ∈ FixedPoints.subalgebra R S H ↔ ∀ h : H, h • s = s := Iff.rfl

variable [Module.Finite R S]

theorem isIntegral_fixedSubalgebra :
    Algebra.IsIntegral R (FixedPoints.subalgebra R S H) :=
  Algebra.IsIntegral.of_injective (FixedPoints.subalgebra R S H).val Subtype.val_injective

theorem finite_fixed : Module.Finite (FixedPoints.subalgebra R S H) S :=
  Module.Finite.of_restrictScalars_finite R _ S

variable [IsDedekindDomain R] [IsDedekindDomain S]

/-- The fixed ring of a group of automorphisms of a finite Dedekind extension is Dedekind. -/
theorem isDedekindDomain_fixed : IsDedekindDomain (FixedPoints.subalgebra R S H) := by
  set A := FixedPoints.subalgebra R S H
  have hN : IsNoetherian R A := isNoetherian_of_injective A.val.toLinearMap Subtype.val_injective
  have : Algebra.IsIntegral R A := isIntegral_fixedSubalgebra H
  refine (isDedekindDomain_iff A (FractionRing A)).2 ⟨inferInstance, isNoetherian_of_tower R hN,
    Ring.DimensionLEOne.of_isIntegral R A, ?_⟩
  intro x hx
  let FS := FractionRing S
  have hinj : Function.Injective (algebraMap A FS) := by
    rw [IsScalarTower.algebraMap_eq A S FS]
    exact (IsFractionRing.injective S FS).comp Subtype.val_injective
  let f : FractionRing A →ₐ[A] FS := IsFractionRing.liftAlgHom (g := Algebra.ofId A FS) hinj
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (IsIntegral.tower_top (A := S) (hx.map f))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : (b : S) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have hfab : f (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) =
      algebraMap S FS a / algebraMap S FS b := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply A S FS,
      IsScalarTower.algebraMap_apply A S FS]
    rfl
  have hsb : s * b = a := by
    apply IsFractionRing.injective S FS
    have hb' : algebraMap S FS b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S FS)).2 hb0
    rw [map_mul, hs, hfab, div_mul_cancel₀ _ hb']
  have hfix : ∀ σ : H, σ • s = s := by
    intro σ
    have h1 : σ • (s * (b : S)) = s * b := by rw [hsb]; exact a.2 σ
    rw [smul_mul', b.2 σ] at h1
    exact mul_right_cancel₀ hb0 h1
  refine ⟨⟨s, hfix⟩, f.toRingHom.injective ?_⟩
  change f (algebraMap A (FractionRing A) ⟨s, hfix⟩) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A S FS]
  exact hs

end FixedRing

section NormTrick

variable {S : Type*} [CommRing S] [IsDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (H : Subgroup G) [Finite H]
include hc

/-- An `H`-fixed element of `L = Frac S` is a quotient of `H`-fixed elements of `S`. -/
theorem exists_fixed_mul_eq (x : L) (hx : ∀ h ∈ H, h • x = x) :
    ∃ c1 c2 : S, (∀ h ∈ H, h • c1 = c1) ∧ (∀ h ∈ H, h • c2 = c2) ∧ c2 ≠ 0 ∧
      x * algebraMap S L c2 = algebraMap S L c1 := by
  classical
  letI := Fintype.ofFinite H
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap S L b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).2 hb0
  set P : S := ∏ h ∈ Finset.univ.erase (1 : H), (h : G) • b with hP
  have hc2 : ∏ h : H, (h : G) • b = b * P := by
    rw [hP, ← Finset.mul_prod_erase Finset.univ (fun h : H => (h : G) • b) (Finset.mem_univ 1)]
    simp
  have hfix2 : ∀ g ∈ H, g • ∏ h : H, (h : G) • b = ∏ h : H, (h : G) • b := by
    intro g hg
    rw [Finset.smul_prod']
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : H)) _ _ (fun h => ?_)
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, Subgroup.coe_mk, mul_smul]
  have hmul : algebraMap S L a / algebraMap S L b * algebraMap S L (∏ h : H, (h : G) • b) =
      algebraMap S L (a * P) := by
    rw [hc2, map_mul, map_mul, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hb']
  refine ⟨a * P, ∏ h : H, (h : G) • b, fun g hg => ?_, hfix2, ?_, hmul⟩
  · apply IsFractionRing.injective S L
    rw [← hc, ← hmul, smul_mul', hx g hg, hc, hfix2 g hg]
  · rw [Finset.prod_ne_zero_iff]
    exact fun h _ => (smul_ne_zero_iff_ne _).2 hb0

end NormTrick

end RamanujanPetersson.Swan

end

end

-- ===== S4.Def_RP_Swan_GlobVal =====
section

/-!
# S4-Swan (K2), part 16: the valuation condition for subgroups of an inertia group

For `S / R` finite Dedekind with Galois group `G`, `Q` a height-one prime of `S` with finite residue field, and
`H ≤ Q.inertia G`, every nonzero `H`-fixed `x ∈ L = Frac S` has `v_Q(x) ∈ |H| ℤ`
(`exists_adicAdd_fixed_eq`): write `x = c1 / c2` with `c_i ∈ S^H` (`exists_fixed_mul_eq`), and use that
`S^H` is Dedekind (`isDedekindDomain_fixed`) with `e(Q | Q ∩ S^H) = |Q.inertia H| = |H|` (`GlobE`).
For the local data `inertiaLocData` this is the `val` condition of `QData` and of `Tower`
(`inertiaLocData_val`), and the norm of the uniformizer is quotient data (`inertiaQData`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace RamanujanPetersson.Swan

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L]

end LocData

section Val

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

include R hc in
/-- For `H ≤ Q.inertia G`, `v_Q(x) ∈ |H| ℤ` for every nonzero `H`-fixed `x ∈ L`. -/
theorem exists_adicAdd_fixed_eq (H : Subgroup G) (hH : H ≤ Q.asIdeal.inertia G) (x : L)
    (hx : ∀ h ∈ H, h • x = x) (hx0 : x ≠ 0) :
    ∃ k : ℤ, adicAdd Q x = (((Nat.card H : ℤ) * k : ℤ) : WithTop ℤ) := by
  obtain ⟨c1, c2, h1, h2, hc2, hx12⟩ := exists_fixed_mul_eq hc H x hx
  let A := FixedPoints.subalgebra R S H
  haveI : IsDedekindDomain A := isDedekindDomain_fixed H
  haveI : Module.Finite A S := finite_fixed H
  have hI : Nat.card (Q.asIdeal.inertia H) = Nat.card H := by
    have : Q.asIdeal.inertia H = ⊤ := by
      ext σ
      simp only [Subgroup.mem_top, iff_true]
      exact hH σ.2
    rw [this, Subgroup.card_top]
  have hinj := IsFractionRing.injective S L
  have hc1 : c1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx12
    exact hx0 ((mul_eq_zero.1 hx12).resolve_right ((map_ne_zero_iff _ hinj).2 hc2))
  let a1 : A := ⟨c1, (mem_fixedSubalgebra_iff H c1).2 fun h => h1 h h.2⟩
  let a2 : A := ⟨c2, (mem_fixedSubalgebra_iff H c2).2 fun h => h2 h h.2⟩
  obtain ⟨k1, hk1⟩ := exists_adicAdd_algebraMap_eq (L := L) H Q a1
    (fun h => hc1 (congrArg Subtype.val h))
  obtain ⟨k2, hk2⟩ := exists_adicAdd_algebraMap_eq (L := L) H Q a2
    (fun h => hc2 (congrArg Subtype.val h))
  rw [hI] at hk1 hk2
  change adicAdd Q (algebraMap S L c1) = _ at hk1
  change adicAdd Q (algebraMap S L c2) = _ at hk2
  have hv := congrArg (adicAdd Q) hx12
  rw [AddValuation.map_mul, hk1, hk2] at hv
  obtain ⟨t, ht⟩ : ∃ t : ℤ, adicAdd Q x = t := by
    induction h : adicAdd Q x with
    | top => exact absurd ((AddValuation.top_iff _).1 h) hx0
    | coe t => exact ⟨t, rfl⟩
  rw [ht, ← WithTop.coe_add, WithTop.coe_inj] at hv
  refine ⟨k1 - k2, ?_⟩
  rw [ht, WithTop.coe_inj]
  linarith [mul_sub (Nat.card H : ℤ) k1 k2]

end Val

end RamanujanPetersson.Swan

end

end

-- ===== S4.Def_RP_TameInertia_Count =====
section

/-!
# Tame inertia, part Count: the inertia orbit of an `N`-th root of the small root is full (S4-PD item (2), T8 count)

Let `S / R` be a finite Galois extension of Dedekind domains with group `G`, `P` a prime of `S` with finite residue
field, `F = a ∈ K = Frac R` a pole of order `c` at `P ∩ R` with `gcd(c, N) = 1`, `w` the unique root of
`X^(p+1) - F X + 1` with `v_P(w) < 1`, and `z^N = w`. Then `v_P(w) = |I| c` (`adicAdd_small_root`), while `v_P(z)`
is divisible by the order of the stabilizer `H` of `z` in `I = I(P)` (Swan `exists_adicAdd_fixed_eq`), so
`N |H| k = |I| c = |I : H| |H| c`, hence `N ∣ |I z|`; the orbit lies in the `N`-th roots of `w`, so it is all of them:
`∃ τ ∈ I, τ z = ζ z` for every `ζ` with `ζ^N = 1` (`exists_inertia_smul_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain WithZero

namespace RamanujanPetersson
namespace TameInertia

open Swan

noncomputable section

section Small

variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L]

/-- The small root of the trinomial has `v_P(w) = -v_P(F)` (additive valuations). -/
theorem adicAdd_small_root (P : HeightOneSpectrum S) {p : ℕ} (hp : 0 < p) {F w : L}
    (hF : 1 < P.valuation L F) (hw : (trin p F).IsRoot w) (hwv : P.valuation L w < 1) (t : ℤ)
    (ht : adicAdd P F = ((-t : ℤ) : WithTop ℤ)) : adicAdd P w = (t : WithTop ℤ) := by
  have hw' := (trin_isRoot_iff p F w).1 hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw'
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [map_zero] at hF
    exact not_lt_of_ge zero_le hF
  have hwv0 : P.valuation L w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
  have hFv0 : P.valuation L F ≠ 0 := (Valuation.ne_zero_iff _).2 hF0
  have hc0 : 0 < log (P.valuation L F) := by
    rw [← exp_log hFv0, ← exp_zero, exp_lt_exp] at hF
    exact hF
  have ha0 : log (P.valuation L w) < 0 := by
    rw [← exp_log hwv0, ← exp_zero, exp_lt_exp] at hwv
    exact hwv
  rcases trin_val_cases (P.valuation L) hw' (exp_log hwv0).symm (exp_log hFv0).symm hc0 with h | h
  · rw [adicAdd_apply, negLogV_of_ne P hF0] at ht
    have ht' := WithTop.coe_inj.1 ht
    rw [adicAdd_apply, negLogV_of_ne P hw0, h, WithTop.coe_inj]
    linarith
  · exfalso
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have := mul_neg_of_pos_of_neg hp' ha0
    linarith

end Small

section Count

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {K L : Type*} [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (P : HeightOneSpectrum S) [Finite (S ⧸ P.asIdeal)]

include R hc in
/-- **T8 count.** The inertia orbit of an `N`-th root `z` of the small root `w` contains `ζ z` for every
`N`-th root of unity `ζ`, when the pole order `c` of `a` at `P ∩ R` is prime to `N`. -/
theorem exists_inertia_smul_eq {p : ℕ} (hp : 0 < p) {N : ℕ} (hN : 0 < N) {a : K} {c : ℕ}
    (hcN : Nat.Coprime c N) (ha : adicAdd (P.under R) a = ((-(c : ℤ) : ℤ) : WithTop ℤ))
    (hF : 1 < P.valuation L (algebraMap K L a)) (hs : (trin p (algebraMap K L a)).Splits)
    (hfix : ∀ σ : G, σ • algebraMap K L a = algebraMap K L a)
    {w z ζ : L} (hw : (trin p (algebraMap K L a)).IsRoot w) (hwv : P.valuation L w < 1)
    (hz : z ^ N = w) (hζ : ζ ^ N = 1) :
    ∃ τ ∈ P.asIdeal.inertia G, τ • z = ζ * z := by
  classical
  have hw0 : w ≠ 0 := by
    rintro rfl
    have hw' := (trin_isRoot_iff p _ _).1 hw
    simp at hw'
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact hw0 hz.symm
  -- the stabilizer of `z` in the inertia group
  set I := P.asIdeal.inertia G with hIdef
  let St : Subgroup I := MulAction.stabilizer I z
  let H : Subgroup G := St.map I.subtype
  have hH : H ≤ I := Subgroup.map_subtype_le _
  have hzH : ∀ h ∈ H, h • z = z := by
    rintro _ ⟨h, hh, rfl⟩
    exact hh
  have hHSt : Nat.card H = Nat.card St := Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcard : Nat.card St * (MulAction.orbit I z).ncard = Nat.card I := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.card_mul_index St
  -- valuations
  obtain ⟨k, hk⟩ := exists_adicAdd_fixed_eq (R := R) hc P H hH z hzH hz0
  have hFv := adicAdd_algebraMap_eq (A := R) (L := L) G P a (-(c : ℤ)) ha
  have h1 : adicAdd P w = (((N : ℤ) * ((Nat.card H : ℤ) * k) : ℤ) : WithTop ℤ) := by
    rw [← hz, AddValuation.map_pow, hk, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have h2 : adicAdd P w = (((Nat.card I : ℤ) * c : ℤ) : WithTop ℤ) :=
    adicAdd_small_root P hp hF hw hwv _ (by rw [hFv]; congr 1; ring)
  have h3 : (N : ℤ) * ((Nat.card H : ℤ) * k) = (Nat.card I : ℤ) * c := WithTop.coe_inj.1 (h1.symm.trans h2)
  set O := (MulAction.orbit I z).ncard with hOdef
  have hH0 : (Nat.card H : ℤ) ≠ 0 := by
    have : 0 < Nat.card H := Nat.card_pos
    exact_mod_cast this.ne'
  have h4 : (Nat.card H : ℤ) * ((N : ℤ) * k) = (Nat.card H : ℤ) * ((O : ℤ) * c) := by
    rw [← hcard, ← hHSt] at h3
    push_cast at h3
    linear_combination h3
  have h5 := mul_left_cancel₀ hH0 h4
  have h6 : (N : ℤ) ∣ ((O * c : ℕ) : ℤ) := ⟨k, by push_cast; linarith⟩
  have h7 : N ∣ O := Nat.Coprime.dvd_of_dvd_mul_right hcN.symm (Int.natCast_dvd_natCast.1 h6)
  have hOfin : (MulAction.orbit I z).Finite := Set.finite_range _
  have hOpos : 0 < O := (Set.ncard_pos hOfin).2 ⟨z, MulAction.mem_orbit_self z⟩
  have hNO : N ≤ O := Nat.le_of_dvd hOpos h7
  -- the orbit lies in the `N`-th roots of `w`
  by_contra hne
  have hmem : ζ * z ∈ (nthRoots N w).toFinset := by
    rw [Multiset.mem_toFinset, mem_nthRoots hN, mul_pow, hζ, one_mul, hz]
  have hsub : MulAction.orbit I z ⊆ (((nthRoots N w).toFinset.erase (ζ * z) : Finset L) : Set L) := by
    rintro y ⟨τ, rfl⟩
    rw [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Multiset.mem_toFinset,
      mem_nthRoots hN]
    refine ⟨?_, fun h => hne ⟨τ, τ.2, h⟩⟩
    have hτw : (τ : G) • w = w := fix_small_root hc P hp hF hs τ.2 (hfix τ) hw hwv
    show ((τ : G) • z) ^ N = w
    rw [← smul_pow', hz, hτw]
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, Finset.card_erase_of_mem hmem] at hle
  have hcardN : (nthRoots N w).toFinset.card ≤ N := (Multiset.toFinset_card_le _).trans (card_nthRoots N w)
  omega

end Count

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Pole =====
section

/-!
# Tame inertia, part Pole: a pole element of order `≡ 1 mod N` (S4-PD item (2), T4)

Let `A` be a domain with fraction field `K` and `v` a height-one prime of a Dedekind domain `R0` with the same
fraction field. If some `a ∈ A` has a pole at `v` (`1 < v(a)`), then for every `N = M + 1 ≥ 1` some `f ∈ A` has
a pole of order exactly `N n + 1` with `n > 0` (`exists_pole_mod`). Proof: write a uniformizer as `b / c`
with `b, c ∈ A`; for `k` large, `f₁ = a^k b` and `f₂ = a^k c` have consecutive pole orders `n₀, n₀ + 1`, and
`f₁^M f₂` has pole order `N n₀ + 1`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace TameInertia

open IsDedekindDomain

noncomputable section

section Pole

variable {A K R0 : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

theorem val_exp_of_ne_zero (v : HeightOneSpectrum R0) {x : K} (hx : x ≠ 0) :
    ∃ α : ℤ, v.valuation K x = WithZero.exp α :=
  ⟨WithZero.log (v.valuation K x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩

/-- **T4.** From one pole at `v` in `A`, a pole of order exactly `(M + 1) n + 1` with `n > 0`. -/
theorem exists_pole_mod (v : HeightOneSpectrum R0) (M : ℕ) {a : A}
    (ha : 1 < v.valuation K (algebraMap A K a)) :
    ∃ (f : A) (n : ℕ), 0 < n ∧
      v.valuation K (algebraMap A K f) = WithZero.exp ((((M + 1) * n + 1 : ℕ)) : ℤ) := by
  have ha0 : algebraMap A K a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact not_lt_of_ge zero_le' ha
  obtain ⟨α, hα⟩ := val_exp_of_ne_zero v ha0
  have hα0 : 0 < α := by
    rw [hα, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    exact ha
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective A π
  have hc0 : algebraMap A K c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  obtain ⟨γ, hγ⟩ := val_exp_of_ne_zero v hc0
  have hb : v.valuation K (algebraMap A K b) = WithZero.exp (γ - 1) := by
    have h : algebraMap A K b = π * algebraMap A K c := by
      rw [← hbc]
      field_simp
    rw [h, map_mul, hπ, hγ, ← WithZero.exp_add]
    congr 1
    ring
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = (2 - γ).toNat := ⟨_, rfl⟩
  have hk1 : 2 - γ ≤ (k : ℤ) := by rw [hk]; exact Int.self_le_toNat _
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, n0 = (k : ℤ) * α + (γ - 1) := ⟨_, rfl⟩
  have hn0pos : 0 < n0 := by
    have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    have : (k : ℤ) ≤ (k : ℤ) * α := by nlinarith
    omega
  refine ⟨(a ^ k * b) ^ M * (a ^ k * c), n0.toNat, by omega, ?_⟩
  simp only [map_mul, map_pow, hα, hb, hγ, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  push_cast
  rw [Int.toNat_of_nonneg hn0pos.le, hn0]
  simp only [nsmul_eq_mul]
  ring

/-- The pole order `(M + 1) n + 1` is prime to `M + 1`. -/
theorem coprime_pole_order (M n : ℕ) : Nat.Coprime ((M + 1) * n + 1) (M + 1) := by
  exact (Nat.coprime_mul_left_add_left 1 (M + 1) n).2 (Nat.coprime_one_left _)

end Pole

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Lift =====
section

/-!
# Tame inertia, part Lift: inertia at a GIVEN prime of the pro-chart surjects onto finite-level inertia (S4-PD (2), T8 lift)

* `exists_inertia_lift`: for a finite Galois level `L ≤ K_U` and a prime `Q` of the pro-chart, every `τ` in the inertia
  group of `Q ∩ B_L` is the restriction of some `g` in the inertia group of `Q` (the argument of `CP4a.bdryLift`,
  kept at the given prime `Q`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- Inertia lifting at a given prime `Q` of the pro-chart. -/
theorem exists_inertia_lift {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] [IsGalois K L] {Q : Ideal (proChart A K R0)} [Q.IsPrime] {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ (Q.comap (inclU R0 hLU)).inertia (L ≃ₐ[K] L)) :
    ∃ g ∈ Q.inertia (Pi1 A K), ∀ y : L,
      g (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (τ y) := by
  obtain ⟨g1, hg1L⟩ := CP4a.exists_lift_level hLU τ
  obtain ⟨h, hhH, hh⟩ := CP4a.exists_fix_mul_mem_inertia hLU Q g1 fun b hb => by
    obtain ⟨y, rfl⟩ := CP4a.exists_inclU_eq hLU b hb
    exact CP4a.inclU_sub_mem hLU hτ rfl hg1L y
  refine ⟨g1 * h, AddSubgroup.mem_inertia.2 hh, fun y => ?_⟩
  have hfix : h (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hhH _ ((IntermediateField.mem_restrict hLU _).2 y.2)
  rw [AlgEquiv.mul_apply, hfix, hg1L]

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_TameInertia_Stab =====
section

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


end

-- ===== S4.Def_RP_TameInertia_Main =====
section

/-!
# Tame inertia, part Main: `Hom(I_x, ℤ/N) = ℤ/N(-1)` (S4-PD item (2))

At a boundary prime `Q` of the pro-chart (a pole at `x = Q ∩ R0`), with `N` a unit and `ζ` a primitive `N`-th root of
unity fixed by inertia: the Kummer character `θ = kchar ζ Z` of the radical `Z` of `exists_inertia_zeta_mul` is a
locally constant homomorphism `I(Q) → ℤ/N` taking the value `1`, every locally constant homomorphism
`χ : I(Q) → ℤ/N` is `k θ` for a unique `k`, and `θ` is twisted by the cyclotomic character: for `φ ∈ Pi1` stabilising
`Q` with `φ ζ = ζ ^ w`, `θ σ = w θ (φ⁻¹ σ φ)` (`exists_tame_char`). So `Hom(I(Q), ℤ/N) ≅ ℤ/N(-1)` as a module over the
decomposition group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

theorem epow_one_eq {E : Type} [Field E] {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N) :
    epow ζ (1 : ZMod N) = ζ := by
  rw [epow, ZMod.val_one_eq_one_mod, pow_mod_N hζ, pow_one]

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

end

end TameInertia
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_KumAll =====
section

/-!
# S4-PD (4)/(5), E1 part K: the Kummer-closure property over every `E₀' ⊇ constFieldU`

* `constLevel_le_map_of_le`: the constant levels `K(𝔽_{p^m})` lie in every `E` over `E₀' ⊇ constFieldU`;
* `kumClosure_of_picDiv_of_le`: `PicDivU A K p l` gives `KumClosure l E₀' K_U` for every intermediate field
  `E₀' ⊇ constFieldU` of `K_U / K` (e.g. the fixed field of a closed subgroup of `π₁^geo`, such as a boundary inertia
  group). The proof of `kumClosure_of_picDiv` never used finiteness of `E` over the base, only `E ⊇ constFieldU`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField IsDedekindDomain RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh

noncomputable section

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  {p : ℕ} [Fact p.Prime] [CharP K p]

/-- `𝔽_{p^m} ⊆ constFieldU ⊆ E₀'`, so the constant level `K(𝔽_{p^m})` lies in every `E ⊇ E₀'`. -/
theorem constLevel_le_map_of_le {e m : ℕ} (hm : 0 < m) {E₀ : IntermediateField K (maxUnram A K)}
    (hE₀ : constFieldU A K (p ^ e) ≤ E₀) (E : IntermediateField E₀ (maxUnram A K)) :
    constLevel K p m ≤ (E.restrictScalars K).map (maxUnram A K).val := by
  have hCU : constLevel K p m ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup (constLevel_mem_unramSet A (p := p) hm)
  rw [constLevel, IntermediateField.adjoin_le_iff]
  intro x hx
  have hxC : x ∈ constLevel K p m := IntermediateField.subset_adjoin K _ hx
  have hxx : x ^ (p ^ m) = x := by
    rw [Polynomial.mem_rootSet] at hx
    have h2 := hx.2
    simp only [map_sub, map_pow, Polynomial.aeval_X] at h2
    exact sub_eq_zero.1 h2
  have hy : IsConst (p ^ e) (⟨x, hCU hxC⟩ : maxUnram A K) := ⟨m, hm, by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, show (p ^ e) ^ m = (p ^ m) ^ e by rw [← pow_mul, ← pow_mul, mul_comm]]
    exact pow_pow_eq_self hxx e⟩
  have hyE₀ : (⟨x, hCU hxC⟩ : maxUnram A K) ∈ E₀ := hE₀ (IntermediateField.subset_adjoin K _ hy)
  have hyE : (⟨x, hCU hxC⟩ : maxUnram A K) ∈ E := E.algebraMap_mem (⟨_, hyE₀⟩ : E₀)
  rw [IntermediateField.coe_map]
  exact ⟨_, hyE, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **The Kummer-closure property of `K_U / E₀'` for EVERY `E₀' ⊇ E₀ = constFieldU`** (no finiteness of `E₀'`
over `E₀`), from `Pic(V̄)/l = 0`. Same proof as `kumClosure_of_picDiv`. -/
theorem kumClosure_of_picDiv_of_le (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (e : ℕ) (l : ℕ) [NeZero l] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    {E₀ : IntermediateField K (maxUnram A K)} (hE₀ : constFieldU A K (p ^ e) ≤ E₀) :
    KumClosure l E₀ (maxUnram A K) := by
  intro E L _ _ hGal b hb
  haveI := hGal
  have hb' : ∀ σ : L ≃ₐ[E] L, ∃ c : L, σ (b : L) = c ^ l * (b : L) := by
    intro σ
    obtain ⟨c, hc⟩ := hb σ
    refine ⟨(c : L), ?_⟩
    have h1 := congrArg Units.val hc
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at h1
    change σ (b : L) / (b : L) = (c : L) ^ l at h1
    rw [← h1, div_mul_cancel₀ _ b.ne_zero]
  -- the finite level `ML ∋ b`
  obtain ⟨ML, hML, hβML⟩ := exists_unramSet_of_finite A K {(((b : L) : maxUnram A K) : AlgebraicClosure K)}
    (fun x hx => by rw [Finset.mem_singleton.1 hx]; exact ((b : L) : maxUnram A K).2)
  haveI : FiniteDimensional K ML := hML.1
  haveI : IsGalois K ML := hML.2.1
  have hLU : ML ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hML
  obtain ⟨bL, hbL⟩ : ∃ bL : ML, (bL : AlgebraicClosure K) = (((b : L) : maxUnram A K) : AlgebraicClosure K) :=
    ⟨⟨(((b : L) : maxUnram A K) : AlgebraicClosure K), hβML (IntermediateField.subset_adjoin K _ (by simp))⟩, rfl⟩
  -- `ME = ML ∩ E`
  obtain ⟨E', hE'⟩ : ∃ E' : IntermediateField K (AlgebraicClosure K),
      E' = (E.restrictScalars K).map (maxUnram A K).val := ⟨_, rfl⟩
  obtain ⟨ME, hMEd⟩ : ∃ ME : IntermediateField K (AlgebraicClosure K), ME = ML ⊓ E' := ⟨_, rfl⟩
  have hle : ME ≤ ML := by rw [hMEd]; exact inf_le_left
  have hMEE : ME ≤ E' := by rw [hMEd]; exact inf_le_right
  have hME : ∀ x : ML, (x : AlgebraicClosure K) ∈ ME ↔
      ∃ e : E, ((e : maxUnram A K) : AlgebraicClosure K) = x := by
    intro x
    rw [hMEd, IntermediateField.mem_inf]
    constructor
    · rintro ⟨-, h⟩
      rw [hE', ← SetLike.mem_coe, IntermediateField.coe_map] at h
      obtain ⟨y, hy, hyx⟩ := h
      exact ⟨⟨y, hy⟩, hyx⟩
    · rintro ⟨e, he⟩
      refine ⟨x.2, ?_⟩
      rw [hE', ← SetLike.mem_coe, IntermediateField.coe_map]
      exact ⟨(e : maxUnram A K), e.2, he⟩
  haveI : FiniteDimensional K ME := FiniteDimensional.of_injective
    (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).injective
  haveI : Algebra.IsSeparable K ME := Algebra.IsSeparable.of_algHom (F := K) (E' := ML) (IntermediateField.inclusion hle)
  haveI : IsFractionRing (integralClosure A ML) ML := integralClosure.isFractionRing_of_finite_extension (A := A) K ML
  haveI : IsDedekindDomain (integralClosure A ML) := integralClosure.isDedekindDomain (A := A) (K := K) (L := ML)
  haveI : IsFractionRing (integralClosure A ME) ME := integralClosure.isFractionRing_of_finite_extension (A := A) K ME
  haveI : IsDedekindDomain (integralClosure A ME) := integralClosure.isDedekindDomain (A := A) (K := K) (L := ME)
  have hb0 : (b : L) ≠ 0 := b.ne_zero
  -- valuations of `bL` on a fibre over `B_ME` agree mod `l`
  have horb : ∀ w w' : HeightOneSpectrum (integralClosure A ML), underI A hle w = underI A hle w' →
      (l : ℤ) ∣ WithZero.log (w.valuation ML bL) - WithZero.log (w'.valuation ML bL) := fun w w' h =>
    orbit_dvd A E₀ E hLU hle hME (l : ℤ) bL
      (fun τ hτ w => hgrp_dvd A hperf _ E L l hLU hML (b : L) hb0 hb' bL hbL hτ w) w w' h
  -- the divisor `D = v(b)` on `B_ME`
  let w₀ : HeightOneSpectrum (integralClosure A ME) → HeightOneSpectrum (integralClosure A ML) :=
    fun P => Classical.choose (exists_underI_eq A hle P)
  have hw₀ : ∀ P, underI A hle (w₀ P) = P := fun P => Classical.choose_spec (exists_underI_eq A hle P)
  let D : HeightOneSpectrum (integralClosure A ME) → ℤ := fun P => WithZero.log ((w₀ P).valuation ML bL)
  have hfin : (Function.support D).Finite := by
    refine ((finite_log_val_ne_zero (B := integralClosure A ML) bL).image (underI A hle)).subset ?_
    intro P hP
    exact ⟨w₀ P, hP, hw₀ P⟩
  obtain ⟨m, hm, a, ha0, hdivD⟩ := hPic ME inferInstance (hle.trans hLU) D hfin
  -- the level `M = ML ⊔ C_m`
  have hM : ML ⊔ constLevel K p m ∈ unramSet A K := sup_mem_unramSet A K hML (constLevel_mem_unramSet A hm)
  haveI : FiniteDimensional K ↥(ML ⊔ constLevel K p m) := hM.1
  haveI : IsGalois K ↥(ML ⊔ constLevel K p m) := hM.2.1
  have hMC : ME ⊔ constLevel K p m ≤ ML ⊔ constLevel K p m := sup_le_sup_right hle _
  have hLM : ML ≤ ML ⊔ constLevel K p m := le_sup_left
  haveI : FiniteDimensional K ↥(ME ⊔ constLevel K p m) := FiniteDimensional.of_injective
    (IntermediateField.inclusion hMC).toLinearMap (IntermediateField.inclusion hMC).injective
  haveI : Algebra.IsSeparable K ↥(ME ⊔ constLevel K p m) :=
    Algebra.IsSeparable.of_algHom (F := K) (E' := ↥(ML ⊔ constLevel K p m)) (IntermediateField.inclusion hMC)
  haveI : IsFractionRing (integralClosure A ↥(ML ⊔ constLevel K p m)) ↥(ML ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K _
  haveI : IsDedekindDomain (integralClosure A ↥(ML ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := A) (K := K) (L := ↥(ML ⊔ constLevel K p m))
  haveI : IsFractionRing (integralClosure A ↥(ME ⊔ constLevel K p m)) ↥(ME ⊔ constLevel K p m) :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K _
  haveI : IsDedekindDomain (integralClosure A ↥(ME ⊔ constLevel K p m)) :=
    integralClosure.isDedekindDomain (A := A) (K := K) (L := ↥(ME ⊔ constLevel K p m))
  have hbL0 : bL ≠ 0 := by
    intro h
    apply hb0
    have h2 : (((b : L) : maxUnram A K) : AlgebraicClosure K) = 0 := by rw [← hbL, h, ZeroMemClass.coe_zero]
    simpa using h2
  have hbM0 : IntermediateField.inclusion hLM bL ≠ 0 := (map_ne_zero _).2 hbL0
  have ha'0 : IntermediateField.inclusion hMC a ≠ 0 := (map_ne_zero _).2 ha0
  have hdiv : ∀ W : HeightOneSpectrum (integralClosure A ↥(ML ⊔ constLevel K p m)), (l : ℤ) ∣
      WithZero.log (W.valuation (↥(ML ⊔ constLevel K p m))
        (IntermediateField.inclusion hMC a * IntermediateField.inclusion hLM bL)) := by
    intro W
    rw [log_val_mul W ha'0 hbM0, ← val_underI A hMC hM hperf W a, ← val_underI A hLM hM hperf W bL]
    have hP : underI A hle (underI A hLM W) =
        underI A (le_sup_left : ME ≤ ME ⊔ constLevel K p m) (underI A hMC W) := by
      rw [underI_trans, underI_trans]
    have h1 : (l : ℤ) ∣ WithZero.log ((w₀ (underI A (le_sup_left : ME ≤ ME ⊔ constLevel K p m)
        (underI A hMC W))).valuation ML bL) +
        WithZero.log ((underI A hMC W).valuation (↥(ME ⊔ constLevel K p m)) a) := hdivD (underI A hMC W)
    have h2 := horb (underI A hLM W) _ (hP.trans (hw₀ _).symm)
    have h3 := dvd_add h1 h2
    rwa [show ∀ x y z : ℤ, x + y + (z - x) = y + z from fun x y z => by ring] at h3
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq
    (((IntermediateField.inclusion hMC a * IntermediateField.inclusion hLM bL : ↥(ML ⊔ constLevel K p m)) :
      AlgebraicClosure K)) (Nat.pos_of_ne_zero (NeZero.ne l))
  have hγU : γ ∈ maxUnram A K := root_mem_maxUnram_of_dvd A hM hN (mul_ne_zero ha'0 hbM0) hdiv hγ
  -- `a ∈ E`
  have haE' : (a : AlgebraicClosure K) ∈ E' := sup_le hMEE (by rw [hE']; exact constLevel_le_map_of_le A hm hE₀ E) a.2
  rw [← SetLike.mem_coe, hE', IntermediateField.coe_map] at haE'
  obtain ⟨y, hyE, hya⟩ := haE'
  refine ⟨⟨y, hyE⟩, ?_, ⟨γ, hγU⟩, Subtype.ext ?_⟩
  · intro h0
    apply ha0
    apply Subtype.ext
    have hy0 : y = 0 := congrArg Subtype.val h0
    rw [ZeroMemClass.coe_zero, ← hya, hy0, map_zero]
  · simp only [IntermediateField.coe_pow, IntermediateField.coe_mul, IntermediateField.algebraMap_apply]
    rw [hγ, IntermediateField.coe_mul]
    exact congrArg₂ (· * ·) hya.symm hbL

end

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_Cone_CdSub =====
section

/-!
# S4-PD (4)/(5), E1: `cd_l ≤ 1` for every CLOSED subgroup of `π₁^geo` (e.g. boundary inertia groups)

`Δ ≤ π₁^geo` closed. `E₀' := K_U^Δ ⊇ constFieldU`, `Gal(K_U/E₀') ≅ Δ` (closed: infinite Galois correspondence;
homeomorphism: compact to Hausdorff), and `hypL_of_field` applies to `K_U / E₀'`:
* C1: `isC1_subfield` (a subfield of an algebraic extension containing a C1 field is C1) with Tsen
  (`isC1_constFieldU`), giving `allC1_of_le`;
* Kummer closure: `kumClosure_of_picDiv_of_le` (from `PicDivU`).
Results: `hypL_of_closed`, **`h2_closed_eq_zero`** (`H²(Δ, M) = 0` for finite `lⁿ`-torsion `M` with open kernel),
`inertia_isClosed` (the inertia group `Q.inertia (Pi1 A K)` of a prime of the pro-chart is closed) and
`inertia_inf_isClosed` (so `I_s ∩ π₁^geo` is a closed subgroup of `π₁^geo`).
No local ramification theory is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Tsen RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh Topology

/-- A subfield `S` of an algebraic extension `Ω/F` containing the image of a C1 field `F` is C1. -/
theorem isC1_subfield {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (hF : IsC1 F) (S : Subfield Ω) (hS : ∀ x : F, algebraMap F Ω x ∈ S) : IsC1 S := by
  letI : Algebra F S := ((algebraMap F Ω).codRestrict S hS).toAlgebra
  let f : S →ₐ[F] Ω := { S.subtype with commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic F S := ⟨fun y => by
    obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := F) (y : Ω)
    refine ⟨q, hq0, f.toRingHom.injective ?_⟩
    rw [map_zero]
    show f (Polynomial.aeval y q) = 0
    rw [← Polynomial.aeval_algHom_apply]
    exact hq⟩
  exact hF.of_algebraic

section Closed

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  (Fq : Type) [Field Fq] [Fintype Fq] [Algebra Fq K] {e : ℕ} (he : 0 < e) (hq : Fintype.card Fq = p ^ e)
  [Algebra (RatFunc Fq) K] [IsScalarTower Fq (RatFunc Fq) K] [Algebra.IsAlgebraic (RatFunc Fq) K]

include he hq in
/-- Every extension of an intermediate field `E₀' ⊇ constFieldU` inside `K_U` is C1 (Tsen). -/
theorem allC1_of_le {E₀ : IntermediateField K (maxUnram A K)} (hE₀ : constFieldU A K (p ^ e) ≤ E₀) :
    AllC1 E₀ (maxUnram A K) := fun E _ => by
  haveI : Algebra.IsAlgebraic (constFieldU A K (p ^ e)) (maxUnram A K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (constFieldU A K (p ^ e))
  exact isC1_subfield (isC1_constFieldU A K Fq he hq) E.toSubfield
    (fun x => E.algebraMap_mem (⟨(x : maxUnram A K), hE₀ x.2⟩ : E₀))

/-- `Δ ≃* Gal(K_U / E₀)` when `Δ` is the fixing subgroup of `E₀`. -/
noncomputable def fixEquiv (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) : Δ ≃* Gal(maxUnram A K / E₀) :=
  (MulEquiv.subgroupCongr h.symm).trans (fixingSubgroupEquiv E₀)

theorem fixEquiv_apply (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) (σ : Δ) (x : maxUnram A K) :
    fixEquiv A E₀ Δ h σ x = (σ : Pi1 A K) x := rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem fixEquiv_continuous (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) : Continuous (fixEquiv A E₀ Δ h) := by
  refine continuous_of_continuousAt_one (fixEquiv A E₀ Δ h) ?_
  intro s hs
  rw [map_one] at hs
  rw [Filter.mem_map]
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff E₀ (maxUnram A K) s).1 hs
  have := hF
  let b := Module.finBasis E₀ F
  let W : Set Δ := Subtype.val ⁻¹' ⋂ i, (fixElt A K (b i : maxUnram A K) : Set (Pi1 A K))
  have hW : IsOpen W :=
    continuous_subtype_val.isOpen_preimage _ (isOpen_iInter_of_finite fun i => fixElt_isOpen A K _)
  have h1 : (1 : Δ) ∈ W :=
    show ((1 : Δ) : Pi1 A K) ∈ ⋂ i, (fixElt A K (b i : maxUnram A K) : Set (Pi1 A K)) from
      Set.mem_iInter.2 fun i => (fixElt A K _).one_mem
  refine Filter.mem_of_superset (hW.mem_nhds h1) ?_
  intro σ hσ
  have hσ' : ∀ i, (σ : Pi1 A K) (b i : maxUnram A K) = (b i : maxUnram A K) := fun i =>
    (Set.mem_iInter.1 (show (σ : Pi1 A K) ∈ ⋂ i, (fixElt A K (b i : maxUnram A K) : Set (Pi1 A K)) from hσ)) i
  apply hFs
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hlin : (fixEquiv A E₀ Δ h σ).toLinearMap ∘ₗ F.val.toLinearMap = F.val.toLinearMap :=
    b.ext fun i => hσ' i
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

theorem fixEquiv_symm_continuous (E₀ : IntermediateField K (maxUnram A K)) (Δ : Subgroup (Pi1 A K))
    (h : E₀.fixingSubgroup = Δ) [CompactSpace Δ] : Continuous (fixEquiv A E₀ Δ h).symm := by
  have : T2Space Gal(maxUnram A K / E₀) := krullTopology_t2
  exact (Continuous.homeoOfEquivCompactToT2 (f := (fixEquiv A E₀ Δ h).toEquiv)
    (fixEquiv_continuous A E₀ Δ h)).symm.continuous

include he hq in
/-- **`HypL l Δ`** (hence `cd_l(Δ) ≤ 1`) for every closed subgroup `Δ ≤ π₁^geo`, given `Pic(V̄)/l = 0`. -/
theorem hypL_of_closed (hperf : ∀ (P : Ideal A) [P.IsMaximal], PerfectField P.ResidueField)
    (l : ℕ) [Fact l.Prime] (hN : IsUnit (l : A)) (hPic : PicDivU A K p l)
    (Δ : Subgroup (Pi1 A K)) (hΔ : IsClosed (Δ : Set (Pi1 A K))) (hΔg : Δ ≤ pi1geo A K (p ^ e)) :
    HypL l Δ := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hl : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap A K) l]
    exact (hN.map (algebraMap A K)).ne_zero
  haveI : CompactSpace Δ := isCompact_iff_compactSpace.mp hΔ.isCompact
  have hfix : (fixedField Δ).fixingSubgroup = Δ :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨Δ, hΔ⟩ : ClosedSubgroup (Pi1 A K))
  have hE₀ : constFieldU A K (p ^ e) ≤ fixedField Δ :=
    (IntermediateField.le_iff_le Δ _).2 (hΔg.trans (fixingSubgroup_constFieldU A K (p ^ e)).ge)
  obtain ⟨ζ, hζ⟩ := exists_zeta_constFieldU A K he l hl
  have hζ' : IsPrimitiveRoot (IntermediateField.inclusion hE₀ ζ) l :=
    hζ.map_of_injective (IntermediateField.inclusion hE₀).injective
  exact hypL_of_equiv l (fixEquiv A _ Δ hfix) (fixEquiv_continuous A _ Δ hfix)
    (fixEquiv_symm_continuous A _ Δ hfix)
    (hypL_of_field l hζ' (allC1_of_le A Fq he hq hE₀) (kumClosure_of_picDiv_of_le A hperf e l hN hPic hE₀))

end Closed

section Inertia

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

/-- The orbit map `σ ↦ σ • x` on the pro-chart is locally constant (stabilisers are open). -/
theorem isLocallyConstant_smul_proChart (x : proChart A K R0) :
    IsLocallyConstant fun σ : Pi1 A K => σ • x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro σ
  have h1 : (fixElt A K (x : maxUnram A K) : Set (Pi1 A K)) ∈ 𝓝 (1 : Pi1 A K) :=
    (fixElt_isOpen A K _).mem_nhds (Subgroup.one_mem _)
  have h2 : Filter.Tendsto (fun τ : Pi1 A K => σ⁻¹ * τ) (𝓝 σ) (𝓝 1) := by
    have := (continuous_mul_left σ⁻¹).tendsto σ
    rwa [inv_mul_cancel] at this
  filter_upwards [h2 h1] with τ hτ
  have hτ' : (σ⁻¹ * τ) (x : maxUnram A K) = x := hτ
  apply Subtype.ext
  show τ (x : maxUnram A K) = σ (x : maxUnram A K)
  calc τ (x : maxUnram A K) = (σ * (σ⁻¹ * τ)) (x : maxUnram A K) := by rw [mul_inv_cancel_left]
    _ = σ (x : maxUnram A K) := by rw [AlgEquiv.mul_apply, hτ']

/-- The inertia group of an ideal of the pro-chart is closed in `π₁(U)`. -/
theorem inertia_isClosed (Q : Ideal (proChart A K R0)) :
    IsClosed ((Q.inertia (Pi1 A K) : Subgroup (Pi1 A K)) : Set (Pi1 A K)) := by
  have h : ((Q.inertia (Pi1 A K) : Subgroup (Pi1 A K)) : Set (Pi1 A K)) =
      ⋂ x : proChart A K R0, (fun σ : Pi1 A K => σ • x) ⁻¹' {y | y - x ∈ Q} := by
    ext σ
    exact ⟨fun h => Set.mem_iInter.2 fun x => h x, fun h x => Set.mem_iInter.1 h x⟩
  rw [h]
  exact isClosed_iInter fun x =>
    ⟨by rw [← Set.preimage_compl]; exact isLocallyConstant_smul_proChart A K R0 x _⟩

/-- `I_Q ∩ π₁^geo` is closed. -/
theorem inertia_inf_isClosed (q : ℕ) (Q : Ideal (proChart A K R0)) :
    IsClosed ((Q.inertia (Pi1 A K) ⊓ pi1geo A K q : Subgroup (Pi1 A K)) : Set (Pi1 A K)) := by
  rw [Subgroup.coe_inf]
  exact (inertia_isClosed A K R0 Q).inter (pi1geo_isClosed A K q)

end Inertia

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_TameInertia_Coef =====
section

/-!
# Tame inertia, part Coef: homomorphisms to `N`-torsion modules (S4-PD item (2), T9)

Abstract step: let `θ : Γ → ℤ/N` with `θ σ₀ = 1` be such that every locally constant homomorphism `Γ → ℤ/N` is a
multiple of `θ`. Then for every abelian group `M` killed by `N`, every locally constant homomorphism `χ : Γ → M` is
`σ ↦ (θ σ).val • χ σ₀` (`eq_val_nsmul_of_gen`), and conversely `σ ↦ (θ σ).val • m` is a locally constant homomorphism
for every `m` with value `m` at `σ₀`. So `Hom(Γ, M) ≅ M` by evaluation at `σ₀`. The proof separates points of `M` by
characters `M → ℚ/ℤ` (`CharacterModule`) and identifies the `N`-torsion of `ℚ/ℤ` with `ℤ/N` (`toQCircle`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Circ

variable (N : ℕ) [NeZero N]

end Circ

section Gen

variable {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] {N : ℕ} [NeZero N] {θ : Γ → ZMod N}
  {M : Type*} [AddCommGroup M] (hM : ∀ m : M, N • m = 0)

include hM in
theorem nsmul_mod_eq (k : ℕ) (m : M) : (k % N) • m = k • m := by
  conv_rhs => rw [← Nat.mod_add_div k N]
  rw [add_nsmul, mul_nsmul', hM, add_zero]

end Gen

end

end TameInertia
end RamanujanPetersson


end


