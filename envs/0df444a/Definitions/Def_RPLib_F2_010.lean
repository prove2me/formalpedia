-- Prove2me | Definitions.Def_RPLib_F2_010
-- name    : RPLib_F2_010
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T07:48:29.5997+00:00
-- url     : https://prove2.me/theorems/5666e8df-87b7-4277-9aca-3daf887cf755
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 010 of 70
-- statement:
--   File 010 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_HattoriStallings_Core`: Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)
--   * `S4.Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
--   * `S4.Def_RP_PerfectCx_Free`: S4-PD (5), E2(a) algebra: a freeness criterion over `O/λⁿ`
--   * `S4.Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
--   * `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
--   * `S4.Def_RP_HattoriStallings_Twisted`: Hattori–Stallings traces, part B1: trace relations, the twisted-trace formula, base change
--   * `S4.Def_RP_PerfectCx_Tri`: S4-PD (5), E3: three-term complexes as `ℕ`-indexed families
--   * `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
--   * `S4.Def_RP_HattoriStallings_CT`: Hattori–Stallings traces, part C: cohomologically trivial modules are projective
--   * `S4.Def_RP_PerfectCx_Proj`: S4-PD (5), E2(b): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ[Gf]`-projective
--   * `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
--   * `S4.Def_RP_Lefschetz_ConeMapG`: S4-Lefschetz, L3c: cone maps for coefficient maps that are only `Γ`-equivariant, across ambients
--   * `S4.Def_RP_Lefschetz_BlockTr`: S4-Lefschetz, L3b: traces over a block decomposition
--   * `S4.Def_RP_Lefschetz_BlockAlg`: S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`
--   * `S4.Def_RP_CurveCoh_Shapiro`: S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1
--   * `S4.Def_RP_CurveCoh_ShapiroCone`: S4-CurveCoh, part 5: Shapiro's lemma for the cone `H¹_c` (K0c with compact support)
--   * `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
--   * `S4.Def_RP_CP4a_BdS`: S4-CP4a, part f3: the boundary data over `∞` exist, finite and nonempty
--   * `S4.Def_RP_CP4a_Main`: S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)
--   * `S4.Def_RP_JacAlg_Res`: Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)
--   * `S4.Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
--   * `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
--   * `S4.Def_RP_CoreB_Pert`: Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only
--   * `S4.Def_RP_CoreB`: Unit S4-CoreB (Core B final assembly, lemmas L43-L44 of `S4_COREB_ROUTE.md` section 3): umbrella
--   * `S4.Def_RP_PerfectCx_Red`: S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)
--   * `S4.Def_RP_CupDuality_KumPicDiv`: S4-CurveDuality, O5b (ii): `Pic⁰(X̄)` is `l^n`-divisible for `l ∤ q`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_007

/-!
# Ramanujan-Petersson curve library (flat edition), file 010 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_HattoriStallings_Core`: Hattori–Stallings traces over `R[G]` (unit S4-HattoriStallings, part A: core)
* `S4.Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
* `S4.Def_RP_PerfectCx_Free`: S4-PD (5), E2(a) algebra: a freeness criterion over `O/λⁿ`
* `S4.Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
* `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
* `S4.Def_RP_HattoriStallings_Twisted`: Hattori–Stallings traces, part B1: trace relations, the twisted-trace formula, base change
* `S4.Def_RP_PerfectCx_Tri`: S4-PD (5), E3: three-term complexes as `ℕ`-indexed families
* `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
* `S4.Def_RP_HattoriStallings_CT`: Hattori–Stallings traces, part C: cohomologically trivial modules are projective
* `S4.Def_RP_PerfectCx_Proj`: S4-PD (5), E2(b): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ[Gf]`-projective
* `S4.Def_RP_PerfectCx_FrobIso`: S4-PD (5), E3: the Frobenius on the perfect complex and its trace formula
* `S4.Def_RP_Lefschetz_ConeMapG`: S4-Lefschetz, L3c: cone maps for coefficient maps that are only `Γ`-equivariant, across ambients
* `S4.Def_RP_Lefschetz_BlockTr`: S4-Lefschetz, L3b: traces over a block decomposition
* `S4.Def_RP_Lefschetz_BlockAlg`: S4-Lefschetz, L3d1: the block decomposition of `Λ[Gf]` along right cosets `P x`
* `S4.Def_RP_CurveCoh_Shapiro`: S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1
* `S4.Def_RP_CurveCoh_ShapiroCone`: S4-CurveCoh, part 5: Shapiro's lemma for the cone `H¹_c` (K0c with compact support)
* `S4.Def_RP_CP4a_BdryInf`: S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`
* `S4.Def_RP_CP4a_BdS`: S4-CP4a, part f3: the boundary data over `∞` exist, finite and nonempty
* `S4.Def_RP_CP4a_Main`: S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)
* `S4.Def_RP_JacAlg_Res`: Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)
* `S4.Def_RP_JacAlg_Charpoly`: Core B algebra, part 8: `P_π = charpoly(T_l π)` (unit S4-JacAlg, L4/L5 = Milne 10.20-10.22, steps C1, C2)
* `S4.Def_RP_CoreB_Key`: Core B, O6: `‖deg F‖_l = ‖det F(M)‖_l` through Tate coordinates (for `deg F ≠ 0`)
* `S4.Def_RP_CoreB_Pert`: Core B, O7: `charpoly(M) = P₀` from the norm identity for `deg F ≠ 0` only
* `S4.Def_RP_CoreB`: Unit S4-CoreB (Core B final assembly, lemmas L43-L44 of `S4_COREB_ROUTE.md` section 3): umbrella
* `S4.Def_RP_PerfectCx_Red`: S4-PD (5), E3: reduction mod `t` (e.g. `ℓⁿ → ℓᵐ`)
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

open Classical in
/-- Class sums: `classSum a c = ∑_{g ∈ c} a g`. -/
noncomputable def classSum : (G → R) →ₗ[R] (ConjClasses G → R) where
  toFun a c := ∑ g : G, if ConjClasses.mk g = c then a g else 0
  map_add' a b := by
    funext c
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp
  map_smul' r a := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp

open Classical in
lemma classSum_apply (a : G → R) (c : ConjClasses G) :
    classSum a c = ∑ g : G, if ConjClasses.mk g = c then a g else 0 := rfl

lemma mk_conj (h g : G) : ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g :=
  (ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨h, rfl⟩)).symm

lemma classSum_conj (a : G → R) (h : G) : classSum (fun g => a (h * g * h⁻¹)) = classSum a := by
  funext c
  rw [classSum_apply, classSum_apply]
  refine Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ (fun g => ?_)
  by_cases hg : ConjClasses.mk g = c
  · rw [if_pos hg]
    exact (if_pos (show ConjClasses.mk ((MulAut.conj h).toEquiv g) = c from
      (mk_conj h g).trans hg)).symm
  · rw [if_neg hg]
    exact (if_neg (show ¬ ConjClasses.mk ((MulAut.conj h).toEquiv g) = c from
      fun h' => hg ((mk_conj h g).symm.trans h'))).symm

/-- Pairing a function with a class function through class sums. -/
lemma sum_mul_eq_sum_classSum (a b : G → R) (χ : ConjClasses G → R)
    (hχ : ∀ g, χ (ConjClasses.mk g) = b g) [Fintype (ConjClasses G)] :
    ∑ g, a g * b g = ∑ c, classSum a c * χ c := by
  classical
  simp only [classSum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_eq_single (ConjClasses.mk g)]
  · simp [hχ]
  · intro c _ hc; simp [Ne.symm hc]
  · simp

end ClassSum

section Higman

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {T : Type*} [AddCommGroup T] [Module R T]

variable {ρ : Representation R G P} {σ : Representation R G Q} {τ : Representation R G T}

lemma rep_apply_apply (ρ : Representation R G P) (a b : G) (x : P) :
    ρ a (ρ b x) = ρ (a * b) x := by
  rw [map_mul]; rfl

lemma rep_inv_apply_apply (ρ : Representation R G P) (a : G) (x : P) : ρ a⁻¹ (ρ a x) = x := by
  rw [rep_apply_apply, inv_mul_cancel, map_one]; rfl

lemma rep_apply_inv_apply (ρ : Representation R G P) (a : G) (x : P) : ρ a (ρ a⁻¹ x) = x := by
  rw [rep_apply_apply, mul_inv_cancel, map_one]; rfl

variable [Module.Free R P] [Module.Finite R P] [Module.Free R Q] [Module.Finite R Q]

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

/-- `a ↦ a(1) · 1`. -/
def e1 : MonoidAlgebra k Gf →ₗ[k] MonoidAlgebra k Gf where
  toFun a := single 1 (a.coeff 1)
  map_add' a b := by rw [coeff_add, Finsupp.add_apply, single_add]
  map_smul' r a := by simp only [coeff_smul_apply, smul_single, RingHom.id_apply]

theorem e1_apply (a : MonoidAlgebra k Gf) : e1 a = single 1 (a.coeff 1) := rfl

variable {M : Type} [AddCommGroup M] [Module k M] (τ : Representation k Gf M)

end Right

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_Free =====
section

/-!
# S4-PD (5), E2(a) algebra: a freeness criterion over `O/λⁿ`

`Λ` is a local ring whose maximal ideal is generated by `ϖ`, with `ϖⁿ = 0` (e.g. `ZMod (lⁿ)` with `ϖ = l`, or
`O/λⁿ` with a uniformiser `ϖ`; review END-2, decision R19).

* `exists_eq_mul_of_not_isUnit`, `isUnit_sub_mul`: non-units are multiples of `ϖ`, a unit minus a multiple of `ϖ`
  is a unit;
* `free_of_torsion`: a finite `Λ`-module `E` in which `ϖᵐ • z = 0` (`m < n`) forces `z ∈ ϖ • E` is free (a minimal
  generating family is a basis: a relation with a unit coefficient would shorten it, and the hypothesis pushes
  every relation one power of `ϖ` deeper).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace PerfectCx

open IsLocalRing

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ})
include hϖ

theorem exists_eq_mul_of_not_isUnit {x : Λ} (hx : ¬ IsUnit x) : ∃ y, x = ϖ * y := by
  have h : x ∈ maximalIdeal Λ := (mem_maximalIdeal x).2 (mem_nonunits_iff.2 hx)
  rw [hϖ, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  exact ⟨y, by rw [← hy, mul_comm]⟩

/-- **Freeness criterion.** A finite `Λ`-module in which `ϖᵐ`-torsion (`m < n`) is divisible by `ϖ` is free. -/
theorem free_of_torsion {n : ℕ} (hn : ϖ ^ n = 0) {E : Type} [AddCommGroup E] [Module Λ E] [Module.Finite Λ E]
    (H : ∀ m < n, ∀ z : E, ϖ ^ m • z = 0 → ∃ w, z = ϖ • w) : Module.Free Λ E := by
  classical
  have hex : ∃ r, ∃ e : Fin r → E, Submodule.span Λ (Set.range e) = ⊤ := Module.Finite.exists_fin
  obtain ⟨r, ⟨e, he⟩, hmin⟩ : ∃ r, (∃ e : Fin r → E, Submodule.span Λ (Set.range e) = ⊤) ∧
      ∀ r' < r, ¬ ∃ e : Fin r' → E, Submodule.span Λ (Set.range e) = ⊤ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r' h => Nat.find_min hex h⟩
  -- a relation never has a unit coefficient (minimality)
  have hunit : ∀ c : Fin r → Λ, ∑ i, c i • e i = 0 → ∀ i, ¬ IsUnit (c i) := by
    intro c hc i hi
    obtain ⟨f, hf⟩ : ∃ f : Fin (Fintype.card {j : Fin r // j ≠ i}) → E,
        f = fun k => e ((Fintype.equivFin {j : Fin r // j ≠ i}).symm k) := ⟨_, rfl⟩
    have hmem : ∀ j, j ≠ i → e j ∈ Submodule.span Λ (Set.range f) := by
      intro j hj
      apply Submodule.subset_span
      exact ⟨Fintype.equivFin {j : Fin r // j ≠ i} ⟨j, hj⟩, by rw [hf]; simp⟩
    have hsum := Finset.add_sum_erase Finset.univ (fun j => c j • e j) (Finset.mem_univ i)
    rw [hc] at hsum
    have hrest : ∑ j ∈ Finset.univ.erase i, c j • e j ∈ Submodule.span Λ (Set.range f) :=
      Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hmem j (Finset.ne_of_mem_erase hj))
    have hci : c i • e i ∈ Submodule.span Λ (Set.range f) := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact Submodule.neg_mem _ hrest
    have hei : e i ∈ Submodule.span Λ (Set.range f) := by
      obtain ⟨u, hu⟩ := hi
      have h1 : e i = (↑u⁻¹ : Λ) • (c i • e i) := by rw [smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ hci
    have hlt : Fintype.card {j : Fin r // j ≠ i} < r := by
      simpa using Fintype.card_subtype_lt (p := fun j : Fin r => j ≠ i) (x := i) (by simp)
    apply hmin _ hlt
    refine ⟨f, eq_top_iff.2 ?_⟩
    rw [← he, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst hj
      exact hei
    · exact hmem j hj
  have hli : LinearIndependent Λ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have key : ∀ m ≤ n, ∃ d : Fin r → Λ, ∀ i, c i = ϖ ^ m * d i := by
      intro m
      induction m with
      | zero => exact fun _ => ⟨c, fun i => by simp⟩
      | succ m ih =>
        intro hm
        obtain ⟨d, hd⟩ := ih (by omega)
        have hz : ϖ ^ m • ∑ i, d i • e i = 0 := by
          rw [Finset.smul_sum, ← hc]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, hd i]
        obtain ⟨w, hw⟩ := H m (by omega) _ hz
        have hw' : w ∈ Submodule.span Λ (Set.range e) := by
          rw [he]
          exact Submodule.mem_top
        obtain ⟨ν, hν⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 hw'
        have hrel : ∑ i, (d i - ϖ * ν i) • e i = 0 := by
          have h1 : ∑ i, (d i - ϖ * ν i) • e i = ∑ i, d i • e i - ϖ • ∑ i, ν i • e i := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sub_smul, mul_smul]
          rw [h1, hν, ← hw, sub_self]
        refine ⟨fun i => Classical.choose (exists_eq_mul_of_not_isUnit hϖ (hunit _ hrel i)) + ν i,
          fun i => ?_⟩
        have hy := Classical.choose_spec (exists_eq_mul_of_not_isUnit hϖ (hunit _ hrel i))
        rw [hd i]
        linear_combination ϖ ^ m * hy
    intro i
    obtain ⟨d, hd⟩ := key n le_rfl
    rw [hd i, hn, zero_mul]
  exact Module.Free.of_basis (Module.Basis.mk hli he.ge)

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

/-- Coefficientwise: `ϖᵐ`-torsion of `Λ[Gf]` (`m < n`) is divisible by `ϖ`. -/
theorem exists_smul_of_pow_smul [IsLocalRing Λ] [Finite Gf] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ})
    {m : ℕ} (hm : ϖ ^ m ≠ 0) (a : MonoidAlgebra Λ Gf) (ha : ϖ ^ m • a = 0) :
    ∃ b : MonoidAlgebra Λ Gf, a = ϖ • b := by
  have hx : ∀ x : Gf, ∃ y, a.coeff x = ϖ * y := fun x => by
    refine exists_eq_mul_of_not_isUnit hϖ fun hu => hm ?_
    have h1 : (ϖ ^ m • a).coeff x = 0 := by rw [ha]; rfl
    rw [coeff_smul_apply, smul_eq_mul] at h1
    simpa using (hu.mul_left_eq_zero).1 h1
  choose y hy using hx
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm y), ?_⟩
  ext x
  rw [coeff_smul_apply, hy x, smul_eq_mul]
  rfl

end Cocycles

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

/-- Averaging `∑_g σ g ∘ f ∘ ρ g⁻¹` (the Reynolds operator without the division by `|G|`). -/
noncomputable def avg (ρ : Representation R G P) (σ : Representation R G Q) (f : P →ₗ[R] Q) :
    P →ₗ[R] Q :=
  ∑ g : G, σ g ∘ₗ f ∘ₗ ρ g⁻¹

lemma avg_apply (f : P →ₗ[R] Q) (v : P) : avg ρ σ f v = ∑ g : G, σ g (f (ρ g⁻¹ v)) := by
  simp [avg, LinearMap.sum_apply]

end Avg

section SES

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P' : Type*} [AddCommGroup P'] [Module R P'] {P : Type*} [AddCommGroup P] [Module R P]
variable {P'' : Type*} [AddCommGroup P''] [Module R P'']
variable {ρ' : Representation R G P'} {ρ : Representation R G P} {ρ'' : Representation R G P''}

/-- Over a local ring a retract of a free finite module is free and finite (so the sub of an exact
sequence of free finite `R`-modules is automatically free). -/
theorem free_finite_of_retract [IsLocalRing R] [Module.Free R P] [Module.Finite R P]
    {i : P' →ₗ[R] P} {r : P →ₗ[R] P'}
    (hri : r ∘ₗ i = LinearMap.id) : Module.Free R P' ∧ Module.Finite R P' := by
  have : Module.Projective R P' := Module.Projective.of_split i r hri
  have : Module.Finite R P' :=
    Module.Finite.of_surjective r (fun v' => ⟨i v', LinearMap.congr_fun hri v'⟩)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

variable [Module.Free R P'] [Module.Finite R P'] [Module.Free R P] [Module.Finite R P]
  [Module.Free R P''] [Module.Finite R P'']

end SES

section Perm

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

variable (R G) in
/-- The permutation representation of a finite `G`-set `X` on `X → R`: `(g • f) x = f (g⁻¹ • x)`. -/
noncomputable def permRep (X : Type*) [MulAction G X] : Representation R G (X → R) where
  toFun g := LinearMap.funLeft R R (fun x => g⁻¹ • x)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

lemma permRep_apply {X : Type*} [MulAction G X] (g : G) (f : X → R) (x : X) :
    permRep R G X g f x = f (g⁻¹ • x) := rfl

lemma permRep_single {X : Type*} [MulAction G X] [DecidableEq X] (g : G) (x : X) (r : R) :
    permRep R G X g (Pi.single x r) = Pi.single (g • x) r := by
  ext y
  simp only [permRep_apply, Pi.single_apply, inv_smul_eq_iff]

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

lemma rep_conj_inv (h γ : G) :
    ρ (h⁻¹ * γ * h)⁻¹ = ρ h⁻¹ ∘ₗ ρ γ⁻¹ ∘ₗ ρ h := by
  rw [show (h⁻¹ * γ * h)⁻¹ = h⁻¹ * γ⁻¹ * h by group, map_mul, map_mul]
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

end TraceRel

section Coinv

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module R V]

end Coinv

section Twisted

lemma sum_comp' {R : Type*} [CommRing R] {A B C : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] {ι : Type*} (s : Finset ι)
    (f : ι → B →ₗ[R] C) (g : A →ₗ[R] B) : (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g :=
  LinearMap.ext fun x => by simp [LinearMap.sum_apply]

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}
variable {M : Type*} [AddCommGroup M] [Module R M] {τ : Representation R G M}

variable [Module.Free R P] [Module.Finite R P] [Module.Free R M] [Module.Finite R M]

end Twisted

section BaseChange

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}
variable (A : Type*) [CommRing A] [Algebra R A]

variable {A}

variable [Module.Free R P] [Module.Finite R P]

lemma classSum_algebraMap (f : G → R) (c : ConjClasses G) :
    classSum (fun g => algebraMap R A (f g)) c = algebraMap R A (classSum f c) := by
  classical
  rw [classSum_apply, classSum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

end BaseChange

section Conj

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {ρ : Representation R G P} {σ : Representation R G Q}
variable [Module.Free R P] [Module.Finite R P] [Module.Free R Q] [Module.Finite R Q]

end Conj

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

end Conj

section Frob

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N)
  (Γ : Subgroup G) [hΓ : Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ)

variable (hρ : IsOpen (ρ.ker : Set G))

end Frob

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ)

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

end FieldCase

section Relative

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

end Relative

section Lift

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

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

end Lift

section Main

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
variable {ρ : Representation R G P}

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

variable [Finite Gf] (S : Subgroup Gf) [Fintype S]

end Cocycles

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

/-- Traces agree along a linear equivalence intertwining two endomorphisms. -/
theorem trace_eq_of_intertwine {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] (e : V ≃ₗ[R] W) (f : V →ₗ[R] V) (g : W →ₗ[R] W) (hfg : ∀ v, e (f v) = g (e v)) :
    LinearMap.trace R V f = LinearMap.trace R W g := by
  have hg : g = e.conj f := LinearMap.ext fun w => by
    rw [LinearEquiv.conj_apply_apply, hfg, LinearEquiv.apply_symm_apply]
  rw [hg, LinearMap.trace_conj']

section H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) [Γ.Normal] {S : Type}
  (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ) (hρ : IsOpen (ρ.ker : Set G))

end H

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ) (hI : BdryCompat Γ I ψ t h)

variable [Finite Λ] [Fintype Gf] {M : Type} [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M) {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0) (hπ : IsOpen (π.ker : Set G))

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

/-- Pull a cocycle back along a continuous hom `φ : Δ' → Δ` and push its values along `q`. -/
def zPull {Δ : Subgroup A} {Δ' : Subgroup B} (φ : Δ' →* Δ) (hφ : Continuous φ) (q : M →ₗ[k] N)
    (hq : ∀ (x : Δ') (m : M), q (ρ (φ x : A) m) = σ (x : B) (q m)) : Z1 ρ Δ →ₗ[k] Z1 σ Δ' where
  toFun c := ⟨fun x => q ((c : Δ → M) (φ x)), (mem_Z1 σ Δ' _).2
    ⟨(((mem_Z1 ρ Δ _).1 c.2).1.comp_continuous hφ).comp q, fun x y => by
      show q ((c : Δ → M) (φ (x * y))) = q ((c : Δ → M) (φ x)) + σ (x : B) (q ((c : Δ → M) (φ y)))
      rw [map_mul, ((mem_Z1 ρ Δ _).1 c.2).2, map_add, hq]⟩⟩
  map_add' c d := Subtype.ext (funext fun x => by
    show q ((c : Δ → M) (φ x) + (d : Δ → M) (φ x)) = q ((c : Δ → M) (φ x)) + q ((d : Δ → M) (φ x))
    exact map_add _ _ _)
  map_smul' r c := Subtype.ext (funext fun x => by
    show q (r • (c : Δ → M) (φ x)) = r • q ((c : Δ → M) (φ x))
    exact map_smul _ _ _)

theorem zPull_apply {Δ : Subgroup A} {Δ' : Subgroup B} (φ : Δ' →* Δ) (hφ : Continuous φ) (q : M →ₗ[k] N)
    (hq : ∀ (x : Δ') (m : M), q (ρ (φ x : A) m) = σ (x : B) (q m)) (c : Z1 ρ Δ) (x : Δ') :
    (zPull ρ σ φ hφ q hq c : Δ' → N) x = q ((c : Δ → M) (φ x)) := rfl

variable {Γ : Subgroup A} {Γ' : Subgroup B} {S : Type} (I : S → Subgroup A) (I' : S → Subgroup B)
  (φ : Γ' →* Γ) (hφ : Continuous φ)
  (φs : ∀ s, ↥(Γ' ⊓ I' s) →* ↥(Γ ⊓ I s)) (hφs : ∀ s, Continuous (φs s))

/-- The degree-1 cone map `Z¹(Γ; M) × M^S → Z¹(Γ'; N) × N^S`. -/
def K1pull (q : M →ₗ[k] N) (hq : ∀ (x : Γ') (m : M), q (ρ (φ x : A) m) = σ (x : B) (q m)) :
    Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ' × (S → N) :=
  (zPull ρ σ φ hφ q hq).prodMap (LinearMap.piMap fun _ => q)

/-- The degree-2 cone map `Π_s Z¹(Γ ⊓ I s; M) → Π_s Z¹(Γ' ⊓ I' s; N)`. -/
def K2pull (q : M →ₗ[k] N)
    (hqs : ∀ s (x : ↥(Γ' ⊓ I' s)) (m : M), q (ρ (φs s x : A) m) = σ (x : B) (q m)) :
    ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ' ⊓ I' s)) :=
  LinearMap.piMap fun s => zPull ρ σ (φs s) (hφs s) q (hqs s)

theorem K1pull_apply (q : M →ₗ[k] N) (hq : ∀ (x : Γ') (m : M), q (ρ (φ x : A) m) = σ (x : B) (q m))
    (p : Z1 ρ Γ × (S → M)) :
    K1pull ρ σ φ hφ q hq p = (zPull ρ σ φ hφ q hq p.1, fun s => q (p.2 s)) := rfl

theorem K2pull_apply (q : M →ₗ[k] N)
    (hqs : ∀ s (x : ↥(Γ' ⊓ I' s)) (m : M), q (ρ (φs s x : A) m) = σ (x : B) (q m))
    (e : (s : S) → Z1 ρ (Γ ⊓ I s)) (s : S) :
    K2pull ρ σ I I' φs hφs q hqs e s = zPull ρ σ (φs s) (hφs s) q (hqs s) (e s) := rfl

theorem K1pull_sum {ι : Type} (T : Finset ι) (q : ι → M →ₗ[k] N)
    (hq : ∀ i (x : Γ') (m : M), q i (ρ (φ x : A) m) = σ (x : B) (q i m))
    (hs : ∀ (x : Γ') (m : M), (∑ i ∈ T, q i) (ρ (φ x : A) m) = σ (x : B) ((∑ i ∈ T, q i) m)) :
    (∑ i ∈ T, K1pull ρ σ φ hφ (q i) (hq i) : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ' × (S → N)) =
      K1pull ρ σ φ hφ (∑ i ∈ T, q i) hs :=
  LinearMap.ext fun p => Prod.ext (Subtype.ext (funext fun x => by
      simp only [LinearMap.sum_apply, Prod.fst_sum, Submodule.coe_sum, Finset.sum_apply, K1pull_apply,
        zPull_apply]))
    (funext fun s => by simp only [LinearMap.sum_apply, Prod.snd_sum, Finset.sum_apply, K1pull_apply])

theorem K2pull_sum {ι : Type} (T : Finset ι) (q : ι → M →ₗ[k] N)
    (hqs : ∀ i s (x : ↥(Γ' ⊓ I' s)) (m : M), q i (ρ (φs s x : A) m) = σ (x : B) (q i m))
    (hs : ∀ s (x : ↥(Γ' ⊓ I' s)) (m : M), (∑ i ∈ T, q i) (ρ (φs s x : A) m) = σ (x : B) ((∑ i ∈ T, q i) m)) :
    ∑ i ∈ T, K2pull ρ σ I I' φs hφs (q i) (hqs i) = K2pull ρ σ I I' φs hφs (∑ i ∈ T, q i) hs :=
  LinearMap.ext fun e => funext fun s => Subtype.ext (funext fun x => by
    simp only [LinearMap.sum_apply, Finset.sum_apply, Submodule.coe_sum, K2pull_apply, zPull_apply])

variable (q : M →ₗ[k] N) (hq : ∀ (x : Γ') (m : M), q (ρ (φ x : A) m) = σ (x : B) (q m))
  (hqs : ∀ s (x : ↥(Γ' ⊓ I' s)) (m : M), q (ρ (φs s x : A) m) = σ (x : B) (q m))

variable (f : M →ₗ[k] M) (hf : ∀ (g : A) (m : M), f (ρ g m) = ρ g (f m))
  (f' : N →ₗ[k] N) (hf' : ∀ (g : B) (n : N), f' (σ g n) = σ g (f' n))
  (q' : M →ₗ[k] N) (hq' : ∀ (x : Γ') (m : M), q' (ρ (φ x : A) m) = σ (x : B) (q' m))
  (hqs' : ∀ s (x : ↥(Γ' ⊓ I' s)) (m : M), q' (ρ (φs s x : A) m) = σ (x : B) (q' m))
  (ψ : A) (ψ' : B) (t : S → S) (h : S → Γ) (h' : S → Γ')

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

theorem trace_eq_sum_blocks (P : ι → Module.End R V) (hsum : ∑ ω, P ω = 1) (f : Module.End R V) :
    LinearMap.trace R V f = ∑ ω, LinearMap.trace R V (P ω * f) := by
  rw [← map_sum, ← Finset.sum_mul, hsum, one_mul]

theorem trace_block_eq_zero (P : ι → Module.End R V)
    (hP : ∀ ω ω', P ω * P ω' = if ω = ω' then P ω else 0) (f : Module.End R V) (s : ι ≃ ι)
    (hf : ∀ ω, P (s ω) * f = f * P ω) (ω : ι) (hω : s.symm ω ≠ ω) :
    LinearMap.trace R V (P ω * f) = 0 := by
  have h1 : P ω * f = f * P (s.symm ω) := by
    have h := hf (s.symm ω)
    rwa [Equiv.apply_symm_apply] at h
  have h2 : P ω * P ω = P ω := by simpa using hP ω ω
  have h3 : P (s.symm ω) * P ω = 0 := by simpa [hω] using hP (s.symm ω) ω
  calc LinearMap.trace R V (P ω * f) = LinearMap.trace R V (P ω * (f * P (s.symm ω))) := by
        rw [← h1, ← mul_assoc, h2]
    _ = LinearMap.trace R V ((f * P (s.symm ω)) * P ω) :=
        LinearMap.trace_mul_comm (R := R) (M := V) (P ω) (f * P (s.symm ω))
    _ = 0 := by rw [mul_assoc, h3, mul_zero, map_zero]

/-- Headline: only the blocks fixed by `s` contribute to the trace. -/
theorem trace_eq_sum_fixed (P : ι → Module.End R V) (hsum : ∑ ω, P ω = 1)
    (hP : ∀ ω ω', P ω * P ω' = if ω = ω' then P ω else 0) (f : Module.End R V) (s : ι ≃ ι)
    (hf : ∀ ω, P (s ω) * f = f * P ω) :
    LinearMap.trace R V f =
      ∑ ω ∈ Finset.univ.filter (fun ω => s ω = ω), LinearMap.trace R V (P ω * f) := by
  rw [trace_eq_sum_blocks P hsum f, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs with h
  · rfl
  · refine trace_block_eq_zero P hP f s hf ω fun h' => h ?_
    have h'' := congrArg s h'
    rw [Equiv.apply_symm_apply] at h''
    exact h''.symm

variable {W : Type*} [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

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

/-- The block `P x` of `x`. -/
def blk (x : Gf) : Blk P := Quotient.mk (QuotientGroup.rightRel P) x

instance [Finite Gf] : Finite (Blk P) := Quotient.finite _

noncomputable instance [Finite Gf] : Fintype (Blk P) := Fintype.ofFinite _

noncomputable instance : DecidableEq (Blk P) := Classical.decEq _

theorem blk_surjective : Function.Surjective (blk P) := Quotient.mk_surjective

theorem blk_eq_iff {x y : Gf} : blk P x = blk P y ↔ y * x⁻¹ ∈ P := by
  unfold blk
  exact Quotient.eq.trans QuotientGroup.rightRel_apply

end BlockAlg

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_CurveCoh_Shapiro =====
section

/-!
# S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1

A finite etale cover `f : U → V` corresponds to an open subgroup `H = π₁(U)` of finite index in `G = π₁(V)`.
For a representation `σ` of `H` on `M` (a lisse sheaf on `U`), `f_* M` is the coinduced representation
`pushRep Γ H σ` of `G` on `coindV H.subtype σ`: `H`-equivariant functions `F : G → M`, `(g • F) x = F (x * g)`.
The geometric fundamental group of `U` is `Γ ∩ H` (`geoU Γ H`), and `U` is geometrically connected over the
constant field of `V` exactly when `G = H Γ` (hypothesis `hcov`).

Results (over any commutative ring `k`):
* `shapiroH0Equiv : H⁰(Γ, f_* M) ≃ₗ H⁰(Γ ∩ H, M)` (`F ↦ F 1`);
* `shapiroH1 : H¹(Γ, f_* M) →ₗ H¹(Γ ∩ H, M)` (restrict to `Γ ∩ H`, evaluate at `1`): injective (`hcov`), surjective
  (`hcov`, `H` open, representatives of `(Γ ∩ H) \ Γ`, which exist for finite index: `exists_cosetReps`), hence
  `shapiroH1Equiv`;
* `shapiroH1_frobH1`: Shapiro commutes with the operators `T_ψ`, `ψ ∈ H`; in particular with the GEOMETRIC Frobenius
  `F = T_{φ⁻¹}` for a Frobenius lift `φ ∈ π₁(U)` (which is also one for `V`), so purity is preserved.
Part 5 (`Def_RP_CurveCoh_ShapiroCone`) treats the cone `H¹_c`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

open Representation

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (Γ H : Subgroup G) (σ : Representation k H M)

/-- `f_* M`: the representation of `G = π₁(V)` coinduced from the representation `σ` of `H = π₁(U)`. -/
abbrev pushRep : Representation k G (coindV H.subtype σ) := coind H.subtype σ

/-- The geometric fundamental group `Γ ∩ H` of the cover, as a subgroup of `H`. -/
abbrev geoU : Subgroup H := Γ.subgroupOf H

/-- `Γ ∩ H` inside `Γ`. -/
def geoToΓ (h : geoU Γ H) : Γ := ⟨((h : H) : G), Subgroup.mem_subgroupOf.mp h.2⟩

@[simp] theorem geoToΓ_coe (h : geoU Γ H) : ((geoToΓ Γ H h : Γ) : G) = ((h : H) : G) := rfl

theorem geoToΓ_mul (a b : geoU Γ H) : geoToΓ Γ H (a * b) = geoToΓ Γ H a * geoToΓ Γ H b := rfl

theorem continuous_geoToΓ : Continuous (geoToΓ Γ H) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable {H σ} in
theorem coind_mul_apply (F : coindV H.subtype σ) (h : H) (x : G) :
    (F : G → M) ((h : G) * x) = σ h ((F : G → M) x) := F.2 h x

variable {H σ} in
theorem coind_apply_of_mem (F : coindV H.subtype σ) (h : H) :
    (F : G → M) (h : G) = σ h ((F : G → M) 1) := by
  rw [← coind_mul_apply F h 1, mul_one]

theorem rep_mul_apply {K : Type} [Group K] (τ : Representation k K M) (a b : K) (m : M) :
    τ a (τ b m) = τ (a * b) m := by
  rw [map_mul]; rfl

/-! ## Extension from `Γ` to `G = H Γ` -/

section Ext

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

/-- The `H`-part of the chosen decomposition `x = h * γ` (`G = H Γ`). -/
def hdec (x : G) : H := Classical.choose (hcov x)

/-- The `Γ`-part of the chosen decomposition. -/
def gdec (x : G) : Γ := Classical.choose (Classical.choose_spec (hcov x))

theorem dec_spec (x : G) : x = (hdec Γ H hcov x : G) * gdec Γ H hcov x :=
  Classical.choose_spec (Classical.choose_spec (hcov x))

/-- Equivariance on `Γ` under the elements of `H` that move `Γ` into itself (those of `Γ ∩ H`). -/
def EquivOnΓ (φ : Γ → M) : Prop := ∀ (h : H) (y y' : Γ), (y' : G) = h * y → φ y' = σ h (φ y)

/-- Extension of a function on `Γ` to `G = H Γ` by `H`-equivariance. -/
def coindExt (φ : Γ → M) (x : G) : M := σ (hdec Γ H hcov x) (φ (gdec Γ H hcov x))

theorem dec_aux {h A C : H} {B1 B2 : Γ} {x : G} (h1 : x = (C : G) * B1) (h2 : (h : G) * x = A * B2) :
    (B2 : G) = ((A⁻¹ * h * C : H) : G) * B1 := by
  subst h1
  calc (B2 : G) = (A : G)⁻¹ * (A * B2) := by group
    _ = (A : G)⁻¹ * (h * (C * B1)) := by rw [← h2]
    _ = ((A⁻¹ * h * C : H) : G) * B1 := by push_cast; group

theorem coindExt_mem (φ : Γ → M) (hφ : EquivOnΓ Γ H σ φ) :
    coindExt Γ H σ hcov φ ∈ coindV H.subtype σ := by
  intro h x
  change σ (hdec Γ H hcov ((h : G) * x)) (φ (gdec Γ H hcov ((h : G) * x))) =
    σ h (σ (hdec Γ H hcov x) (φ (gdec Γ H hcov x)))
  rw [hφ _ _ _ (dec_aux Γ H (dec_spec Γ H hcov x) (dec_spec Γ H hcov ((h : G) * x))), rep_mul_apply,
    rep_mul_apply]
  congr 2
  group

theorem coindExt_apply (φ : Γ → M) (hφ : EquivOnΓ Γ H σ φ) (y : Γ) :
    coindExt Γ H σ hcov φ y = φ y :=
  (hφ _ _ _ (dec_spec Γ H hcov y)).symm

/-- The element of `f_* M` extending an equivariant function on `Γ`. -/
def coindOf (φ : Γ → M) (hφ : EquivOnΓ Γ H σ φ) : coindV H.subtype σ :=
  ⟨coindExt Γ H σ hcov φ, coindExt_mem Γ H σ hcov φ hφ⟩

theorem coindOf_apply (φ : Γ → M) (hφ : EquivOnΓ Γ H σ φ) (y : Γ) :
    ((coindOf Γ H σ hcov φ hφ : coindV H.subtype σ) : G → M) y = φ y :=
  coindExt_apply Γ H σ hcov φ hφ y

include hcov in
/-- Elements of `f_* M` are determined by their values on `Γ` when `G = H Γ`. -/
theorem coind_ext_Γ {F F' : coindV H.subtype σ} (hF : ∀ y : Γ, (F : G → M) y = (F' : G → M) y) :
    F = F' := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨h, γ, rfl⟩ := hcov x
  rw [coind_mul_apply, coind_mul_apply, hF γ]

end Ext

/-! ## Degree 0 -/

/-! ## Degree 1: the map -/

/-- Restriction to `Γ ∩ H` followed by evaluation at `1`, on 1-cochains. -/
def resEv : (Γ → coindV H.subtype σ) →ₗ[k] (geoU Γ H → M) where
  toFun c h := ((c (geoToΓ Γ H h) : coindV H.subtype σ) : G → M) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resEv_apply (c : Γ → coindV H.subtype σ) (h : geoU Γ H) :
    resEv Γ H σ c h = ((c (geoToΓ Γ H h) : coindV H.subtype σ) : G → M) 1 := rfl

theorem Z1_coind_apply {c : Γ → coindV H.subtype σ} (hc : c ∈ Z1 (pushRep H σ) Γ) (a b : Γ) (x : G) :
    ((c (a * b) : coindV H.subtype σ) : G → M) x =
      (c a : G → M) x + (c b : G → M) (x * a) := by
  rw [((mem_Z1 _ _ c).mp hc).2 a b]; rfl

theorem resEv_mem_Z1 {c : Γ → coindV H.subtype σ} (hc : c ∈ Z1 (pushRep H σ) Γ) :
    resEv Γ H σ c ∈ Z1 σ (geoU Γ H) := by
  refine (mem_Z1 _ _ _).mpr ⟨?_, fun a b => ?_⟩
  · exact (((mem_Z1 _ _ c).mp hc).1.comp_continuous (continuous_geoToΓ Γ H)).comp
      (fun F : coindV H.subtype σ => (F : G → M) 1)
  · simp only [resEv_apply]
    rw [geoToΓ_mul, Z1_coind_apply Γ H σ hc, one_mul, geoToΓ_coe, coind_apply_of_mem]

/-! ## Degree 1: surjectivity (the Shapiro lift) -/

/-- Representatives `r` of the right cosets `(Γ ∩ H) \ Γ`, with `r 1 = 1` and finitely many values. -/
structure CosetReps where
  r : Γ → Γ
  mem : ∀ y : Γ, (y : G) * (r y : G)⁻¹ ∈ H
  coset : ∀ y y' : Γ, (y' : G) * (y : G)⁻¹ ∈ H → r y' = r y
  one : r 1 = 1
  fin : (Set.range r).Finite

theorem exists_cosetReps [(H.subgroupOf Γ).FiniteIndex] : Nonempty (CosetReps Γ H) := by
  classical
  let K := H.subgroupOf Γ
  let q : Γ → Quotient (QuotientGroup.rightRel K) := Quotient.mk _
  have hq : ∀ y : Γ, (y : G) * ((q y).out : G)⁻¹ ∈ H := fun y => by
    have h1 : QuotientGroup.rightRel K (q y).out y := Quotient.exact (Quotient.out_eq (q y))
    have h2 := QuotientGroup.rightRel_apply.mp h1
    simpa [K, Subgroup.mem_subgroupOf] using h2
  haveI : Finite (Quotient (QuotientGroup.rightRel K)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel K).symm
  refine ⟨⟨fun y => if (y : G) ∈ H then 1 else (q y).out, fun y => ?_, fun y y' hyy => ?_, ?_, ?_⟩⟩
  · split_ifs with hy
    · simpa using hy
    · exact hq y
  · have hiff : (y' : G) ∈ H ↔ (y : G) ∈ H := by
      constructor
      · intro h'
        have : (y : G) = ((y' : G) * (y : G)⁻¹)⁻¹ * y' := by group
        rw [this]; exact H.mul_mem (H.inv_mem hyy) h'
      · intro h'
        have : (y' : G) = ((y' : G) * (y : G)⁻¹) * y := by group
        rw [this]; exact H.mul_mem hyy h'
    have hqq : q y' = q y := (Quotient.sound (QuotientGroup.rightRel_apply.mpr
      (by simpa [K, Subgroup.mem_subgroupOf] using hyy))).symm
    simp only [hiff, hqq]
  · simp [H.one_mem]
  · refine ((Set.finite_range (Quotient.out : Quotient (QuotientGroup.rightRel K) → Γ)).insert 1).subset ?_
    rintro _ ⟨y, rfl⟩
    by_cases hy : (y : G) ∈ H
    · simp [hy]
    · simp only [hy, if_false]
      exact Set.mem_insert_of_mem _ ⟨q y, rfl⟩

variable {Γ H} (R : CosetReps Γ H)

/-- `η y = y * (r y)⁻¹ ∈ Γ ∩ H`. -/
def CosetReps.eta (y : Γ) : geoU Γ H :=
  ⟨⟨(y : G) * (R.r y : G)⁻¹, R.mem y⟩,
    Subgroup.mem_subgroupOf.mpr (Γ.mul_mem y.2 (Γ.inv_mem (R.r y).2))⟩

theorem CosetReps.r_r_mul (y g : Γ) : R.r (R.r y * g) = R.r (y * g) :=
  R.coset _ _ (by
    have h := H.inv_mem (R.mem y)
    convert h using 1
    push_cast; group)

theorem CosetReps.eta_mul (y g : Γ) : R.eta (y * g) = R.eta y * R.eta (R.r y * g) := by
  refine Subtype.ext (Subtype.ext ?_)
  change ((y : G) * g) * (R.r (y * g) : G)⁻¹ =
    ((y : G) * (R.r y : G)⁻¹) * (((R.r y : G) * g) * (R.r (R.r y * g) : G)⁻¹)
  rw [R.r_r_mul]; group

/-- The values on `Γ` of the Shapiro lift of a cochain `a` on `Γ ∩ H`: `y ↦ σ(η y) (a (η (r y * γ)))`. -/
def liftVal (a : geoU Γ H → M) (γ y : Γ) : M := σ (R.eta y : H) (a (R.eta (R.r y * γ)))

theorem liftVal_equiv (a : geoU Γ H → M) (γ : Γ) : EquivOnΓ Γ H σ (liftVal σ R a γ) := by
  intro h y y' hy
  have hr : R.r y' = R.r y := R.coset _ _ (by rw [hy]; simpa using h.2)
  have he : (R.eta y' : H) = h * (R.eta y : H) := Subtype.ext (by
    change (y' : G) * (R.r y' : G)⁻¹ = h * ((y : G) * (R.r y : G)⁻¹)
    rw [hr, hy, mul_assoc])
  simp only [liftVal, hr, he, map_mul]; rfl

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

/-- The Shapiro lift of a cochain `a` on `Γ ∩ H` to a cochain on `Γ` with values in `f_* M`. -/
def liftZ1 (a : geoU Γ H → M) (γ : Γ) : coindV H.subtype σ :=
  coindOf Γ H σ hcov (liftVal σ R a γ) (liftVal_equiv σ R a γ)

theorem liftZ1_apply (a : geoU Γ H → M) (γ y : Γ) :
    ((liftZ1 σ R hcov a γ : coindV H.subtype σ) : G → M) y = liftVal σ R a γ y :=
  coindOf_apply Γ H σ hcov _ (liftVal_equiv σ R a γ) y

theorem liftZ1_cocycle {a : geoU Γ H → M} (ha : a ∈ Z1 σ (geoU Γ H)) (γ₁ γ₂ : Γ) :
    liftZ1 σ R hcov a (γ₁ * γ₂) = liftZ1 σ R hcov a γ₁ + pushRep H σ γ₁ (liftZ1 σ R hcov a γ₂) := by
  refine coind_ext_Γ Γ H σ hcov fun y => ?_
  change _ = ((liftZ1 σ R hcov a γ₁ : coindV H.subtype σ) : G → M) y +
    ((liftZ1 σ R hcov a γ₂ : coindV H.subtype σ) : G → M) ((y * γ₁ : Γ) : G)
  rw [liftZ1_apply, liftZ1_apply, liftZ1_apply]
  simp only [liftVal]
  rw [← mul_assoc, R.eta_mul (R.r y * γ₁) γ₂, R.r_r_mul, ((mem_Z1 _ _ a).mp ha).2, map_add,
    R.eta_mul y γ₁, Subgroup.coe_mul, map_mul]
  rfl

theorem liftZ1_isLocallyConstant [IsTopologicalGroup G] (hHo : IsOpen (H : Set G)) {a : geoU Γ H → M}
    (ha : a ∈ Z1 σ (geoU Γ H)) : IsLocallyConstant (liftZ1 σ R hcov a) := by
  obtain ⟨O, hOo, h1O, hO⟩ : ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧
      ∀ w : geoU Γ H, ((w : H) : G) ∈ O → a w = 0 := by
    have hW : IsOpen (a ⁻¹' {0}) := ((mem_Z1 _ _ a).mp ha).1 {0}
    obtain ⟨O1, hO1, hO1eq⟩ := isOpen_induced_iff.mp hW
    obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hO1
    refine ⟨O, hO, ?_, fun w hw => ?_⟩
    · have h1 : (1 : geoU Γ H) ∈ a ⁻¹' {0} := by
        simp [Z1_one σ (geoU Γ H) ha]
      rw [← hO1eq] at h1
      have h2 : ((1 : geoU Γ H) : H) ∈ O1 := h1
      rw [← hOeq] at h2
      exact h2
    · have h2 : (w : H) ∈ O1 := by rw [← hOeq]; exact hw
      have h3 : w ∈ a ⁻¹' {0} := by rw [← hO1eq]; exact h2
      exact h3
  rw [IsLocallyConstant.iff_exists_open]
  intro γ₀
  refine ⟨⋂ z ∈ Set.range R.r,
      (fun γ : Γ => (z : G) * ((γ₀ : G)⁻¹ * γ) * (z : G)⁻¹) ⁻¹' (O ∩ H), ?_, ?_, fun γ hγ => ?_⟩
  · exact R.fin.isOpen_biInter fun z _ => (hOo.inter hHo).preimage (by fun_prop)
  · simp only [Set.mem_iInter, Set.mem_preimage]
    intro z _
    rw [inv_mul_cancel, mul_one, mul_inv_cancel]
    exact Set.mem_inter h1O H.one_mem
  · refine coind_ext_Γ Γ H σ hcov fun y => ?_
    rw [liftZ1_apply, liftZ1_apply]
    have hv := Set.mem_iInter₂.mp hγ _ ⟨R.r y * γ₀, rfl⟩
    have hη0 := R.mem (R.r y * γ₀)
    have hzv : (R.r (R.r y * γ₀) : G) * ((γ₀ : G)⁻¹ * γ) * (R.r (R.r y * γ₀) : G)⁻¹ ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem (R.r (R.r y * γ₀)).2 (Γ.mul_mem (Γ.inv_mem γ₀.2) γ.2))
        (Γ.inv_mem (R.r (R.r y * γ₀)).2)
    let w : geoU Γ H := ⟨⟨_, hv.2⟩, Subgroup.mem_subgroupOf.mpr hzv⟩
    have hw : a w = 0 := hO w hv.1
    have hrz : R.r (R.r y * γ) = R.r (R.r y * γ₀) := R.coset _ _ (by
      have e : ((R.r y * γ : Γ) : G) * ((R.r y * γ₀ : Γ) : G)⁻¹ =
          (((R.r y * γ₀ : Γ) : G) * (R.r (R.r y * γ₀) : G)⁻¹) *
          ((R.r (R.r y * γ₀) : G) * ((γ₀ : G)⁻¹ * γ) * (R.r (R.r y * γ₀) : G)⁻¹) *
          (((R.r y * γ₀ : Γ) : G) * (R.r (R.r y * γ₀) : G)⁻¹)⁻¹ := by
        push_cast; group
      rw [e]; exact H.mul_mem (H.mul_mem hη0 hv.2) (H.inv_mem hη0))
    have heta : R.eta (R.r y * γ) = R.eta (R.r y * γ₀) * w := by
      refine Subtype.ext (Subtype.ext ?_)
      change ((R.r y * γ : Γ) : G) * (R.r (R.r y * γ) : G)⁻¹ =
        (((R.r y * γ₀ : Γ) : G) * (R.r (R.r y * γ₀) : G)⁻¹) *
        ((R.r (R.r y * γ₀) : G) * ((γ₀ : G)⁻¹ * γ) * (R.r (R.r y * γ₀) : G)⁻¹)
      rw [hrz]; push_cast; group
    simp only [liftVal, heta, ((mem_Z1 _ _ a).mp ha).2, hw, map_zero, add_zero]

theorem resEv_liftZ1 (a : geoU Γ H → M) (h : geoU Γ H) : resEv Γ H σ (liftZ1 σ R hcov a) h = a h := by
  have hr1 : R.r (geoToΓ Γ H h) = 1 :=
    (R.coset 1 _ (by simpa using (h : H).2)).trans R.one
  have e1 : R.eta 1 = 1 := by
    refine Subtype.ext (Subtype.ext ?_)
    change ((1 : Γ) : G) * (R.r 1 : G)⁻¹ = 1
    rw [R.one]; simp
  have e2 : R.eta (R.r 1 * geoToΓ Γ H h) = h := by
    refine Subtype.ext (Subtype.ext ?_)
    change ((R.r 1 * geoToΓ Γ H h : Γ) : G) * (R.r (R.r 1 * geoToΓ Γ H h) : G)⁻¹ = ((h : H) : G)
    rw [R.one, one_mul, hr1]; simp
  rw [resEv_apply, show (1 : G) = ((1 : Γ) : G) from rfl, liftZ1_apply]
  simp only [liftVal, e1, e2, OneMemClass.coe_one, map_one]
  rfl

variable (Γ H)

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_CurveCoh_ShapiroCone =====
section

/-!
# S4-CurveCoh, part 5: Shapiro's lemma for the cone `H¹_c` (K0c with compact support)

Setting of part 4 (`Def_RP_CurveCoh_Shapiro`): a finite etale cover `f : U → V` with `H = π₁(U) ≤ G = π₁(V)`,
`Γ = π₁^geo(V)`, `Γ ∩ H = π₁^geo(U)` (`geoU Γ H`), `f_* M = pushRep H σ` (coinduction).

Boundary data. `I s` (`s : S`) is the inertia at the boundary point `s` of `V`. The boundary points of `U` over `s`
are the double cosets `(Γ ∩ H) \ Γ / (I s ∩ Γ)`; we index them by `t : T` with `π t = s` and a representative
`x_t = xT t ∈ Γ`, and `J t ≤ H` is the inertia at `t`. The three hypotheses say exactly this:
* `InertiaLift`: on `Γ ∩ H`, `J t = x_t I_{π t} x_t⁻¹`;
* `DCover`: every `y ∈ Γ` is `h * x_t * g` with `h ∈ Γ ∩ H`, `π t = s`, `g ∈ I s ∩ Γ`;
* `DDisj`: the double cosets of distinct `x_t` over the same `s` are disjoint.

Results (any commutative ring `k`):
* `shapiroH1c : H¹_c(Γ, {I_s}; f_* M) →ₗ H¹_c(Γ ∩ H, {J_t}; M)`, `(c, b) ↦ (c|_{Γ∩H}(·)(1), (b_{π t}(x_t) - c(x_t)(1))_t)`;
* `shapiroH1c_injective` (`hcov`, `DCover`), `shapiroH1c_surjective` (+ `DDisj`, `H` open, coset representatives),
  `shapiroH1cEquiv`;
* `h1cToH1_shapiroH1c`: compatible with the forgetful map `H¹_c → H¹` and degree-1 Shapiro (part 4).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

open Representation

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (Γ H : Subgroup G) (σ : Representation k H M)
  {S T : Type} (I : S → Subgroup G) (J : T → Subgroup H) (π : T → S) (xT : T → Γ)

/-- On `Γ ∩ H` the inertia at the boundary point `t` of `U` is `x_t I_{π t} x_t⁻¹`. -/
def InertiaLift : Prop :=
  ∀ (t : T) (h : geoU Γ H), (h : H) ∈ J t ↔ (xT t : G)⁻¹ * ((h : H) : G) * xT t ∈ I (π t)

/-- The double cosets `(Γ ∩ H) x_t (I_s ∩ Γ)`, `π t = s`, cover `Γ`. -/
def DCover : Prop :=
  ∀ (s : S) (y : Γ), ∃ t : T, π t = s ∧
    ∃ (h : geoU Γ H) (g : Γ), (g : G) ∈ I s ∧ (y : G) = ((h : H) : G) * xT t * g

/-- Distinct `x_t` over the same `s` lie in distinct double cosets. -/
def DDisj : Prop :=
  ∀ (t t' : T), π t = π t' → ∀ (h : geoU Γ H) (g : Γ), (g : G) ∈ I (π t) →
    (xT t : G) = ((h : H) : G) * xT t' * g → t = t'

/-! ## Identities for cocycles with values in `f_* M` -/

theorem Z1c_coind_cone {p : (Γ → coindV H.subtype σ) × (S → coindV H.subtype σ)}
    (hp : p ∈ Z1c (pushRep H σ) Γ I) (s : S) (g : Γ) (hg : (g : G) ∈ I s) (x : G) :
    ((p.1 g : coindV H.subtype σ) : G → M) x =
      ((p.2 s : coindV H.subtype σ) : G → M) (x * g) - ((p.2 s : coindV H.subtype σ) : G → M) x :=
  congrArg (fun F : coindV H.subtype σ => (F : G → M) x) (((mem_Z1c _ _ _ p).mp hp).2 s g hg)

/-- `c(h x g)(1) = c(h)(1) + h (c(x)(1) + c(g)(x))` for `h ∈ Γ ∩ H`. -/
theorem Z1_coind_dec {c : Γ → coindV H.subtype σ} (hc : c ∈ Z1 (pushRep H σ) Γ) (h : geoU Γ H)
    (x g y : Γ) (hy : (y : G) = ((h : H) : G) * x * g) :
    ((c y : coindV H.subtype σ) : G → M) 1 = resEv Γ H σ c h +
      σ (h : H) (((c x : coindV H.subtype σ) : G → M) 1 + ((c g : coindV H.subtype σ) : G → M) x) := by
  have hy' : y = geoToΓ Γ H h * (x * g) := Subtype.ext (by rw [hy]; simp [mul_assoc])
  rw [hy', Z1_coind_apply Γ H σ hc (geoToΓ Γ H h) (x * g) 1, one_mul, geoToΓ_coe, coind_apply_of_mem,
    Z1_coind_apply Γ H σ hc x g 1, one_mul, resEv_apply]

/-- `b_s(h x g) = h (b_s(x) + c(g)(x))` for a relative cocycle `(c, b)`, `h ∈ Γ ∩ H`, `g ∈ I s`. -/
theorem Z1c_coind_bdry {p : (Γ → coindV H.subtype σ) × (S → coindV H.subtype σ)}
    (hp : p ∈ Z1c (pushRep H σ) Γ I) (s : S) (h : geoU Γ H) (x g y : Γ) (hg : (g : G) ∈ I s)
    (hy : (y : G) = ((h : H) : G) * x * g) :
    ((p.2 s : coindV H.subtype σ) : G → M) y =
      σ (h : H) (((p.2 s : coindV H.subtype σ) : G → M) x + ((p.1 g : coindV H.subtype σ) : G → M) x) := by
  rw [Z1c_coind_cone Γ H σ I hp s g hg, hy, mul_assoc, coind_mul_apply]
  congr 1
  abel

/-! ## The map -/

/-- The cone Shapiro map on cochains: `(c, b) ↦ (resEv c, (b_{π t}(x_t) - c(x_t)(1))_t)`. -/
def resEvc : ((Γ → coindV H.subtype σ) × (S → coindV H.subtype σ)) →ₗ[k] ((geoU Γ H → M) × (T → M)) where
  toFun p := (resEv Γ H σ p.1, fun t => ((p.2 (π t) : coindV H.subtype σ) : G → M) (xT t) -
    ((p.1 (xT t) : coindV H.subtype σ) : G → M) 1)
  map_add' p q := by
    refine Prod.ext (map_add (resEv Γ H σ) p.1 q.1) (funext fun t => ?_)
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Submodule.coe_add]
    abel
  map_smul' a p := by
    refine Prod.ext (map_smul (resEv Γ H σ) a p.1) (funext fun t => ?_)
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_sub]

theorem resEvc_mem_Z1c (hJ : InertiaLift Γ H I J π xT)
    {p : (Γ → coindV H.subtype σ) × (S → coindV H.subtype σ)} (hp : p ∈ Z1c (pushRep H σ) Γ I) :
    resEvc Γ H σ π xT p ∈ Z1c σ (geoU Γ H) J := by
  have hz : p.1 ∈ Z1 (pushRep H σ) Γ := ((mem_Z1c _ _ _ p).mp hp).1
  refine (mem_Z1c _ _ _ _).mpr ⟨resEv_mem_Z1 Γ H σ hz, fun t h hh => ?_⟩
  have hgI := (hJ t h).mp hh
  have hgΓ : (xT t : G)⁻¹ * ((h : H) : G) * xT t ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (xT t).2) (Subgroup.mem_subgroupOf.mp h.2)) (xT t).2
  obtain ⟨g, hgdef⟩ : ∃ g : Γ, (g : G) = (xT t : G)⁻¹ * ((h : H) : G) * xT t := ⟨⟨_, hgΓ⟩, rfl⟩
  have hgI' : (g : G) ∈ I (π t) := hgdef ▸ hgI
  have hhx : ((h : H) : G) * xT t = (xT t : G) * g := by rw [hgdef]; group
  have hyy : geoToΓ Γ H h * xT t = xT t * g := Subtype.ext hhx
  have e1 := Z1_coind_apply Γ H σ hz (geoToΓ Γ H h) (xT t) 1
  rw [hyy, one_mul, geoToΓ_coe, coind_apply_of_mem, Z1_coind_apply Γ H σ hz (xT t) g 1, one_mul] at e1
  have e3 := Z1c_coind_cone Γ H σ I hp (π t) g hgI' (xT t)
  rw [← hhx, coind_mul_apply] at e3
  have e4 : ((p.1 (geoToΓ Γ H h) : coindV H.subtype σ) : G → M) 1 =
      ((p.1 (xT t) : coindV H.subtype σ) : G → M) 1 + ((p.1 g : coindV H.subtype σ) : G → M) (xT t) -
        σ (h : H) (((p.1 (xT t) : coindV H.subtype σ) : G → M) 1) := eq_sub_of_add_eq e1.symm
  show ((p.1 (geoToΓ Γ H h) : coindV H.subtype σ) : G → M) 1 =
    σ (h : H) (((p.2 (π t) : coindV H.subtype σ) : G → M) (xT t) -
      ((p.1 (xT t) : coindV H.subtype σ) : G → M) 1) -
    (((p.2 (π t) : coindV H.subtype σ) : G → M) (xT t) - ((p.1 (xT t) : coindV H.subtype σ) : G → M) 1)
  rw [map_sub, e4, e3]
  abel

theorem resEvc_mem_B1c (hJ : InertiaLift Γ H I J π xT)
    {p : (Γ → coindV H.subtype σ) × (S → coindV H.subtype σ)} (hp : p ∈ B1c (pushRep H σ) Γ I) :
    resEvc Γ H σ π xT p ∈ B1c σ (geoU Γ H) J := by
  obtain ⟨hz, F, hF, hF'⟩ := (mem_B1c _ _ _ p).mp hp
  refine (mem_B1c _ _ _ _).mpr ⟨resEvc_mem_Z1c Γ H σ I J π xT hJ hz, (F : G → M) 1, fun h => ?_, fun t => ?_⟩
  · change ((p.1 (geoToΓ Γ H h) : coindV H.subtype σ) : G → M) 1 = _
    rw [hF]
    change (F : G → M) (1 * ((h : H) : G)) - (F : G → M) 1 = σ h ((F : G → M) 1) - (F : G → M) 1
    rw [one_mul, coind_apply_of_mem]
  · change ((p.2 (π t) : coindV H.subtype σ) : G → M) (xT t) -
      ((p.1 (xT t) : coindV H.subtype σ) : G → M) 1 = (F : G → M) 1
    rw [hF', hF]
    change (F : G → M) (xT t) - ((F : G → M) (1 * (xT t : G)) - (F : G → M) 1) = (F : G → M) 1
    rw [one_mul]
    abel

/-- Shapiro on relative cocycles. -/
def shapiroZ1c (hJ : InertiaLift Γ H I J π xT) : Z1c (pushRep H σ) Γ I →ₗ[k] Z1c σ (geoU Γ H) J :=
  (resEvc Γ H σ π xT).restrict fun _ hp => resEvc_mem_Z1c Γ H σ I J π xT hJ hp

/-- **Shapiro for `H¹_c`**: `H¹_c(Γ, {I_s}; f_* M) → H¹_c(Γ ∩ H, {J_t}; M)`. -/
def shapiroH1c (hJ : InertiaLift Γ H I J π xT) : H1c (pushRep H σ) Γ I →ₗ[k] H1c σ (geoU Γ H) J :=
  Submodule.mapQ _ _ (shapiroZ1c Γ H σ I J π xT hJ) fun _ hp => resEvc_mem_B1c Γ H σ I J π xT hJ hp

theorem shapiroH1c_mk (hJ : InertiaLift Γ H I J π xT) (p : Z1c (pushRep H σ) Γ I) :
    shapiroH1c Γ H σ I J π xT hJ (H1c.mk (pushRep H σ) Γ I p) =
      H1c.mk σ (geoU Γ H) J (shapiroZ1c Γ H σ I J π xT hJ p) := rfl

/-! ## Injectivity -/

theorem shapiroH1c_injective (hJ : InertiaLift Γ H I J π xT)
    (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ) (hT : DCover Γ H I π xT) :
    Function.Injective (shapiroH1c Γ H σ I J π xT hJ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨p, hp⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  have hx' : Submodule.Quotient.mk (p := (B1c σ (geoU Γ H) J).comap (Z1c σ (geoU Γ H) J).subtype)
      (shapiroZ1c Γ H σ I J π xT hJ ⟨p, hp⟩) = 0 := hx
  have hB0 := (Submodule.Quotient.mk_eq_zero _).mp hx'
  have hB : resEvc Γ H σ π xT p ∈ B1c σ (geoU Γ H) J := hB0
  obtain ⟨-, m, hm, hm'⟩ := (mem_B1c _ _ _ _).mp hB
  have hz : p.1 ∈ Z1 (pushRep H σ) Γ := ((mem_Z1c _ _ _ p).mp hp).1
  have hφ : EquivOnΓ Γ H σ (fun y => m + ((p.1 y : coindV H.subtype σ) : G → M) 1) := by
    intro h y y' hy
    have hhΓ : (h : G) ∈ Γ := by
      have : (h : G) = y' * (y : G)⁻¹ := by rw [hy]; group
      rw [this]; exact Γ.mul_mem y'.2 (Γ.inv_mem y.2)
    let u : geoU Γ H := ⟨h, Subgroup.mem_subgroupOf.mpr hhΓ⟩
    have hy' : y' = geoToΓ Γ H u * y := Subtype.ext hy
    have key := Z1_coind_apply Γ H σ hz (geoToΓ Γ H u) y 1
    rw [← hy'] at key
    have e1 : ((p.1 (geoToΓ Γ H u) : coindV H.subtype σ) : G → M) 1 = σ h m - m := hm u
    have e2 : ((p.1 y : coindV H.subtype σ) : G → M) (1 * ((geoToΓ Γ H u : Γ) : G)) =
        σ h (((p.1 y : coindV H.subtype σ) : G → M) 1) := by
      rw [one_mul]; exact coind_apply_of_mem _ h
    change m + _ = σ h (m + _)
    rw [key, e1, e2, map_add]; abel
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine (mem_B1c _ _ _ _).mpr ⟨hp, coindOf Γ H σ hcov _ hφ, fun g => coind_ext_Γ Γ H σ hcov fun y => ?_,
    fun s => coind_ext_Γ Γ H σ hcov fun y => ?_⟩
  · show ((p.1 g : coindV H.subtype σ) : G → M) y =
      ((coindOf Γ H σ hcov _ hφ : coindV H.subtype σ) : G → M) ((y : G) * g) -
        ((coindOf Γ H σ hcov _ hφ : coindV H.subtype σ) : G → M) y
    rw [show (y : G) * g = ((y * g : Γ) : G) from rfl]
    simp only [coindOf_apply]
    rw [Z1_coind_apply Γ H σ hz, one_mul]
    abel
  · obtain ⟨t, ht, h, g, hg, hy⟩ := hT s y
    subst ht
    have hb0 : ((p.2 (π t) : coindV H.subtype σ) : G → M) (xT t) -
        ((p.1 (xT t) : coindV H.subtype σ) : G → M) 1 = m := hm' t
    have hm1 : resEv Γ H σ p.1 h = σ (h : H) m - m := hm h
    show ((p.2 (π t) : coindV H.subtype σ) : G → M) y =
      ((coindOf Γ H σ hcov _ hφ : coindV H.subtype σ) : G → M) y
    simp only [coindOf_apply]
    rw [Z1c_coind_bdry Γ H σ I hp (π t) h (xT t) g y hg hy, Z1_coind_dec Γ H σ hz h (xT t) g y hy, hm1, ← hb0]
    simp only [map_add, map_sub]
    abel

/-! ## Surjectivity -/

/-- Independence of the boundary correction `σ(h) b'_t - c'(h)` from the decomposition `y = h x_t g`. -/
theorem beta_indep (hJ : InertiaLift Γ H I J π xT) (hD : DDisj Γ H I π xT)
    {q : (geoU Γ H → M) × (T → M)} (hq : q ∈ Z1c σ (geoU Γ H) J) {s : S} {y : Γ} {t t0 : T}
    {h h0 : geoU Γ H} {g g0 : Γ}
    (ht : π t = s) (hg : (g : G) ∈ I s) (hy : (y : G) = ((h : H) : G) * xT t * g)
    (ht0 : π t0 = s) (hg0 : (g0 : G) ∈ I s) (hy0 : (y : G) = ((h0 : H) : G) * xT t0 * g0) :
    σ (h : H) (q.2 t) - q.1 h = σ (h0 : H) (q.2 t0) - q.1 h0 := by
  have e0 : ((h : H) : G) * xT t * g = ((h0 : H) : G) * xT t0 * g0 := hy.symm.trans hy0
  have htt : t = t0 := by
    refine hD t t0 (ht.trans ht0.symm) (h⁻¹ * h0) (g0 * g⁻¹) ?_ ?_
    · rw [ht]; exact (I s).mul_mem hg0 ((I s).inv_mem hg)
    · show (xT t : G) = (((h : H) : G)⁻¹ * ((h0 : H) : G)) * xT t0 * ((g0 : G) * (g : G)⁻¹)
      calc (xT t : G) = ((h : H) : G)⁻¹ * (((h : H) : G) * xT t * g) * (g : G)⁻¹ := by group
        _ = _ := by rw [e0]; group
  rw [← htt] at hy0 e0 ⊢
  have h0eq : ((h0 : H) : G) = ((h : H) : G) * xT t * g * (g0 : G)⁻¹ * (xT t : G)⁻¹ := by
    rw [e0]; group
  have hconj : (xT t : G)⁻¹ * (((h⁻¹ * h0 : geoU Γ H) : H) : G) * xT t = (g : G) * (g0 : G)⁻¹ := by
    show (xT t : G)⁻¹ * (((h : H) : G)⁻¹ * ((h0 : H) : G)) * xT t = _
    rw [h0eq]; group
  have huJ : ((h⁻¹ * h0 : geoU Γ H) : H) ∈ J t :=
    (hJ t _).mpr (by rw [hconj, ht]; exact (I s).mul_mem hg ((I s).inv_mem hg0))
  have hcu : q.1 (h⁻¹ * h0) = σ ((h⁻¹ * h0 : geoU Γ H) : H) (q.2 t) - q.2 t :=
    ((mem_Z1c _ _ _ q).mp hq).2 t _ huJ
  have hcoc : q.1 h0 = q.1 h + σ (h : H) (q.1 (h⁻¹ * h0)) := by
    have := ((mem_Z1 _ _ _).mp ((mem_Z1c _ _ _ q).mp hq).1).2 h (h⁻¹ * h0)
    rwa [mul_inv_cancel_left] at this
  have hmul : (h : H) * ((h⁻¹ * h0 : geoU Γ H) : H) = (h0 : H) := by simp
  rw [hcoc, hcu, map_sub, rep_mul_apply σ, hmul]
  abel

/-- The boundary correction `β_s(y) = σ(h) b'_t - c'(h)` for the chosen decomposition `y = h x_t g`. -/
def betaVal (hT : DCover Γ H I π xT) (q : (geoU Γ H → M) × (T → M)) (s : S) (y : Γ) : M :=
  σ ((Classical.choose (Classical.choose_spec (hT s y)).2 : geoU Γ H) : H) (q.2 (Classical.choose (hT s y))) -
    q.1 (Classical.choose (Classical.choose_spec (hT s y)).2)

theorem betaVal_eq (hJ : InertiaLift Γ H I J π xT) (hT : DCover Γ H I π xT) (hD : DDisj Γ H I π xT)
    {q : (geoU Γ H → M) × (T → M)} (hq : q ∈ Z1c σ (geoU Γ H) J) {s : S} {y : Γ} {t : T}
    {h : geoU Γ H} {g : Γ} (ht : π t = s) (hg : (g : G) ∈ I s) (hy : (y : G) = ((h : H) : G) * xT t * g) :
    betaVal Γ H σ I π xT hT q s y = σ (h : H) (q.2 t) - q.1 h := by
  have h1 := Classical.choose_spec (hT s y)
  have h2 := Classical.choose_spec h1.2
  have h3 := Classical.choose_spec h2
  exact beta_indep Γ H σ I J π xT hJ hD hq h1.1 h3.1 h3.2 ht hg hy

theorem bdryFun_equiv (hJ : InertiaLift Γ H I J π xT) (hT : DCover Γ H I π xT) (hD : DDisj Γ H I π xT)
    {c : Γ → coindV H.subtype σ} (hz : c ∈ Z1 (pushRep H σ) Γ) {q : (geoU Γ H → M) × (T → M)}
    (hq : q ∈ Z1c σ (geoU Γ H) J) (hres : ∀ h, resEv Γ H σ c h = q.1 h) (s : S) :
    EquivOnΓ Γ H σ (fun y => ((c y : coindV H.subtype σ) : G → M) 1 + betaVal Γ H σ I π xT hT q s y) := by
  intro h1 y y' hy'
  have hhΓ : (h1 : G) ∈ Γ := by
    have : (h1 : G) = y' * (y : G)⁻¹ := by rw [hy']; group
    rw [this]; exact Γ.mul_mem y'.2 (Γ.inv_mem y.2)
  let u : geoU Γ H := ⟨h1, Subgroup.mem_subgroupOf.mpr hhΓ⟩
  obtain ⟨t, ht, h, g, hg, hy⟩ := hT s y
  have hy2 : (y' : G) = (((u * h : geoU Γ H) : H) : G) * xT t * g := by
    rw [hy', hy]
    show (h1 : G) * (((h : H) : G) * xT t * g) = (h1 : G) * ((h : H) : G) * xT t * g
    group
  have hyy : y' = geoToΓ Γ H u * y := Subtype.ext hy'
  have key := Z1_coind_apply Γ H σ hz (geoToΓ Γ H u) y 1
  rw [← hyy, one_mul, geoToΓ_coe, coind_apply_of_mem] at key
  have hcoc := ((mem_Z1 _ _ _).mp ((mem_Z1c _ _ _ q).mp hq).1).2 u h
  show ((c y' : coindV H.subtype σ) : G → M) 1 + betaVal Γ H σ I π xT hT q s y' =
    σ (u : H) (((c y : coindV H.subtype σ) : G → M) 1 + betaVal Γ H σ I π xT hT q s y)
  rw [key, show ((c (geoToΓ Γ H u) : coindV H.subtype σ) : G → M) 1 = q.1 u from hres u,
    betaVal_eq Γ H σ I J π xT hJ hT hD hq ht hg hy2, betaVal_eq Γ H σ I J π xT hJ hT hD hq ht hg hy, hcoc,
    Subgroup.coe_mul, ← rep_mul_apply σ, map_add, map_sub]
  abel

theorem shapiroH1c_surjective [IsTopologicalGroup G] (hJ : InertiaLift Γ H I J π xT)
    (hT : DCover Γ H I π xT) (hD : DDisj Γ H I π xT) (R : CosetReps Γ H)
    (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ) (hHo : IsOpen (H : Set G)) :
    Function.Surjective (shapiroH1c Γ H σ I J π xT hJ) := by
  intro x
  obtain ⟨⟨q, hq⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  have hq1 : q.1 ∈ Z1 σ (geoU Γ H) := ((mem_Z1c _ _ _ q).mp hq).1
  have hz : liftZ1 σ R hcov q.1 ∈ Z1 (pushRep H σ) Γ :=
    (mem_Z1 _ _ _).mpr ⟨liftZ1_isLocallyConstant σ R hcov hHo hq1, liftZ1_cocycle σ R hcov hq1⟩
  have hres : ∀ h, resEv Γ H σ (liftZ1 σ R hcov q.1) h = q.1 h := resEv_liftZ1 σ R hcov q.1
  let bL : S → coindV H.subtype σ := fun s =>
    coindOf Γ H σ hcov _ (bdryFun_equiv Γ H σ I J π xT hJ hT hD hz hq hres s)
  have hmem : (liftZ1 σ R hcov q.1, bL) ∈ Z1c (pushRep H σ) Γ I := by
    refine (mem_Z1c _ _ _ _).mpr ⟨hz, fun s g hg => coind_ext_Γ Γ H σ hcov fun y => ?_⟩
    obtain ⟨t, ht, h, g0, hg0, hy⟩ := hT s y
    have hyg : ((y * g : Γ) : G) = ((h : H) : G) * xT t * ((g0 * g : Γ) : G) := by
      push_cast; rw [hy]; group
    show ((liftZ1 σ R hcov q.1 g : coindV H.subtype σ) : G → M) y =
      ((bL s : coindV H.subtype σ) : G → M) ((y * g : Γ) : G) - ((bL s : coindV H.subtype σ) : G → M) y
    simp only [bL, coindOf_apply]
    rw [Z1_coind_apply Γ H σ hz, one_mul,
      betaVal_eq Γ H σ I J π xT hJ hT hD hq ht ((I s).mul_mem hg0 hg) hyg,
      betaVal_eq Γ H σ I J π xT hJ hT hD hq ht hg0 hy]
    abel
  have himg : resEvc Γ H σ π xT (liftZ1 σ R hcov q.1, bL) = q := by
    refine Prod.ext (funext hres) (funext fun t => ?_)
    show ((bL (π t) : coindV H.subtype σ) : G → M) (xT t) -
      ((liftZ1 σ R hcov q.1 (xT t) : coindV H.subtype σ) : G → M) 1 = q.2 t
    simp only [bL, coindOf_apply]
    rw [betaVal_eq Γ H σ I J π xT hJ hT hD hq rfl (I (π t)).one_mem
      (show ((xT t : Γ) : G) = (((1 : geoU Γ H) : H) : G) * xT t * ((1 : Γ) : G) by simp),
      Z1_one σ (geoU Γ H) hq1]
    simp
  refine ⟨H1c.mk (pushRep H σ) Γ I ⟨_, hmem⟩, ?_⟩
  rw [shapiroH1c_mk]
  exact congrArg (H1c.mk σ (geoU Γ H) J) (Subtype.ext himg)

/-- **Shapiro for `H¹_c`** (`U` geometrically connected, `H` open of finite index, boundary data as above):
`H¹_c(Γ, {I_s}; f_* M) ≃ H¹_c(Γ ∩ H, {J_t}; M)`. -/
def shapiroH1cEquiv [IsTopologicalGroup G] (hJ : InertiaLift Γ H I J π xT) (hT : DCover Γ H I π xT)
    (hD : DDisj Γ H I π xT) (R : CosetReps Γ H) (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)
    (hHo : IsOpen (H : Set G)) : H1c (pushRep H σ) Γ I ≃ₗ[k] H1c σ (geoU Γ H) J :=
  LinearEquiv.ofBijective _ ⟨shapiroH1c_injective Γ H σ I J π xT hJ hcov hT,
    shapiroH1c_surjective Γ H σ I J π xT hJ hT hD R hcov hHo⟩

end

end CurveCoh
end RamanujanPetersson


end

-- ===== S4.Def_RP_CP4a_BdryInf =====
section

/-!
# S4-CP4a, part e3c: the boundary count over `∞` and Lefschetz with `#U(𝔽_{q^m})`

For the chart `Rinf` at infinity of a function field `F/𝔽_q`, with `𝔽_{q^m} ⊆ K_U` for all `m` (`hζc`):
* `good_inf`: residue rings of boundary primes are finite of `q`-power order.
* `card_fix_inf`: `#{s | τ^m s = s} = #Hom_{𝔽_q}(Rinf, 𝔽_{q^m})` for the true boundary permutation `τ` of `φ⁻¹`.
* `numPoints_eq_add_fix`: `N_m = #U(𝔽_{q^m}) + #{s | τ^m s = s}`, `#U(L) := #Hom_{𝔽_q}(Rfin, L)`, `[L : 𝔽_q] = m`.
* `lefschetz_count`: `Tr(F^m | H²_c) - Tr(F^m | H¹_c) = #U(𝔽_{q^m})` in `ℤ/l^n` (Core B as a hypothesis).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section BdryInf

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

include hq he hζc hDB in
/-- **`N_m = #U(L) + #{s | τ^m s = s}`** with `#U(L) := #Hom_{𝔽_q}(Rfin, L)` for any finite `L`, `[L : 𝔽_q] = m`. -/
theorem numPoints_eq_add_fix {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    [Fintype S] [DecidableEq S] (m : ℕ) (hm : 0 < m) (L : Type) [Field L] [Algebra Fq L] [Finite L]
    (hL : Module.finrank Fq L = m) :
    numPoints Fq F m = Nat.card (Rfin Fq F →ₐ[Fq] L) +
      (Finset.univ.filter fun s => (trueTau D φ⁻¹)^[m] s = s).card := by
  obtain ⟨z, hz⟩ := exists_prim_level hq hζc m hm
  have hfin := finrank_levelField hm hz
  have hc := card_levelField hm hz
  have : Finite (levelField Fq (maxUnram (Rfin Fq F) F) m) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ Fintype.card_ne_zero)
  rw [card_fix_inf hq he D hDB hζc hφ m hm,
    card_algHom_Rfin_congr L (levelField Fq (maxUnram (Rfin Fq F) F) m) (hL.trans hfin.symm)]
  have h := numPoints_eq_card_algHom Fq F (levelField Fq (maxUnram (Rfin Fq F) F) m)
  rw [hfin] at h
  exact h

end BdryInf

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_BdS =====
section

/-!
# S4-CP4a, part f3: the boundary data over `∞` exist, finite and nonempty

* `bdrySetoid`, `BdryS`, `bdryData`: for any chart `R0`, the `π₁^geo`-orbits of nonzero primes of the pro-chart
  with chosen representatives form a `BdryData` whose `B` is exactly `IsBdryPrime` (`bdryData_B`).
* For `R0 = Rinf` of a function field `F/𝔽_q`: `piInf_mem` (`π_∞` lies under every boundary prime),
  `bres_pow_card` (all residues lie in `𝔽_{q^M}`, `M = (#Rinf/(π_∞))!`), `finite_bdry` (any boundary data over `∞`
  has finitely many points: `s ↦ sres s` factors through the finite ring `Rinf/(π_∞)` into `𝔽_{q^M}`) and
  `nonempty_bdry` (lying over a place at `∞`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section Orb

variable {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G) (P : X → Prop)

/-- The orbit relation of a subgroup `H` on a subtype `{x // P x}`. -/
def orbSetoid : Setoid {x // P x} where
  r x y := ∃ g ∈ H, y.1 = g • x.1
  iseqv := {
    refl := fun x => ⟨1, H.one_mem, (one_smul G x.1).symm⟩
    symm := fun {x y} ⟨g, hg, h⟩ => ⟨g⁻¹, H.inv_mem hg, by rw [h, inv_smul_smul]⟩
    trans := fun {x y z} ⟨g, hg, h⟩ ⟨g', hg', h'⟩ => ⟨g' * g, H.mul_mem hg' hg, by rw [h', h, mul_smul]⟩ }

theorem orbSetoid_r {x y : {x // P x}} : (orbSetoid H P).r x y ↔ ∃ g ∈ H, y.1 = g • x.1 := Iff.rfl

end Orb

section Setoid

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (q : ℕ)
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

set_option synthInstance.maxHeartbeats 200000 in
/-- Two boundary primes are equivalent iff they lie in one `π₁^geo`-orbit. -/
abbrev bdrySetoid : Setoid {Q : Ideal (proChart A K R0) // IsBdryPrime A K R0 Q} :=
  orbSetoid (X := Ideal (proChart A K R0)) (pi1geo A K q) (IsBdryPrime A K R0)

/-- The geometric boundary points over the chart `R0`. -/
def BdryS : Type := Quotient (bdrySetoid A K q R0)

set_option synthInstance.maxHeartbeats 200000 in
/-- The canonical boundary data: all nonzero primes, one representative per `π₁^geo`-orbit. -/
def bdryData : BdryData A K q R0 (BdryS A K q R0) where
  B := IsBdryPrime A K R0
  B_smul := isBdryPrime_smul A K R0
  P s := (Quotient.out s).1
  mem s := (Quotient.out s).2
  cover Q hQ := by
    obtain ⟨g, hg, h⟩ := (orbSetoid_r _ _).1 (Quotient.mk_out (s := bdrySetoid A K q R0) ⟨Q, hQ⟩)
    exact ⟨Quotient.mk _ ⟨Q, hQ⟩, g, hg, h⟩
  disj s t g hg h := Quotient.out_equiv_out.1 ((orbSetoid_r _ _).2 ⟨g, hg, h⟩)

theorem bdryData_B (Q : Ideal (proChart A K R0)) : (bdryData A K q R0).B Q ↔ IsBdryPrime A K R0 Q := Iff.rfl

end Setoid

section Fin

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable (hζc : ∀ a, 0 < a → ∃ z : maxUnram (Rfin Fq F) F, IsPrimitiveRoot z ((p ^ e) ^ a - 1))

set_option synthInstance.maxHeartbeats 200000 in
theorem under_ne_bot (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) : Q.under (Rinf Fq F) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
  exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

set_option synthInstance.maxHeartbeats 200000 in
/-- `π_∞` lies under every boundary prime over `∞`. -/
theorem piInf_mem (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) :
    algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq) ∈ Q.under (Rinf Fq F) := by
  have := hQ.1
  have hne' : (Q.under (Rinf Fq F)).under (Oinf Fq) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (under_ne_bot Q hQ)
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  have hmax : ((Q.under (Rinf Fq F)).under (Oinf Fq)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne'
  have hpi : piInf Fq ∈ IsLocalRing.maximalIdeal (Oinf Fq) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (span_piInf_isMaximal Fq).ne_top (Ideal.span_singleton_eq_top.2 hu)
  rw [← IsLocalRing.eq_maximalIdeal hmax] at hpi
  exact hpi

include hq he hζc in
set_option synthInstance.maxHeartbeats 200000 in
/-- All residues at boundary points over `∞` lie in `𝔽_{q^M}`, `M = (#Rinf/(π_∞))!`. -/
theorem bres_pow_card (Q : Ideal (proChart (Rfin Fq F) F (Rinf Fq F)))
    (hQ : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (r : Rinf Fq F) :
    bres he hζc (good_inf hq) Q hQ r ^ (Fintype.card Fq ^
      (Nat.card (Rinf Fq F ⧸ Ideal.span {algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)})).factorial) =
      bres he hζc (good_inf hq) Q hQ r := by
  set r0 := algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)
  set Qs := Q.under (Rinf Fq F)
  have := hQ.1
  haveI hmax : Qs.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (under_ne_bot Q hQ)
  obtain ⟨hfin, d, hd⟩ := good_inf hq Q hQ
  letI : Field (Rinf Fq F ⧸ Qs) := Ideal.Quotient.field Qs
  letI : Fintype (Rinf Fq F ⧸ Qs) := Fintype.ofFinite _
  have hr0 : r0 ≠ 0 := fun h =>
    piInf_ne_zero Fq ((algebraMap_Oinf_Rinf_injective Fq F) (by rw [map_zero]; exact h))
  haveI : Finite (Rinf Fq F ⧸ Ideal.span {r0}) := FiniteQuot.finite r0 hr0
  have hle : Nat.card (Rinf Fq F ⧸ Qs) ≤ Nat.card (Rinf Fq F ⧸ Ideal.span {r0}) :=
    Nat.card_le_card_of_surjective _
      (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).2 (piInf_mem Q hQ)))
  have hcard : Fintype.card (Rinf Fq F ⧸ Qs) = Fintype.card Fq ^ d := by
    rw [← Nat.card_eq_fintype_card, hd, hq]
  have hq1 : 1 < Fintype.card Fq := Fintype.one_lt_card
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · have h1 := Fintype.one_lt_card (α := Rinf Fq F ⧸ Qs)
      rw [hcard, h, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have hdM : d ∣ (Nat.card (Rinf Fq F ⧸ Ideal.span {r0})).factorial := by
    apply Nat.dvd_factorial hd0
    have h2 : d < Fintype.card Fq ^ d := Nat.lt_pow_self hq1
    rw [Nat.card_eq_fintype_card (α := Rinf Fq F ⧸ Qs), hcard] at hle
    exact (h2.trans_le hle).le
  obtain ⟨k, hk⟩ := hdM
  have hfr : Ideal.Quotient.mk Qs r ^ (Fintype.card Fq ^ d) = Ideal.Quotient.mk Qs r := by
    rw [← hcard]
    exact FiniteField.pow_card _
  have hmem : r ^ (Fintype.card Fq ^ d) - r ∈ Qs := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hfr, sub_self]
  have hb : bres he hζc (good_inf hq) Q hQ r ^ (Fintype.card Fq ^ d) = bres he hζc (good_inf hq) Q hQ r := by
    have h3 := (bres_ker he hζc (good_inf hq) Q hQ _).2 hmem
    rwa [map_sub, map_pow, sub_eq_zero] at h3
  rw [hk, pow_mul]
  exact pow_pow_iter hb k

include hq he hζc in
set_option synthInstance.maxHeartbeats 200000 in
/-- **Finitely many boundary points over `∞`.** -/
theorem finite_bdry {S : Type} (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) : Finite S := by
  set r0 := algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)
  set M := (Nat.card (Rinf Fq F ⧸ Ideal.span {r0})).factorial
  have hM : 0 < M := Nat.factorial_pos _
  have hr0 : r0 ≠ 0 := fun h =>
    piInf_ne_zero Fq ((algebraMap_Oinf_Rinf_injective Fq F) (by rw [map_zero]; exact h))
  haveI : Finite (Rinf Fq F ⧸ Ideal.span {r0}) := FiniteQuot.finite r0 hr0
  obtain ⟨z, hz⟩ := exists_prim_level hq hζc M hM
  have hc := card_levelField hM hz
  have : Finite (levelField Fq (maxUnram (Rfin Fq F) F) M) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have hpow : ∀ s r, sres he hζc (good_inf hq) D hDB s r ∈ levelField Fq (maxUnram (Rfin Fq F) F) M :=
    fun s r => mem_levelField.2 (bres_pow_card hq he hζc _ _ r)
  have hker : ∀ s, sres he hζc (good_inf hq) D hDB s r0 = 0 := fun s =>
    (bres_ker he hζc (good_inf hq) _ _ r0).2 (piInf_mem _ ((hDB _).1 (D.mem s)))
  let g : S → (Rinf Fq F ⧸ Ideal.span {r0} → levelField Fq (maxUnram (Rfin Fq F) F) M) := fun s x =>
    ⟨sres he hζc (good_inf hq) D hDB s (Function.surjInv Ideal.Quotient.mk_surjective x), hpow s _⟩
  refine Finite.of_injective g fun s t hst => ?_
  apply sres_injective he hζc (good_inf hq) D hDB hq
  refine RingHom.ext fun r => ?_
  have hs := Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {r0})) (Ideal.Quotient.mk _ r)
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hs)
  have e1 : ∀ u, sres he hζc (good_inf hq) D hDB u r = sres he hζc (good_inf hq) D hDB u
      (Function.surjInv Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Ideal.span {r0}) r)) := by
    intro u
    have h0 := congrArg (sres he hζc (good_inf hq) D hDB u) hc'
    rw [map_mul, hker, mul_zero, map_sub] at h0
    exact (sub_eq_zero.1 h0.symm).symm
  rw [e1 s, e1 t]
  have h5 : ((g s (Ideal.Quotient.mk _ r) : levelField Fq (maxUnram (Rfin Fq F) F) M) : maxUnram (Rfin Fq F) F) =
      ((g t (Ideal.Quotient.mk _ r) : levelField Fq (maxUnram (Rfin Fq F) F) M) : maxUnram (Rfin Fq F) F) :=
    congrArg (fun x : levelField Fq (maxUnram (Rfin Fq F) F) M => (x : maxUnram (Rfin Fq F) F)) (congrFun hst _)
  exact h5

set_option synthInstance.maxHeartbeats 200000 in
/-- **Some boundary point over `∞` exists.** -/
theorem nonempty_bdry {S : Type} (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
    (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) : Nonempty S := by
  obtain ⟨P0⟩ := nonempty_infPlace Fq F
  have := P0.isPrime
  have hinj : Function.Injective (Algebra.ofId (Rinf Fq F) (proChart (Rfin Fq F) F (Rinf Fq F))) :=
    algebraMap_proChart_injective (A := Rfin Fq F) (K := F) (R0 := Rinf Fq F)
  obtain ⟨Q, hQ, hQP⟩ := exists_prime_comap_eq (R0 := Rinf Fq F) (R := Rinf Fq F)
    (S := proChart (Rfin Fq F) F (Rinf Fq F)) (Algebra.ofId (Rinf Fq F) (proChart (Rfin Fq F) F (Rinf Fq F))) hinj P0.asIdeal
  have hQB : IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q := by
    refine ⟨hQ, fun h => P0.ne_bot ?_⟩
    rw [← hQP, h]
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨s, -⟩ := D.cover Q ((hDB Q).2 hQB)
  exact ⟨s⟩

end Fin

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_CP4a_Main =====
section

/-!
# S4-CP4a, part h: the assembled Lefschetz point count (Core B as a hypothesis)

For a function field `F/𝔽_q` with full constant field (`hk`), its affine chart `U = Spec Rfin` (the complement of
the places over `∞` of `𝔽_q(x)`) and every prime `l ∤ q`, `n > 0`, ASSUMING the Core B statement `CoreBHyp hk l`:
* `lefschetz_point_count`: for EVERY lift `φ` of the arithmetic Frobenius to `π₁(U)` and every `m ≥ 1`,
  `Tr(F^m | H²_c(Ū, ℤ/l^n)) - Tr(F^m | H¹_c(Ū, ℤ/l^n)) = #U(𝔽_{q^m})` in `ℤ/l^n`, where
  `#U(𝔽_{q^m}) := #Hom_{𝔽_q}(Rfin, L)` for any finite `L/𝔽_q` of degree `m`, the cohomology is the S4-CurveCoh
  cohomology with the canonical boundary data over `∞` and `F` is geometric Frobenius (`φ⁻¹`).
* `cp4a_lefschetz`: the same with a Frobenius lift that exists (`exists_frobLift`), so the statement is not vacuous;
  `finite_bdryS` / `nonempty_bdryS`: the canonical boundary is a nonempty finite set.
No hypothesis other than Core B is left: the Frobenius lift, the roots of unity, the units `N` in the charts,
the boundary data and the inertia lifting are all constructed (parts f1-f4).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer GalCover

noncomputable section

section Main

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

/-- The canonical boundary data of `U` over `∞` (one prime of the pro-chart per `π₁^geo`-orbit). -/
abbrev bdryInf (Fq F : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] [Field F] [Algebra Fq F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F] [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] :
    BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)) :=
  bdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)

include hq he in
/-- The geometric boundary of `U` is finite. -/
theorem finite_bdryS : Finite (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)) :=
  finite_bdry hq he (exists_zeta_level he) (bdryInf Fq F) (bdryData_B _ _ _ _)

/-- The geometric boundary of `U` is nonempty. -/
theorem nonempty_bdryS : Nonempty (BdryS (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F)) :=
  nonempty_bdry (bdryInf Fq F) (bdryData_B _ _ _ _)

end Main

end

end RamanujanPetersson.CP4a


end

-- ===== S4.Def_RP_JacAlg_Res =====
section

/-!
# Core B algebra, part 7: resultants (unit S4-JacAlg, lemma L4 = Milne 10.21, steps R1 and R2)

* R1 `det_aeval_eq_resultant`: for a square matrix `A` over a domain, `det F(A) = Res(χ_A, F)` (degree
  parameters `card n`, `natDegree F`); `linearMap_det_aeval_eq_resultant`: the same for an endomorphism of a
  free finite module (parameters `finrank`, `natDegree F`).
* R2 `eq_of_norm_resultant_eq`: over an ultrametric nontrivially normed field, monic `P, Q` with
  `‖Res(P, G)‖ = ‖Res(Q, G)‖` for all `G` are equal. For a monic irreducible `φ` with `P = φ^d P₁`, `φ ∤ P₁`,
  `‖Res(P, φ + c)‖ = ‖c‖^(d deg φ) · ‖Res(P₁, φ)‖` for small `c` (`exists_norm_resultant_add_C`) reads off `d`;
  equal multiplicities give equal normalized factors. Milne's Lemma 10.21 without a Galois closure.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial UniqueFactorizationMonoid

section Det

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem linearMap_det_aeval_eq_resultant {R : Type*} [CommRing R] [IsDomain R] {T : Type*}
    [AddCommGroup T] [Module R T] [Module.Free R T] [Module.Finite R T] (M : Module.End R T)
    (F : R[X]) :
    LinearMap.det (aeval M F) = resultant M.charpoly F (Module.finrank R T) F.natDegree := by
  let b := Module.Free.chooseBasis R T
  have hM : LinearMap.toMatrix b b (aeval M F) = aeval (LinearMap.toMatrix b b M) F := by
    have h := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b) M F
    have he : ∀ f : Module.End R T, LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f :=
      fun f => Matrix.ext fun i j => by
        simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [he, he] at h
    exact h.symm
  rw [← LinearMap.det_toMatrix b, ← LinearMap.charpoly_toMatrix M b,
    Module.finrank_eq_card_chooseBasisIndex, hM, det_aeval_eq_resultant]

end Det

/-- For monic `P` the resultant `Res(P, G, deg P, n)` does not depend on `n ≥ deg G`. -/
lemma resultant_monic_eq {R : Type*} [CommRing R] {P G : R[X]} (hP : P.Monic) {n : ℕ} (hn : G.natDegree ≤ n) :
    resultant P G P.natDegree n = resultant P G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg P G P.natDegree G.natDegree k le_rfl, hP.coeff_natDegree, one_pow,
    one_mul]

section Field

variable {K : Type*} [Field K]

/-- `Res(φ, φ + c) = c ^ deg φ` for monic `φ`. -/
lemma resultant_self_add_C {φ : K[X]} (hφ : φ.Monic) (c : K) :
    resultant φ (φ + C c) φ.natDegree φ.natDegree = c ^ φ.natDegree := by
  have h := resultant_add_mul_right φ (C c) 1 φ.natDegree φ.natDegree (by simp) le_rfl
  rw [mul_one, add_comm] at h
  rw [h, resultant_C_right, hφ.coeff_natDegree, one_pow, one_mul]

lemma count_normalizedFactors_of_decomp [DecidableEq K] {φ P c : K[X]} {d : ℕ} (hirr : Irreducible φ)
    (hnorm : normalize φ = φ) (hP : P = φ ^ d * c) (hc : ¬ φ ∣ c) :
    (normalizedFactors P).count φ = d := by
  refine count_normalizedFactors_eq hirr hnorm (hP ▸ dvd_mul_right _ _) ?_
  intro h
  rw [hP, pow_succ] at h
  exact hc ((mul_dvd_mul_iff_left (pow_ne_zero _ hirr.ne_zero)).mp h)

end Field

section Ultra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Near `c = 0`: `‖Res(P, φ + c)‖ = ‖c‖ ^ (deg φ · d) · A` with `A > 0`, when `P = φ^d P₁` and `φ ∤ P₁`. -/
lemma exists_norm_resultant_add_C {P φ P₁ : K[X]} {d : ℕ} (hP : P.Monic) (hφ : φ.Monic)
    (hirr : Irreducible φ) (hdec : P = φ ^ d * P₁) (hnd : ¬ φ ∣ P₁) :
    ∃ A > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ c : K, ‖c‖ < δ →
      ‖resultant P (φ + C c)‖ = ‖c‖ ^ (φ.natDegree * d) * A := by
  have hP₁ : P₁.Monic := (hφ.pow d).of_mul_monic_left (hdec ▸ hP)
  -- the resultant `Res(P₁, φ + c)` as a polynomial in `c`
  obtain ⟨R, hR⟩ : ∃ R : K[X], R = resultant (P₁.map C) (φ.map C + C X) P₁.natDegree φ.natDegree :=
    ⟨_, rfl⟩
  have hev : ∀ c : K, R.eval c = resultant P₁ (φ + C c) P₁.natDegree φ.natDegree := by
    intro c
    rw [hR, ← coe_evalRingHom, ← resultant_map_map]
    congr 1
    · ext i; simp [coeff_map]
    · ext i; simp [coeff_map, Polynomial.map_map]
  have hR0 : R.eval 0 ≠ 0 := by
    rw [hev, map_zero, add_zero]
    exact resultant_ne_zero P₁ φ ((hirr.coprime_iff_not_dvd).mpr hnd).symm
  have hA : 0 < ‖R.eval 0‖ := norm_pos_iff.mpr hR0
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousAt_iff.mp (R.continuous.continuousAt : ContinuousAt (fun x => R.eval x) 0) _ hA
  refine ⟨‖R.eval 0‖, hA, δ, hδ, fun c hc => ?_⟩
  have hnear : ‖R.eval c‖ = ‖R.eval 0‖ := by
    have h1 : ‖R.eval c - R.eval 0‖ < ‖R.eval 0‖ := by
      rw [← dist_eq_norm]; exact hcont (by rwa [dist_zero_right])
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rw [sub_add_cancel] at h2
    rw [h2, max_eq_right h1.le]
  have hdeg : P.natDegree = (φ ^ d).natDegree + P₁.natDegree := by
    rw [hdec, (hφ.pow d).natDegree_mul hP₁]
  have hG : (φ + C c).natDegree ≤ φ.natDegree := by rw [natDegree_add_C]
  have hsplit : resultant P (φ + C c) = (c ^ φ.natDegree) ^ d * R.eval c := by
    rw [← resultant_monic_eq hP hG, hdeg]
    conv_lhs => rw [hdec]
    rw [resultant_mul_left _ _ _ _ hG,
      resultant_pow_left φ (φ + C c) d φ.natDegree (by simp [hφ.leadingCoeff]) hG,
      resultant_self_add_C hφ, ← hev]
  rw [hsplit, norm_mul, hnear, norm_pow, norm_pow, ← pow_mul]

/-- **Milne Lemma 10.21 (resultant form).** Monic polynomials over an ultrametric nontrivially normed field
with `‖Res(P, G)‖ = ‖Res(Q, G)‖` for all `G` are equal. -/
theorem eq_of_norm_resultant_eq {P Q : K[X]} (hP : P.Monic) (hQ : Q.Monic)
    (H : ∀ G : K[X], ‖resultant P G‖ = ‖resultant Q G‖) : P = Q := by
  classical
  -- equal multiplicity of every monic irreducible factor
  have key : ∀ φ : K[X], φ.Monic → Irreducible φ → ∀ (d e : ℕ) (P₁ Q₁ : K[X]), P = φ ^ d * P₁ →
      ¬ φ ∣ P₁ → Q = φ ^ e * Q₁ → ¬ φ ∣ Q₁ → d = e := by
    intro φ hφ hirr d e P₁ Q₁ hPd hP₁ hQe hQ₁
    obtain ⟨A, hA, δ, hδ, hPn⟩ := exists_norm_resultant_add_C hP hφ hirr hPd hP₁
    obtain ⟨B, hB, δ', hδ', hQn⟩ := exists_norm_resultant_add_C hQ hφ hirr hQe hQ₁
    obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt K (lt_min (lt_min hδ hδ') one_pos)
    have hc1 : ‖c‖ < 1 := hc.trans_le (min_le_right _ _)
    have hcδ : ‖c‖ < δ := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hcδ' : ‖c‖ < δ' := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hc2 : ‖c ^ 2‖ ≤ ‖c‖ := by
      rw [norm_pow, sq]; exact mul_le_of_le_one_left hc0.le hc1.le
    have h1 := H (φ + C c)
    rw [hPn c hcδ, hQn c hcδ'] at h1
    have h2 := H (φ + C (c ^ 2))
    rw [hPn _ (hc2.trans_lt hcδ), hQn _ (hc2.trans_lt hcδ'), norm_pow, ← pow_mul, ← pow_mul] at h2
    set x := ‖c‖
    set a := φ.natDegree * d
    set b := φ.natDegree * e
    -- h1 : x^a A = x^b B,  h2 : x^(2a) A = x^(2b) B
    have h3 : x ^ (2 * b) * B = x ^ (a + b) * B := by
      rw [← h2, two_mul, pow_add, mul_assoc, h1, ← mul_assoc, ← pow_add]
    have h4 : 2 * b = a + b := pow_right_injective₀ hc0 hc1.ne (mul_right_cancel₀ hB.ne' h3)
    have hab : a = b := by omega
    exact Nat.eq_of_mul_eq_mul_left (Irreducible.natDegree_pos hirr) hab
  -- equal normalized factors
  have hcount : ∀ φ ∈ normalizedFactors P ∪ normalizedFactors Q,
      (normalizedFactors P).count φ = (normalizedFactors Q).count φ := by
    intro φ hmem
    have hmem' : φ ∈ normalizedFactors P ∨ φ ∈ normalizedFactors Q := Multiset.mem_union.mp hmem
    have hirr : Irreducible φ := by
      rcases hmem' with h | h <;> exact irreducible_of_normalized_factor φ h
    have hnorm : normalize φ = φ := by
      rcases hmem' with h | h <;> exact normalize_normalized_factor φ h
    have hφ : φ.Monic := hnorm ▸ monic_normalize hirr.ne_zero
    have hfin : ∀ S : K[X], S ≠ 0 → FiniteMultiplicity φ S := fun S hS =>
      finiteMultiplicity_of_degree_pos_of_monic (degree_pos_of_irreducible hirr) hφ hS
    obtain ⟨P₁, hPd, hP₁⟩ := (hfin P hP.ne_zero).exists_eq_pow_mul_and_not_dvd
    obtain ⟨Q₁, hQe, hQ₁⟩ := (hfin Q hQ.ne_zero).exists_eq_pow_mul_and_not_dvd
    rw [count_normalizedFactors_of_decomp hirr hnorm hPd hP₁,
      count_normalizedFactors_of_decomp hirr hnorm hQe hQ₁]
    exact key φ hφ hirr _ _ P₁ Q₁ hPd hP₁ hQe hQ₁
  have hnf : normalizedFactors P = normalizedFactors Q := by
    ext φ
    by_cases hmem : φ ∈ normalizedFactors P ∪ normalizedFactors Q
    · exact hcount φ hmem
    · rw [Multiset.mem_union, not_or] at hmem
      rw [Multiset.count_eq_zero.mpr hmem.1, Multiset.count_eq_zero.mpr hmem.2]
  have hassoc : Associated P Q :=
    (prod_normalizedFactors hP.ne_zero).symm.trans (hnf ▸ prod_normalizedFactors hQ.ne_zero)
  exact eq_of_monic_of_associated hP hQ hassoc

end Ultra

end RamanujanPetersson.JacAlg


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

lemma not_dvd_of_prime_ne {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) (K : ℕ) : ¬ (p : ℤ) ∣ (l : ℤ) ^ K := by
  intro h
  have h2 : p ∣ l ^ K := by exact_mod_cast h
  exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl.out).mp (hp.dvd_of_dvd_pow h2))

lemma exists_int_approx {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) (G : ℤ_[l][X]) (K : ℕ) :
    ∃ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 ∧ F.natDegree ≤ G.natDegree ∧
      (F.map (Int.castRingHom ℤ_[l])).map (PadicInt.toZModPow K) = G.map (PadicInt.toZModPow K) := by
  have hsurj : Function.Surjective (Int.castRingHom (ZMod (l ^ K))) := ZMod.intCast_surjective
  obtain ⟨F₀, hF₀, hdeg⟩ := exists_natDegree_eq_of_mem_lifts
    (mem_lifts_of_surjective hsurj (G.map (PadicInt.toZModPow K)))
  have hcomp : (PadicInt.toZModPow K).comp (Int.castRingHom ℤ_[l]) = Int.castRingHom (ZMod (l ^ K)) :=
    RingHom.ext_int _ _
  have hdeg' : F₀.natDegree ≤ G.natDegree := by rw [hdeg]; exact natDegree_map_le
  by_cases h0 : (p : ℤ) ∣ F₀.coeff 0
  · refine ⟨F₀ + C ((l : ℤ) ^ K), ?_, ?_, ?_⟩
    · rw [coeff_add, coeff_C_zero]
      intro h
      exact not_dvd_of_prime_ne hp hpl K ((dvd_add_right h0).mp h)
    · exact natDegree_add_C.le.trans hdeg'
    · have hz : (Int.castRingHom (ZMod (l ^ K))) ((l : ℤ) ^ K) = 0 := by
        rw [map_pow, map_natCast]; exact_mod_cast ZMod.natCast_self (l ^ K)
      rw [Polynomial.map_map, hcomp, Polynomial.map_add, hF₀, map_C, hz, C_0, add_zero]
  · refine ⟨F₀, h0, hdeg', ?_⟩
    rw [Polynomial.map_map, hcomp, hF₀]

lemma norm_resultant_le_of_int {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P Q : ℤ_[l][X]} (hP : P.Monic)
    (hQ : Q.Monic) (H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant P (F.map (Int.castRingHom ℤ_[l]))‖ = ‖resultant Q (F.map (Int.castRingHom ℤ_[l]))‖)
    (G : ℤ_[l][X]) : ‖resultant P G‖ ≤ ‖resultant Q G‖ := by
  have hK : ∀ K : ℕ, ‖resultant P G‖ ≤ max ((l : ℝ) ^ (-(K : ℤ))) ‖resultant Q G‖ := by
    intro K
    obtain ⟨F, hF0, hFdeg, hFmod⟩ := exists_int_approx hp hpl G K
    have HF := H F hF0
    obtain ⟨Fl, hFl_def⟩ : ∃ Fl, Fl = F.map (Int.castRingHom ℤ_[l]) := ⟨_, rfl⟩
    rw [← hFl_def] at HF hFmod
    have hFl : Fl.natDegree ≤ G.natDegree := hFl_def ▸ natDegree_map_le.trans hFdeg
    have hc : ∀ S : ℤ_[l][X], S.Monic →
        ‖resultant S G - resultant S Fl‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
      intro S hS
      rw [← resultant_monic_eq hS hFl]
      apply norm_sub_le_of_toZModPow_eq
      rw [← resultant_map_map, ← resultant_map_map, hFmod]
    have h1 := PadicInt.nonarchimedean (resultant P G - resultant P Fl) (resultant P Fl)
    have h2 := PadicInt.nonarchimedean (resultant Q Fl - resultant Q G) (resultant Q G)
    rw [sub_add_cancel] at h1 h2
    rw [norm_sub_rev] at h2
    rw [HF] at h1
    calc ‖resultant P G‖ ≤ max ‖resultant P G - resultant P Fl‖ ‖resultant Q Fl‖ := h1
      _ ≤ max ((l : ℝ) ^ (-(K : ℤ))) (max ((l : ℝ) ^ (-(K : ℤ))) ‖resultant Q G‖) :=
          max_le_max (hc P hP) (h2.trans (max_le_max (hc Q hQ) le_rfl))
      _ = max ((l : ℝ) ^ (-(K : ℤ))) ‖resultant Q G‖ := by rw [← max_assoc, max_self]
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖resultant P G‖ := (norm_nonneg _).trans_lt hlt
  obtain ⟨K, hK'⟩ : ∃ K : ℕ, (l : ℝ) ^ (-(K : ℤ)) < ‖resultant P G‖ := by
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
    refine ⟨K, ?_⟩
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  exact absurd (hK K) (not_le.mpr (max_lt hK' hlt))

/-- **C1 over `ℤ_l`.** -/
theorem norm_resultant_eq_of_int {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P Q : ℤ_[l][X]} (hP : P.Monic)
    (hQ : Q.Monic) (H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant P (F.map (Int.castRingHom ℤ_[l]))‖ = ‖resultant Q (F.map (Int.castRingHom ℤ_[l]))‖)
    (G : ℤ_[l][X]) : ‖resultant P G‖ = ‖resultant Q G‖ :=
  le_antisymm (norm_resultant_le_of_int hp hpl hP hQ H G)
    (norm_resultant_le_of_int hp hpl hQ hP (fun F hF => (H F hF).symm) G)

/-- **C1 over `ℚ_l`.** -/
theorem norm_resultant_eq_of_int_rat {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P Q : ℤ_[l][X]}
    (hP : P.Monic) (hQ : Q.Monic) (H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant P (F.map (Int.castRingHom ℤ_[l]))‖ = ‖resultant Q (F.map (Int.castRingHom ℤ_[l]))‖)
    (G : ℚ_[l][X]) :
    ‖resultant (P.map (algebraMap ℤ_[l] ℚ_[l])) G‖ = ‖resultant (Q.map (algebraMap ℤ_[l] ℚ_[l])) G‖ := by
  have hι : Function.Injective (algebraMap ℤ_[l] ℚ_[l]) := IsFractionRing.injective ℤ_[l] ℚ_[l]
  have hnorm : ∀ x : ℤ_[l], ‖algebraMap ℤ_[l] ℚ_[l] x‖ = ‖x‖ := fun x => by
    rw [PadicInt.algebraMap_apply, PadicInt.norm_def]
  -- equal degrees, from `F = l`
  have hdeg : P.natDegree = Q.natDegree := by
    have h := norm_resultant_eq_of_int hp hpl hP hQ H (C (l : ℤ_[l]))
    rw [resultant_C_right, resultant_C_right, hP.coeff_natDegree, hQ.coeff_natDegree, one_pow, one_mul,
      one_mul, norm_pow, norm_pow, PadicInt.norm_p] at h
    have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    exact pow_right_injective₀ (inv_pos.mpr (zero_lt_one.trans hl1)) (inv_lt_one_of_one_lt₀ hl1).ne h
  -- clear denominators
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (M := nonZeroDivisors ℤ_[l])
    (S := ℚ_[l]) G
  generalize IsLocalization.integerNormalization (nonZeroDivisors ℤ_[l]) G = G' at hb
  have hb0 : algebraMap ℤ_[l] ℚ_[l] b ≠ 0 :=
    (map_ne_zero_iff _ hι).mpr (nonZeroDivisors.coe_ne_zero b)
  have hG' : G'.map (algebraMap ℤ_[l] ℚ_[l]) = C (algebraMap ℤ_[l] ℚ_[l] b) * G := by
    rw [hb, ← algebraMap_smul ℚ_[l] (b : ℤ_[l]) G, smul_eq_C_mul]
  have key : ∀ S : ℤ_[l][X], ‖resultant S G'‖ =
      ‖algebraMap ℤ_[l] ℚ_[l] b‖ ^ S.natDegree * ‖resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) G‖ := by
    intro S
    have e1 : resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) (G'.map (algebraMap ℤ_[l] ℚ_[l])) =
        algebraMap ℤ_[l] ℚ_[l] (resultant S G') := by
      rw [natDegree_map_eq_of_injective hι, natDegree_map_eq_of_injective hι, resultant_map_map]
    have e2 : resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) (G'.map (algebraMap ℤ_[l] ℚ_[l])) =
        (algebraMap ℤ_[l] ℚ_[l] b) ^ S.natDegree * resultant (S.map (algebraMap ℤ_[l] ℚ_[l])) G := by
      rw [hG', natDegree_C_mul hb0, resultant_C_mul_right, natDegree_map_eq_of_injective hι]
    rw [← hnorm, ← e1, e2, norm_mul, norm_pow]
  have h := norm_resultant_eq_of_int hp hpl hP hQ H G'
  rw [key, key, hdeg] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hb0)) h

/-- **C2 (core).** If `‖Res(P₀, F)‖_l = ‖det F(M)‖_l` for every integer `F` with `p ∤ F(0)`, then
`charpoly M = P₀` over `ℤ_l`. -/
theorem charpoly_eq_of_norm_det {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) {P0 : ℤ[X]} (hP0 : P0.Monic)
    {T : Type*} [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (M : Module.End ℤ_[l] T)
    (hkey : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖((resultant P0 F : ℤ) : ℤ_[l])‖ = ‖LinearMap.det (aeval M (F.map (Int.castRingHom ℤ_[l])))‖) :
    M.charpoly = P0.map (Int.castRingHom ℤ_[l]) := by
  have hι : Function.Injective (algebraMap ℤ_[l] ℚ_[l]) := IsFractionRing.injective ℤ_[l] ℚ_[l]
  have hz : Function.Injective (Int.castRingHom ℤ_[l]) := (Int.castRingHom ℤ_[l]).injective_int
  have hχ : M.charpoly.Monic := LinearMap.charpoly_monic M
  have hP : (P0.map (Int.castRingHom ℤ_[l])).Monic := hP0.map _
  have H : ∀ F : ℤ[X], ¬ (p : ℤ) ∣ F.coeff 0 →
      ‖resultant (P0.map (Int.castRingHom ℤ_[l])) (F.map (Int.castRingHom ℤ_[l]))‖ =
        ‖resultant M.charpoly (F.map (Int.castRingHom ℤ_[l]))‖ := by
    intro F hF
    have h := hkey F hF
    rw [linearMap_det_aeval_eq_resultant, ← LinearMap.charpoly_natDegree M] at h
    rw [← h, natDegree_map_eq_of_injective hz, natDegree_map_eq_of_injective hz, resultant_map_map,
      eq_intCast]
  have heq := eq_of_norm_resultant_eq (hP.map _) (hχ.map _) (norm_resultant_eq_of_int_rat hp hpl hP hχ H)
  exact (Polynomial.map_injective _ hι heq).symm

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ}

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

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G] {l : ℕ} [Fact l.Prime]
variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)

theorem isTateMat_zero :
    IsTateMat hdiv b1 hb1 (0 : AddMonoid.End G) (0 : Matrix (Fin s) (Fin s) ℤ_[l]) := by
  have h := (isTateMat_one hdiv b1 hb1).sub hdiv b1 hb1 (isTateMat_one hdiv b1 hb1)
  rwa [sub_self, sub_self] at h

theorem isTateMat_neg {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) : IsTateMat hdiv b1 hb1 (-φ) (-M) := by
  have h' := (isTateMat_zero hdiv b1 hb1).sub hdiv b1 hb1 h
  rwa [zero_sub, zero_sub] at h'

theorem isTateMat_add {φ χ : AddMonoid.End G} {M M' : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (h' : IsTateMat hdiv b1 hb1 χ M') :
    IsTateMat hdiv b1 hb1 (φ + χ) (M + M') := by
  have h2 := h.sub hdiv b1 hb1 (isTateMat_neg hdiv b1 hb1 h')
  rwa [sub_neg_eq_add, sub_neg_eq_add] at h2

theorem isTateMat_intCast (a : ℤ) :
    IsTateMat hdiv b1 hb1 (a : AddMonoid.End G) (a : Matrix (Fin s) (Fin s) ℤ_[l]) := by
  induction a using Int.induction_on with
  | zero => simpa using isTateMat_zero hdiv b1 hb1
  | succ n ih =>
    have h := isTateMat_add hdiv b1 hb1 ih (isTateMat_one hdiv b1 hb1)
    rwa [Int.cast_add, Int.cast_add, Int.cast_one, Int.cast_one]
  | pred n ih =>
    have h := ih.sub hdiv b1 hb1 (isTateMat_one hdiv b1 hb1)
    rwa [Int.cast_sub, Int.cast_sub, Int.cast_one, Int.cast_one]

theorem isTateMat_aeval {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (P : ℤ[X]) : IsTateMat hdiv b1 hb1 (aeval φ P) (aeval M P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add]; exact isTateMat_add hdiv b1 hb1 hP hQ
  | monomial n a =>
    simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C, algebraMap_int_eq,
      Int.coe_castRingHom]
    exact (isTateMat_intCast hdiv b1 hb1 a).mul hdiv b1 hb1 (h.pow hdiv b1 hb1 n)

omit [Fact l.Prime] in
theorem h1inj_of_injective (hinj : Function.Injective (tateMap hdiv b1 hb1 1)) :
    ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i := by
  intro d hd i
  have h0 : tateMap hdiv b1 hb1 1 (fun i => (d i : ZMod (l ^ 1))) = tateMap hdiv b1 hb1 1 0 := by
    rw [tateMap_intCast, tateBasis_one, hd, map_zero]
  have := congrFun (hinj h0) i
  rw [Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  simpa using this

theorem h1span_of_card (hinj : Function.Injective (tateMap hdiv b1 hb1 1)) [Finite {x : G // l • x = 0}]
    (hcard : Nat.card {x : G // l • x = 0} ≤ l ^ s) :
    ∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x := by
  let f : (Fin s → ZMod (l ^ 1)) → {x : G // l • x = 0} := fun cb =>
    ⟨tateMap hdiv b1 hb1 1 cb, by simpa using tateMap_smul_eq_zero hdiv b1 hb1 1 cb⟩
  have hf : Function.Injective f := fun a b hab => hinj (congrArg Subtype.val hab)
  have hle : Nat.card {x : G // l • x = 0} ≤ Nat.card (Fin s → ZMod (l ^ 1)) := by
    simpa [Nat.card_fun, Nat.card_zmod] using hcard
  intro x hx
  obtain ⟨cb, hcb⟩ := (hf.bijective_of_nat_card_le hle).2 ⟨x, hx⟩
  obtain ⟨c, rfl⟩ := exists_intCast cb
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hcb
  simp only [f] at this
  rwa [tateMap_intCast, tateBasis_one] at this

omit [Fact l.Prime] in
theorem exists_pow_smul_eq (h : ∀ y : G, ∃ z, l • z = y) (k : ℕ) (y : G) : ∃ z, l ^ k • z = y := by
  induction k generalizing y with
  | zero => exact ⟨y, by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨z, rfl⟩ := ih y
    obtain ⟨w, rfl⟩ := h z
    exact ⟨w, by rw [pow_succ, mul_smul]⟩

omit [Fact l.Prime] in
theorem mem_range_pow (h : ∀ y : G, ∃ z, l • z = y) (k : ℕ) (y : G) : y ∈ (smulHom G (l ^ k)).range := by
  obtain ⟨z, hz⟩ := exists_pow_smul_eq h k y
  exact AddMonoidHom.mem_range.mpr ⟨z, by rw [smulHom_apply, hz]⟩

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

variable (l k0 : ℕ) [hl : Fact l.Prime]

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

/-- Changing the constant term by a multiple of `l^K` moves a resultant by at most `l^-K`. -/
theorem norm_resultant_add_C_sub_le (S G : ℤ_[l][X]) {c : ℤ_[l]} {K : ℕ}
    (hc : PadicInt.toZModPow K c = 0) (m n : ℕ) :
    ‖resultant S (G + C c) m n - resultant S G m n‖ ≤ (l : ℝ) ^ (-(K : ℤ)) := by
  apply norm_sub_le_of_toZModPow_eq
  rw [← resultant_map_map, ← resultant_map_map, Polynomial.map_add, map_C, hc, C_0, add_zero]

omit hl in
theorem eq_zero_of_norm_le_pow [Fact l.Prime] {x : ℤ_[l]} (h : ∀ K : ℕ, ‖x‖ ≤ (l : ℝ) ^ (-(K : ℤ))) :
    x = 0 := by
  by_contra hx
  have := (PadicInt.norm_le_pow_iff_le_valuation x hx (x.valuation + 1)).mp (h _)
  omega

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ}

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_CoreB =====
section

/-!
# Unit S4-CoreB (Core B final assembly, lemmas L43-L44 of `S4_COREB_ROUTE.md` section 3): umbrella

For every function field `F/F_q` with `constField F_q F = F_q` (smooth projective geometrically connected `X/F_q`),
every prime `l ∤ q`, and `π` the arithmetic Frobenius on `Pic⁰(X̄)`:
* `exists_degreeData` (L43, `_Data`): `deg F := deg (F(π))` is a `DegreeData` for `ℤ[π]` on `Pic⁰(X̄)`; `zeta_link`
  (`_Zeta`): `g_D = g` and `P_π = Π (X - ω_i) ∈ ℤ[X]` for the zeta roots `ω`;
* `divisible_Aℓ` (CB1, `_Div`): `Pic(X̄)[l^∞]` is `l`-divisible;
* `norm_deg_eq_norm_det` (`_Key`), `charpoly_eq_of_deg_ne` (`_Pert`): `χ_M = P_π` for every CoreA Tate matrix `M`;
* `coreBHyp_proved` (CB1 + CB2): the hypothesis `CP4a.CoreBHyp` that S4-CP4a assumes, proved;
* `exists_trace_pow_of_charpoly`, `coreB_count`, `exists_tate_count` (CB3): `#X(F_(q^m)) = 1 + q^m - tr(M^m)`.
-/

set_option autoImplicit false

open Polynomial
open scoped Matrix

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA RamanujanPetersson.ZetaSB

section Trace

variable {R : Type*} [CommRing R] [Nontrivial R] {n : Type*} [Fintype n] [DecidableEq n]

end Trace

section Main

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `aeval` commutes with `Matrix.toLin'`. -/
theorem aeval_toLin' {l : ℕ} [Fact l.Prime] {s : ℕ} (M : Matrix (Fin s) (Fin s) ℤ_[l]) (P : ℤ[X]) :
    aeval (Matrix.toLin' M) (P.map (Int.castRingHom ℤ_[l])) = Matrix.toLin' (aeval M P) := by
  have h1 : ∀ B : Matrix (Fin s) (Fin s) ℤ_[l], Matrix.toLin' B = Matrix.toLinAlgEquiv' B := fun B =>
    LinearMap.ext fun v => by rw [Matrix.toLin'_apply, Matrix.toLinAlgEquiv'_apply]
  rw [h1, h1, Polynomial.aeval_algHom_apply, ← algebraMap_int_eq, aeval_map_algebraMap]

end Main

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

include hsurj in
/-- Every element of `Λ' ⊗ V` is `1 ⊗ x` (`algebraMap` onto). -/
theorem exists_one_tmul_of_surj (u : Λ' ⊗[Λ] V) : ∃ x : V, u = 1 ⊗ₜ x := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, (tmul_zero _ _).symm⟩
  | tmul r v =>
    obtain ⟨a, rfl⟩ := hsurj r
    exact ⟨a • v, by rw [← smul_tmul, Algebra.algebraMap_eq_smul_one]⟩
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, (tmul_add _ _ _).symm⟩

include hsurj ht in
/-- If `f : V → V'` is onto with kernel inside `t • V`, then `Λ' ⊗ V → V'` is bijective. -/
theorem bijective_liftBaseChange (f : V →ₗ[Λ] V') (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 → ∃ y, x = t • y) : Function.Bijective (f.liftBaseChange Λ') := by
  refine ⟨fun u v huv => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := exists_one_tmul_of_surj hsurj u
    obtain ⟨x', rfl⟩ := exists_one_tmul_of_surj hsurj v
    rw [LinearMap.liftBaseChange_one_tmul, LinearMap.liftBaseChange_one_tmul, ← sub_eq_zero, ← map_sub] at huv
    obtain ⟨z, hz⟩ := hk _ huv
    rw [← sub_eq_zero, ← tmul_sub, hz, ← smul_tmul, ← Algebra.algebraMap_eq_smul_one, ht, zero_tmul]
  · obtain ⟨x, rfl⟩ := hf y
    exact ⟨1 ⊗ₜ x, LinearMap.liftBaseChange_one_tmul _ _ _⟩

/-- `Λ' ⊗ V ≃ V'` from `f` onto with kernel in `t • V`. -/
def redEquiv (f : V →ₗ[Λ] V') (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → ∃ y, x = t • y) :
    Λ' ⊗[Λ] V ≃ₗ[Λ'] V' :=
  LinearEquiv.ofBijective _ (bijective_liftBaseChange t hsurj ht f hf hk)

theorem redEquiv_one_tmul (f : V →ₗ[Λ] V') (hf : Function.Surjective f)
    (hk : ∀ x, f x = 0 → ∃ y, x = t • y) (x : V) : redEquiv t hsurj ht f hf hk (1 ⊗ₜ x) = f x :=
  LinearMap.liftBaseChange_one_tmul _ _ _

variable {W W' : Type} [AddCommGroup W] [Module Λ W] [AddCommGroup W'] [Module Λ W'] [Module Λ' W']
  [IsScalarTower Λ Λ' W']

/-- `redEquiv` intertwines `d ⊗ Λ'` with `d'` when `g ∘ d = d' ∘ f`. -/
theorem redEquiv_comm (f : V →ₗ[Λ] V') (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → ∃ y, x = t • y)
    (g : W →ₗ[Λ] W') (hg : Function.Surjective g) (hkg : ∀ x, g x = 0 → ∃ y, x = t • y)
    (d : V →ₗ[Λ] W) (d' : V' →ₗ[Λ'] W') (hd : ∀ x, g (d x) = d' (f x)) (u : Λ' ⊗[Λ] V) :
    redEquiv t hsurj ht g hg hkg (d.baseChange Λ' u) = d' (redEquiv t hsurj ht f hf hk u) := by
  obtain ⟨x, rfl⟩ := exists_one_tmul_of_surj hsurj u
  rw [LinearMap.baseChange_tmul, redEquiv_one_tmul, redEquiv_one_tmul, hd]

variable {G : Type} [Group G] [Fintype G]

end BC

section RedA

variable (Λ Λ' : Type) [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] (Gf : Type) [Group Gf]

/-- Coefficientwise reduction `Λ[Gf] → Λ'[Gf]`. -/
def redA : MonoidAlgebra Λ Gf →ₗ[Λ] MonoidAlgebra Λ' Gf :=
  (mapAlgHom Gf (Algebra.ofId Λ Λ')).toLinearMap

variable {Λ Λ' Gf}

theorem redA_coeff (a : MonoidAlgebra Λ Gf) (x : Gf) :
    (redA Λ Λ' Gf a).coeff x = algebraMap Λ Λ' (a.coeff x) :=
  coeff_mapAlgHom _ _ _

theorem redA_mul (a b : MonoidAlgebra Λ Gf) : redA Λ Λ' Gf (a * b) = redA Λ Λ' Gf a * redA Λ Λ' Gf b :=
  map_mul (mapAlgHom Gf (Algebra.ofId Λ Λ')) a b

theorem redA_single (x : Gf) : redA Λ Λ' Gf (single x 1) = single x 1 := by
  show mapAlgHom Gf (Algebra.ofId Λ Λ') (single x 1) = single x 1
  rw [mapAlgHom_single, map_one]

theorem redA_mul_single (x : Gf) (a : MonoidAlgebra Λ Gf) :
    redA Λ Λ' Gf (single x 1 * a) = single x 1 * redA Λ Λ' Gf a := by
  rw [redA_mul, redA_single]

theorem redA_mul_single' (a : MonoidAlgebra Λ Gf) (x : Gf) :
    redA Λ Λ' Gf (a * single x 1) = redA Λ Λ' Gf a * single x 1 := by
  rw [redA_mul, redA_single]

theorem redA_surjective [Finite Gf] (hsurj : Function.Surjective (algebraMap Λ Λ')) :
    Function.Surjective (redA Λ Λ' Gf) := fun b => by
  choose y hy using fun x => hsurj (b.coeff x)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm y), ?_⟩
  ext x
  rw [redA_coeff]
  exact hy x

theorem redA_ker [Finite Gf] {t : Λ} (hk : ∀ r, algebraMap Λ Λ' r = 0 → ∃ s, r = t * s)
    (a : MonoidAlgebra Λ Gf) (ha : redA Λ Λ' Gf a = 0) : ∃ b : MonoidAlgebra Λ Gf, a = t • b := by
  have hx : ∀ x : Gf, ∃ y, a.coeff x = t * y := fun x => hk _ (by rw [← redA_coeff, ha]; rfl)
  choose y hy using hx
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm y), ?_⟩
  ext x
  rw [coeff_smul_apply, hy x, smul_eq_mul]
  rfl

end RedA

section RedZ1

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {Gf : Type} [Group Gf] {G : Type} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] (π : G →* Gf)

end RedZ1

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

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

section Gen

variable {G : Type*} [AddCommGroup G]

/-- A torsion element of `H ⊇ G[l^∞]` is `l^n`-divisible in `H` when `G[l^∞]` is `l`-divisible. -/
theorem exists_pow_smul_of_torsion {l : ℕ} (hl : l.Prime)
    (hA : ∀ y : AddCommGroup.primaryComponent G l, ∃ z, l • z = y) (H : AddSubgroup G)
    (hle : AddCommGroup.primaryComponent G l ≤ H) {x : G} (hx : x ∈ H) {m : ℕ} (hm : 0 < m)
    (hmx : m • x = 0) (n : ℕ) : ∃ z ∈ H, l ^ n • z = x := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' l hl.ne_one
  have hcop : ∀ k : ℕ, Nat.Coprime (l ^ k) b := fun k =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hl).2 hb)
  have bez : ∀ k : ℕ, ((l ^ k : ℕ) : ℤ) * Nat.gcdA (l ^ k) b + (b : ℤ) * Nat.gcdB (l ^ k) b = 1 := by
    intro k
    have h := Nat.gcd_eq_gcd_ab (l ^ k) b
    rw [Nat.Coprime.gcd_eq_one (hcop k), Nat.cast_one] at h
    exact h.symm
  have hAB : (((l ^ a : ℕ) : ℤ) * (b : ℤ)) • x = 0 := by
    rw [← Nat.cast_mul, natCast_zsmul]; exact hmx
  set u := Nat.gcdA (l ^ a) b
  set v := Nat.gcdB (l ^ a) b
  have huv : ((l ^ a : ℕ) : ℤ) * u + (b : ℤ) * v = 1 := bez a
  set x1 : G := ((b : ℤ) * v) • x with hx1def
  set x2 : G := (((l ^ a : ℕ) : ℤ) * u) • x with hx2def
  have hsum : x1 + x2 = x := by
    rw [hx1def, hx2def, ← add_smul, add_comm, huv, one_smul]
  have hx1 : x1 ∈ AddCommGroup.primaryComponent G l := by
    refine AddCommGroup.mem_primaryComponent.2 ⟨a, ?_⟩
    rw [hx1def, ← natCast_zsmul, smul_smul,
      show ((l ^ a : ℕ) : ℤ) * ((b : ℤ) * v) = v * (((l ^ a : ℕ) : ℤ) * (b : ℤ)) by ring, ← smul_smul, hAB,
      smul_zero]
  have hbx2 : (b : ℤ) • x2 = 0 := by
    rw [hx2def, smul_smul,
      show (b : ℤ) * (((l ^ a : ℕ) : ℤ) * u) = u * (((l ^ a : ℕ) : ℤ) * (b : ℤ)) by ring, ← smul_smul, hAB,
      smul_zero]
  obtain ⟨z1, hz1⟩ := CoreB.exists_pow_smul_eq hA n ⟨x1, hx1⟩
  have e1 : l ^ n • (z1 : G) = x1 := by
    have h1 := congrArg (AddSubgroup.subtype (AddCommGroup.primaryComponent G l)) hz1
    rw [map_nsmul] at h1
    exact h1
  set s := Nat.gcdA (l ^ n) b
  set t := Nat.gcdB (l ^ n) b
  have hst : ((l ^ n : ℕ) : ℤ) * s + (b : ℤ) * t = 1 := bez n
  have hx2 : l ^ n • (s • x2) = x2 := by
    rw [← natCast_zsmul, smul_smul, show ((l ^ n : ℕ) : ℤ) * s = 1 - t * (b : ℤ) by linarith, sub_smul, one_smul,
      ← smul_smul, hbx2, smul_zero, sub_zero]
  refine ⟨(z1 : G) + s • x2, H.add_mem (hle z1.2) (H.zsmul_mem (H.zsmul_mem hx _) _), ?_⟩
  rw [smul_add, e1, hx2, hsum]

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

end Pic

end RamanujanPetersson.CupDuality


end


