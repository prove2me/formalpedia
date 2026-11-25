-- Prove2me | Definitions.Def_RPLib_FX_EtP1_19
-- name    : RPLib_FX_EtP1_19
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:25:48.299795+00:00
-- url     : https://prove2.me/theorems/a5fa3efa-c0f0-5a95-8f65-1875d4b5f3df
-- title:
--   Étale cohomology of the projective line, library file 19 of 34
-- statement:
--   File 19 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Hs`: S4-EtCompact, part 61: global sections of `R¹g_*` lift over a PID (F7f of plan v5)
--   * `S4.Def_RP_EtCompact_H2Pid`: S4-EtCompact, part 62: `H²(Spec A, Λ) = 0` for a PID with `cd(κ(η)) ≤ 1` (curve core, degree 2)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_18

/-!
# Étale cohomology of the projective line, library file 19 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Hs`: S4-EtCompact, part 61: global sections of `R¹g_*` lift over a PID (F7f of plan v5)
* `S4.Def_RP_EtCompact_H2Pid`: S4-EtCompact, part 62: `H²(Spec A, Λ) = 0` for a PID with `cd(κ(η)) ≤ 1` (curve core, degree 2)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Hs =====
section

/-!
# S4-EtCompact, part 61: global sections of `R¹g_*` lift over a PID (F7f of plan v5)

`A` a principal ideal domain, `g = gen A : Spec κ(η) ⟶ Spec A`.

* **`lift_all`**: for `c : g_* Q ⟶ C` epi killing `g_* p`, every `b : Λ ⟶ C` is `a ≫ c` (noetherian induction on the
  closed set `(Good b)ᶜ`: the generic point is good (`Step.gen_good`), a bad closed point `(π)` is removed by
  `Step.exists_step` without creating new bad points);
* **`hs_gen`**: the hypothesis `hs` of `H_push_two_eq_zero'` for `N` with Galois-trivial `d`-torsion stalk.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.Hs

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

variable {A : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {Λ : Type} [CommRing Λ]

/-- **Every `b : Λ ⟶ C` lifts** through `c`. -/
theorem lift_all {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))}
    {ι : Ns ⟶ I} {p : I ⟶ Q}
    (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    (hN : ∀ (σ : Gal (x0 A)) (v : stalk Λ Ns (x0 A)), galRep Λ Ns (x0 A) σ v = v)
    [Injective I] [Mono ι] [Epi p] (hιp : ι ≫ p = 0)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ) (hd : ∀ v : stalk Λ Ns (x0 A), d • v = 0)
    {C : EtSh Λ (Spec (CommRingCat.of A))} (c : (push (gen A) Λ).obj Q ⟶ C) [Epi c]
    (hc : (push (gen A) Λ).map p ≫ c = 0) (b : unitSh Λ (Spec (CommRingCat.of A)) ⟶ C) :
    ∃ a : unitSh Λ (Spec (CommRingCat.of A)) ⟶ (push (gen A) Λ).obj Q, a ≫ c = b := by
  have key : ∀ Z : TopologicalSpace.Closeds (Spec (CommRingCat.of A)),
      ∀ b : unitSh Λ (Spec (CommRingCat.of A)) ⟶ C, (Supp.Good A b)ᶜ ⊆ (Z : Set (Spec (CommRingCat.of A))) →
        ∃ a : unitSh Λ (Spec (CommRingCat.of A)) ⟶ (push (gen A) Λ).obj Q, a ≫ c = b := by
    intro Z
    refine WellFoundedLT.induction (motive := fun Z : TopologicalSpace.Closeds (Spec (CommRingCat.of A)) =>
      ∀ b : unitSh Λ (Spec (CommRingCat.of A)) ⟶ C, (Supp.Good A b)ᶜ ⊆ (Z : Set (Spec (CommRingCat.of A))) →
        ∃ a : unitSh Λ (Spec (CommRingCat.of A)) ⟶ (push (gen A) Λ).obj Q, a ≫ c = b) Z ?_
    intro Z ih b hb
    by_cases hZ : ∀ y, y ∈ Supp.Good A b
    · exact ⟨0, by rw [zero_comp]; exact (Supp.eq_zero_of b hZ).symm⟩
    simp only [not_forall] at hZ
    obtain ⟨x, hxb⟩ := hZ
    have hx0 : x.asIdeal ≠ ⊥ := fun h => hxb (Step.gen_good hex hN hdA hζ hζG hd c hc b x h)
    obtain ⟨π, hπx⟩ : ∃ π : A, x.asIdeal = Ideal.span {π} :=
      ⟨Submodule.IsPrincipal.generator x.asIdeal, (Submodule.IsPrincipal.span_singleton_generator x.asIdeal).symm⟩
    have hπ : π ≠ 0 := fun h => hx0 (hπx.trans (Ideal.span_singleton_eq_bot.2 h))
    obtain ⟨a, hxa, hga⟩ := Step.exists_step hex hN hιp hdA hζ hζG hd c hc b x π hπ hπx
    have hmax : x.asIdeal.IsMaximal := IsPrime.to_maximal_ideal (hpi := x.isPrime) hx0
    have hsub : (Supp.Good A (b - a ≫ c))ᶜ ⊆ (Supp.Good A b)ᶜ \ {x} := by
      intro y hy
      refine ⟨fun hyb => hy ?_, fun hyx => hy ?_⟩
      · by_cases hπy : π ∈ y.asIdeal
        · have hle : x.asIdeal ≤ y.asIdeal := by
            rw [hπx, Ideal.span_le, Set.singleton_subset_iff]
            exact hπy
          have hxy : x = y := PrimeSpectrum.ext (hmax.eq_of_le y.isPrime.ne_top hle)
          rw [← hxy]
          exact hxa
        · exact KCe.good_sub b (a ≫ c) hyb (hga y hπy)
      · rw [Set.mem_singleton_iff.1 hyx]
        exact hxa
    have hlt : (⟨(Supp.Good A (b - a ≫ c))ᶜ, (Supp.isOpen_good A _).isClosed_compl⟩ :
        TopologicalSpace.Closeds (Spec (CommRingCat.of A))) < Z :=
      SetLike.lt_iff_le_and_exists.2 ⟨fun y hy => hb (hsub hy).1, x, hb hxb, fun h => h hxa⟩
    obtain ⟨a', ha'⟩ := ih _ hlt (b - a ≫ c) fun y hy => hy
    exact ⟨a' + a, by rw [Preadditive.add_comp, ha', sub_add_cancel]⟩
  exact key ⊤ b (by simp)

/-- **The hypothesis `hs` of `H_push_two_eq_zero'`** over a PID. -/
theorem hs_gen (N : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))))
    (hN : ∀ (σ : Gal (x0 A)) (v : stalk Λ N (x0 A)), galRep Λ N (x0 A) σ v = v)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ) (hd : ∀ v : stalk Λ N (x0 A), d • v = 0)
    (b : unitSh Λ (Spec (CommRingCat.of A)) ⟶ R1 (gen A) Λ N) :
    ∃ a : unitSh Λ (Spec (CommRingCat.of A)) ⟶ (push (gen A) Λ).obj (Qt Λ N),
      a ≫ cokernel.π (LerayG.pushπ (push (gen A) Λ) N) = b := by
  have hS := (ShortComplex.exact_cokernel (Injective.ι N)).map ((geomPtAt (x0 A)).stalkF Λ)
  rw [ShortComplex.moduleCat_exact_iff] at hS
  exact lift_all (ι := Injective.ι N) (p := cokernel.π (Injective.ι N)) (fun y hy => hS y hy) hN
    (cokernel.condition _) hdA hζ hζG hd (cokernel.π (LerayG.pushπ (push (gen A) Λ) N)) (cokernel.condition _) b

end RamanujanPetersson.EtCompact.Hs

end

end

-- ===== S4.Def_RP_EtCompact_H2Pid =====
section

/-!
# S4-EtCompact, part 62: `H²(Spec A, Λ) = 0` for a PID with `cd(κ(η)) ≤ 1` (curve core, degree 2)

* **`H_two_eq_zero_of_root`**: `A` a PID, `H²(Spec κ(η), -) = 0`, `d` a unit of `A` with a primitive `d`-th root of
  unity in `A`, `d • Λ = 0`: `H²(Spec A, Λ) = 0` (`Λ_U ≅ g_* Λ_η` (`SgUnit.unitIsoPush`), `H_push_two_eq_zero'` with
  `Hs.hs_gen`);
* **`H_A1_two_eq_zero`**: `H²(A¹_k, Λ) = 0` for `k` algebraically closed, `ℓ ≠ char k`, `ℓ^m • Λ = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.H2Pid

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac

/-- **`H²(Spec A, Λ) = 0`** for a PID `A` whose generic point has `H² = 0`. -/
theorem H_two_eq_zero_of_root (A : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] {Λ : Type} [CommRing Λ]
    (hη : ∀ (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (e : H Λ M 2), e = 0)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ₀ : A} (hζ₀ : IsPrimitiveRoot ζ₀ d) (hΛ : (d : Λ) = 0)
    (e : H Λ (unitSh Λ (Spec (CommRingCat.of A))) 2) : e = 0 := by
  have hζ : IsPrimitiveRoot (algebraMap A (SeparableClosure (κ0 A)) ζ₀) d :=
    hζ₀.map_of_injective Chart.alg_injective
  have hζG : ∀ σ : Gal (x0 A), σ (algebraMap A (SeparableClosure (κ0 A)) ζ₀) = algebraMap A _ ζ₀ := by
    intro σ
    rw [IsScalarTower.algebraMap_apply A (κ0 A) (SeparableClosure (κ0 A)), AlgEquiv.commutes]
  have hN : ∀ (σ : Gal (x0 A)) (v : stalk Λ (unitSh Λ _) (x0 A)), galRep Λ (unitSh Λ _) (x0 A) σ v = v := by
    intro σ v
    rw [galRep_unitSh]
    rfl
  have hd : ∀ v : stalk Λ (unitSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (x0 A),
      d • v = 0 := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  have h0 := H_push_two_eq_zero' hη (unitSh Λ _) (Hs.hs_gen (unitSh Λ _) hN hdA hζ hζG hd)
    (e.comp (Abelian.Ext.mk₀ (SgUnit.unitIsoPush A (Λ := Λ)).hom) (add_zero 2))
  have he : e = (e.comp (Abelian.Ext.mk₀ (SgUnit.unitIsoPush A (Λ := Λ)).hom) (add_zero 2)).comp
      (Abelian.Ext.mk₀ (SgUnit.unitIsoPush A (Λ := Λ)).inv) (add_zero 2) := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id,
      Abelian.Ext.comp_mk₀_id]
  rw [he, h0, Abelian.Ext.zero_comp]

/-- **`H²(A¹_k, Λ) = 0`** (`k` algebraically closed, `ℓ ≠ char k`, `ℓ^m = 0` in `Λ`). -/
theorem H_A1_two_eq_zero (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime]
    (hl : (l : k) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
    (e : H Λ (unitSh Λ (Spec (CommRingCat.of k[X]))) 2) : e = 0 := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hlm : ((l ^ m : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne k hlm
  have hdA : IsUnit ((l ^ m : ℕ) : k[X]) := by
    rw [← map_natCast (C : k →+* k[X])]
    exact isUnit_C.2 (isUnit_iff_ne_zero.2 hlm)
  exact H_two_eq_zero_of_root k[X] (fun M e => H_genPt_eq_zero k l hl m hΛ 0 M e) hdA
    (hζ.map_of_injective C_injective) hΛ e

end RamanujanPetersson.EtCompact.H2Pid

end

end


