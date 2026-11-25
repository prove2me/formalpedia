-- Prove2me | Definitions.Def_RPLib_FX_EtP1_41
-- name    : RPLib_FX_EtP1_41
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:49:42.660077+00:00
-- url     : https://prove2.me/theorems/c6259a7e-75ea-501d-8baf-963365e2c74d
-- title:
--   Étale cohomology of the projective line, library file 41 (an extra file from a re-cut)
-- statement:
--   File 41 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
--   * `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
--   * `S4.Def_RP_EtCompact_LerayG`: S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)
--   * `S4.Def_RP_EtCompact_CechH`: S4-EtCompact: Cech complexes with extra codegeneracies; fibres of Cech nerves (O8c (B), file C1)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_19

/-!
# Étale cohomology of the projective line, library file 41 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
* `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
* `S4.Def_RP_EtCompact_LerayG`: S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)
* `S4.Def_RP_EtCompact_CechH`: S4-EtCompact: Cech complexes with extra codegeneracies; fibres of Cech nerves (O8c (B), file C1)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1Pts =====
section

/-!
# S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)

* `P1.genPt K`: the generic point `(0)`; `closure {genPt} = univ`, so `P^1_K` is irreducible (hence connected).
* `P1.infPt K`: the point `∞ = (X₀)`; every point whose ideal contains `X₀` is `∞` (`P1.eq_infPt_of_X0_mem`).
* The image of the chart `chartA1 : A^1_K ⟶ P^1_K` is `D₊(X₀)`, its complement is `{∞}`, so `{∞}` is closed and
  `Spec κ(∞) ⟶ P^1_K` is a closed immersion; for algebraically closed `K`, `κ(∞) ≅ K` is algebraically closed.
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable (K : Type u) [Field K]

/-! ### The generic point -/

theorem P1.isGenericPoint_genPt : IsGenericPoint (P1.genPt K) (Set.univ : Set (P1 K)) :=
  P1.closure_genPt K

/-! ### The point at infinity -/

/-! ### The chart `A^1_K ⊆ P^1_K` and its complement `{∞}` -/

theorem P1.infPt_not_mem_range : P1.infPt K ∉ (chartA1 K).opensRange := by
  rw [P1.mem_range_chartA1_iff]
  exact fun h => h rfl

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Pt =====
section

/-!
# S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)

For a scheme `X` with a point `x0` such that `Spec κ(x0) ⟶ X` is an isomorphism (`X` "is" `Spec κ(x0)`) and
`Gal(κ(x0)^sep/κ(x0))` trivial (e.g. `κ(x0)` separably closed: `gal_subsingleton`), the unit sheaf `Λ_X` is
projective (`unitSh_projective`, via the S4-EtSheaves Galois description `specField_homEquiv`), hence
**`H^n(X, F) = 0` for `n ≥ 1`** (`H_eq_zero_of_point`, `H_subsingleton_of_point`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

/-- The absolute Galois group of a separably closed residue field is trivial. -/
theorem gal_subsingleton {X : Scheme.{u}} (x : X) [IsSepClosed (X.residueField x)] : Subsingleton (Gal x) := by
  constructor
  intro σ τ
  apply AlgEquiv.ext
  intro y
  obtain ⟨c, rfl⟩ := IsSepClosed.algebraMap_surjective (k := X.residueField x)
    (K := SeparableClosure (X.residueField x)) y
  rw [AlgEquiv.commutes, AlgEquiv.commutes]

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (Λ : Type u) [CommRing Λ]

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_LerayG =====
section

/-!
# S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)

Generic part (`LerayG`): `adj : L ⊣ R` between abelian categories, `L` preserving monomorphisms, `eAB : L A ≅ B`.
For `N : D` with injective presentation `N ↪ I ↠ Qt N`:
* `R1 R N := coker(R I → R (Qt N))` (`= R¹R N`), short exact `presA : 0 → R N → R I → C → 0` and
  `presB : 0 → C → R (Qt N) → R1 → 0`;
* `lift_push`: lifting `A`-sections along `R φ` from lifting `B`-sections along `φ`.
Under `hη : Ext²(B, -) = 0` and `hR : R1 R (Qt M) = 0` for all `M` (`R²R = 0`):
* **`H_push_Qt_eq_zero`**: `Ext^(m+1)(A, R (Qt M)) = 0`;
* **`H_push_eq_zero_of_R1`**: `Ext^(n+3)(A, R N) = 0` if `Ext^(n+1)(A, R1 R N) = 0`;
* **`H_push_two_eq_zero`**: `Ext²(A, R N) = 0` if every `A`-section of `R1 R N` lifts to `R (Qt N)`.
Specialised to `pull g ⊣ push g`, `A = Λ_X`, `B = Λ_Y` (étale cohomology `H Λ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

namespace LerayG

open Abelian

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [EnoughInjectives D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

variable [R.PreservesZeroMorphisms]

variable [L.PreservesMonomorphisms]

variable {A : C} {B : D} (eAB : L.obj A ≅ B)

variable [HasExt.{w} C] [HasExt.{w} D]

include adj in
/-- `0 → R N → R I → R (I/N) → 0` is short exact when `R1 R N = 0`. -/
theorem push_injPres_shortExact (N : D) (hR : IsZero (R1 R N)) : (presI R N).ShortExact where
  exact := presI_exact adj N
  mono_f := by
    have := plim adj
    exact R.map_mono (Injective.ι N)
  epi_g := Preadditive.epi_of_cokernel_zero (hR.eq_of_tgt _ _)

include adj eAB in
/-- **`Ext^(m+1)(A, R (I/M)) = 0`** under `Ext²(B, -) = 0` and `R²R = 0`. -/
theorem H_push_Qt_eq_zero (hη : ∀ (M : D) (e : Ext.{w} B M 2), e = 0)
    (hR : ∀ M : D, IsZero (R1 R (Qt M))) :
    ∀ (m : ℕ) (M : D) (e : Ext.{w} A (R.obj (Qt M)) (m + 1)), e = 0 := by
  intro m
  induction m with
  | zero =>
    intro M e
    have hS := push_injPres_shortExact adj (Qt M) (hR M)
    have : Injective (presI R (Qt M)).X₂ := injective_push adj (Injective.under (Qt M))
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS e (Ext.eq_zero_of_injective _)
      (show 0 + 1 = 0 + 1 from rfl)
    obtain ⟨a, ha⟩ := lift_push adj eAB (cokernel.π (Injective.ι (Qt M)))
      (lift_of_ext_one B (injPres_shortExact (Qt M)) (H_Qt_one_eq_zero hη M)) (Ext.homEquiv₀ x₃)
    have hx : x₃ = (Ext.mk₀ a).comp (Ext.mk₀ (R.map (cokernel.π (Injective.ι (Qt M))))) (zero_add 0) := by
      rw [Ext.mk₀_comp_mk₀, ha, Ext.mk₀_homEquiv₀_apply]
    have hc : (Ext.mk₀ (R.map (cokernel.π (Injective.ι (Qt M))))).comp hS.extClass (zero_add 1) = 0 :=
      hS.comp_extClass
    rw [hx, Ext.comp_assoc_of_second_deg_zero, hc, Ext.comp_zero]
  | succ m ih =>
    intro M e
    have hS := push_injPres_shortExact adj (Qt M) (hR M)
    have : Injective (presI R (Qt M)).X₂ := injective_push adj (Injective.under (Qt M))
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS e (Ext.eq_zero_of_injective _)
      (show m + 1 + 1 = m + 1 + 1 from rfl)
    rw [ih (Qt M) x₃, Ext.zero_comp]

include adj eAB in
/-- **`Ext^(n+3)(A, R N) = 0`** when `Ext^(n+1)(A, R¹R N) = 0` (and `Ext²(B, -) = 0`, `R²R = 0`). -/
theorem H_push_eq_zero_of_R1 (hη : ∀ (M : D) (e : Ext.{w} B M 2), e = 0)
    (hR : ∀ M : D, IsZero (R1 R (Qt M))) (n : ℕ) (N : D)
    (h1 : ∀ e : Ext.{w} A (R1 R N) (n + 1), e = 0) (e : Ext.{w} A (R.obj N) (n + 3)) : e = 0 := by
  have : Injective (presA R N).X₂ := injective_push adj (Injective.under N)
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ (presA_shortExact adj N) e
    (Ext.eq_zero_of_injective _) (show n + 2 + 1 = n + 3 from rfl)
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ (presB_shortExact R N) x₃
    (H_push_Qt_eq_zero adj eAB hη hR (n + 1) N _) (show n + 1 + 1 = n + 2 from rfl)
  rw [h1 y, Ext.zero_comp, Ext.zero_comp]

end LerayG

open RamanujanPetersson.EtSheaves

universe u

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (Λ : Type u) [CommRing Λ]

variable {g Λ}

/-- **`H^(n+3)(X, g_* N) = 0`** when `H^(n+1)(X, R¹g_* N) = 0` (and `H²(Y, -) = 0`, `R²g_* = 0`). -/
theorem H_push_eq_zero_of_R1 (hη : ∀ (M : EtSh Λ Y) (e : H Λ M 2), e = 0)
    (hR : ∀ M : EtSh Λ Y, IsZero (R1 g Λ (Qt Λ M))) (n : ℕ) (N : EtSh Λ Y)
    (h1 : ∀ e : H Λ (R1 g Λ N) (n + 1), e = 0) (e : H Λ ((push g Λ).obj N) (n + 3)) : e = 0 := by
  have := LerayG.pzm (pullAdj g Λ)
  exact LerayG.H_push_eq_zero_of_R1 (pullAdj g Λ) (pullConst Λ g (ModuleCat.of Λ Λ)) hη hR n N h1 e

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_CechH =====
section

/-!
# S4-EtCompact: Cech complexes with extra codegeneracies; fibres of Cech nerves (O8c (B), file C1)

* `Cech.ExtraCodeg X`: maps `h_n : X[n+1] ⟶ X[n]` of a cosimplicial module with `δ₀ ≫ h = 𝟙` and
  `δ_{j+1} ≫ h = h ≫ δ_j`; **`Cech.ExtraCodeg.exactAt_succ`**: then the alternating coface complex is exact in
  every degree `n + 1` (the contracting homotopy `d h + h d = 𝟙`).
* `Cech.fib_ext`, `Cech.exists_fib`: an element of `Φ.fiber` of a finite wide pullback is determined by, and can be
  built from, compatible projections (`Φ.fiber` preserves finite limits).
* `Cech.cons`: for a section `σ` of `Φ.fiber f`, prepending `σ (base x)` to `x`; `Cech.δ_zero_cons`,
  `Cech.δ_succ_cons`: the extra degeneracy identities on the fibres of `(Arrow.mk f).cechNerve`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicTopology Opposite Simplicial

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe v u w

section Htpy

variable {Λ : Type u} [CommRing Λ] (X : CosimplicialObject (ModuleCat.{v} Λ))

/-- Extra codegeneracies of a cosimplicial module: `h_n : X[n+1] ⟶ X[n]` with `δ₀ ≫ h = 𝟙` and
`δ_{j+1} ≫ h = h ≫ δ_j`. -/
structure ExtraCodeg where
  h : ∀ n : ℕ, X.obj ⦋n + 1⦌ ⟶ X.obj ⦋n⦌
  h_δ₀ : ∀ n : ℕ, X.δ (n := n) 0 ≫ h n = 𝟙 _
  h_δ_succ : ∀ (n : ℕ) (j : Fin (n + 2)), X.δ (n := n + 1) j.succ ≫ h (n + 1) = h n ≫ X.δ j

variable {X}

theorem objD_comp_h (e : ExtraCodeg X) (n : ℕ) :
    AlternatingCofaceMapComplex.objD X (n + 1) ≫ e.h (n + 1) =
      𝟙 _ - e.h n ≫ AlternatingCofaceMapComplex.objD X n := by
  rw [AlternatingCofaceMapComplex.objD, AlternatingCofaceMapComplex.objD, Preadditive.sum_comp,
    Preadditive.comp_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, e.h_δ₀,
    e.h_δ_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul]

theorem d_eq (m : ℕ) : ((alternatingCofaceMapComplex (ModuleCat.{v} Λ)).obj X).d m (m + 1) =
    AlternatingCofaceMapComplex.objD X m :=
  CochainComplex.of_d (fun n => X.obj ⦋n⦌) (AlternatingCofaceMapComplex.objD X) m

/-- **Extra codegeneracies make the alternating coface complex exact in positive degrees.** -/
theorem ExtraCodeg.exactAt_succ (e : ExtraCodeg X) (n : ℕ) :
    ((alternatingCofaceMapComplex (ModuleCat.{v} Λ)).obj X).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rintro (x : X.obj ⦋n + 1⦌) hx
  refine ⟨(e.h n).hom x, ?_⟩
  have hx' : (AlternatingCofaceMapComplex.objD X (n + 1)).hom x = 0 := by
    rw [← d_eq]; exact hx
  have h1 : (e.h (n + 1)).hom ((AlternatingCofaceMapComplex.objD X (n + 1)).hom x) =
      x - (AlternatingCofaceMapComplex.objD X n).hom ((e.h n).hom x) :=
    congrArg (fun φ => φ.hom x) (objD_comp_h e n)
  rw [hx', map_zero] at h1
  show (((alternatingCofaceMapComplex (ModuleCat.{v} Λ)).obj X).d n (n + 1)).hom ((e.h n).hom x) = x
  rw [d_eq]
  exact (sub_eq_zero.1 h1.symm).symm

end Htpy

section Fib

variable {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C] (P : C ⥤ Type w)
  [PreservesFiniteLimits P] {V W : C} (f : V ⟶ W)

/-- The limit cone of a finite wide pullback stays a limit after `P`. -/
def fibLim (n : ℕ) :
    IsLimit (P.mapCone (limit.cone
      (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f)))) :=
  isLimitOfPreserves P (limit.isLimit _)

theorem fib_ext {n : ℕ} (x y : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)))
    (h : ∀ j, P.map (WidePullback.π (fun _ : Fin (n + 1) => f) j) x =
      P.map (WidePullback.π (fun _ : Fin (n + 1) => f) j) y) : x = y := by
  apply (Types.isLimitEquivSections (fibLim P f n)).injective
  apply Subtype.ext
  funext j
  rcases j with _ | j
  · have e : ∀ z, ((Types.isLimitEquivSections (fibLim P f n)) z).1 none =
        P.map f (((Types.isLimitEquivSections (fibLim P f n)) z).1 (some 0)) := fun z =>
      (((Types.isLimitEquivSections (fibLim P f n)) z).2
        (WidePullbackShape.Hom.term (J := Fin (n + 1)) 0)).symm
    rw [e x, e y]
    exact congrArg (P.map f) (h 0)
  · exact h j

theorem exists_fib {n : ℕ} (a : Fin (n + 1) → P.obj V) (w : P.obj W) (ha : ∀ j, P.map f (a j) = w) :
    ∃ x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)),
      ∀ j, P.map (WidePullback.π (fun _ : Fin (n + 1) => f) j) x = a j := by
  let s : (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f) ⋙ P).sections :=
    ⟨fun j : WidePullbackShape (Fin (n + 1)) => match j with
      | none => w
      | some j => a j, by
      rintro (_ | j) (_ | j') (g : WidePullbackShape.Hom _ _)
      · cases g
        exact Functor.map_id_apply
          (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f) ⋙ P) _ _
      · cases g
      · cases g
        exact ha j
      · cases g
        exact Functor.map_id_apply
          (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f) ⋙ P) _ _⟩
  refine ⟨(Types.isLimitEquivSections (fibLim P f n)).symm s, fun j => ?_⟩
  exact Types.isLimitEquivSections_symm_apply (fibLim P f n) s (some j)

theorem δ_π {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.δ i ≫ WidePullback.π (fun _ : Fin (n + 1) => f) j =
      WidePullback.π (fun _ : Fin (n + 2) => f) (i.succAbove j) := by
  exact WidePullback.lift_π ..

theorem δ_base {n : ℕ} (i : Fin (n + 2)) :
    (Arrow.mk f).cechNerve.δ i ≫ WidePullback.base (fun _ : Fin (n + 1) => f) =
      WidePullback.base (fun _ : Fin (n + 2) => f) := by
  exact WidePullback.lift_base ..

variable {P f} (σ : P.obj W → P.obj V) (hσ : ∀ w, P.map f (σ w) = w)

/-- The family `(σ (base x), π₀ x, …, πₙ x)`. -/
def consFun {n : ℕ} (x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f))) :
    Fin (n + 2) → P.obj V :=
  Fin.cons (σ (P.map (WidePullback.base (fun _ : Fin (n + 1) => f)) x))
    (fun j => P.map (WidePullback.π (fun _ : Fin (n + 1) => f) j) x)

omit [PreservesFiniteLimits P] in
theorem consFun_zero {n : ℕ} (x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f))) :
    consFun σ x 0 = σ (P.map (WidePullback.base (fun _ : Fin (n + 1) => f)) x) :=
  Fin.cons_zero _ _

omit [PreservesFiniteLimits P] in
theorem consFun_succ {n : ℕ} (x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)))
    (j : Fin (n + 1)) : consFun σ x j.succ = P.map (WidePullback.π (fun _ : Fin (n + 1) => f) j) x :=
  Fin.cons_succ _ _ _

include hσ in
omit [PreservesFiniteLimits P] in
theorem consFun_spec {n : ℕ} (x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)))
    (j : Fin (n + 2)) :
    P.map f (consFun σ x j) = P.map (WidePullback.base (fun _ : Fin (n + 1) => f)) x := by
  induction j using Fin.cases with
  | zero => rw [consFun_zero]; exact hσ _
  | succ j => rw [consFun_succ, ← Functor.map_comp_apply, WidePullback.π_arrow]

/-- Prepending `σ (base x)`: the extra degeneracy on the fibres of the Cech nerve. -/
def cons {n : ℕ} (x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f))) :
    P.obj (widePullback W (fun _ : Fin (n + 2) => V) (fun _ => f)) :=
  (exists_fib P f (consFun σ x) _ (consFun_spec σ hσ x)).choose

theorem cons_π {n : ℕ} (x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f)))
    (j : Fin (n + 2)) :
    P.map (WidePullback.π (fun _ : Fin (n + 2) => f) j) (cons σ hσ x) = consFun σ x j :=
  (exists_fib P f (consFun σ x) _ (consFun_spec σ hσ x)).choose_spec j

theorem δ_zero_cons {n : ℕ} (x : P.obj (widePullback W (fun _ : Fin (n + 1) => V) (fun _ => f))) :
    P.map ((Arrow.mk f).cechNerve.δ (n := n) 0) (cons σ hσ x) = x := by
  refine fib_ext (n := n) P f _ _ fun j => ?_
  rw [← Functor.map_comp_apply, δ_π, Fin.succAbove_zero, cons_π, consFun_succ]

theorem δ_succ_cons {n : ℕ} (j : Fin (n + 2))
    (x : P.obj (widePullback W (fun _ : Fin (n + 2) => V) (fun _ => f))) :
    P.map ((Arrow.mk f).cechNerve.δ (n := n + 1) j.succ) (cons σ hσ x) =
      cons σ hσ (P.map ((Arrow.mk f).cechNerve.δ (n := n) j) x) := by
  refine fib_ext (n := n + 1) P f _ _ fun k => ?_
  rw [← Functor.map_comp_apply, δ_π, cons_π, cons_π]
  induction k using Fin.cases with
  | zero =>
    rw [Fin.succ_succAbove_zero, consFun_zero, consFun_zero, ← Functor.map_comp_apply, δ_base]
  | succ k =>
    rw [Fin.succ_succAbove_succ, consFun_succ, consFun_succ, ← Functor.map_comp_apply, δ_π]

end Fib

end RamanujanPetersson.EtCompact.Cech

end

end


