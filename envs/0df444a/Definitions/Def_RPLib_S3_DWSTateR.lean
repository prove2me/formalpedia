-- Prove2me | Definitions.Def_RPLib_S3_DWSTateR
-- name    : RPLib_S3_DWSTateR
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:54:37.334204+00:00
-- url     : https://prove2.me/theorems/988b80ed-2ad8-40d8-83aa-e9acdf535d9b
-- title:
--   Weight-two Ramanujan-Petersson library: Frobenius and the Tate subgroup `H`
-- statement:
--   Frobenius and the Tate subgroup `H`.
--
--   For the Tate data `(f, g, N)` (`f : K_F(E') → K_F(E)` is `F`-rational):
--   * `sig_jFF`, **`sig_fL`** : Galois automorphisms `σ ∈ Aut(L/F)` commute with `f_L` (`σ ∘ f_L = f_L ∘ σ`);
--   * `HT L N f` : the subgroup of `S ∈ E[N]` whose translation fixes `f_L(L(E'))`;
--   * **`ptMap_mem_HT`**, **`frob_mem_HT`** : `H` is Galois-stable, in particular Frobenius-stable;
--   * `finite_HT`, **`card_HT_ne_zero`** (`p ∤ #H`), **`mem_fieldRange_fL_iff_HT`** : `f_L(L(E')) = L(E)^H`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateP

/-!
# S3-DWS-Tate, file R (BR3): Frobenius and the Tate subgroup `H`

For the Tate data `(f, g, N)` (`f : K_F(E') → K_F(E)` is `F`-rational):
* `sig_jFF`, **`sig_fL`** : Galois automorphisms `σ ∈ Aut(L/F)` commute with `f_L` (`σ ∘ f_L = f_L ∘ σ`);
* `HT L N f` : the subgroup of `S ∈ E[N]` whose translation fixes `f_L(L(E'))`;
* **`ptMap_mem_HT`**, **`frob_mem_HT`** : `H` is Galois-stable, in particular Frobenius-stable;
* `finite_HT`, **`card_HT_ne_zero`** (`p ∤ #H`), **`mem_fieldRange_fL_iff_HT`** : `f_L(L(E')) = L(E)^H`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Frob

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L] {N : ℕ}

attribute [local instance] finite_coordinateRing decEqFF

/-- Galois automorphisms fix the base change of `F`-rational functions. -/
lemma sig_jFF (σ : L ≃ₐ[F] L) (k : W.toAffine.FunctionField) : sig W σ (jFF W L k) = jFF W L k := by
  have e : (sig W σ).toAlgHom.comp (jFF W L) = jFF W L := by
    apply algHom_ext_gen0 W
    · have hx : jFF W L (x0 W) = gx W L := jFF_x
      rw [AlgHom.comp_apply, hx]
      exact sig_gx σ
    · have hy : jFF W L (y0 W) = gy W L := jFF_y
      rw [AlgHom.comp_apply, hy]
      exact sig_gy σ
  exact AlgHom.congr_fun e k

/-- `σ ∘ f_L = f_L ∘ σ` for `σ ∈ Aut(L/F)`: the base-changed Tate map is `F`-rational. -/
lemma sig_fL [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (σ : L ≃ₐ[F] L) (k : FF W' L) : sig W σ (fL L f k) = fL L f (sig W' σ k) := by
  let φ : FF W' L →ₐ[L] FF W L :=
    { ((sig W σ).toAlgHom.comp (((fL L f).restrictScalars F).comp (sig W' σ).symm.toAlgHom)).toRingHom with
      commutes' := fun a => by
        show sig W σ (fL L f ((sig W' σ).symm (algebraMap L (FF W' L) a))) = algebraMap L (FF W L) a
        rw [sig_symm_L, AlgHom.commutes, sig_L, AlgEquiv.apply_symm_apply] }
  have hφ : φ = fL L f := by
    apply algHom_ext_gen W' L
    · show sig W σ (fL L f ((sig W' σ).symm (gx W' L))) = fL L f (gx W' L)
      have h1 : (sig W' σ).symm (gx W' L) = gx W' L := by rw [AlgEquiv.symm_apply_eq, sig_gx]
      have hx : jFF W' L (x0 W') = gx W' L := jFF_x
      rw [h1, ← hx, fL_jFF, sig_jFF]
    · show sig W σ (fL L f ((sig W' σ).symm (gy W' L))) = fL L f (gy W' L)
      have h1 : (sig W' σ).symm (gy W' L) = gy W' L := by rw [AlgEquiv.symm_apply_eq, sig_gy]
      have hy : jFF W' L (y0 W') = gy W' L := jFF_y
      rw [h1, ← hy, fL_jFF, sig_jFF]
  have h := AlgHom.congr_fun hφ (sig W' σ k)
  change sig W σ (fL L f ((sig W' σ).symm (sig W' σ k))) = fL L f (sig W' σ k) at h
  rwa [AlgEquiv.symm_apply_apply] at h

lemma sig_symm_fL [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (σ : L ≃ₐ[F] L) (k : FF W' L) : (sig W σ).symm (fL L f k) = fL L f ((sig W' σ).symm k) := by
  rw [AlgEquiv.symm_apply_eq, sig_fL, AlgEquiv.apply_symm_apply]

variable (L N) in
/-- `H` : the points `S ∈ E[N]` whose translation fixes `f_L(L(E'))`. -/
noncomputable def HT [Algebra.IsAlgebraic F L]
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) : AddSubgroup (Pt W L) where
  carrier := {S | S ∈ torsN W L N ∧ ∀ e ∈ (fL L f).fieldRange, tau W L S e = e}
  add_mem' := by
    rintro S T ⟨hS, hS'⟩ ⟨hT, hT'⟩
    refine ⟨add_mem hS hT, fun e he => ?_⟩
    rw [tau_add_apply W L S T e, hT' e he, hS' e he]
  zero_mem' := ⟨zero_mem _, fun e _ => tau_zero_apply W L e⟩
  neg_mem' := by
    rintro S ⟨hS, hS'⟩
    refine ⟨neg_mem hS, fun e he => ?_⟩
    calc tau W L (-S) e = tau W L (-S) (tau W L S e) := by rw [hS' e he]
      _ = e := by rw [← tau_add_apply W L (-S) S e, neg_add_cancel, tau_zero_apply W L e]

lemma mem_HT [Algebra.IsAlgebraic F L] {f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField}
    {S : Pt W L} : S ∈ HT L N f ↔ S ∈ torsN W L N ∧ ∀ e ∈ (fL L f).fieldRange, tau W L S e = e :=
  Iff.rfl

lemma HT_le_torsN [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) :
    HT L N f ≤ torsN W L N := fun _ hS => hS.1

/-- `H` is stable under `Aut(L/F)`. -/
lemma ptMap_mem_HT [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (σ : L ≃ₐ[F] L) {S : Pt W L} (hS : S ∈ HT L N f) : ptMap σ S ∈ HT L N f := by
  obtain ⟨hS1, hS2⟩ := hS
  refine ⟨?_, fun e he => ?_⟩
  · rw [mem_torsN] at hS1 ⊢
    rw [← ptMap_nsmul, hS1]
    exact (ptMap_eq_zero σ).mpr rfl
  · obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp he
    have h2 := sig_tau σ S ((sig W σ).symm (fL L f k))
    rw [AlgEquiv.apply_symm_apply, sig_symm_fL,
      hS2 (fL L f ((sig W' σ).symm k)) (AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩), sig_fL, AlgEquiv.apply_symm_apply] at h2
    exact h2.symm

/-- **BR3**: `H` is Frobenius-stable. -/
lemma frob_mem_HT [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) :
    ∀ T ∈ HT L N f, RPLib.EllFq.frob W L T ∈ HT L N f := fun T hT => by
  rw [frob_eq_ptMap]
  exact ptMap_mem_HT f _ hT

lemma finite_HT [Algebra.IsAlgebraic F L] (hNF : (N : F) ≠ 0)
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) : Finite (HT L N f) := by
  haveI := finite_torsN (W := W) (L := L) hNF
  exact Finite.of_injective _ (AddSubgroup.inclusion_injective (HT_le_torsN f))

/-- `p ∤ #H`. -/
lemma card_HT_ne_zero [Algebra.IsAlgebraic F L] (hNF : (N : F) ≠ 0)
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) : (Nat.card (HT L N f) : L) ≠ 0 := by
  haveI := finite_torsN (W := W) (L := L) hNF
  obtain ⟨k, hk⟩ := AddSubgroup.card_dvd_of_le (HT_le_torsN (L := L) (N := N) f)
  have h : (Nat.card (torsN W L N) : L) ≠ 0 := card_kerSet_ne_zero (Set.mem_singleton _) hNF
  rw [hk, Nat.cast_mul] at h
  exact left_ne_zero_of_mul h

/-- **`f_L(L(E')) = L(E)^H`.** -/
theorem mem_fieldRange_fL_iff_HT [Algebra.IsAlgebraic F L] (hNF : (N : F) ≠ 0)
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField)
    (hfg : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W) (k : FF W L) :
    k ∈ (fL L f).fieldRange ↔ InvG (HT L N f) k := by
  rw [mem_fieldRange_fL_iff hNF f g hfg k]
  constructor
  · intro h S hS
    exact h S hS.1 hS.2
  · intro h S hS hS'
    exact h S ⟨hS, hS'⟩

end Frob

end RPLib.DWS


