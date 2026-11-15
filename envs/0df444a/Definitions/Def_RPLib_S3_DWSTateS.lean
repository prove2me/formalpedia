-- Prove2me | Definitions.Def_RPLib_S3_DWSTateS
-- name    : RPLib_S3_DWSTateS
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:55:46.144655+00:00
-- url     : https://prove2.me/theorems/a848b3ba-0f4d-46ee-ab52-9a0d324a8044
-- title:
--   Weight-two Ramanujan-Petersson library: the Vélu quotient by `H` has function field `f_L(L(E'))`
-- statement:
--   The Vélu quotient by `H` has function field `f_L(L(E'))`.
--
--   * `invG_of_mem_qR` : functions pulled back from `E/G` are `G`-invariant;
--   * **`exists_sigma`** : if `φ : L(E') → L(E)` has range `L(E)^G`, then `φ = pull2_G ∘ σ` for an
--     `L`-isomorphism `σ : L(E') ≃ L(E/G)`;
--   * `sig_pull2_qPt`, **`sig_sigma`** : `σ` commutes with Galois automorphisms fixing `X_G, Y_G` (e.g. Frobenius);
--   * **`exists_velu_sigma`** : the Tate data case (`G = H`, `φ = f_L`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateR

/-!
# S3-DWS-Tate, file S (BR2b): the Vélu quotient by `H` has function field `f_L(L(E'))`

* `invG_of_mem_qR` : functions pulled back from `E/G` are `G`-invariant;
* **`exists_sigma`** : if `φ : L(E') → L(E)` has range `L(E)^G`, then `φ = pull2_G ∘ σ` for an
  `L`-isomorphism `σ : L(E') ≃ L(E/G)`;
* `sig_pull2_qPt`, **`sig_sigma`** : `σ` commutes with Galois automorphisms fixing `X_G, Y_G` (e.g. Frobenius);
* **`exists_velu_sigma`** : the Tate data case (`G = H`, `φ = f_L`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section VeluSigma

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L] {N : ℕ}

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G] {W₁ : WeierstrassCurve F} [W₁.IsElliptic]

/-- Functions pulled back from `E/G` are `G`-invariant. -/
lemma invG_of_mem_qR (hW₁ : (W₁.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {k : FF W L}
    (hk : k ∈ qR hW₁) : InvG G k := by
  intro S hS
  obtain ⟨u, rfl⟩ := (AlgHom.mem_range _).mp hk
  have e : (tau W L S).toAlgHom.comp (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁)) =
      pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) := by
    apply algHom_ext_gen W₁ L
    · rw [AlgHom.comp_apply, pull2_gx, px_qPt]
      exact (goodQ_qx (G := G)).1 S hS
    · rw [AlgHom.comp_apply, pull2_gy, py_qPt]
      exact (goodQ_qy (G := G)).1 S hS
  exact AlgHom.congr_fun e u

set_option maxHeartbeats 400000 in
/-- **`φ` factors through the Vélu quotient by an isomorphism** when its range is `L(E)^G`. -/
theorem exists_sigma (hG : (Fintype.card G : L) ≠ 0)
    (hW₁ : (W₁.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) (φ : FF W' L →ₐ[L] FF W L)
    (hφ : ∀ k, k ∈ φ.range ↔ InvG G k) :
    ∃ σ : FF W' L ≃ₐ[L] FF W₁ L, ∀ k, pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) (σ k) = φ k := by
  have hR : φ.range = (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁)).range := by
    apply le_antisymm
    · intro k hk
      exact invG_mem_qR hG hW₁ ((hφ k).mp hk)
    · intro k hk
      exact (hφ k).mpr (invG_of_mem_qR hW₁ hk)
  obtain ⟨e1, he1⟩ : ∃ e1 : FF W' L ≃ₐ[L] φ.range, ∀ x, (e1 x : FF W L) = φ x :=
    ⟨AlgEquiv.ofInjective φ φ.toRingHom.injective, fun x => AlgEquiv.ofInjective_apply _ _ x⟩
  obtain ⟨e2, he2⟩ : ∃ e2 : FF W₁ L ≃ₐ[L] (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁)).range,
      ∀ x, (e2 x : FF W L) = pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) x :=
    ⟨AlgEquiv.ofInjective _ (pull2_injective _ _), fun x => AlgEquiv.ofInjective_apply _ _ x⟩
  refine ⟨e1.trans ((Subalgebra.equivOfEq _ _ hR).trans e2.symm), fun k => ?_⟩
  have h3 : ((Subalgebra.equivOfEq _ _ hR (e1 k) : (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁)).range) : FF W L) =
      φ k := by
    rw [Subalgebra.equivOfEq_apply]; exact he1 k
  rw [← he2, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, h3]

/-- The Vélu pullback commutes with a Galois automorphism fixing `X_G` and `Y_G`. -/
lemma sig_pull2_qPt (γ : L ≃ₐ[F] L) (hW₁ : (W₁.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hx : sig W γ (qx G) = qx G) (hy : sig W γ (qy G) = qy G) (k : FF W₁ L) :
    sig W γ (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) k) = pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) (sig W₁ γ k) := by
  let φ : FF W₁ L →ₐ[L] FF W L :=
    { ((sig W γ).toAlgHom.comp (((pull2 (qPt hW₁) (qPt_ne_ιQ hW₁)).restrictScalars F).comp
        (sig W₁ γ).symm.toAlgHom)).toRingHom with
      commutes' := fun a => by
        show sig W γ (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) ((sig W₁ γ).symm (algebraMap L (FF W₁ L) a))) =
          algebraMap L (FF W L) a
        rw [sig_symm_L, AlgHom.commutes, sig_L, AlgEquiv.apply_symm_apply] }
  have hφ : φ = pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) := by
    apply algHom_ext_gen W₁ L
    · show sig W γ (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) ((sig W₁ γ).symm (gx W₁ L))) =
        pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) (gx W₁ L)
      have h1 : (sig W₁ γ).symm (gx W₁ L) = gx W₁ L := by rw [AlgEquiv.symm_apply_eq, sig_gx]
      rw [h1, pull2_gx, px_qPt]
      exact hx
    · show sig W γ (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) ((sig W₁ γ).symm (gy W₁ L))) =
        pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) (gy W₁ L)
      have h1 : (sig W₁ γ).symm (gy W₁ L) = gy W₁ L := by rw [AlgEquiv.symm_apply_eq, sig_gy]
      rw [h1, pull2_gy, py_qPt]
      exact hy
  have h := AlgHom.congr_fun hφ (sig W₁ γ k)
  change sig W γ (pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) ((sig W₁ γ).symm (sig W₁ γ k))) =
    pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) (sig W₁ γ k) at h
  rwa [AlgEquiv.symm_apply_apply] at h

/-- `σ` is Galois-equivariant (for `γ` fixing `X_G, Y_G`, e.g. Frobenius when `G` is Frobenius-stable). -/
theorem sig_sigma [Algebra.IsAlgebraic F L] (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (γ : L ≃ₐ[F] L) (hW₁ : (W₁.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hx : sig W γ (qx G) = qx G) (hy : sig W γ (qy G) = qy G) (σ : FF W' L ≃ₐ[L] FF W₁ L)
    (hσ : ∀ k, pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) (σ k) = fL L f k) (k : FF W' L) :
    σ (sig W' γ k) = sig W₁ γ (σ k) := by
  apply pull2_injective (qPt hW₁) (qPt_ne_ιQ hW₁)
  rw [hσ, ← sig_fL f γ k, ← hσ, sig_pull2_qPt γ hW₁ hx hy]

/-- **BR2b (Tate data)**: `E/H` exists over `F` and `f_L = pull2_H ∘ σ` with `σ : L(E') ≃ L(E/H)`. -/
theorem exists_velu_sigma [Algebra.IsAlgebraic F L] (hNF : (N : F) ≠ 0)
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField)
    (hfg : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W) [Fintype (HT L N f)] :
    ∃ W₁ : WeierstrassCurve F, ∃ _ : W₁.IsElliptic,
      ∃ hW₁ : (W₁.baseChange (FF W L)).toAffine.Equation (qx (HT L N f)) (qy (HT L N f)),
        ∃ σ : FF W' L ≃ₐ[L] FF W₁ L, ∀ k, pull2 (qPt hW₁) (qPt_ne_ιQ hW₁) (σ k) = fL L f k := by
  have hG : (Fintype.card (HT L N f) : L) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]; exact card_HT_ne_zero hNF f
  obtain ⟨W₁, hE, hW₁⟩ := exists_quotient hG (frob_mem_HT f)
  have := hE
  obtain ⟨σ, hσ⟩ := exists_sigma hG hW₁ (fL L f) (fun k => by
    rw [← mem_fieldRange_fL_iff_HT hNF f g hfg k, AlgHom.mem_range, AlgHom.mem_fieldRange])
  exact ⟨W₁, hE, hW₁, σ, hσ⟩

end VeluSigma

end RPLib.DWS


