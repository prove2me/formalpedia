-- Prove2me | Definitions.Def_RPLib_S3_DWSOVC
-- name    : RPLib_S3_DWSOVC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:28:14.44793+00:00
-- url     : https://prove2.me/theorems/d036e1a0-7235-43a6-8937-271dc0201429
-- title:
--   Weight-two Ramanujan-Petersson library: representatives of isomorphisms (O1, V3a + V4)
-- statement:
--   Representatives of isomorphisms (O1, V3a + V4).
--
--   * `hasGenI_G` : the generic point represents the identity.
--   * `eq_ιQ_of_hasGenI_zero` : a translation-invariant point of `W'(L(E))` is constant.
--   * `hasGenI_comp_rep` : the pulled-back representative of a composite.
--   * **`exists_algEquiv`** : if `v ∘ u = id` for isogenies `u, v`, then a representative `Φ` of `u` is
--     `genPt ψ` for an `L`-isomorphism of function fields `ψ : L(E') ≃ L(E)`.
--   * **`hasGenI_ptHom`** : `ptMap C^ι (G)` represents the point map of a change of variables `C` over `L`;
--     `eq_ptHom_of_hasGenI` : a map with that representative is the point map.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOVB

/-!
# S3-DWS-Ordinary, part VC: representatives of isomorphisms (O1, V3a + V4)

* `hasGenI_G` : the generic point represents the identity.
* `eq_ιQ_of_hasGenI_zero` : a translation-invariant point of `W'(L(E))` is constant.
* `hasGenI_comp_rep` : the pulled-back representative of a composite.
* **`exists_algEquiv`** : if `v ∘ u = id` for isogenies `u, v`, then a representative `Φ` of `u` is
  `genPt ψ` for an `L`-isomorphism of function fields `ψ : L(E') ≃ L(E)`.
* **`hasGenI_ptHom`** : `ptMap C^ι (G)` represents the point map of a change of variables `C` over `L`;
  `eq_ptHom_of_hasGenI` : a map with that representative is the point map.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Rep

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma hasGenI_G : HasGenI (AddMonoidHom.id (Pt W L)) (G W L) := fun S => by
  rw [map_tau_G]; rfl

/-- A translation-invariant point of `W'(L(E))` is constant. -/
lemma eq_ιQ_of_hasGenI_zero {Z : (W'.baseChange (FF W L)).toAffine.Point} (h : HasGenI 0 Z) :
    ∃ C : Pt W' L, Z = ιQ W W' L C := by
  by_cases hZ : Z = 0
  · exact ⟨0, by rw [hZ, map_zero]⟩
  have hinv : ∀ S, Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Z = Z := fun S => by
    rw [h S, AddMonoidHom.zero_apply, map_zero, add_zero]
  haveI : Infinite (Pt W L) := infinite_pt
  have hconst : ∀ f : FF W L, (∀ S, tau W L S f = f) → ∃ c : L, f = algebraMap L (FF W L) c := by
    intro f hf
    by_contra hc
    push_neg at hc
    have hfin := finite_fixed hc
    rw [Set.eq_univ_of_forall hf] at hfin
    exact Set.infinite_univ hfin
  obtain ⟨a, ha⟩ := hconst (px Z) fun S => by
    rw [tau_apply]
    have e := congrArg px (hinv S)
    rw [px_map] at e
    exact e
  obtain ⟨b, hb⟩ := hconst (py Z) fun S => by
    rw [tau_apply]
    have e := congrArg py (hinv S)
    rw [py_map] at e
    exact e
  exact eq_ιQ_of_const hZ ha hb

/-- The representative of a composite, pulled back along the first representative. -/
lemma hasGenI_comp_rep {W'' : WeierstrassCurve F} [W''.IsElliptic] {φ : Pt W L →+ Pt W' L}
    {ψ : Pt W' L →+ Pt W'' L} {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    {Ψ : (W''.baseChange (FF W' L)).toAffine.Point} (hψ : HasGenI ψ Ψ) (hφ : HasGenI φ Φ)
    (hc : ∀ C, Φ ≠ ιQ W W' L C) :
    HasGenI (ψ.comp φ) (Point.map (W' := W''.toAffine) ((pull2 Φ hc).restrictScalars F) Ψ) := fun S => by
  have hcomp : ((tauHom W L S).restrictScalars F).comp ((pull2 Φ hc).restrictScalars F) =
      ((pull2 Φ hc).restrictScalars F).comp ((tauHom W' L (φ S)).restrictScalars F) := by
    apply AlgHom.ext
    intro f
    exact AlgHom.congr_fun (tau_comp_pull2 Φ hc hφ S) f
  rw [Point.map_map, hcomp, ← Point.map_map, hψ (φ S), map_add, map_pull2_ιQ]
  rfl

/-- **A representative of an invertible isogeny is a carried generic point.** -/
theorem exists_algEquiv {u : Pt W L →+ Pt W' L} {v : Pt W' L →+ Pt W L}
    {Φ : (W'.baseChange (FF W L)).toAffine.Point} {Ψ : (W.baseChange (FF W' L)).toAffine.Point}
    (hu : HasGenI u Φ) (hv : HasGenI v Ψ) (hvu : ∀ P, v (u P) = P) :
    ∃ ψ : FF W' L ≃ₐ[L] FF W L, genPt ψ = Φ := by
  haveI : Infinite (Pt W L) := infinite_pt
  obtain ⟨P₁, hP₁⟩ := exists_ne (0 : Pt W L)
  have hc : ∀ C, Φ ≠ ιQ W W' L C := fun C hC => hP₁ (by
    have e := hvu P₁
    rw [hu.eq_zero_of_const C hC, AddMonoidHom.zero_apply, map_zero] at e
    exact e.symm)
  have hc' : ∀ C, Ψ ≠ ιQ W' W L C := fun C hC => hP₁ (by
    have e := hvu P₁
    rw [hv.eq_zero_of_const C hC, AddMonoidHom.zero_apply] at e
    exact e.symm)
  have hΞ := hasGenI_comp_rep hv hu hc
  have hid : v.comp u = AddMonoidHom.id (Pt W L) := by ext P; exact hvu P
  rw [hid] at hΞ
  have h0 := hΞ.add (hasGenI_G (W := W) (L := L)).neg
  rw [add_neg_cancel] at h0
  obtain ⟨C, hC⟩ := eq_ιQ_of_hasGenI_zero h0
  have hΞC : Point.map (W' := W.toAffine) ((pull2 Φ hc).restrictScalars F) Ψ = pS W L C := by
    rw [pS]
    show _ = G W L + ιQ W W L C
    rw [← hC]
    abel
  have key : (pull2 Φ hc).comp (pull2 Ψ hc') = tauHom W L C := by
    apply algHom_ext_gen W L
    · rw [AlgHom.comp_apply, pull2_gx, tauHom_gx, ← hΞC, px_map]
      rfl
    · rw [AlgHom.comp_apply, pull2_gy, tauHom_gy, ← hΞC, py_map]
      rfl
  have hsurj : Function.Surjective (pull2 Φ hc) := fun g => by
    refine ⟨pull2 Ψ hc' ((tau W L C).symm g), ?_⟩
    have e := AlgHom.congr_fun key ((tau W L C).symm g)
    rw [AlgHom.comp_apply] at e
    rw [e, ← tau_apply, AlgEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofBijective (pull2 Φ hc) ⟨pull2_injective Φ hc, hsurj⟩, ?_⟩
  rw [genPt]
  exact map_pull2_G Φ hc

end Rep

section PtHom

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma ptMap_congr {K : Type*} [Field K] [DecidableEq K] {V V' : WeierstrassCurve K}
    {C₁ C₂ : VariableChange K} (e : C₁ = C₂) (h₁ : C₁ • V = V') (h₂ : C₂ • V = V')
    (P : V.toAffine.Point) : RPLib.TateNF.ptMap C₁ h₁ P = RPLib.TateNF.ptMap C₂ h₂ P := by
  subst e; rfl

/-- **The generic image of a change of variables represents its point map.** -/
theorem hasGenI_ptHom {C : VariableChange L} (h : C • W.baseChange L = W'.baseChange L) :
    HasGenI (RPLib.TateNF.ptHom C h)
      (RPLib.TateNF.ptMap (C.map (ιF W L : L →+* FF W L)) (vc_bc (ιF W L) h) (G W L)) := fun S => by
  rw [ptMap_map ((tauHom W L S).restrictScalars F) (vc_bc (ιF W L) h) (G W L), map_tau_G, pS]
  rw [ptMap_congr (C₂ := C.map (ιF W L : L →+* FF W L)) ?_ _ (vc_bc (ιF W L) h), RPLib.TateNF.ptMap_add]
  · congr 1
    rw [RPLib.TateNF.ptHom_apply]
    show _ = Point.map (W' := W'.toAffine) (ιF W L) (RPLib.TateNF.ptMap C h S)
    rw [ptMap_map (ιF W L) h S]
    rfl
  · rw [VariableChange.map_map]
    congr 1
    ext a
    exact (tauHom W L S).commutes a

/-- A map represented by `ptMap C^ι (G)` is the point map of `C`. -/
theorem eq_ptHom_of_hasGenI {u : Pt W L →+ Pt W' L} {C : VariableChange L}
    (h : C • W.baseChange L = W'.baseChange L)
    (hu : HasGenI u (RPLib.TateNF.ptMap (C.map (ιF W L : L →+* FF W L)) (vc_bc (ιF W L) h) (G W L))) :
    u = RPLib.TateNF.ptHom C h := by
  have h0 := hu.add (hasGenI_ptHom h).neg
  rw [add_neg_cancel] at h0
  have e := h0.eq_zero_of_const 0 (by rw [map_zero])
  rw [← sub_eq_add_neg] at e
  exact sub_eq_zero.mp e

end PtHom

end RamanujanPetersson.S3.DWSO


