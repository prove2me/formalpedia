-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogO
-- name    : RPLib_S3_DWSIsogO
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:00:45.200995+00:00
-- url     : https://prove2.me/theorems/36632e03-1fa5-4c18-984d-3d8d753cbce1
-- title:
--   Weight-two Ramanujan-Petersson library: the universal property of `E → E/G` and the dual isogeny
-- statement:
--   The universal property of `E → E/G` and the dual isogeny.
--
--   * `exists_pull_of_inv` : a point of `W₁(L(E))` fixed by every `τ_T`, `T ∈ G`, comes from `W₁(L(E/G))`.
--   * **`exists_factor`** : an isogeny `α : E → E₁` that kills `G` factors as `β ∘ qmap` with `β` an isogeny.
--   * **`exists_dual`** : the dual `ψ : E/G → E` with `ψ ∘ qmap = [#G]`, `qmap ∘ ψ = [#G]`, commuting with Frobenius.
--   * **`exists_quot_isog_dual`** : Vélu quotient with its dual; `W` and `W'` are `F_q`-isogenous both ways.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogN

/-!
# S3-DWS-Isog, part O: the universal property of `E → E/G` and the dual isogeny

* `exists_pull_of_inv` : a point of `W₁(L(E))` fixed by every `τ_T`, `T ∈ G`, comes from `W₁(L(E/G))`.
* **`exists_factor`** : an isogeny `α : E → E₁` that kills `G` factors as `β ∘ qmap` with `β` an isogeny.
* **`exists_dual`** : the dual `ψ : E/G → E` with `ψ ∘ qmap = [#G]`, `qmap ∘ ψ = [#G]`, commuting with Frobenius.
* **`exists_quot_isog_dual`** : Vélu quotient with its dual; `W` and `W'` are `F_q`-isogenous both ways.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Factor

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G] {W' : WeierstrassCurve F} [W'.IsElliptic]
  {W₁ : WeierstrassCurve F} [W₁.IsElliptic]

lemma exists_pull_of_inv (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    {A : (W₁.baseChange (FF W L)).toAffine.Point}
    (hA : ∀ T ∈ G, Point.map (W' := W₁.toAffine) ((tauHom W L T).restrictScalars F) A = A) :
    ∃ A' : (W₁.baseChange (FF W' L)).toAffine.Point,
      Point.map (W' := W₁.toAffine) ((pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F) A' = A := by
  by_cases hA0 : A = 0
  · exact ⟨0, by rw [hA0, map_zero]⟩
  have hix : InvG G (px A) := fun T hT => by
    have h := congrArg px (hA T hT)
    rw [px_map] at h
    rw [tau_apply]; exact h
  have hiy : InvG G (py A) := fun T hT => by
    have h := congrArg py (hA T hT)
    rw [py_map] at h
    rw [tau_apply]; exact h
  obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp (invG_mem_qR hG hW' hix)
  obtain ⟨v, hv⟩ := (AlgHom.mem_range _).mp (invG_mem_qR hG hW' hiy)
  have hu' : (pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F u = px A := by
    rw [AlgHom.restrictScalars_apply]; exact hu
  have hv' : (pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F v = py A := by
    rw [AlgHom.restrictScalars_apply]; exact hv
  have hinj : Function.Injective ((pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F) := by
    intro a b h
    rw [AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply] at h
    exact pull2_injective _ _ h
  have hns := nonsingular_px_py hA0
  rw [← hu', ← hv'] at hns
  refine ⟨Point.some u v ((baseChange_nonsingular (W := W₁.toAffine)
    (f := (pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F) hinj u v).mp hns), ?_⟩
  rw [Point.map_some]
  conv_rhs => rw [eq_some_px_py hA0]
  exact some_eq_some hu' hv'

/-- **Universal property of the quotient.** An isogeny killing `G` factors through `E → E/G`. -/
theorem exists_factor (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    {α : Pt W L →+ Pt W₁ L} {A : (W₁.baseChange (FF W L)).toAffine.Point} (hα : HasGenI α A)
    (hker : ∀ T ∈ G, α T = 0) :
    ∃ β : Pt W' L →+ Pt W₁ L, IsIsog β ∧ β.comp (qmap hG hW') = α := by
  have hA : ∀ T ∈ G, Point.map (W' := W₁.toAffine) ((tauHom W L T).restrictScalars F) A = A :=
    fun T hT => by rw [hα T, hker T hT, map_zero, add_zero]
  obtain ⟨A', hA'⟩ := exists_pull_of_inv hG hW' hA
  have hsurj := qmap_surjective hG hW'
  have hwd : ∀ P₁ P₂, qmap hG hW' P₁ = qmap hG hW' P₂ → α P₁ = α P₂ := by
    intro P₁ P₂ h
    have h1 : P₁ - P₂ ∈ G := (qmap_eq_zero_iff hG hW').mp (by rw [map_sub, h, sub_self])
    have h2 := hker _ h1
    rwa [map_sub, sub_eq_zero] at h2
  let β : Pt W' L →+ Pt W₁ L := AddMonoidHom.mk' (fun Q => α (Function.surjInv hsurj Q)) (by
    intro Q₁ Q₂
    rw [← map_add]
    apply hwd
    rw [map_add, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj])
  have hβ : ∀ P, β (qmap hG hW' P) = α P := fun P => hwd _ _ (Function.surjInv_eq hsurj _)
  refine ⟨β, ⟨A', fun Q => ?_⟩, AddMonoidHom.ext hβ⟩
  obtain ⟨P, rfl⟩ := hsurj Q
  have hcomp : ((pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F).comp
      ((tauHom W' L (qmap hG hW' P)).restrictScalars F) =
      ((tauHom W L P).restrictScalars F).comp ((pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F) :=
    AlgHom.ext fun f => (AlgHom.congr_fun (tau_comp_pull2 _ _ (hasGenI_qmap hG hW') P) f).symm
  apply Point.map_injective (W' := W₁.toAffine) (f := (pull2 (qPt hW') (qPt_ne_ιQ hW')).restrictScalars F)
  rw [Point.map_map, hcomp, ← Point.map_map, hA', hα P, map_add, hA', map_pull2_ιQ, hβ]

/-- **The dual of the quotient isogeny.** -/
theorem exists_dual (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    ∃ ψ : Pt W' L →+ Pt W L, IsIsog ψ ∧ ψ ≠ 0 ∧
      (∀ P, ψ (qmap hG hW' P) = Fintype.card G • P) ∧
      (∀ Q, qmap hG hW' (ψ Q) = Fintype.card G • Q) ∧
      (∀ Q, ψ (RPLib.EllFq.frob W' L Q) = RPLib.EllFq.frob W L (ψ Q)) := by
  obtain ⟨Φ, hΦ⟩ : IsEndo (((Fintype.card G : ℤ) : AddMonoid.End (Pt W L))) :=
    (mem_endRing).mp (intCast_mem _ _)
  have hα : HasGenI (W' := W) (((Fintype.card G : ℤ) : AddMonoid.End (Pt W L))) Φ := fun S => hΦ S
  have hn : ∀ P : Pt W L, ((Fintype.card G : ℤ) : AddMonoid.End (Pt W L)) P = Fintype.card G • P :=
    fun P => by show (Fintype.card G : ℤ) • P = _; exact natCast_zsmul P _
  have hker : ∀ T ∈ G, ((Fintype.card G : ℤ) : AddMonoid.End (Pt W L)) T = 0 := fun T hT => by
    rw [hn]
    have h : Fintype.card G • (⟨T, hT⟩ : G) = 0 := card_nsmul_eq_zero
    exact congrArg Subtype.val h
  obtain ⟨ψ, hψ, hcomp⟩ := exists_factor (W₁ := W) hG hW' hα hker
  have hψq : ∀ P, ψ (qmap hG hW' P) = Fintype.card G • P := fun P => by
    rw [← hn, ← hcomp]; rfl
  have hsurj := qmap_surjective hG hW'
  refine ⟨ψ, hψ, fun h0 => ?_, hψq, fun Q => ?_, fun Q => ?_⟩
  · have h1 : ((Fintype.card G : ℤ) : AddMonoid.End (Pt W L)) = 0 := by
      refine AddMonoidHom.ext fun P => ?_
      show ((Fintype.card G : ℤ) : AddMonoid.End (Pt W L)) P = 0
      rw [hn, ← hψq, h0, AddMonoidHom.zero_apply]
    have h2 := intCast_eq_zero (W := W) (L := L) h1
    have h3 : 0 < Fintype.card G := Fintype.card_pos
    omega
  · obtain ⟨P, rfl⟩ := hsurj Q
    rw [hψq, map_nsmul]
  · obtain ⟨P, rfl⟩ := hsurj Q
    rw [← qmap_frob hG hW' hFr, hψq, hψq, map_nsmul]

theorem isIsogenous_dual (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G))
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) : IsIsogenous W' W L := by
  obtain ⟨ψ, hψ, h0, -, -, hfr⟩ := exists_dual hG hW' hFr
  exact ⟨ψ, hψ, h0, hfr⟩

end Factor

section Headline

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- **Vélu quotient with its dual over `F_q`.** For a finite Frobenius-stable `G ⊆ E(L)` with `p ∤ #G` there is an
elliptic `W'/F_q` and isogenies `φ : E → E'`, `ψ : E' → E` over `F_q` with `ker φ = G`, `φ` surjective,
`ψ ∘ φ = [#G]`, `φ ∘ ψ = [#G]`; the curves are isogenous both ways and have the same trace. -/
theorem exists_quot_isog_dual (G : AddSubgroup (Pt W L)) [Fintype G] (hG : (Fintype.card G : L) ≠ 0)
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    ∃ W' : WeierstrassCurve F, ∃ _ : W'.IsElliptic, ∃ φ : Pt W L →+ Pt W' L, ∃ ψ : Pt W' L →+ Pt W L,
      IsIsog φ ∧ IsIsog ψ ∧ (∀ S, φ S = 0 ↔ S ∈ G) ∧ Function.Surjective φ ∧
      (∀ P, ψ (φ P) = Fintype.card G • P) ∧ (∀ Q, φ (ψ Q) = Fintype.card G • Q) ∧
      (∀ P, φ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (φ P)) ∧
      (∀ Q, ψ (RPLib.EllFq.frob W' L Q) = RPLib.EllFq.frob W L (ψ Q)) ∧
      IsIsogenous W W' L ∧ IsIsogenous W' W L ∧ RPLib.EllFq.trace W' = RPLib.EllFq.trace W := by
  obtain ⟨W', hE, hW'⟩ := exists_quotient hG hFr
  have := hE
  obtain ⟨ψ, hψ, -, h1, h2, h3⟩ := exists_dual hG hW' hFr
  exact ⟨W', hE, qmap hG hW', ψ, ⟨qPt hW', hasGenI_qmap hG hW'⟩, hψ,
    fun S => qmap_eq_zero_iff hG hW', qmap_surjective hG hW', h1, h2, qmap_frob hG hW' hFr, h3,
    isIsogenous_quot hG hW' hFr, isIsogenous_dual hG hW' hFr,
    (isIsogenous_quot hG hW' hFr).trace_eq.symm⟩

end Headline

end RPLib.DWS


