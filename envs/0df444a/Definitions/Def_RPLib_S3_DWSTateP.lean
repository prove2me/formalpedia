-- Prove2me | Definitions.Def_RPLib_S3_DWSTateP
-- name    : RPLib_S3_DWSTateP
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:53:37.832272+00:00
-- url     : https://prove2.me/theorems/017b83ac-1902-4418-b7d3-b6e8ff10f168
-- title:
--   Weight-two Ramanujan-Petersson library: Galois correspondence for the translations by `E[N]`
-- statement:
--   Galois correspondence for the translations by `E[N]`.
--
--   `TN W L N = Multiplicative E[N]` acts on `L(E)` by translations (`tauAct`, faithful). Its fixed field is the
--   `[N]`-pullback field (file O), so for any subfield `K1` containing `ψ(L(E))` (`ψ(G) = N • G`):
--   **`mem_iff_of_mulN`** : `k ∈ K1 ↔ k` is fixed by every `S ∈ E[N]` whose translation fixes `K1`.
--   `mem_fieldRange_fL_iff` : the case `K1 = fL f (L(E'))` for the Tate data `(f, g, N)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateO

/-!
# S3-DWS-Tate, file P (BR2a, part 2): Galois correspondence for the translations by `E[N]`

`TN W L N = Multiplicative E[N]` acts on `L(E)` by translations (`tauAct`, faithful). Its fixed field is the
`[N]`-pullback field (file O), so for any subfield `K1` containing `ψ(L(E))` (`ψ(G) = N • G`):
**`mem_iff_of_mulN`** : `k ∈ K1 ↔ k` is fixed by every `S ∈ E[N]` whose translation fixes `K1`.
`mem_fieldRange_fL_iff` : the case `K1 = fL f (L(E'))` for the Tate data `(f, g, N)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Galois

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L] {N : ℕ}

attribute [local instance] finite_coordinateRing decEqFF

variable (W L N) in
/-- `E[N]`, written multiplicatively. -/
abbrev TN := Multiplicative (torsN W L N)

variable (W L N) in
/-- `E[N] → Aut_L(L(E))`, `S ↦ τ_S`. -/
noncomputable def tauMul : TN W L N →* (FF W L ≃ₐ[L] FF W L) where
  toFun t := tau W L ((Multiplicative.toAdd t : torsN W L N) : Pt W L)
  map_one' := by
    apply AlgEquiv.ext
    intro k
    exact tau_zero_apply W L k
  map_mul' s t := by
    apply AlgEquiv.ext
    intro k
    rw [AlgEquiv.mul_apply]
    exact tau_add_apply W L ((Multiplicative.toAdd s : torsN W L N) : Pt W L)
      ((Multiplicative.toAdd t : torsN W L N) : Pt W L) k

variable (W L N) in
/-- The translation action of `E[N]` on `L(E)`. -/
noncomputable def tauAct : MulSemiringAction (TN W L N) (FF W L) :=
  MulSemiringAction.compHom (FF W L) (tauMul W L N)

attribute [local instance] tauAct

lemma smul_eq_tau (t : TN W L N) (k : FF W L) :
    t • k = tau W L ((Multiplicative.toAdd t : torsN W L N) : Pt W L) k := rfl

/-- **Galois correspondence**: a subfield `K1 ⊇ ψ(L(E))` (`ψ` a pullback along `[N]`, `p ∤ N`) is the fixed
field of the translations by points of `E[N]` that fix it. -/
theorem mem_iff_of_mulN (hNF : (N : F) ≠ 0) {ψ : FF W L →ₐ[L] FF W L}
    (hψ : Point.map (W' := W.toAffine) (ψ.restrictScalars F) (G W L) = N • G W L)
    (K1 : Subfield (FF W L)) (hK1 : ∀ k, ψ k ∈ K1) (k : FF W L) :
    k ∈ K1 ↔ ∀ S ∈ torsN W L N, (∀ e ∈ K1, tau W L S e = e) → tau W L S k = k := by
  constructor
  · intro hk S _ hS
    exact hS k hk
  · intro hk
    have : Finite (torsN W L N) := finite_torsN hNF
    have h0 : ∀ x : FixedPoints.subfield (TN W L N) (FF W L),
        algebraMap (FixedPoints.subfield (TN W L N) (FF W L)) (FF W L) x ∈ K1 := by
      intro x
      have hx2 : ∀ t : TN W L N, t • (x : FF W L) = x := x.2
      have hx : InvG (torsN W L N) (x : FF W L) := fun S hS => hx2 (Multiplicative.ofAdd ⟨S, hS⟩)
      obtain ⟨k', hk'⟩ := (AlgHom.mem_range _).mp ((mem_range_iff_inv hNF hψ _).mpr hx)
      show (x : FF W L) ∈ K1
      rw [← hk']
      exact hK1 k'
    let E1 : IntermediateField (FixedPoints.subfield (TN W L N) (FF W L)) (FF W L) :=
      K1.toIntermediateField h0
    have hE : k ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup E1) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      obtain ⟨t, rfl⟩ := FixedPoints.toAlgAut_surjective (TN W L N) (FF W L) σ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      exact hk _ (Multiplicative.toAdd t).2 (fun e he => hσ e he)
    rw [IsGalois.fixedField_fixingSubgroup] at hE
    exact hE

/-- The Tate data case: `K1 = fL f (L(E'))` where `(f ∘ g)(P0) = N • P0`. -/
theorem mem_fieldRange_fL_iff [Algebra.IsAlgebraic F L] {W' : WeierstrassCurve F} [W'.IsElliptic]
    (hNF : (N : F) ≠ 0) (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField)
    (hfg : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W) (k : FF W L) :
    k ∈ (fL L f).fieldRange ↔
      ∀ S ∈ torsN W L N, (∀ e ∈ (fL L f).fieldRange, tau W L S e = e) → tau W L S k = k := by
  have e1 : ((fL L f).comp (fL L g)).restrictScalars F =
      ((fL L f).restrictScalars F).comp ((fL L g).restrictScalars F) := rfl
  have e2 : Point.map (W' := W.toAffine) ((fL L g).restrictScalars F) (G W L) = PhiF L g :=
    map_pull2_G _ _
  have hψ : Point.map (W' := W.toAffine) (((fL L f).comp (fL L g)).restrictScalars F) (G W L) =
      N • G W L := by
    rw [e1, ← Point.map_map, e2, map_fL_PhiF f g N hfg]
  exact mem_iff_of_mulN hNF hψ ((fL L f).fieldRange.toSubfield)
    (fun k => AlgHom.mem_fieldRange.mpr ⟨fL L g k, rfl⟩) k

end Galois

end RPLib.DWS


