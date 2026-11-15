-- Prove2me | Definitions.Def_RPLib_S3_DWSTateW
-- name    : RPLib_S3_DWSTateW
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:21:39.033435+00:00
-- url     : https://prove2.me/theorems/03be83ad-c5e5-4dce-8915-e5529a7324ea
-- title:
--   Weight-two Ramanujan-Petersson library: an isomorphism of function fields induces an isomorphism of groups
-- statement:
--   An isomorphism of function fields induces an isomorphism of groups.
--
--   `ψ : L(E') ≃ₐ[L] L(E)`.
--
--   * `Conj ψ θ` : `τ_S ∘ ψ = ψ ∘ τ'_{θ S}` for every `S`; `conj_of_hasGenI`, `hasGenI_of_conj` (`HasGenI θ (genPt ψ)`).
--   * `eq_of_tau_eq` : translations are separated.
--   * **`exists_conj`** : every `ψ` has such a `θ` (translate so that `Tr ψ₀ 0 0`, then `exists_hasGenI_of_tr`).
--   * `conj_inv`, `conj_inv'` : `θ'` (for `ψ.symm`) is a two-sided inverse of `θ`.
--   * **`conj_frob`** : if `ψ` commutes with the Galois action of `γ`, so does `θ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateV

/-!
# S3-DWS-Tate, part W: an isomorphism of function fields induces an isomorphism of groups

`ψ : L(E') ≃ₐ[L] L(E)`.

* `Conj ψ θ` : `τ_S ∘ ψ = ψ ∘ τ'_{θ S}` for every `S`; `conj_of_hasGenI`, `hasGenI_of_conj` (`HasGenI θ (genPt ψ)`).
* `eq_of_tau_eq` : translations are separated.
* **`exists_conj`** : every `ψ` has such a `θ` (translate so that `Tr ψ₀ 0 0`, then `exists_hasGenI_of_tr`).
* `conj_inv`, `conj_inv'` : `θ'` (for `ψ.symm`) is a two-sided inverse of `θ`.
* **`conj_frob`** : if `ψ` commutes with the Galois action of `γ`, so does `θ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Conj

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- `ψ` intertwines the translations `τ_S` of `E` with the translations `τ'_{θ S}` of `E'`. -/
def Conj (ψ : FF W' L ≃ₐ[L] FF W L) (θ : Pt W L →+ Pt W' L) : Prop :=
  ∀ S k, tau W L S (ψ k) = ψ (tau W' L (θ S) k)

/-- Translations are separated. -/
lemma eq_of_tau_eq {S S' : Pt W L} (h : ∀ m : FF W L, tau W L S m = tau W L S' m) : S = S' := by
  apply eq_of_ord_eq
  intro f _
  have h1 := ord_tau S f 0
  rw [h, ord_tau, zero_add, zero_add] at h1
  exact h1.symm

lemma conj_of_hasGenI {ψ : FF W' L ≃ₐ[L] FF W L} {θ : Pt W L →+ Pt W' L} (h : HasGenI θ (genPt ψ)) :
    Conj ψ θ := by
  have key : ∀ S, (tauHom W L S).comp ψ.toAlgHom = ψ.toAlgHom.comp (tauHom W' L (θ S)) := by
    intro S
    have e : Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (genPt ψ) =
        Point.map (W' := W'.toAffine) (ψ.toAlgHom.restrictScalars F) (pS W' L (θ S)) := by
      rw [h S, map_pS2]; rfl
    apply algHom_ext_gen W' L
    · have hx := congrArg px e
      rw [px_map, px_map, px_genPt, ← tau_gx, tau_apply] at hx
      exact hx
    · have hy := congrArg py e
      rw [py_map, py_map, py_genPt, ← tau_gy, tau_apply] at hy
      exact hy
  intro S k
  have e := AlgHom.congr_fun (key S) k
  rw [tau_apply, tau_apply]
  exact e

lemma hasGenI_of_conj {ψ : FF W' L ≃ₐ[L] FF W L} {θ : Pt W L →+ Pt W' L} (h : Conj ψ θ) :
    HasGenI θ (genPt ψ) := by
  intro S
  have hc : ((tauHom W L S).restrictScalars F).comp (ψ.toAlgHom.restrictScalars F) =
      (ψ.toAlgHom.restrictScalars F).comp ((tauHom W' L (θ S)).restrictScalars F) := by
    apply AlgHom.ext
    intro k
    have e := h S k
    rw [tau_apply, tau_apply] at e
    exact e
  have e : Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) (genPt ψ) =
      Point.map (W' := W'.toAffine) (ψ.toAlgHom.restrictScalars F) (pS W' L (θ S)) := by
    rw [genPt, Point.map_map, hc, ← Point.map_map, map_tau_G]
  rw [e, map_pS2, genPt]

/-- **Every isomorphism of function fields intertwines translations along some `θ`.** -/
theorem exists_conj (ψ : FF W' L ≃ₐ[L] FF W L) : ∃ θ : Pt W L →+ Pt W' L, Conj ψ θ := by
  obtain ⟨P₀, hP₀⟩ := exists_tr ψ.symm 0
  have h1 : Tr ψ P₀ 0 := by
    have h2 := hP₀.symm
    rw [AlgEquiv.symm_symm] at h2
    exact h2
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : FF W' L ≃ₐ[L] FF W L, ψ₀ = ψ.trans (tau W L P₀) := ⟨_, rfl⟩
  have hψ₀a : ∀ k, ψ₀ k = tau W L P₀ (ψ k) := fun k => by rw [hψ₀]; rfl
  have h0 : Tr ψ₀ 0 0 := fun f hf => by rw [hψ₀a, ord_tau, zero_add]; exact h1 f hf
  obtain ⟨θ, hθ⟩ := exists_hasGenI_of_tr h0
  have hc := conj_of_hasGenI hθ
  refine ⟨θ, fun S k => ?_⟩
  have e := hc S k
  rw [hψ₀a, hψ₀a, ← tau_add_apply, add_comm, tau_add_apply] at e
  exact (tau W L P₀).injective e

lemma conj_inv {ψ : FF W' L ≃ₐ[L] FF W L} {θ : Pt W L →+ Pt W' L} {θ' : Pt W' L →+ Pt W L}
    (h : Conj ψ θ) (h' : Conj ψ.symm θ') (S : Pt W L) : θ' (θ S) = S := by
  apply eq_of_tau_eq
  intro m
  have e1 := h S (ψ.symm m)
  rw [AlgEquiv.apply_symm_apply, h' (θ S) m, AlgEquiv.apply_symm_apply] at e1
  exact e1.symm

lemma conj_inv' {ψ : FF W' L ≃ₐ[L] FF W L} {θ : Pt W L →+ Pt W' L} {θ' : Pt W' L →+ Pt W L}
    (h : Conj ψ θ) (h' : Conj ψ.symm θ') (T : Pt W' L) : θ (θ' T) = T :=
  conj_inv h' (by rw [AlgEquiv.symm_symm]; exact h) T

/-- **Galois equivariance.** -/
lemma conj_frob {ψ : FF W' L ≃ₐ[L] FF W L} {θ : Pt W L →+ Pt W' L} (h : Conj ψ θ) (γ : L ≃ₐ[F] L)
    (hγ : ∀ k, ψ (sig W' γ k) = sig W γ (ψ k)) (S : Pt W L) : θ (ptMap γ S) = ptMap γ (θ S) := by
  apply eq_of_tau_eq
  intro k
  apply ψ.injective
  rw [← h]
  obtain ⟨k₀, rfl⟩ : ∃ k₀, k = sig W' γ k₀ := ⟨(sig W' γ).symm k, by rw [AlgEquiv.apply_symm_apply]⟩
  rw [hγ, ← sig_tau γ S (ψ k₀), h S k₀, ← hγ, sig_tau γ (θ S) k₀]

lemma conj_frob' {ψ : FF W' L ≃ₐ[L] FF W L} {θ : Pt W L →+ Pt W' L} (h : Conj ψ θ)
    (hγ : ∀ k, ψ (sig W' (frobAut (F := F) L) k) = sig W (frobAut (F := F) L) (ψ k)) (S : Pt W L) :
    θ (RPLib.EllFq.frob W L S) = RPLib.EllFq.frob W' L (θ S) := by
  rw [frob_eq_ptMap, frob_eq_ptMap]
  exact conj_frob h _ hγ S

end Conj

end RPLib.DWS


