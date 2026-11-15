-- Prove2me | Definitions.Def_RPLib_S3_DWSTateO
-- name    : RPLib_S3_DWSTateO
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:49:02.788531+00:00
-- url     : https://prove2.me/theorems/19132a6e-0ad0-4298-92df-2d1e86e8c1d9
-- title:
--   Weight-two Ramanujan-Petersson library: the `[N]`-pullback field
-- statement:
--   The `[N]`-pullback field.
--
--   * `const_of_tau_inv` : a function fixed by every translation is constant; `const_of_tau_inv_pt` for points.
--   * For `ψ : L(E) →ₐ[L] L(E)` with `ψ(G) = N • G` (e.g. `fL f ∘ fL g`, file N):
--     `tau_comp_of_mulN` (`τ_S ∘ ψ = ψ ∘ τ_{N S}`), `inv_of_mulN`, `exists_eq_comp_tau` (any `IsPull` for `[N]` is
--     `ψ ∘ τ_T`), and **`mem_range_iff_inv`** : `k ∈ range ψ ↔ k` is `E[N]`-invariant (`p ∤ N`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateN

/-!
# S3-DWS-Tate, file O (BR2a, part 1): the `[N]`-pullback field

* `const_of_tau_inv` : a function fixed by every translation is constant; `const_of_tau_inv_pt` for points.
* For `ψ : L(E) →ₐ[L] L(E)` with `ψ(G) = N • G` (e.g. `fL f ∘ fL g`, file N):
  `tau_comp_of_mulN` (`τ_S ∘ ψ = ψ ∘ τ_{N S}`), `inv_of_mulN`, `exists_eq_comp_tau` (any `IsPull` for `[N]` is
  `ψ ∘ τ_T`), and **`mem_range_iff_inv`** : `k ∈ range ψ ↔ k` is `E[N]`-invariant (`p ∤ N`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Const

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- A function fixed by every translation is constant. -/
lemma const_of_tau_inv {k : FF W L} (hk : ∀ S, tau W L S k = k) :
    ∃ c : L, k = algebraMap L (FF W L) c := by
  by_contra hc
  push_neg at hc
  have hk0 : k ≠ 0 := fun h => hc 0 (by rw [h, map_zero])
  obtain ⟨P, hP⟩ := exists_pole hk0 hc
  have hall : ∀ Q, ord W L k Q < 0 := fun Q => by
    have h1 := ord_tau (P - Q) k Q
    have e : Q + (P - Q) = P := by abel
    rw [hk, e] at h1
    rw [h1]
    exact hP
  have hk' : k⁻¹ ≠ 0 := inv_ne_zero hk0
  have hc' : ∀ c : L, k⁻¹ ≠ algebraMap L (FF W L) c := by
    intro c hkc
    apply hc c⁻¹
    rw [map_inv₀, ← hkc, inv_inv]
  obtain ⟨Q, hQ⟩ := exists_pole hk' hc'
  rw [ord_inv] at hQ
  have := hall Q
  omega

/-- A point of `W(L(E))` fixed by every translation is constant. -/
lemma const_of_tau_inv_pt {D : (W.baseChange (FF W L)).toAffine.Point}
    (hD : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) D = D) :
    ∃ T : Pt W L, D = ιP W L T := by
  by_cases h0 : D = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hx : ∀ S, tau W L S (px D) = px D := fun S => by
    have h1 := congrArg px (hD S)
    rw [px_map] at h1
    exact h1
  have hy : ∀ S, tau W L S (py D) = py D := fun S => by
    have h1 := congrArg py (hD S)
    rw [py_map] at h1
    exact h1
  obtain ⟨a, ha⟩ := const_of_tau_inv hx
  obtain ⟨b, hb⟩ := const_of_tau_inv hy
  have hns := nonsingular_px_py h0
  rw [ha, hb] at hns
  have hns' : (W.baseChange L).toAffine.Nonsingular a b :=
    (baseChange_nonsingular (W := W.toAffine) (f := ιF W L) (ιF W L).toRingHom.injective a b).mp hns
  refine ⟨Point.some a b hns', ?_⟩
  rw [ιP, Point.map_some, eq_some_px_py h0]
  exact some_eq_some ha hb

end Const

section MulN

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]
  {N : ℕ} {ψ : FF W L →ₐ[L] FF W L}

attribute [local instance] finite_coordinateRing decEqFF

lemma tau_nsmul_G (S : Pt W L) :
    Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) (N • G W L) =
      N • G W L + ιP W L (N • S) := by
  simp only [map_nsmul, map_tau_G, pS, nsmul_add]

lemma map_pS_of_mulN (hψ : Point.map (W' := W.toAffine) (ψ.restrictScalars F) (G W L) = N • G W L)
    (S : Pt W L) :
    Point.map (W' := W.toAffine) (ψ.restrictScalars F) (pS W L S) = N • G W L + ιP W L S := by
  rw [pS, map_add, hψ, map_ιP_of_algHom]

/-- `τ_S ∘ ψ = ψ ∘ τ_{N S}` for a pullback `ψ` along `[N]`. -/
lemma tau_comp_of_mulN (hψ : Point.map (W' := W.toAffine) (ψ.restrictScalars F) (G W L) = N • G W L)
    (S : Pt W L) : (tauHom W L S).comp ψ = ψ.comp (tauHom W L (N • S)) := by
  apply algHom_ext_gen W L
  · have h1 : (tauHom W L S) (px (N • G W L)) = px (N • G W L + ιP W L (N • S)) := by
      have h := px_map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) (N • G W L)
      rw [tau_nsmul_G] at h
      exact h.symm
    have h2 : ψ (px (pS W L (N • S))) = px (N • G W L + ιP W L (N • S)) := by
      have h := px_map (W' := W.toAffine) (ψ.restrictScalars F) (pS W L (N • S))
      rw [map_pS_of_mulN hψ] at h
      exact h.symm
    have h3 : ψ (gx W L) = px (N • G W L) := by
      have h := px_map (W' := W.toAffine) (ψ.restrictScalars F) (G W L)
      rw [hψ] at h
      exact h.symm
    rw [AlgHom.comp_apply, AlgHom.comp_apply, tauHom_gx, h3, h1, h2]
  · have h1 : (tauHom W L S) (py (N • G W L)) = py (N • G W L + ιP W L (N • S)) := by
      have h := py_map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) (N • G W L)
      rw [tau_nsmul_G] at h
      exact h.symm
    have h2 : ψ (py (pS W L (N • S))) = py (N • G W L + ιP W L (N • S)) := by
      have h := py_map (W' := W.toAffine) (ψ.restrictScalars F) (pS W L (N • S))
      rw [map_pS_of_mulN hψ] at h
      exact h.symm
    have h3 : ψ (gy W L) = py (N • G W L) := by
      have h := py_map (W' := W.toAffine) (ψ.restrictScalars F) (G W L)
      rw [hψ] at h
      exact h.symm
    rw [AlgHom.comp_apply, AlgHom.comp_apply, tauHom_gy, h3, h1, h2]

lemma inv_of_mulN (hψ : Point.map (W' := W.toAffine) (ψ.restrictScalars F) (G W L) = N • G W L)
    {S : Pt W L} (hS : S ∈ torsN W L N) (k : FF W L) : tau W L S (ψ k) = ψ k := by
  have h := AlgHom.congr_fun (tau_comp_of_mulN hψ S) k
  rw [AlgHom.comp_apply, AlgHom.comp_apply, mem_torsN.mp hS, tauHom_zero, AlgHom.id_apply] at h
  exact h

/-- Any `IsPull` for `[N]` is `ψ ∘ τ_T` for some `T`. -/
lemma exists_eq_comp_tau (hψ : Point.map (W' := W.toAffine) (ψ.restrictScalars F) (G W L) = N • G W L)
    {ψ0 : FF W L →ₐ[L] FF W L} {e : ℕ} (hP : IsPull ψ0 e (rsHom W L (N : ℤ) 0)) :
    ∃ T : Pt W L, ψ0 = ψ.comp (tauHom W L T) := by
  set A := Point.map (W' := W.toAffine) (ψ0.restrictScalars F) (G W L) with hAdef
  have hA : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) A =
      A + ιP W L (N • S) := by
    intro S
    have e1 : ((tauHom W L S).restrictScalars F).comp (ψ0.restrictScalars F) =
        (ψ0.restrictScalars F).comp ((tauHom W L (N • S)).restrictScalars F) := by
      apply AlgHom.ext
      intro k
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
      have h := hP.htau S k
      rw [rsN_apply] at h
      exact h
    rw [hAdef, Point.map_map, e1, ← Point.map_map, map_tau_G, pS, map_add, map_ιP_of_algHom]
  have hD : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) (A - N • G W L) =
      A - N • G W L := by
    intro S
    rw [map_sub, hA, tau_nsmul_G]
    abel
  obtain ⟨T, hT⟩ := const_of_tau_inv_pt hD
  have hA' : A = N • G W L + ιP W L T := by rw [← hT]; abel
  refine ⟨T, ?_⟩
  apply algHom_ext_gen W L
  · have h1 := px_map (W' := W.toAffine) (ψ0.restrictScalars F) (G W L)
    have h2 := px_map (W' := W.toAffine) (ψ.restrictScalars F) (pS W L T)
    rw [← hAdef, hA'] at h1
    rw [map_pS_of_mulN hψ] at h2
    rw [AlgHom.comp_apply, tauHom_gx]
    exact h1.symm.trans h2
  · have h1 := py_map (W' := W.toAffine) (ψ0.restrictScalars F) (G W L)
    have h2 := py_map (W' := W.toAffine) (ψ.restrictScalars F) (pS W L T)
    rw [← hAdef, hA'] at h1
    rw [map_pS_of_mulN hψ] at h2
    rw [AlgHom.comp_apply, tauHom_gy]
    exact h1.symm.trans h2

/-- **The `[N]`-pullback field is the field of `E[N]`-invariants** (`p ∤ N`). -/
theorem mem_range_iff_inv (hNF : (N : F) ≠ 0)
    (hψ : Point.map (W' := W.toAffine) (ψ.restrictScalars F) (G W L) = N • G W L) (k : FF W L) :
    k ∈ ψ.range ↔ InvG (torsN W L N) k := by
  constructor
  · intro hk S hS
    obtain ⟨k', rfl⟩ := (AlgHom.mem_range _).mp hk
    exact inv_of_mulN hψ hS k'
  · intro hk
    obtain ⟨ψ0, hP⟩ := exists_isPull_rs_sep (W := W) (L := L) (N : ℤ) 0 (natCast_ne_zero_L hNF)
    obtain ⟨k', rfl⟩ := (AlgHom.mem_range _).mp (invN_mem_range hNF hP hk)
    obtain ⟨T, hT⟩ := exists_eq_comp_tau hψ hP
    rw [hT, AlgHom.comp_apply]
    exact AlgHom.mem_range_self _ _

end MulN

end RPLib.DWS


