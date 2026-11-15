-- Prove2me | Definitions.Def_RPLib_S3_DWSOVD
-- name    : RPLib_S3_DWSOVD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:32:45.993203+00:00
-- url     : https://prove2.me/theorems/0cab8330-10ba-406b-a1c7-42e2013f67f5
-- title:
--   Weight-two Ramanujan-Petersson library: invertible isogenies are changes of variables over `L` (O1, V3b)
-- statement:
--   Invertible isogenies are changes of variables over `L` (O1, V3b).
--
--   * `shape_of_poleOnce` : a generic point with a single pole (`PoleOnce`) has `x = α x₀ + β`,
--     `y = γ y₀ + δ x₀ + ε` (`α ≠ 0`) — Riemann–Roch for `L(2O)`, `L(3O)` via `GoodQ ⊥`.
--   * `exists_tr_rep` : a representative `genPt ψ` can be normalised so that `ψ` fixes the origin.
--   * **`exists_vcL`** : if `u, v` are isogenies with `v ∘ u = id`, then `u` is the point map of a change of
--     variables `C` over `L` with `C • W⁄L = W'⁄L`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOVC

/-!
# S3-DWS-Ordinary, part VD: invertible isogenies are changes of variables over `L` (O1, V3b)

* `shape_of_poleOnce` : a generic point with a single pole (`PoleOnce`) has `x = α x₀ + β`,
  `y = γ y₀ + δ x₀ + ε` (`α ≠ 0`) — Riemann–Roch for `L(2O)`, `L(3O)` via `GoodQ ⊥`.
* `exists_tr_rep` : a representative `genPt ψ` can be normalised so that `ψ` fixes the origin.
* **`exists_vcL`** : if `u, v` are isogenies with `v ∘ u = id`, then `u` is the point map of a change of
  variables `C` over `L` with `C • W⁄L = W'⁄L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Shape

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma goodQ_bot {f : FF W L} (h : ∀ P : Pt W L, P ≠ 0 → Ge 0 f P) :
    GoodQ (⊥ : AddSubgroup (Pt W L)) f :=
  ⟨fun S hS => by
    rw [AddSubgroup.mem_bot] at hS
    subst hS
    rw [tau_zero_apply],
   fun P hP => h P (by rwa [AddSubgroup.mem_bot] at hP)⟩

lemma card_bot_ne : (Fintype.card (⊥ : AddSubgroup (Pt W L)) : L) ≠ 0 := by
  rw [Fintype.card_eq_nat_card, AddSubgroup.card_bot, Nat.cast_one]
  exact one_ne_zero

lemma eq_const_of_ge_neg_one {g : FF W L} (hg : GoodQ (⊥ : AddSubgroup (Pt W L)) g) {n : ℤ}
    (h1 : Ge n g 0) (hn : n = -1) : ∃ c : L, g = algebraMap L (FF W L) c := by
  subst hn
  by_cases hg0 : g = 0
  · exact ⟨0, by rw [hg0, map_zero]⟩
  apply hg.eq_const
  right
  have h2 := hg.ord_ne_neg_one card_bot_ne hg0
  have h3 := h1.resolve_left hg0
  omega

/-- **Riemann–Roch-lite**: a generic point with a single pole has affine shape. -/
theorem shape_of_poleOnce {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : PoleOnce Φ) :
    ∃ α β γ δ ε : L, α ≠ 0 ∧
      px Φ = algebraMap L (FF W L) α * gx W L + algebraMap L (FF W L) β ∧
      py Φ = algebraMap L (FF W L) γ * gy W L + algebraMap L (FF W L) δ * gx W L +
        algebraMap L (FF W L) ε := by
  have gX : GoodQ ⊥ (px Φ) := goodQ_bot hΦ.reg_x
  have gY : GoodQ ⊥ (py Φ) := goodQ_bot hΦ.reg_y
  have gx' : GoodQ (⊥ : AddSubgroup (Pt W L)) (gx W L) := goodQ_bot fun P hP => ge_gx hP
  have gy' : GoodQ (⊥ : AddSubgroup (Pt W L)) (gy W L) := goodQ_bot fun P hP => ge_gy hP
  obtain ⟨α, hα1, hα2⟩ := gX.lead gx' gx_ne_zero' ord_gx_zero (Or.inr hΦ.ord_x.ge)
  obtain ⟨β, hβ⟩ := eq_const_of_ge_neg_one hα1 hα2 (by norm_num)
  obtain ⟨γ, hγ1, hγ2⟩ := gY.lead gy' gy_ne_zero' ord_gy_zero hΦ.ge_y
  obtain ⟨δ, hδ1, hδ2⟩ := hγ1.lead gx' gx_ne_zero' (by rw [ord_gx_zero]; norm_num) hγ2
  obtain ⟨ε, hε⟩ := eq_const_of_ge_neg_one hδ1 hδ2 (by norm_num)
  refine ⟨α, β, γ, δ, ε, ?_, by linear_combination hβ, by linear_combination hε⟩
  rintro rfl
  rw [map_zero, zero_mul, sub_zero] at hβ
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hΦ.x_ne (by rw [hβ, map_zero])
  have e := hΦ.ord_x
  rw [hβ, ord_alg hβ0] at e
  norm_num at e

/-- Normalise a carried generic point so that the isomorphism fixes the origin. -/
theorem exists_tr_rep {u : Pt W L →+ Pt W' L} {ψ : FF W' L ≃ₐ[L] FF W L} (hu : HasGenI u (genPt ψ)) :
    ∃ ψ₀ : FF W' L ≃ₐ[L] FF W L, Tr ψ₀ 0 0 ∧ HasGenI u (genPt ψ₀) := by
  obtain ⟨P₀, hP₀⟩ := exists_tr ψ.symm 0
  have h1 : Tr ψ P₀ 0 := by
    have h2 := hP₀.symm
    rw [AlgEquiv.symm_symm] at h2
    exact h2
  refine ⟨ψ.trans (tau W L P₀), fun f hf => ?_, ?_⟩
  · show ord W L (tau W L P₀ (ψ f)) 0 = _
    rw [ord_tau, zero_add]
    exact h1 f hf
  · have e : genPt (ψ.trans (tau W L P₀)) = genPt ψ + ιQ W W' L (u P₀) := by
      rw [← hu P₀, genPt, genPt, Point.map_map]
      congr 1
    rw [e]
    intro S
    rw [map_add, hu S, map_ιQ_of_algHom]
    abel

end Shape

section VCL

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- **An invertible isogeny is the point map of a change of variables over `L`.** -/
theorem exists_vcL {u : Pt W L →+ Pt W' L} {v : Pt W' L →+ Pt W L} (hu : IsIsog u) (hv : IsIsog v)
    (hvu : ∀ P, v (u P) = P) :
    ∃ (C : VariableChange L) (h : C • W.baseChange L = W'.baseChange L),
      u = RPLib.TateNF.ptHom C h := by
  obtain ⟨Φ, hΦ⟩ := hu
  obtain ⟨Ψ, hΨ⟩ := hv
  obtain ⟨ψ, hψ⟩ := exists_algEquiv hΦ hΨ hvu
  rw [← hψ] at hΦ
  obtain ⟨ψ₀, h0, hu₀⟩ := exists_tr_rep hΦ
  have hP := poleOnce_of_tr h0
  obtain ⟨α, β, γ, δ, ε, hα, hx, hy⟩ := shape_of_poleOnce hP
  obtain ⟨C, h, hC⟩ := exists_vc_of_gen hP.ne hα hx hy
  refine ⟨C, h, eq_ptHom_of_hasGenI h ?_⟩
  rw [hC]
  exact hu₀

end VCL

end RamanujanPetersson.S3.DWSO


