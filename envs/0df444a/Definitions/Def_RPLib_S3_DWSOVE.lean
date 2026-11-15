-- Prove2me | Definitions.Def_RPLib_S3_DWSOVE
-- name    : RPLib_S3_DWSOVE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:34:20.058213+00:00
-- url     : https://prove2.me/theorems/43919f06-5c77-4293-a768-91328b549418
-- title:
--   Weight-two Ramanujan-Petersson library: Frobenius descent (O1, V5) and VC2-F
-- statement:
--   Frobenius descent (O1, V5) and VC2-F.
--
--   * `exists_pt_ne` : a point `P` of `E(L)` with `P, 2P, 3P ≠ 0` (a point of prime order `5` or `7`).
--   * `exists_vcF_of_ptHom` : a change of variables over `L` whose point map commutes with the `q`-Frobenius
--     is defined over `F_q`.
--   * **`exists_vcF`** (VC2-F) : isogenies `u, v` with `v ∘ u = id`, `u` commuting with Frobenius ⇒ `u` is the
--     point map of a change of variables `C` over `F_q` with `C • W = W'`.
--   * `IsoFq.exists_vc` : `F_q`-isomorphic curves are related by a change of variables over `F_q`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOVD
import Definitions.Def_RPLib_S3_DWSTateG

/-!
# S3-DWS-Ordinary, part VE: Frobenius descent (O1, V5) and **VC2-F**

* `exists_pt_ne` : a point `P` of `E(L)` with `P, 2P, 3P ≠ 0` (a point of prime order `5` or `7`).
* `exists_vcF_of_ptHom` : a change of variables over `L` whose point map commutes with the `q`-Frobenius
  is defined over `F_q`.
* **`exists_vcF`** (VC2-F) : isogenies `u, v` with `v ∘ u = id`, `u` commuting with Frobenius ⇒ `u` is the
  point map of a change of variables `C` over `F_q` with `C • W = W'`.
* `IsoFq.exists_vc` : `F_q`-isomorphic curves are related by a change of variables over `F_q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Descent

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- A point `P` with `P, 2P, 3P ≠ 0`. -/
lemma exists_pt_ne : ∃ P : Pt W L, P ≠ 0 ∧ 2 • P ≠ 0 ∧ 3 • P ≠ 0 := by
  have key : ∀ ℓ : ℕ, ℓ.Prime → 3 < ℓ → (ℓ : L) ≠ 0 →
      ∃ P : Pt W L, P ≠ 0 ∧ 2 • P ≠ 0 ∧ 3 • P ≠ 0 := by
    intro ℓ hℓ h3 hℓL
    have hcard := card_En (W := W) (L := L) ℓ hℓL
    have h1 : 1 < (En W L ℓ hℓL).card := by rw [hcard]; nlinarith
    obtain ⟨P, hP, hP0⟩ := Finset.exists_mem_ne h1 0
    rw [mem_En] at hP
    haveI := Fact.mk hℓ
    have hord : addOrderOf P = ℓ := addOrderOf_eq_prime hP hP0
    refine ⟨P, hP0, fun h2 => ?_, fun h3' => ?_⟩
    · have hd := addOrderOf_dvd_of_nsmul_eq_zero h2
      rw [hord] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    · have hd := addOrderOf_dvd_of_nsmul_eq_zero h3'
      rw [hord] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  by_cases h5 : (5 : L) = 0
  · refine key 7 (by norm_num) (by norm_num) ?_
    intro h7
    push_cast at h7
    exact one_ne_zero (by linear_combination (3 : L) * h5 - 2 * h7 : (1 : L) = 0)
  · exact key 5 (by norm_num) (by norm_num) (by exact_mod_cast h5)

lemma frob_surj (P : Pt W L) : ∃ P' : Pt W L, RPLib.EllFq.frob W L P' = P := by
  refine ⟨(RPLib.EllFq.mapPtEquiv W (frobAut (F := F) L)).symm P, ?_⟩
  rw [frob_eq_ptMap]
  exact (RPLib.EllFq.mapPtEquiv W (frobAut (F := F) L)).apply_symm_apply P

/-- **Frobenius descent**: a change of variables over `L` whose point map commutes with Frobenius
comes from `F_q`. -/
theorem exists_vcF_of_ptHom {C : VariableChange L} (h : C • W.baseChange L = W'.baseChange L)
    (hfr : ∀ P, RPLib.TateNF.ptHom C h (RPLib.EllFq.frob W L P) =
      RPLib.EllFq.frob W' L (RPLib.TateNF.ptHom C h P)) :
    ∃ C₀ : VariableChange F, C₀ • W = W' ∧ C₀.map (algebraMap F L) = C := by
  set σ : L →ₐ[F] L := FiniteField.frobeniusAlgHom F L with hσ
  have hsame : ∀ P : Pt W L,
      RPLib.TateNF.ptMap (C.map (σ : L →+* L)) (vc_bc σ h) P = RPLib.TateNF.ptMap C h P := by
    intro P
    obtain ⟨P', rfl⟩ := frob_surj (W := W) P
    have e := ptMap_map σ h P'
    have e2 := hfr P'
    exact e.symm.trans e2.symm
  obtain ⟨P, h1, h2, h3⟩ := exists_pt_ne (W := W) (L := L)
  have hiso1 : IsPtIso C P (RPLib.TateNF.ptMap C h P) := isPtIso_ptMap C h P
  have hiso2 : IsPtIso (C.map (σ : L →+* L)) P (RPLib.TateNF.ptMap C h P) := ⟨vc_bc σ h, hsame P⟩
  have hD : (C.map (σ : L →+* L))⁻¹ * C = 1 :=
    aut_trivial h1 h2 h3 (isPtIso_comp hiso1 (isPtIso_inv hiso2))
  have hCσ : C.map (σ : L →+* L) = C := inv_mul_eq_one.mp hD
  have hfix : ∀ x : L, σ x = x → ∃ y : F, algebraMap F L y = x := fun x hx => by
    have hx' : x ^ Fintype.card F = x := by
      rw [hσ, FiniteField.coe_frobeniusAlgHom] at hx
      exact hx
    exact (RPLib.EllFq.pow_card_eq_self_iff (L := F) x).mp hx'
  obtain ⟨u₀, hu₀⟩ := hfix (C.u : L) (congrArg (fun D : VariableChange L => (D.u : L)) hCσ)
  obtain ⟨r₀, hr₀⟩ := hfix C.r (congrArg VariableChange.r hCσ)
  obtain ⟨s₀, hs₀⟩ := hfix C.s (congrArg VariableChange.s hCσ)
  obtain ⟨t₀, ht₀⟩ := hfix C.t (congrArg VariableChange.t hCσ)
  have hu0 : u₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hu₀
    exact C.u.ne_zero hu₀.symm
  have hmap : (⟨Units.mk0 u₀ hu0, r₀, s₀, t₀⟩ : VariableChange F).map (algebraMap F L) = C := by
    ext
    · simp [VariableChange.map, hu₀]
    · simp [VariableChange.map, hr₀]
    · simp [VariableChange.map, hs₀]
    · simp [VariableChange.map, ht₀]
  refine ⟨⟨Units.mk0 u₀ hu0, r₀, s₀, t₀⟩, ?_, hmap⟩
  apply WeierstrassCurve.map_injective (algebraMap F L).injective
  show (_ • W).map (algebraMap F L) = W'.map (algebraMap F L)
  rw [← map_variableChange, hmap]
  exact h

lemma vc_bcF {C : VariableChange F} (h : C • W = W') :
    C.map (algebraMap F L) • W.baseChange L = W'.baseChange L := by
  subst h
  show _ = (C • W).map (algebraMap F L)
  exact WeierstrassCurve.map_variableChange ..

/-- **VC2-F**: an invertible isogeny commuting with Frobenius is a change of variables over `F_q`. -/
theorem exists_vcF {u : Pt W L →+ Pt W' L} {v : Pt W' L →+ Pt W L} (hu : IsIsog u) (hv : IsIsog v)
    (hvu : ∀ P, v (u P) = P)
    (hfr : ∀ P, u (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (u P)) :
    ∃ (C : VariableChange F) (h : C • W = W'),
      u = RPLib.TateNF.ptHom (C.map (algebraMap F L)) (vc_bcF h) := by
  obtain ⟨C, h, rfl⟩ := exists_vcL hu hv hvu
  obtain ⟨C₀, h₀, hmap⟩ := exists_vcF_of_ptHom h hfr
  refine ⟨C₀, h₀, ?_⟩
  subst hmap
  rfl

/-- `F_q`-isomorphic curves are related by a change of variables over `F_q`. -/
theorem IsoFq.exists_vc (hiso : IsoFq W W' L) : ∃ C : VariableChange F, C • W = W' := by
  obtain ⟨u, v, hu, hv, hvu, -, hfr⟩ := hiso
  obtain ⟨C, h, -⟩ := exists_vcF hu hv hvu hfr
  exact ⟨C, h⟩

end Descent

end RamanujanPetersson.S3.DWSO


