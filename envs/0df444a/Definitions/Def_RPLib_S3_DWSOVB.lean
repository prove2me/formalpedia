-- Prove2me | Definitions.Def_RPLib_S3_DWSOVB
-- name    : RPLib_S3_DWSOVB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:25:28.261433+00:00
-- url     : https://prove2.me/theorems/b800e0fd-8abe-4e6e-8639-a29e0fe16230
-- title:
--   Weight-two Ramanujan-Petersson library: a generic point of affine shape is a change of variables (O1, V2)
-- statement:
--   A generic point of affine shape is a change of variables (O1, V2).
--
--   `Φ ∈ W'(L(E))` with `x(Φ) = α x + β`, `y(Φ) = γ y + δ x + ε` (`α ≠ 0`):
--   * `gamma_sq` : `γ² = α³`;
--   * **`exists_vc_of_gen`** : there is `C` over `L` with `C • W⁄L = W'⁄L` and `ptMap C^ι (G) = Φ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOVA

/-!
# S3-DWS-Ordinary, part VB: a generic point of affine shape is a change of variables (O1, V2)

`Φ ∈ W'(L(E))` with `x(Φ) = α x + β`, `y(Φ) = γ y + δ x + ε` (`α ≠ 0`):
* `gamma_sq` : `γ² = α³`;
* **`exists_vc_of_gen`** : there is `C` over `L` with `C • W⁄L = W'⁄L` and `ptMap C^ι (G) = Φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Gen

variable {F : Type*} [Field F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

theorem gamma_sq {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : Φ ≠ 0) {α β γ δ ε : L}
    (hx : px Φ = algebraMap L (FF W L) α * gx W L + algebraMap L (FF W L) β)
    (hy : py Φ = algebraMap L (FF W L) γ * gy W L + algebraMap L (FF W L) δ * gx W L +
      algebraMap L (FF W L) ε) : γ ^ 2 = α ^ 3 := by
  have e' := (nonsingular_px_py hΦ).1
  rw [equation_iff, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L), bc_a₄ W' L (FF W L),
    bc_a₆ W' L (FF W L), hx, hy] at e'
  have e := gen_equation W L
  rw [equation_iff, bc_a₁ W L (FF W L), bc_a₂ W L (FF W L), bc_a₃ W L (FF W L), bc_a₄ W L (FF W L),
    bc_a₆ W L (FF W L)] at e
  set a₁ := (W.baseChange L).toAffine.a₁
  set a₂ := (W.baseChange L).toAffine.a₂
  set a₃ := (W.baseChange L).toAffine.a₃
  set a₄ := (W.baseChange L).toAffine.a₄
  set a₆ := (W.baseChange L).toAffine.a₆
  set b₁ := (W'.baseChange L).toAffine.a₁
  set b₂ := (W'.baseChange L).toAffine.a₂
  set b₃ := (W'.baseChange L).toAffine.a₃
  set b₄ := (W'.baseChange L).toAffine.a₄
  set b₆ := (W'.baseChange L).toAffine.a₆
  obtain ⟨-, -, -, h3, -, -⟩ := gen_indep (W := W) (L := L)
    (A₀ := ε ^ 2 + b₁ * β * ε + b₃ * ε - β ^ 3 - b₂ * β ^ 2 - b₄ * β - b₆ + γ ^ 2 * a₆)
    (A₁ := 2 * δ * ε + b₁ * (α * ε + β * δ) + b₃ * δ - 3 * α * β ^ 2 - 2 * b₂ * α * β - b₄ * α + γ ^ 2 * a₄)
    (A₂ := δ ^ 2 + b₁ * α * δ - 3 * α ^ 2 * β - b₂ * α ^ 2 + γ ^ 2 * a₂) (A₃ := γ ^ 2 - α ^ 3)
    (B₀ := 2 * γ * ε + b₁ * β * γ + b₃ * γ - γ ^ 2 * a₃) (B₁ := 2 * γ * δ + b₁ * α * γ - γ ^ 2 * a₁)
    (by simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
        linear_combination e' - (algebraMap L (FF W L) γ) ^ 2 * e)
  linear_combination h3

/-- **A generic point of affine shape comes from a change of variables over `L`.** -/
theorem exists_vc_of_gen {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : Φ ≠ 0) {α β γ δ ε : L}
    (hα : α ≠ 0) (hx : px Φ = algebraMap L (FF W L) α * gx W L + algebraMap L (FF W L) β)
    (hy : py Φ = algebraMap L (FF W L) γ * gy W L + algebraMap L (FF W L) δ * gx W L +
      algebraMap L (FF W L) ε) :
    ∃ (C : VariableChange L) (h : C • W.baseChange L = W'.baseChange L),
      RPLib.TateNF.ptMap (C.map (ιF W L : L →+* FF W L)) (vc_bc (ιF W L) h) (G W L) = Φ := by
  have hγ2 := gamma_sq hΦ hx hy
  have hγ : γ ≠ 0 := by
    rintro rfl
    exact hα (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp (by rw [← hγ2]; ring))
  have hU : γ / α ≠ 0 := div_ne_zero hγ hα
  have hU2 : (γ / α) ^ 2 = α := by field_simp; linear_combination hγ2
  have hU3 : (γ / α) ^ 3 = γ := by field_simp; linear_combination hγ2
  set ι := algebraMap L (FF W L) with hι
  have hια : ι α ≠ 0 := (map_ne_zero ι).mpr hα
  have hιγ : ι γ ≠ 0 := (map_ne_zero ι).mpr hγ
  set C : VariableChange L := ⟨(Units.mk0 (γ / α) hU)⁻¹, -β / α, -δ / γ, (-δ / γ) * (-β / α) - ε / γ⟩ with hC
  have hui : ui C = γ / α := by simp [ui, hC]
  have hιF : ∀ a : L, (ιF W L : L →+* FF W L) a = ι a := fun a => rfl
  have hX : vcX (C.map (ιF W L : L →+* FF W L)) (gx W L) = px Φ := by
    rw [hx, vcX, ui_map, hui, hιF, ← map_pow, hU2]
    simp only [VariableChange.map, hC, hιF, map_div₀, map_neg]
    field_simp
    ring
  have hY : vcY (C.map (ιF W L : L →+* FF W L)) (gx W L) (gy W L) = py Φ := by
    rw [hy, vcY, ui_map, hui, hιF, ← map_pow, hU3]
    simp only [VariableChange.map, hC, hιF, map_div₀, map_neg, map_sub, map_mul]
    field_simp
    ring
  have hFF : C.map (ιF W L : L →+* FF W L) • W.baseChange (FF W L) =
      (C • W.baseChange L).map (ιF W L : L →+* FF W L) := by
    rw [← WeierstrassCurve.map_baseChange W (ιF W L), map_variableChange]
  have eV := (equation_vc (W.baseChange (FF W L)) (C.map (ιF W L : L →+* FF W L)) (gx W L) (gy W L)).mpr
    (gen_equation W L)
  rw [hX, hY, hFF, equation_iff, hx, hy] at eV
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, hιF] at eV
  have eW := (nonsingular_px_py hΦ).1
  rw [equation_iff, bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L), bc_a₄ W' L (FF W L),
    bc_a₆ W' L (FF W L), hx, hy] at eW
  set V := C • W.baseChange L with hV
  set d₁ := V.a₁ - (W'.baseChange L).toAffine.a₁
  set d₂ := V.a₂ - (W'.baseChange L).toAffine.a₂
  set d₃ := V.a₃ - (W'.baseChange L).toAffine.a₃
  set d₄ := V.a₄ - (W'.baseChange L).toAffine.a₄
  set d₆ := V.a₆ - (W'.baseChange L).toAffine.a₆
  obtain ⟨h0, h1, h2, -, h4, h5⟩ := gen_indep (W := W) (L := L)
    (A₀ := d₁ * β * ε + d₃ * ε - d₂ * β ^ 2 - d₄ * β - d₆)
    (A₁ := d₁ * (α * ε + β * δ) + d₃ * δ - 2 * d₂ * α * β - d₄ * α) (A₂ := d₁ * α * δ - d₂ * α ^ 2)
    (A₃ := 0) (B₀ := d₁ * β * γ + d₃ * γ) (B₁ := d₁ * α * γ)
    (by simp only [d₁, d₂, d₃, d₄, d₆, map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero]
        linear_combination eV - eW)
  have k₁ : d₁ = 0 := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact (mul_eq_zero.mp h).resolve_right hα
    · exact absurd h hγ
  have k₃ : d₃ = 0 := by
    rw [k₁] at h4
    exact (mul_eq_zero.mp (by linear_combination h4)).resolve_right hγ
  have k₂ : d₂ = 0 := by
    rw [k₁] at h2
    exact (mul_eq_zero.mp (by linear_combination -h2 : d₂ * α ^ 2 = 0)).resolve_right (pow_ne_zero 2 hα)
  have k₄ : d₄ = 0 := by
    rw [k₁, k₂, k₃] at h1
    exact (mul_eq_zero.mp (by linear_combination -h1 : d₄ * α = 0)).resolve_right hα
  have k₆ : d₆ = 0 := by
    rw [k₁, k₂, k₃, k₄] at h0
    linear_combination -h0
  have hVW : V = W'.baseChange L := by
    ext
    · exact sub_eq_zero.mp k₁
    · exact sub_eq_zero.mp k₂
    · exact sub_eq_zero.mp k₃
    · exact sub_eq_zero.mp k₄
    · exact sub_eq_zero.mp k₆
  refine ⟨C, hVW, ?_⟩
  rw [G, RPLib.TateNF.ptMap_some]
  conv_rhs => rw [eq_some_px_py hΦ]
  exact some_eq_some hX hY

end Gen

end RamanujanPetersson.S3.DWSO


