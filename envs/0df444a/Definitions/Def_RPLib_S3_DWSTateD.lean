-- Prove2me | Definitions.Def_RPLib_S3_DWSTateD
-- name    : RPLib_S3_DWSTateD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:24:21.436604+00:00
-- url     : https://prove2.me/theorems/421ca8b5-20b1-4a46-8378-4c71bd81001a
-- title:
--   Weight-two Ramanujan-Petersson library: factorisation through `[N]`, divisibility in `End_{F_q}`, inverse isogenies
-- statement:
--   Factorisation through `[N]`, divisibility in `End_{F_q}`, inverse isogenies.
--
--   For `p ∤ N` the multiplication map `[N]` is separable (`exists_isPull_rs_sep`), so part C applies with `G = E[N]`,
--   `X = [N]^* x`, `Y = [N]^* y`, `R = [N]^* L(E)`.
--   * `torsN`, `mem_torsN`, `invN_mem_range` : every `E[N]`-invariant function is a pullback along `[N]`.
--   * `exists_factorN` : an isogeny killing `E[N]` factors as `χ ∘ [N]` with `χ` an isogeny (Frobenius-equivariant if
--     the original map is).
--   * `endFq_div` (DIV) : `α ∈ End_{F_q}(E)` killing `E[N]` is `N · χ` with `χ ∈ End_{F_q}(E)`.
--   * `exists_inv_isog` (ISO) : an injective `u : E' → E` with `u ∘ w = [N]` for an isogeny `w` has an inverse isogeny.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateC

/-!
# S3-DWS-Tate, part D: factorisation through `[N]`, divisibility in `End_{F_q}`, inverse isogenies

For `p ∤ N` the multiplication map `[N]` is separable (`exists_isPull_rs_sep`), so part C applies with `G = E[N]`,
`X = [N]^* x`, `Y = [N]^* y`, `R = [N]^* L(E)`.
* `torsN`, `mem_torsN`, `invN_mem_range` : every `E[N]`-invariant function is a pullback along `[N]`.
* `exists_factorN` : an isogeny killing `E[N]` factors as `χ ∘ [N]` with `χ` an isogeny (Frobenius-equivariant if
  the original map is).
* `endFq_div` (DIV) : `α ∈ End_{F_q}(E)` killing `E[N]` is `N · χ` with `χ ∈ End_{F_q}(E)`.
* `exists_inv_isog` (ISO) : an injective `u : E' → E` with `u ∘ w = [N]` for an isogeny `w` has an inverse isogeny.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section MulN

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable (W L) in
/-- `E[N]` as an additive subgroup of `E(L)`. -/
abbrev torsN (N : ℕ) : AddSubgroup (Pt W L) := kerSet {(N : AddMonoid.End (Pt W L))}

variable {N : ℕ}

lemma mem_torsN {P : Pt W L} : P ∈ torsN W L N ↔ N • P = 0 := by
  rw [mem_kerSet]
  constructor
  · intro h; exact h _ rfl
  · rintro h α rfl; exact h

lemma rsN_apply (P : Pt W L) : rsHom W L (N : ℤ) 0 P = N • P := by
  rw [rsHom_apply, zero_smul, add_zero, natCast_zsmul]

lemma natCast_ne_zero_L (hNF : (N : F) ≠ 0) : (((N : ℤ) : L)) ≠ 0 := by
  rw [Int.cast_natCast, ← map_natCast (algebraMap F L)]
  exact (_root_.map_ne_zero (algebraMap F L)).mpr hNF

lemma finite_torsN (hNF : (N : F) ≠ 0) : Finite (torsN W L N) :=
  finite_kerSet (Set.mem_singleton _) hNF

variable {ψ : FF W L →ₐ[L] FF W L}

/-- **Every `E[N]`-invariant function is a pullback along `[N]`** (`p ∤ N`). -/
theorem invN_mem_range (hNF : (N : F) ≠ 0) (hP : IsPull ψ 1 (rsHom W L (N : ℤ) 0)) {f : FF W L}
    (hf : InvG (torsN W L N) f) : f ∈ ψ.range := by
  haveI := finite_torsN (W := W) (L := L) hNF
  letI := Fintype.ofFinite (torsN W L N)
  have hG : (Fintype.card (torsN W L N) : L) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_kerSet_ne_zero (Set.mem_singleton _) hNF
  have hinv : ∀ S ∈ torsN W L N, ∀ g : FF W L, tau W L S (ψ g) = ψ g := fun S hS g => by
    rw [hP.htau, rsN_apply, mem_torsN.mp hS, tau_zero_apply]
  have hoff : ∀ g : FF W L, g ≠ 0 → (∀ R : Pt W L, R ≠ 0 → Ge 0 g R) →
      ∀ P : Pt W L, P ∉ torsN W L N → Ge 0 (ψ g) P := by
    intro g hg hR P hPG
    have hNP : N • P ≠ 0 := fun h => hPG (mem_torsN.mpr h)
    have h1 := (hR _ hNP).resolve_left hg
    refine Or.inr ?_
    rw [hP.hord _ hg, rsN_apply]
    push_cast
    omega
  have hX0 : ψ (gx W L) ≠ 0 := fun h => gx_ne_zero' (hP.inj (by rw [h, map_zero]))
  have hY0 : ψ (gy W L) ≠ 0 := fun h => gy_ne_zero' (hP.inj (by rw [h, map_zero]))
  refine invG_mem_of_XY hG (X := ψ (gx W L)) (Y := ψ (gy W L))
    ⟨fun S hS => hinv S hS _, hoff _ gx_ne_zero' fun R hR => ge_gx hR⟩
    ⟨fun S hS => hinv S hS _, hoff _ gy_ne_zero' fun R hR => ge_gy hR⟩ hX0 hY0 ?_ ?_
    (AlgHom.mem_range_self _ _) (AlgHom.mem_range_self _ _) ?_ hf
  · rw [hP.hord _ gx_ne_zero', map_zero, ord_gx_zero]; norm_num
  · rw [hP.hord _ gy_ne_zero', map_zero, ord_gy_zero]; norm_num
  · rintro _ ⟨g, rfl⟩
    exact ⟨g⁻¹, map_inv₀ ψ g⟩

variable {W₁ : WeierstrassCurve F} [W₁.IsElliptic]

/-- **Points fixed by `E[N]`-translations are pullbacks along `[N]`.** -/
lemma exists_lift_of_invN (hNF : (N : F) ≠ 0) (hP : IsPull ψ 1 (rsHom W L (N : ℤ) 0))
    {A : (W₁.baseChange (FF W L)).toAffine.Point}
    (hA : ∀ T ∈ torsN W L N, Point.map (W' := W₁.toAffine) ((tauHom W L T).restrictScalars F) A = A) :
    ∃ A' : (W₁.baseChange (FF W L)).toAffine.Point,
      Point.map (W' := W₁.toAffine) (ψ.restrictScalars F) A' = A := by
  by_cases hA0 : A = 0
  · exact ⟨0, by rw [hA0, map_zero]⟩
  have hix : InvG (torsN W L N) (px A) := fun T hT => by
    have h := congrArg px (hA T hT)
    rw [px_map] at h
    rw [tau_apply]; exact h
  have hiy : InvG (torsN W L N) (py A) := fun T hT => by
    have h := congrArg py (hA T hT)
    rw [py_map] at h
    rw [tau_apply]; exact h
  obtain ⟨u, hu⟩ := (AlgHom.mem_range _).mp (invN_mem_range hNF hP hix)
  obtain ⟨v, hv⟩ := (AlgHom.mem_range _).mp (invN_mem_range hNF hP hiy)
  have hu' : ψ.restrictScalars F u = px A := by rw [AlgHom.restrictScalars_apply]; exact hu
  have hv' : ψ.restrictScalars F v = py A := by rw [AlgHom.restrictScalars_apply]; exact hv
  have hinj : Function.Injective (ψ.restrictScalars F) := fun a b h => hP.inj h
  have hns := nonsingular_px_py hA0
  rw [← hu', ← hv'] at hns
  refine ⟨Point.some u v ((baseChange_nonsingular (W := W₁.toAffine)
    (f := ψ.restrictScalars F) hinj u v).mp hns), ?_⟩
  rw [Point.map_some]
  conv_rhs => rw [eq_some_px_py hA0]
  exact some_eq_some hu' hv'

/-- **Factorisation through `[N]`.** An isogeny `α : E → E₁` killing `E[N]` (`p ∤ N`) is `χ ∘ [N]` for an isogeny
`χ`; `χ` commutes with Frobenius when `α` does. -/
theorem exists_factorN (hNF : (N : F) ≠ 0) {α : Pt W L →+ Pt W₁ L}
    {A : (W₁.baseChange (FF W L)).toAffine.Point} (hα : HasGenI α A) (hker : ∀ T : Pt W L, N • T = 0 → α T = 0) :
    ∃ χ : Pt W L →+ Pt W₁ L, IsIsog χ ∧ (∀ P, χ (N • P) = α P) ∧
      ((∀ P, α (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W₁ L (α P)) →
        ∀ Q, χ (RPLib.EllFq.frob W L Q) = RPLib.EllFq.frob W₁ L (χ Q)) := by
  obtain ⟨ψ, hP⟩ := exists_isPull_rs_sep (W := W) (L := L) (N : ℤ) 0 (natCast_ne_zero_L hNF)
  have hA : ∀ T ∈ torsN W L N,
      Point.map (W' := W₁.toAffine) ((tauHom W L T).restrictScalars F) A = A :=
    fun T hT => by rw [hα T, hker T (mem_torsN.mp hT), map_zero, add_zero]
  obtain ⟨A', hA'⟩ := exists_lift_of_invN hNF hP hA
  have hsurj : Function.Surjective (rsHom W L (N : ℤ) 0) := hP.surjective
  have hwd : ∀ P₁ P₂, rsHom W L (N : ℤ) 0 P₁ = rsHom W L (N : ℤ) 0 P₂ → α P₁ = α P₂ := by
    intro P₁ P₂ h
    rw [rsN_apply, rsN_apply] at h
    have h2 := hker (P₁ - P₂) (by rw [nsmul_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at h2
  let χ : Pt W L →+ Pt W₁ L := AddMonoidHom.mk' (fun Q => α (Function.surjInv hsurj Q)) (by
    intro Q₁ Q₂
    rw [← map_add]
    apply hwd
    rw [map_add, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj])
  have hχ : ∀ P, χ (rsHom W L (N : ℤ) 0 P) = α P := fun P => hwd _ _ (Function.surjInv_eq hsurj _)
  have hχ' : ∀ P, χ (N • P) = α P := fun P => by rw [← rsN_apply, hχ]
  refine ⟨χ, ⟨A', fun Q => ?_⟩, hχ', fun hfr Q => ?_⟩
  · obtain ⟨P, rfl⟩ := hsurj Q
    have hcomp : (ψ.restrictScalars F).comp
        ((tauHom W L (rsHom W L (N : ℤ) 0 P)).restrictScalars F) =
        ((tauHom W L P).restrictScalars F).comp (ψ.restrictScalars F) :=
      AlgHom.ext fun f => by
        show ψ (tauHom W L (rsHom W L (N : ℤ) 0 P) f) = tauHom W L P (ψ f)
        rw [← tau_apply, ← tau_apply, hP.htau]
    apply Point.map_injective (W' := W₁.toAffine) (f := ψ.restrictScalars F)
    rw [Point.map_map, hcomp, ← Point.map_map, hA', hα P, map_add, hA', map_ιQ_of_algHom, hχ]
  · obtain ⟨P, rfl⟩ := hsurj Q
    rw [rsN_apply, map_nsmul, hχ', hχ', hfr]

/-- **(DIV)** An `F_q`-endomorphism killing `E[N]` (`p ∤ N`) is `N` times an `F_q`-endomorphism. -/
theorem endFq_div (hNF : (N : F) ≠ 0) {α : AddMonoid.End (Pt W L)} (hα : α ∈ endFq W L)
    (hker : ∀ T : Pt W L, N • T = 0 → α T = 0) :
    ∃ χ ∈ endFq W L, α = (N : AddMonoid.End (Pt W L)) * χ := by
  obtain ⟨hE, hc⟩ := mem_endFq.mp hα
  obtain ⟨Φ, hΦ⟩ := (mem_endRing).mp hE
  have hαI : HasGenI (W' := W) α Φ := fun S => hΦ S
  obtain ⟨χ, ⟨A', hA'⟩, hχ, hfr⟩ := exists_factorN (W₁ := W) hNF hαI hker
  have hfrα : ∀ P, α (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W L (α P) := fun P =>
    (DFunLike.congr_fun hc P).symm
  have hfrχ := hfr hfrα
  refine ⟨χ, mem_endFq.mpr ⟨(mem_endRing).mpr ⟨A', fun S => hA' S⟩, ?_⟩, ?_⟩
  · refine AddMonoidHom.ext fun P => ?_
    exact (hfrχ P).symm
  · refine AddMonoidHom.ext fun P => ?_
    show α P = N • χ P
    rw [← map_nsmul, hχ]
    rfl

variable {W' : WeierstrassCurve F} [W'.IsElliptic]

/-- **(ISO) Inverse isogenies.** If `u : E' → E` is injective and `u ∘ w = [N]` for an isogeny `w : E → E'` with
`p ∤ N`, then `u` has an inverse isogeny `v`, Frobenius-equivariant when `u` is. (Bijectivity alone is not enough:
`p`-Frobenius twists are bijective and inseparable.) -/
theorem exists_inv_isog (hNF : (N : F) ≠ 0) {u : Pt W' L →+ Pt W L} (hu : Function.Injective u)
    {w : Pt W L →+ Pt W' L} (hw : IsIsog w) (huw : ∀ P, u (w P) = N • P) :
    ∃ v : Pt W L →+ Pt W' L, IsIsog v ∧ (∀ Q, v (u Q) = Q) ∧ (∀ P, u (v P) = P) ∧
      ((∀ Q, u (RPLib.EllFq.frob W' L Q) = RPLib.EllFq.frob W L (u Q)) →
        ∀ P, v (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (v P)) := by
  obtain ⟨Ω, hΩ⟩ := hw
  have hker : ∀ T : Pt W L, N • T = 0 → w T = 0 := fun T hT => hu (by rw [huw, hT, map_zero])
  obtain ⟨v, hv, hvN, -⟩ := exists_factorN (W₁ := W') hNF hΩ hker
  have hwu : ∀ Q, w (u Q) = N • Q := fun Q => hu (by rw [huw, map_nsmul])
  obtain ⟨ψ, hP⟩ := exists_isPull_rs_sep (W := W) (L := L) (N : ℤ) 0 (natCast_ne_zero_L hNF)
  obtain ⟨ψ', hP'⟩ := exists_isPull_rs_sep (W := W') (L := L) (N : ℤ) 0 (natCast_ne_zero_L hNF)
  have hvu : ∀ Q, v (u Q) = Q := fun Q => by
    obtain ⟨R, rfl⟩ := hP'.surjective Q
    rw [rsN_apply, map_nsmul, hvN, hwu]
  have huv : ∀ P, u (v P) = P := fun P => by
    obtain ⟨R, rfl⟩ := hP.surjective P
    rw [rsN_apply, ← huw, hvu]
  refine ⟨v, hv, hvu, huv, fun hfr P => hu ?_⟩
  rw [huv, hfr, huv]

end MulN

end RPLib.DWS


