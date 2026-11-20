-- Prove2me | Definitions.Def_RPLib_F2_055
-- name    : RPLib_F2_055
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T20:23:01.123645+00:00
-- url     : https://prove2.me/theorems/f5014182-bcd2-464d-920c-16d70e166319
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 055 of 70
-- statement:
--   File 055 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
--   * `S4.Def_RP_JacComplete_PicJ`: The Jacobian (unit S4-JacComplete), part `PicJ` (L20, final form)
--   * `S4.Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
--   * `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
--   * `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
--   * `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
--   * `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
--   * `S4.Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
--   * `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
--   * `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--   * `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
--   * `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--   * `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
--   * `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
--   * `S4.Def_RP_ThetaCube_GrB`: S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
--   * `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
--   * `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_053

/-!
# Ramanujan-Petersson curve library (flat edition), file 055 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_PicSurj`: The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)
* `S4.Def_RP_JacComplete_PicJ`: The Jacobian (unit S4-JacComplete), part `PicJ` (L20, final form)
* `S4.Def_RP_JacComplete_AJVal`: The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values
* `S4.Def_RP_JacComplete_AJVal2`: The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`
* `S4.Def_RP_JacComplete_AJGen`: The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`
* `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
* `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
* `S4.Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
* `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
* `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
* `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
* `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
* `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `S4.Def_RP_ThetaCube_GrB`: S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
* `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
* `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_PicSurj =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicSurj` (L20: `jacPic0` is surjective)

* `phi1 : Sym¹ B → B` (identity on points), `ptSet_phi1`, `liftTuple_phi1`;
* `rangeJ K F`: the image of `jacPic0` in `Pic`; `psiJ_mem_rangeJ`; `psiJ_of_pt` (points `y` of `S_g` with `y u0 ≠ 0`);
* **`jacPic0_surjective`**: for `g ≥ 1` the points `Q + c` (`c` = all but one point of a fixed point of `X0`) give
  `[Q] - [q0] ∈ rangeJ` for all `Q` off the zeros of `f = padMap phi1 c u0`, and `pic0_le_of_gen` finishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section One

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] [IsReduced B]
  [Algebra.FiniteType k B]

end One

section Surj

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The image of `jacPic0` in `Pic`. -/
noncomputable def rangeJ : AddSubgroup (PicK K F) where
  carrier := {c | ∃ σ : (lawChunk K F).H, ((Multiplicative.toAdd (jacPic0 K F σ) : Pic0K K F) : PicK K F) = c}
  add_mem' := by
    rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
    exact ⟨σ * τ, congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) (map_mul (jacPic0 K F) σ τ)⟩
  zero_mem' := ⟨1, congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) (map_one (jacPic0 K F))⟩
  neg_mem' := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨σ⁻¹, congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) (map_inv (jacPic0 K F) σ)⟩

theorem psiJ_mem_rangeJ (a : X0 K F) (ha : IsClosed ({a} : Set (X0 K F))) : psiJ K F a ∈ rangeJ K F :=
  ⟨_, jacPic0_lamB K F a ha⟩

open Classical in
set_option maxHeartbeats 400000 in
/-- **L20, surjectivity**: every degree-`0` class is `[σ(D) - D]`. -/
theorem jacPic0_surjective : Function.Surjective (jacPic0 K F) := by
  suffices hle : Pic0K K F ≤ rangeJ K F by
    intro c
    obtain ⟨σ, hσ⟩ := hle (Multiplicative.toAdd c).2
    exact ⟨σ, Multiplicative.toAdd.injective (Subtype.ext hσ)⟩
  rcases Nat.eq_zero_or_pos (genusFK K F) with hg | hg
  · intro c hc
    obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
    have hD : D.deg = 0 := by rw [← degPicK_clsK]; exact (mem_Pic0K K F).1 hc
    show clsK K F D ∈ rangeJ K F
    rw [clsK_eq_zero_of_genus_zero hg hD]
    exact (rangeJ K F).zero_mem
  have hd : 1 + (genusFK K F - 1) = genusFK K F := by omega
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (LawRing K F)
  obtain ⟨y0R, -⟩ := exists_algHom_ker_eq (k := K) m
  let y0 := y0R.comp (awayι (K := K) (lawPre K F).u0)
  let t := liftTuple y0
  let c : Fin (genusFK K F - 1) → (Places.Rfin K F →ₐ[K] K) := fun j => t (Fin.cast hd (Fin.natAdd 1 j))
  let q0 := t (Fin.cast hd (Fin.castAdd (genusFK K F - 1) 0))
  let f := padMap (phi1 (k := K) (B := Places.Rfin K F)) c hd (lawPre K F).u0
  have hyQ : ∀ Q : Places.Rfin K F →ₐ[K] K, Q f = padPt phi1 c hd Q (lawPre K F).u0 := fun Q => by
    rw [← comp_padMap]; rfl
  have hq0 : padPt phi1 c hd q0 = y0 := by
    rw [padPt, liftTuple_phi1]
    conv_rhs => rw [← symPt_liftTuple y0]
    congr 1
    funext i
    have hl : (fun _ : Fin 1 => q0) = fun j => t (Fin.cast hd (Fin.castAdd (genusFK K F - 1) j)) := by
      funext j; rw [Fin.fin_one_eq_zero j]
    rw [hl]
    exact (congrFun (Fin.append_castAdd_natAdd (f := fun j => t (Fin.cast hd j))) (Fin.cast hd.symm i)).trans
      (by simp [t])
  have hy0u : y0 (lawPre K F).u0 ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (lawPre K F).u0).map y0R).ne_zero
  have hq0f : q0 f ≠ 0 := by rw [hyQ, hq0]; exact hy0u
  have hf : f ≠ 0 := fun h => hq0f (by rw [h, map_zero])
  set Θ := ThetaD (lawData K F).Dm3 (lawData K F).Dm2 (lawData K F).c0 (lawData K F).c1
  have hQ : ∀ Q : Places.Rfin K F →ₐ[K] K, Q f ≠ 0 → ∃ a : X0 K F, IsClosed ({a} : Set (X0 K F)) ∧
      psiJ K F a = clsK K F (Zdiv (Finset.univ.image c)) + clsK K F (Finsupp.single (Sum.inl (ptP Q)) 1) -
        clsK K F Θ := by
    intro Q hQf
    obtain ⟨a, ha, hcard, hpsi⟩ := psiJ_of_pt K F (padPt phi1 c hd Q) (by rw [← hyQ]; exact hQf)
    have hpt : ptSet (padPt phi1 c hd Q) = insert Q (Finset.univ.image c) := by
      rw [ptSet_padPt, ptSet_phi1, Finset.insert_eq]
    have hQc : Q ∉ Finset.univ.image c := by
      intro hmem
      rw [hpt, Finset.insert_eq_of_mem hmem] at hcard
      have := Finset.card_image_le (s := Finset.univ) (f := c)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    refine ⟨a, ha, ?_⟩
    rw [hpsi, hpt, Zdiv_insert hQc, clsK_add]
  obtain ⟨a0, ha0, hpsi0⟩ := hQ q0 hq0f
  let S : Finset (Places.Place K F) := (PlacesK.div (incB K F f)).support ∪
    (Set.finite_range (Sum.inr : IsDedekindDomain.HeightOneSpectrum (Places.Rinf K F) → Places.Place K F)).toFinset
  refine pic0_le_of_gen (rangeJ K F) (Sum.inl (ptP q0)) S ?_ ?_
  · intro hmem
    rcases Finset.mem_union.1 hmem with h1 | h1
    · exact (div_incB_ne_zero_iff hf q0).1 (Finsupp.mem_support_iff.1 h1) |> hq0f
    · obtain ⟨P, hP⟩ := (Set.Finite.mem_toFinset _).1 h1
      exact Sum.inr_ne_inl hP
  · intro v hv
    rcases v with P | P
    · obtain ⟨Q, rfl⟩ := exists_ptP P
      have hQf : Q f ≠ 0 := fun h0 => hv (Finset.mem_union_left _
        (Finsupp.mem_support_iff.2 ((div_incB_ne_zero_iff hf Q).2 h0)))
      obtain ⟨a, ha, hpsi⟩ := hQ Q hQf
      have key : clsK K F (Finsupp.single (Sum.inl (ptP Q)) 1) - clsK K F (Finsupp.single (Sum.inl (ptP q0)) 1) =
          psiJ K F a - psiJ K F a0 := by
        rw [hpsi, hpsi0]; abel
      rw [key]
      exact (rangeJ K F).sub_mem (psiJ_mem_rangeJ K F a ha) (psiJ_mem_rangeJ K F a0 ha0)
    · exact (hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 (Set.mem_range_self P)))).elim

end Surj

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicJ =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicJ` (L20, final form)

**`jacPicEquiv K F : J(K) ≃* Multiplicative Pic⁰(X_K)`** (Milne III.7.5-7.6): `kptEquiv` followed by the bijective
class map `jacPic0` (`jacPic0_injective`, `jacPic0_surjective`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section PicJ

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **L20 (Milne III.7.5-7.6)**: `J(K) ≃* Pic⁰(X_K)`, `a ↦ [σ_a(D) - D]`. -/
noncomputable def jacPicEquiv : (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≃* Multiplicative (Pic0K K F) :=
  (kptEquiv K F).trans (MulEquiv.ofBijective (jacPic0 K F) ⟨jacPic0_injective K F, jacPic0_surjective K F⟩)

theorem jacPicEquiv_apply (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    jacPicEquiv K F a = jacPic0 K F (kptEquiv K F a) := rfl

end PicJ

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJVal =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal`: the Abel-Jacobi map on a piece and its values

* `specO K R`, `kptO x` (the `K`-point of `Spec R` at `x : R →ₐ[K] K`), `SpecMap_closedPoint`.
* `jMap φ : Spec R ⟶ J` (`Spec φ ≫ jX0`); its `K`-points have value `ψ(x ∘ φ)` (`jacPicEquiv_jMap`).
* `ajCls P0 Q = [Q] - [P0] ∈ Pic⁰`, `ajK P0 Q = jacPicEquiv⁻¹ (ajCls P0 Q)`, `ajPt P0 Q` (its point of `J`).
* **`ajMap P0 φ κ = const (κ - [Θ] - [P0]) * (jMap φ)⁻¹`** (group law on `Spec R ⟶ J`), with value
  `ajK P0 Q` at every `K`-point `x` with `ψ(x ∘ φ) = κ - [Θ] - [Q]` (`kptO_ajMap`, `ajMap_kpt`).
* **`ajPiece P0 c0 D c := ajMap P0 (lawMapP c0 D c) (kapP c0 D c)`** on the piece `Spec LocR`: value `ajPt P0 Q`
  (value lemmas for the piece: next file; see NOTES session 19).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section SpecPt

variable {K : Type u} [Field K]

end SpecPt

section JMap

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The value of `Spec R ⟶ J` at a `K`-point is `ψ(x ∘ φ)`. -/
theorem jacPicEquiv_jMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (x : R →ₐ[K] K) :
    ((Multiplicative.toAdd (jacPicEquiv K F (kptO x ≫ jMap K F φ)) : Pic0K K F) : PicK K F) =
      psiJ K F (kpt (x.comp φ)) := by
  have e : kptEquiv K F (kptO x ≫ jMap K F φ) =
      ⟨(lawChunk K F).lamB (kpt (x.comp φ)) (JacLaw.isClosed_kpt _),
        (lawChunk K F).lamB_mem_H _ (JacLaw.isClosed_kpt _)⟩ :=
    Subtype.ext (kval_jMap K F φ x)
  rw [jacPicEquiv_apply, e]
  exact jacPic0_lamB K F _ _

variable (P0 : Place K F)

/-- The `K`-point `jacPicEquiv⁻¹ ([Q] - [P0])` of `J`. -/
noncomputable def ajK (Q : Place K F) : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  (jacPicEquiv K F).symm (Multiplicative.ofAdd (ajCls K F P0 Q))

/-- **The Abel-Jacobi point** of `Q`: the closed point of `J` with class `[Q] - [P0]`. -/
noncomputable def ajPt (Q : Place K F) : (Jac K F).left := (ajK K F P0 Q).left (IsLocalRing.closedPoint K)

open Classical in
/-- The constant `κ - [Θ] - [P0]` (in `Pic⁰` as soon as the piece has a `K`-point). -/
noncomputable def ajC (κ : PicK K F) : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  (jacPicEquiv K F).symm (Multiplicative.ofAdd
    (if h : κ - thetaK K F - clsK K F (Finsupp.single P0 1) ∈ Pic0K K F then ⟨_, h⟩ else 0))

/-- **The Abel-Jacobi map on `Spec R`**: `const (κ - [Θ] - [P0]) * (Spec φ ≫ jX0)⁻¹`. -/
noncomputable def ajMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F) :
    specO K R ⟶ Jac K F :=
  (toUnit (specO K R) ≫ ajC K F P0 κ) * (jMap K F φ)⁻¹

theorem ajMap_over {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F) :
    (ajMap K F P0 φ κ).left ≫ (Jac K F).hom = sR K R :=
  Over.w (ajMap K F P0 φ κ)

/-- **Value of the AJ map**: `ajK P0 Q` at a `K`-point `x` with `ψ(x ∘ φ) = κ - [Θ] - [Q]`. -/
theorem kptO_ajMap {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F)
    (x : R →ₐ[K] K) (Q : Place K F)
    (hx : psiJ K F (kpt (x.comp φ)) = κ - thetaK K F - clsK K F (Finsupp.single Q 1)) :
    kptO x ≫ ajMap K F P0 φ κ = ajK K F P0 Q := by
  have h1 : psiJ K F (kpt (x.comp φ)) ∈ Pic0K K F := by
    rw [← jacPicEquiv_jMap K F φ x]
    exact (Multiplicative.toAdd (jacPicEquiv K F (kptO x ≫ jMap K F φ))).2
  have hmem : κ - thetaK K F - clsK K F (Finsupp.single P0 1) ∈ Pic0K K F := by
    have e : κ - thetaK K F - clsK K F (Finsupp.single P0 1) =
        psiJ K F (kpt (x.comp φ)) + (ajCls K F P0 Q : PicK K F) := by
      rw [hx]
      show _ = _ + (clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1))
      abel
    rw [e]
    exact add_mem h1 (ajCls K F P0 Q).2
  rw [ajMap, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    toUnit_unique (kptO x ≫ toUnit (specO K R)) (𝟙 _), Category.id_comp]
  apply (jacPicEquiv K F).injective
  rw [map_mul, map_inv, ajC, ajK, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, dif_pos hmem]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd]
  apply Subtype.ext
  rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, jacPicEquiv_jMap K F φ x, hx]
  show κ - thetaK K F - clsK K F (Finsupp.single P0 1) + -(κ - thetaK K F - clsK K F (Finsupp.single Q 1)) =
    clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1)
  abel

/-- **Value of the AJ map at a closed point** `kpt x`. -/
theorem ajMap_kpt {R : Type u} [CommRing R] [Algebra K R] (φ : LawRing K F →ₐ[K] R) (κ : PicK K F)
    (x : R →ₐ[K] K) (Q : Place K F)
    (hx : psiJ K F (kpt (x.comp φ)) = κ - thetaK K F - clsK K F (Finsupp.single Q 1)) :
    (ajMap K F P0 φ κ).left (kpt x) = ajPt K F P0 Q := by
  rw [ajPt, ← kptO_ajMap K F P0 φ κ x Q hx]
  show _ = (ajMap K F P0 φ κ).left (Spec.map (CommRingCat.ofHom (x : R →+* K)) (IsLocalRing.closedPoint K))
  rw [SpecMap_closedPoint]

end JMap

section Piece

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- **The AJ piece** `Spec LocR ⟶ J` (an open of the chart `Spec B'`, `B' = Rfin (SynF K F c0)`). -/
noncomputable def ajPiece : specO K (LocR c0 D c) ⟶ Jac K F :=
  ajMap K F P0 (lawMapP c0 D c) (kapP c0 D c)

theorem ajPiece_over : (ajPiece P0 c0 D c).left ≫ (Jac K F).hom = sR K (LocR c0 D c) :=
  ajMap_over K F P0 _ _

end Piece

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJVal2 =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJVal2`: values of the AJ piece on the chart `Spec B'`, `B' = Rfin (SynF K F c0)`

* `plC c0 Q` (the place of `F` at a `K`-point `Q` of `B'`), `plP c0 D c x`, `psiJ_plP`.
* **`kptO_ajPiece`**, **`ajPiece_kpt`**: the piece takes the value `ajPt P0 (plP c0 D c x)` (class `[Q] - [P0]`).
* `isOpenImmersion_pieceIn`: `Spec LocR → Spec B'` is an open immersion; `pieceIn_over`.
* **`ajChart P0 c0 : Spec B' ⟶ J`** glued (`JacChunk.glueY`) from the pieces; `ajChart_over`,
  **`ajChart_kpt`**: value `ajPt P0 (plC c0 Q)` at every closed point `kpt Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section PlP

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K)

variable {r : ℕ} (D : NuData K (SynF K F c0) (1 + r)) (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

theorem psiJ_plP (x : LocR c0 D c →ₐ[K] K) :
    psiJ K F (kpt (x.comp (lawMapP c0 D c))) =
      kapP c0 D c - thetaK K F - clsK K F (Finsupp.single (plP c0 D c x) 1) :=
  psiJ_lawMapP c0 D c x

end PlP

section PieceVal

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K) {r : ℕ} (D : NuData K (SynF K F c0) (1 + r))
  (c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K))

/-- **Value of the piece at a closed point** `kpt x`. -/
theorem ajPiece_kpt (x : LocR c0 D c →ₐ[K] K) :
    (ajPiece P0 c0 D c).left (kpt (A := LocR c0 D c) x) = ajPt K F P0 (plP c0 D c x) :=
  ajMap_kpt (R := LocR c0 D c) K F P0 (lawMapP c0 D c) (kapP c0 D c) x _ (psiJ_plP c0 D c x)

end PieceVal

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGen =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGen`: the pieces cover the chart `{c0}`

* `exists_pool`: arbitrarily large finite sets of points off the roots of `b(x)`.
* `PtY K F c0` (points of `B' = Rfin F'` off `x = ∞`), `tpY` (their `F`-points, injective).
* `goodY_ext`: nonspecial `b`-generic sets of such points extend off any finite set.
* `symPt_convPt_eq`: the converted point depends only on the support.
* **`exists_piece_through`**: every closed point `Q0` of `B'` lies on some piece `Spec LocR c0 D c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJGen

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K)

set_option maxHeartbeats 1000000 in
/-- **AJGen: the pieces cover the chart**: every closed point `Q0` of `B'` lies on some piece. -/
theorem exists_piece_through (Q0 : Rfin K (SynF K F c0) →ₐ[K] K) :
    ∃ r : ℕ, ∃ D : NuData K (SynF K F c0) (1 + r), ∃ c : Fin r → (Rfin K (SynF K F c0) →ₐ[K] K),
      ∃ x : LocR c0 D c →ₐ[K] K, x.comp (pieceIn c0 D c) = Q0 := by
  obtain ⟨b, hb0, hsec⟩ := exists_secE Q0
  have hg : genusFK K (SynF K F c0) = genusFK K F := genusFK_eq (synEquiv K F c0)
  obtain ⟨a, ha, ⟨hNS1, hab⟩, hau⟩ := exists_goodTuple (F := F) c0 hb0
  obtain ⟨E, hE⟩ : ∃ E : Finset (Rfin K (SynF K F c0) →ₐ[K] K),
      E = (Finset.univ.image a).map (Function.Embedding.subtype _) := ⟨_, rfl⟩
  have hEc : E.card = genusFK K (SynF K F c0) := by
    rw [hE, Finset.card_map, Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin, hg]
  have hEb : ∀ e ∈ E, b.eval (e (xB K (SynF K F c0))) ≠ 0 := by
    intro e he
    rw [hE] at he
    obtain ⟨e', he', rfl⟩ := Finset.mem_map.1 he
    exact hab e' he'
  have hEx : ∀ e ∈ E, e (xS K F c0) ≠ 0 := by
    intro e he
    rw [hE] at he
    obtain ⟨e', -, rfl⟩ := Finset.mem_map.1 he
    exact e'.2
  have hNS : IsNS K (SynF K F c0) E := const_of_ellFK_eq_one (Zdiv_nonneg E) (by rw [hE]; exact hNS1)
  obtain ⟨s, Z, hs0, hex, hZ, hZc, hQZ, hEZ, hQE, hmZ⟩ := hsec E hEb (2 * genusFK K (SynF K F c0))
  obtain ⟨r, D, c, -, hA, hrole⟩ := exists_nuE hs0 hex hZ hZc hQZ hEZ hQE hEc hNS hmZ
  have hpad : ptSet (padPt (phi1 (k := K) (B := Rfin K (SynF K F c0))) c rfl Q0) = Z \ E := by
    rw [ptSet_padPt1, hA]
  obtain ⟨hgood, hnu⟩ := hrole _ hpad
  refine ⟨r, D, c, exists_pieceIn c0 D c Q0 ?_ ?_ ?_⟩
  · rw [apply_pieceF]; exact hgood
  · intro z hz e he
    rw [ptSet_pieceMap, hz, hnu] at he
    exact hEx e he
  · intro y hy
    exact convU_ne_zero c0 D c y a ha (by rw [ptSet_convφ, hy, hnu, hE]) hau

end AJGen

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_AJGlue =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces

`B' = Rfin (SynF K F c0)`.
* `locallyOfFiniteType_sR`; the piece index `PIdx K F c0` and the open immersions `pj c0 i : Spec LocR → Spec B'`.
* `pj_kpt` (closed points), `pj_cov` (the pieces cover the closed points), `pj_over`.
The glued map `ajChart` is in part `AJGlue2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K)

/-- The pieces cover the closed points of `Spec B'`. -/
theorem pj_cov (t : Spec (.of (Rfin K (SynF K F c0)))) (ht : IsClosed ({t} : Set (Spec (.of (Rfin K (SynF K F c0)))))) :
    ∃ i : PIdx K F c0, ∃ p : Spec (.of (LocR c0 i.2.1 i.2.2)), pj c0 i p = t := by
  obtain ⟨Q0, rfl⟩ := exists_kpt (K := K) (A := Rfin K (SynF K F c0)) t ht
  obtain ⟨r, D, c, x, rfl⟩ := exists_piece_through (F := F) c0 Q0
  exact ⟨⟨r, D, c⟩, kpt (A := LocR c0 D c) x, pj_kpt c0 ⟨r, D, c⟩ x⟩

end Glue

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Pts =====
section

/-!
# Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`

Input for `coheight (zTheta P0) ≤ 1` (file `Codim`, Krull on the chart `X0`):
* `kJ yR`: the `K`-point of `J` at the closed point `yR` of `X0`; `pt_kJ` (it is `jX0 (kpt yR)`) and `cls_kJ`
  (its class is `[Zdiv A] - [Θ]`, `A` the `g` points of `yR`); `deg_thetaK : deg [Θ] = g`;
* `exists_cJ`: the `K`-point `c_φ` with class `[φ] + (g-1)[P0] - [Θ]`;
* `mem_W_of_cls`: a class `[Zdiv S] - (g-1)[P0]` with `#S = g-1` lies on `W`;
* `mem_transl_W`: if `φ` is one of the points of `yR`, then `jX0 (kpt yR) - c_φ ∈ W`;
* `finite_zeros`: a nonzero `u ∈ Rfin` has finitely many zeros.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB

universe u

section Pts

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem cls_kJ (yR : LawRing K F →ₐ[K] K) :
    ((Multiplicative.toAdd (jacPicEquiv K F (kJ yR)) : Pic0K K F) : PicK K F) =
      clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) - thetaK K F := by
  rw [kJ, jacPicEquiv_jMap, AlgHom.comp_id, psiJ, psiS_kpt]
  rfl

end Pts

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_PlusJ =====
section

/-!
# Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula

For `g` points `a_i` of `Rfin` and a slot `i0`, `plusR = plusMap inclR a i0 : Sym^g Rfin → R1`; with `h = plusR(u0)`
and `R2 = R1[1/h]` it induces **`lawMapPlus : LawRing → R2`**, whose `K`-points have class
`[P] + [E] - [Θ]` (`psiJ_lawMapPlus`), `P` the point of `Rfin` under `x`, `E = Σ_{i ≠ i0} a_i` (`plusE`).
Also: the center of a `K`-point `y` of `R1` restricted to `B_{c0}` is the finite place of `y|Rfin` (`isCenter_R1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial AlgebraicGeometry

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.RR

universe u

section PlusJ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable [IsAlgClosed K]

variable (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

open Classical in
/-- **Class formula of the plus-curve**: `ψ(plus(x)) = [P] + [E] - [Θ]`. -/
theorem psiJ_lawMapPlus (x : R2 c0 a i0 →ₐ[K] K) :
    psiJ K F (kpt (x.comp (lawMapPlus c0 a i0))) =
      clsK K F (Finsupp.single (Sum.inl (ptP (ptR2 c0 a i0 x))) 1) + clsK K F (plusE a i0) - thetaK K F := by
  have hinj := injective_update c0 a i0 x
  have e : ∑ i ∈ Finset.univ.erase i0,
      Finsupp.single (Sum.inl (ptP (Function.update a i0 (ptR2 c0 a i0 x) i)) : Place K F) (1 : ℤ) = plusE a i0 :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [psiJ, psiS_kpt]
  change clsK K F (Zdiv (ptSet ((x.comp (lawMapPlus c0 a i0)).comp (awayι (K := K) (lawPre K F).u0)))) -
    thetaK K F = _
  rw [comp_lawMapPlus, ptSet_symPt, Zdiv, Finset.sum_image (fun i _ j _ h => hinj h),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), Function.update_self, clsK_add, e]

end PlusJ

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve6 =====
section

/-!
# Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)

* `ell_two_eq_one`: for `G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`, `ℓ(W0 - G + 2[v]) = 1` for every place `v`;
* `exists_cK`, `exists_c2`: the constant `K`-points of classes `[W0] - (g-2)[P0] - [Θ]` and `g[P0] - [Θ]`;
* `exists_kJ`: a `K`-point of `J` whose closed point lies in `jX0 (X0)` is `kJ yR`;
* `avoid_of_not_mem`: `e ∉ W` makes `f_e` avoid `Θ`;
* **`isGoodFor_of`**: if `e ∉ W`, `c_K e⁻¹ ∈ jX0 (X0)`, and `AJ(q)² e c_2 ∈ jX0 (X0)` whenever `f_e (q) ∈ W`, then
  `e` is good for some `G` (`IsGoodFor P0 W0 e G`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve6

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem ajK_self (P0 : Place K F) : ajK K F P0 P0 = 1 := by
  rw [ajK, ajCls_self, ofAdd_zero, map_one]

end Curve6

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve7 =====
section

/-!
# Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)

* `kapM cK : J ⟶ J`, `e ↦ c_K e⁻¹`; `mu1 P0 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q) e`; `mu2 P0 c2`, `(e, q) ↦ AJ(q)² e c_2`;
* `Bad P0 c2 := mu1⁻¹ W ∩ mu2⁻¹ (J \ jX0 (X0))`, closed in `J × X1`;
* **`Ogood P0 cK c2 := Wᶜ ∩ kapM⁻¹ (jX0 (X0)) ∩ (pr_J Bad)ᶜ`**, open (`isOpen_Ogood`: `pr_J` is closed, `X1` proper);
* **`isGoodFor_of_mem`**: every `K`-point of `Ogood` is good;
* `not_mem_image_Bad`, `mem_Ogood_of`: the converse criterion (all `K`-points `(e, q)` off `Bad`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve7

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

theorem pt_comp_kapM (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    (cK * e⁻¹).left (IsLocalRing.closedPoint K) = (kapM cK).left (e.left (IsLocalRing.closedPoint K)) := by
  rw [← comp_kapM]
  rfl

end Curve7

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_CubeZ =====
section

/-!
# S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`

* instances on `J ⊗ J` and `P := J ⊗ (J ⊗ J)`: integral, locally Noetherian, factorial stalks;
* `q1 q2 q3 : P ⟶ J` (projections), `cubeMap α β ga = lift α (lift β ga)`;
* `cubeZ P0 x0`: the seven-term combination of `(m_S ≫ τ_{x0})^* Θ` on `P`;
* **`cpull_cubeZ`**: `(α, β, ga)^* cubeZ = cubeC (φ ↦ (φ ≫ τ_{x0})^* Θ) α β ga` (seven `Avoid` hypotheses);
* `cpull_cubeZ_hom`: the same for homomorphisms, when `x0 ∉ W`;
* **`cubeC_mem_numKer`**: if a positive multiple of `cubeZ P0 x0` is principal on `P`, the cube relation holds
  numerically for `c φ := (φ ≫ τ_{x0})^* Θ` and all homomorphisms `α β ga`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- A map `J^3 ⟶ J` with a section `(α, β, ga)` is dominant after any translation. -/
lemma isDominant_of_cubeMap (m : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F) (α β ga : Jac K F ⟶ Jac K F)
    (h : cubeMap α β ga ≫ m = 𝟙 _) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant (m ≫ transl (Jac K F) x0).left := by
  have hs : (transl (Jac K F) x0⁻¹ ≫ cubeMap α β ga) ≫ m ≫ transl (Jac K F) x0 = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (cubeMap α β ga), h, Category.id_comp, transl_comp_transl,
      inv_mul_cancel, transl_one]
  have : IsDominant ((transl (Jac K F) x0⁻¹ ≫ cubeMap α β ga).left ≫ (m ≫ transl (Jac K F) x0).left) := by
    rw [← Over.comp_left, hs, Over.id_left]
    infer_instance
  exact IsDominant.of_comp (transl (Jac K F) x0⁻¹ ≫ cubeMap α β ga).left _

instance isDominant_q123 (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant ((q1 K F * q2 K F * q3 K F) ≫ transl (Jac K F) x0).left :=
  isDominant_of_cubeMap _ (𝟙 _) 1 1 (by rw [comp_mul, comp_mul, cubeMap_q1, cubeMap_q2, cubeMap_q3,
    _root_.mul_one, _root_.mul_one]) x0

instance isDominant_q12 (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant ((q1 K F * q2 K F) ≫ transl (Jac K F) x0).left :=
  isDominant_of_cubeMap _ (𝟙 _) 1 1 (by rw [comp_mul, cubeMap_q1, cubeMap_q2, _root_.mul_one]) x0

instance isDominant_q13 (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant ((q1 K F * q3 K F) ≫ transl (Jac K F) x0).left :=
  isDominant_of_cubeMap _ (𝟙 _) 1 1 (by rw [comp_mul, cubeMap_q1, cubeMap_q3, _root_.mul_one]) x0

instance isDominant_q23 (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant ((q2 K F * q3 K F) ≫ transl (Jac K F) x0).left :=
  isDominant_of_cubeMap _ 1 (𝟙 _) 1 (by rw [comp_mul, cubeMap_q2, cubeMap_q3, _root_.mul_one]) x0

instance isDominant_q1 (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant (q1 K F ≫ transl (Jac K F) x0).left :=
  isDominant_of_cubeMap _ (𝟙 _) 1 1 (cubeMap_q1 _ _ _) x0

instance isDominant_q2 (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant (q2 K F ≫ transl (Jac K F) x0).left :=
  isDominant_of_cubeMap _ 1 (𝟙 _) 1 (cubeMap_q2 _ _ _) x0

instance isDominant_q3 (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant (q3 K F ≫ transl (Jac K F) x0).left :=
  isDominant_of_cubeMap _ 1 1 (𝟙 _) (cubeMap_q3 _ _ _) x0

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Sym =====
section

/-!
# S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`

* `algebraMap_generic`, **`cpull_eq_pullback`**: for a dominant map, `cpull` is `JacDivisors.pullback`;
* `negJ = (𝟙 J)⁻¹` (the inverse map), `comp_negJ : φ ≫ negJ = φ⁻¹`;
* `DTh P0 x0 := τ_{x0}^* Θ + (negJ ≫ τ_{x0})^* Θ`: Weil (`DTh_mem`), effective (`DTh_nonneg`);
* `avoid_DTh`: every homomorphism avoids `DTh P0 x0` when `x0 ∉ W`;
* **`cpull_DTh`**: `φ^* D' = (φ ≫ τ_{x0})^* Θ + (φ⁻¹ ≫ τ_{x0})^* Θ`;
* **`cpull_inv_DTh`**: `(φ⁻¹)^* D' = φ^* D'` (exact symmetry).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (φ : C ⟶ Y) [IsDominant φ]

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The inverse map `[-1] : J ⟶ J`. -/
noncomputable def negJ : Jac K F ⟶ Jac K F := (𝟙 (Jac K F))⁻¹

lemma comp_negJ (φ : Jac K F ⟶ Jac K F) : φ ≫ negJ K F = φ⁻¹ := by
  rw [negJ, GrpObj.comp_inv, Category.comp_id]

lemma negJ_negJ : negJ K F ≫ negJ K F = 𝟙 _ := by
  rw [comp_negJ, negJ, inv_inv]

instance isDominant_negJ : IsDominant (negJ K F).left := by
  have : IsDominant ((negJ K F).left ≫ (negJ K F).left) := by
    rw [← Over.comp_left, negJ_negJ, Over.id_left]
    infer_instance
  exact IsDominant.of_comp (negJ K F).left _

instance isDominant_transl (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant (transl (Jac K F) x0).left := by
  have : IsDominant ((transl (Jac K F) x0⁻¹).left ≫ (transl (Jac K F) x0).left) := by
    rw [← Over.comp_left, transl_comp_transl, inv_mul_cancel, transl_one, Over.id_left]
    infer_instance
  exact IsDominant.of_comp (transl (Jac K F) x0⁻¹).left _

instance isDominant_negJ_transl (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    IsDominant (negJ K F ≫ transl (Jac K F) x0).left := by
  rw [Over.comp_left]
  infer_instance

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Maps =====
section

/-!
# S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `cpull_pbTh_X1`, **`cpull_cubeZ_X1`**: the cube divisor pulled back along any `f : X1 ⟶ J^3`;
* `comp_finprod`: composition distributes over finite products in the hom-group;
* `psiS P0 n β S := Π_{k : β k ∈ S} pr_k ≫ aj` (blocks given by `β : Fin n → Fin 3`), `psiS_mul`;
* `Phi3 P0 n β := (psiS {0}, psiS {1}, psiS {2})`, `Phi3_q1`, `Phi3_q2`, `Phi3_q3`;
* **`line_psiS_transl`**: along the `i0`-th line through `p`, `psiS S ≫ τ_{x0}` is `f_e` (if `β i0 ∈ S`) or the
  constant `e`, for `e = (p ≫ psiE S i0) * x0`;
* `cpull_const_Theta`: a constant map off `W` pulls `Θ` back to `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Maps

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- Composition distributes over finite products of maps to `J`. -/
theorem comp_finprod {X Y : Over (Spec (.of K))} (f : X ⟶ Y) {I : Type*} (s : Finset I)
    (g : I → (Y ⟶ Jac K F)) : f ≫ ∏ i ∈ s, g i = ∏ i ∈ s, f ≫ g i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact MonObj.comp_one f
  | @insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

end Maps

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Good =====
section

/-!
# S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `IsSat n i B`: `B` contains the `i`-th line through each of its `K`-points; `isSat_iUnion`, `isSat_empty`;
* `ConstAlong n i φ`: `φ` is constant along the `i`-th lines; `isSat_preimage`, closure under `≫`, `*`, `⁻¹`,
  constants, `psiE`, `epsS := psiE · x0`;
* `ne_univ_of_compl`: finitely many closed sets with nonempty complements do not cover an irreducible space;
* `exists_ne_place`: every place has a different one;
* **`bad P0 n β i x0 cK c2 A`** `= ⋃ badC`: `e_S(p) ∉ Ogood` (all `S`), `p_k = A l` (`k ≠ i`), `p_k = p_k'`
  (`k ≠ k'`, both `≠ i`), in Abel-Jacobi coordinates; **`isClosed_bad`**, **`isSat_bad`**, **`bad_ne_univ`** (when
  `x0 ∈ Ogood`), **`of_not_mem_bad`** (the three conditions at a good `K`-point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Good

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem constAlong_mul {n : ℕ} {i : Fin n} {φ ψ : PP K F n ⟶ Jac K F} (hφ : ConstAlong n i φ)
    (hψ : ConstAlong n i ψ) : ConstAlong n i (φ * ψ) := fun p => by
  simp only [MonObj.comp_mul, hφ p, hψ p]

theorem constAlong_inv {n : ℕ} {i : Fin n} {φ : PP K F n ⟶ Jac K F} (hφ : ConstAlong n i φ) :
    ConstAlong n i φ⁻¹ := fun p => by
  simp only [GrpObj.comp_inv, hφ p]

variable (n : ℕ) (β : Fin n → Fin 3) (i : Fin n) (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {s : ℕ}
  (A : Fin s → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))

end Good

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrB =====
section

/-!
# S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
* `sum_blk_tauS`, `sum_blk_fiber`: block sums;
* `grJ d S m fR`: `Σ_{b ∈ S} q_b^# trJ d (f_l f_l') + Σ_i f_l(m_i) f_l'(m_i)` on `J^3`;
* **`ffMap_det_grJ`**: `Φ3^# det (grJ) = (det_k)^2` (`det M^2 = det (Mᵀ M)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section GrB

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- **The Gram matrix on `J^3`**: `Σ_{b ∈ S} q_b^# trJ d (f_l f_l') + Σ_i f_l(m_i) f_l'(m_i)`. -/
noncomputable def grJ (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (S : Finset (Fin 3)) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) {I : Type*} (fR : I → Places.Rfin K F) :
    Matrix I I (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left.functionField :=
  Matrix.of fun l l' => ∑ b ∈ S, fpull (qb K F b).left (trJ d (fR l * fR l')) +
    ∑ i, fpull (toUnit (Jac K F ⊗ (Jac K F ⊗ Jac K F)) ≫ m i).left (phiX K F (incB K F (fR l))) *
      fpull (toUnit (Jac K F ⊗ (Jac K F ⊗ Jac K F)) ≫ m i).left (phiX K F (incB K F (fR l')))

variable (P0 : Place K F)

end GrB

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_JacFrob_Val2 =====
section

/-!
# S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`

Generic:
* `ptOf_comp_xMap`, `symPt_comp_symMap`, `ptSet_comp_symMap`: the support of `y ∘ symMap f` is `(supp y) ∘ f`;
* `thetaK`, `psiJ_kpt`: `psiJ (kpt y) = [Z(y|S_g)] - [Θ]`; `cls_of_kpt`, `cls_mor`, `cls_mor_hom`: classes of `a` and `a ≫ mor φ hφ`.

For `J = J_{F-bar}` over `k-bar`:
* `PhiR_eq_pow`: `Φ b = (σ⁻¹ b)^q` on `Rfin`; `ptP_comp_PhiR`: the place of `χ ∘ Φ` is `σ_*` of the place of `χ`;
* `comp_PhiR_injective`, `Zdiv_image_PhiR`, `Zdiv_ptSet_PhiS`: `Z(y ∘ Φ_S) = σ_* Z(y)`;
* `cTheta = σ_*[Θ] - [Θ] ∈ Pic⁰`; **`jacPicEquiv_piJ0`**: `[a ≫ π_J⁰] = σ_*[a] + cTheta`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory IsDedekindDomain
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR
open RamanujanPetersson.PicDescent

universe u

section SymPt

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

end SymPt

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

/-- The translation part of `π_J⁰`: `c = σ_*[Θ] - [Θ]`. -/
noncomputable def cTheta : PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  sigPic Fq F Ω hk (thetaK (kbar Fq Ω) (Fbar Fq F Ω)) - thetaK (kbar Fq Ω) (Fbar Fq F Ω)

set_option synthInstance.maxHeartbeats 100000 in
theorem cTheta_mem_Pic0K : cTheta Fq F Ω hk ∈ Pic0K (kbar Fq Ω) (Fbar Fq F Ω) := by
  rw [mem_Pic0K, cTheta, map_sub, degPicK_sigPic, sub_self]

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Hom =====
section

/-!
# S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects

Generic (JacComplete context): `ptW` (a `K`-point of `J` inside `jX0(D(φ u0))` comes from a `K`-point of
`S_g[1/u0][1/φ u0]`), `UJ W` (the dense open `fst⁻¹W ∩ snd⁻¹W ∩ μ⁻¹W` of `J × J`), and `isMonHom_of_cls`:
a map `ψ : J ⟶ J` acting on the classes of the `K`-points over a dense open `W` through an additive map `s`
is a homomorphism of group objects. For `J = J_{F-bar}`: **`isMonHom_piJ`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (ψ : Jac K F ⟶ Jac K F) (s : PicK K F ≃+ PicK K F) (W : (Jac K F).left.Opens)

theorem one_hom_of_mul_hom (h : μ ≫ ψ = (ψ ⊗ₘ ψ) ≫ μ) : η ≫ ψ = η := by
  have hx : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ ψ =
      ((1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ ψ) * ((1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ ψ) :=
    calc (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ ψ
        = ((1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) * 1) ≫ ψ := by rw [_root_.mul_one]
      _ = lift 1 1 ≫ μ ≫ ψ := by rw [CategoryTheory.Hom.mul_def, Category.assoc]
      _ = lift 1 1 ≫ (ψ ⊗ₘ ψ) ≫ μ := by rw [h]
      _ = _ := by rw [← Category.assoc, lift_map, CategoryTheory.Hom.mul_def]
  rw [MonObj.one_eq_one]
  exact (mul_left_cancel ((_root_.mul_one _).trans hx)).symm

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_All =====
section

/-!
# S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`

Generic: `exists_kpt_mem` (every nonempty open of `J` contains a `K`-point), `invMul a` (`x ↦ x⁻¹ * a`),
`cls_all` (a homomorphism acting through `s` on the classes of the `K`-points over a dense open does so everywhere).
For `J = J_{F-bar}`: **`jacPicEquiv_piJ_all`**, **`piBar_jacPicEquiv_piJ`** (review R4, through `Ψ : PicBar ≃+ PicK`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `x ↦ x⁻¹ * a` as a map `J ⟶ J`. -/
noncomputable def invMul (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : Jac K F ⟶ Jac K F :=
  (𝟙 (Jac K F))⁻¹ * (toUnit _ ≫ a)

theorem comp_invMul (a b : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : b ≫ invMul a = b⁻¹ * a := by
  rw [invMul, comp_mul_toUnit, GrpObj.comp_inv, Category.comp_id]

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end


