-- Prove2me | Definitions.Def_AlgebraicGeometry_ResolvedModelGlue
-- name    : AlgebraicGeometry_ResolvedModelGlue
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/67d926d2-d5be-5196-93cc-5fc4c7f17caf
-- title:
--   Gluing local resolutions at finitely many points of a scheme
-- statement:
--   Three input structures and the glued scheme they produce, all for schemes in universe $0$.
--
--   `GlueInput X N` is bare gluing data: points $x_n \in X$ indexed by $N$; an open $X^0 \subseteq X$ whose membership condition is exactly $y \in X^0 \iff y \neq x_n$ for all $n$; opens $U_n$ with $x_n \in U_n$ and $x_m \notin U_n$ for $m \neq n$; schemes $Y_n$ with morphisms $q_n : Y_n \to U_n$; and open immersions $j_n : U_n \cap X^0 \to Y_n$ over $U_n$, i.e. $j_n$ followed by $q_n$ is the inclusion $U_n \cap X^0 \subseteq U_n$. From these, `Y''` is the colimit of the wide span with base $U_n \cap X^0$ and legs $Y_n$, $X^0$ along $j_n$ and the inclusion, `glued` is the colimit of the wide span with base $X^0$ and legs the $Y''_n$, and `toDR : glued ⟶ X` is induced by $X^0 \hookrightarrow X$ and $q_n$ followed by $U_n \hookrightarrow X$. All structure maps are open immersions; `openCover` is the resulting cover of `glued` indexed by `Option N`. Under the hypothesis that a point of $Y_n$ whose image in $U_n$ lies in $X^0$ is in the image of $j_n$, the images of $\iota_{X^0}$ and $\iota_{Y_n}$ are the `toDR`-preimages of $X^0$ and $U_n$, so the squares over $X^0$ and over $U_n$ are cartesian; properness, flatness after composing to a base, local Noetherianity, reducedness, irreducibility and integrality of `glued`, and invertibility of `toDR` restricted to opens inside $X^0$, are deduced from the corresponding properties of the pieces, the irreducibility argument using that each $\mathrm{toDR}^{-1}\{x_n\}$ has empty interior.
--
--   `ChartInput X N` adds charts: schemes $S_n$ with opens $V^{\mathrm{c}}_n$, proper morphisms $\rho_n : \mathrm{Res}_n \to S_n$ that restrict to isomorphisms over $V^{\mathrm{c}}_n$ and whose preimage of the complement of $V^{\mathrm{c}}_n$ has empty interior, $\mathrm{Res}_n$ locally Noetherian; natural numbers $\mathrm{thick}(n) \ge 1$; étale $f_n : U_n \to S_n$ with $f_n(y) \in V^{\mathrm{c}}_n \iff y \neq x_n$ and a flatness/maximal-ideal/residue-field condition on the stalk map at $x_n$; and a base $B$ with $\pi_X : X \to B$, $\sigma_n : S_n \to B$, $f_n \sigma_n = \pi_X|_{U_n}$ and $\rho_n \sigma_n$ flat. It yields $Y_n := U_n \times_{S_n} \mathrm{Res}_n$ with $q_n$ the first projection (proper), $j_n$ from the inverse of the first projection of $U_n \cap X^0 \times_{U_n} Y_n$, a `GlueInput`, the required preimage condition, the flat second projection $g_n : Y_n \to \mathrm{Res}_n$, local Noetherianity of $Y_n$, and that $\{y : q_n(y) = x_n\}$ is the $g_n\rho_n$-preimage of the complement of $V^{\mathrm{c}}_n$ and has empty interior.
--
--   `RawChartInput` is the same data with $x$ injective and each $\{x_n\}$ closed, $N$ finite, $X^0$ defined as the complement of $\bigcup_n \{x_n\}$, and with $f_n$ replaced by a morphism $f_{0,n}$ on a possibly larger open $U_{0,n}$ that is only locally of finite presentation, the stalk condition being imposed at every point over $x_n$. Given opens $V_n$ around $x_n$ on which $V_n \hookrightarrow U_{0,n} \to S_n$ is étale, shrinking to the image of $V_n$ intersected with the complement of the other nodes produces a `ChartInput`; `hnbhd_of` derives the existence of such $V_n$ from a hypothesised criterion for étaleness near a point from flatness, generation of the maximal ideal and an isomorphism of residue fields, which is taken as an assumption rather than proved.
--
--   **Relation to Mathlib.** The gluing is performed with Mathlib's colimits of locally directed diagrams of open immersions of schemes (wide spans, `Scheme.IsLocallyDirected.openCover`) rather than with `Scheme.GlueData`; the three input structures, the glued scheme and the morphism to $X$ are the project's own.
--
--   **Where it is used.** The construction is the geometric step that replaces finitely many singular points of an integral model by prescribed local resolutions pulled back along étale charts to model surfaces, as needed for a resolved Deligne–Rapoport style model of a modular curve over the integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ResolvedModelGlue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue

structure GlueInput (X : Scheme.{0}) (N : Type) where

  x : N → X

  X0 : X.Opens
  mem_X0 : ∀ y : X, y ∈ X0 ↔ ∀ n, y ≠ x n

  U : N → X.Opens
  x_mem_U : ∀ n, x n ∈ U n
  x_not_mem_U : ∀ n m, m ≠ n → x m ∉ U n

  Y : N → Scheme.{0}
  q : ∀ n, Y n ⟶ (U n : Scheme.{0})

  j : ∀ n, ((U n ⊓ X0 : X.Opens) : Scheme.{0}) ⟶ Y n
  j_isOpenImmersion : ∀ n, IsOpenImmersion (j n)
  j_q : ∀ n, j n ≫ q n = X.homOfLE inf_le_left

attribute [instance] GlueInput.j_isOpenImmersion

namespace GlueInput

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

def F₁ (n : N) : WidePushoutShape Bool ⥤ Scheme.{0} :=
  WidePushoutShape.wideSpan ((D.U n ⊓ D.X0 : X.Opens) : Scheme.{0})
    (fun b => Bool.casesOn b (D.Y n) ((D.X0 : X.Opens) : Scheme.{0}))
    (fun b => match b with
      | true => X.homOfLE inf_le_right
      | false => D.j n)

instance F₁_isOpenImmersion (n : N) {i k : WidePushoutShape Bool} (f : i ⟶ k) :
    IsOpenImmersion ((D.F₁ n).map f) := by
  obtain - | b := f
  · change IsOpenImmersion (𝟙 _); infer_instance
  · cases b
    · change IsOpenImmersion (D.j n); infer_instance
    · change IsOpenImmersion (X.homOfLE (inf_le_right : D.U n ⊓ D.X0 ≤ D.X0)); infer_instance

def Y'' (n : N) : Scheme.{0} := colimit (D.F₁ n)

def toX'' (n : N) : D.Y'' n ⟶ X :=
  colimit.desc (D.F₁ n) (WidePushoutShape.mkCocone ((D.U n ⊓ D.X0).ι)
    (fun b => match b with
      | true => D.X0.ι
      | false => D.q n ≫ (D.U n).ι)
    (by
      rintro (_ | _)
      · show D.j n ≫ D.q n ≫ (D.U n).ι = (D.U n ⊓ D.X0).ι
        rw [← Category.assoc, D.j_q, Scheme.homOfLE_ι]
      · show X.homOfLE inf_le_right ≫ D.X0.ι = (D.U n ⊓ D.X0).ι
        rw [Scheme.homOfLE_ι]))

def ιX0'' (n : N) : ((D.X0 : X.Opens) : Scheme.{0}) ⟶ D.Y'' n := colimit.ι (D.F₁ n) (some true)

def ιY'' (n : N) : D.Y n ⟶ D.Y'' n := colimit.ι (D.F₁ n) (some false)

instance (n : N) : IsOpenImmersion (D.ιX0'' n) :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover (D.F₁ n)).f (some true)))
instance (n : N) : IsOpenImmersion (D.ιY'' n) :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover (D.F₁ n)).f (some false)))

@[reassoc (attr := simp)]
theorem ιX0''_toX'' (n : N) : D.ιX0'' n ≫ D.toX'' n = D.X0.ι := colimit.ι_desc _ _

@[reassoc (attr := simp)]
theorem ιY''_toX'' (n : N) : D.ιY'' n ≫ D.toX'' n = D.q n ≫ (D.U n).ι := colimit.ι_desc _ _

@[reassoc]
theorem homOfLE_ιX0'' (n : N) : X.homOfLE inf_le_right ≫ D.ιX0'' n = D.j n ≫ D.ιY'' n :=
  (colimit.w (D.F₁ n) (WidePushoutShape.Hom.init true)).trans
    (colimit.w (D.F₁ n) (WidePushoutShape.Hom.init false)).symm

def F₂ : WidePushoutShape N ⥤ Scheme.{0} :=
  WidePushoutShape.wideSpan ((D.X0 : X.Opens) : Scheme.{0}) (fun n => D.Y'' n) (fun n => D.ιX0'' n)

instance F₂_isOpenImmersion {i k : WidePushoutShape N} (f : i ⟶ k) : IsOpenImmersion (D.F₂.map f) := by
  obtain - | n := f
  · change IsOpenImmersion (𝟙 _); infer_instance
  · change IsOpenImmersion (D.ιX0'' n); infer_instance

def glued : Scheme.{0} := colimit D.F₂

def toDR : D.glued ⟶ X :=
  colimit.desc D.F₂ (WidePushoutShape.mkCocone D.X0.ι (fun n => D.toX'' n) (fun n => D.ιX0''_toX'' n))

def ιX0 : ((D.X0 : X.Opens) : Scheme.{0}) ⟶ D.glued := colimit.ι D.F₂ none

def ιY''glued (n : N) : D.Y'' n ⟶ D.glued := colimit.ι D.F₂ (some n)

def ιY (n : N) : D.Y n ⟶ D.glued := D.ιY'' n ≫ D.ιY''glued n

instance : IsOpenImmersion D.ιX0 :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover D.F₂).f none))
instance (n : N) : IsOpenImmersion (D.ιY''glued n) :=
  inferInstanceAs (IsOpenImmersion ((Scheme.IsLocallyDirected.openCover D.F₂).f (some n)))
instance (n : N) : IsOpenImmersion (D.ιY n) := by dsimp [ιY]; infer_instance

@[reassoc (attr := simp)]
theorem ιX0''_ιY''glued (n : N) : D.ιX0'' n ≫ D.ιY''glued n = D.ιX0 :=
  colimit.w D.F₂ (WidePushoutShape.Hom.init n)

@[reassoc (attr := simp)]
theorem ιX0_toDR : D.ιX0 ≫ D.toDR = D.X0.ι := colimit.ι_desc _ _

@[reassoc (attr := simp)]
theorem ιY''glued_toDR (n : N) : D.ιY''glued n ≫ D.toDR = D.toX'' n := colimit.ι_desc _ _

@[reassoc (attr := simp)]
theorem ιY_toDR (n : N) : D.ιY n ≫ D.toDR = D.q n ≫ (D.U n).ι := by
  simp [ιY]

@[reassoc]
theorem homOfLE_ιX0 (n : N) : X.homOfLE inf_le_right ≫ D.ιX0 = D.j n ≫ D.ιY n := by
  rw [← D.ιX0''_ιY''glued n, D.homOfLE_ιX0''_assoc n]; rfl

theorem ι_jointly_surjective (y : D.glued) :
    (∃ x0, D.ιX0.base x0 = y) ∨ ∃ n yn, (D.ιY n).base yn = y := by
  obtain ⟨(_ | n), yi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective D.F₂ y
  · exact Or.inl ⟨yi, rfl⟩
  · obtain ⟨(_ | b), z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (D.F₁ n) yi
    ·
      refine Or.inl ⟨(X.homOfLE inf_le_right).base z, ?_⟩
      have := congr($(D.ιX0''_ιY''glued n).base ((X.homOfLE inf_le_right).base z))
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      rw [← this]
      have h1 := congr($(colimit.w (D.F₁ n) (WidePushoutShape.Hom.init true)).base z)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
      exact congrArg _ h1
    · cases b
      · exact Or.inr ⟨n, z, rfl⟩
      · refine Or.inl ⟨z, ?_⟩
        have := congr($(D.ιX0''_ιY''glued n).base z)
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
        exact this.symm

theorem ιY_eq_ιX0_iff (n : N) (yn : D.Y n) (x0 : D.X0) :
    (D.ιY n).base yn = D.ιX0.base x0 ↔
      ∃ w : ↥(D.U n ⊓ D.X0), (D.j n).base w = yn ∧ (X.homOfLE inf_le_right).base w = x0 := by
  constructor
  · intro h

    have h2 : (colimit.ι D.F₂ (some n)).base ((D.ιY'' n).base yn) = (colimit.ι D.F₂ none).base x0 := h
    obtain ⟨k, fi, fj, w, hw1, hw2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff D.F₂).mp h2
    obtain - | k := k
    · obtain - | _ := fj
      obtain - | _ := fi

      change (D.ιX0'' n).base w = (D.ιY'' n).base yn at hw1
      change w = x0 at hw2
      subst hw2

      obtain ⟨k', fi', fj', w', hw1', hw2'⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (D.F₁ n)).mp hw1
      obtain - | b := k'
      · obtain - | _ := fi'
        obtain - | _ := fj'
        exact ⟨w', hw2', hw1'⟩
      ·
        obtain - | _ := fi'
        obtain - | _ := fj'
    ·
      obtain - | _ := fj
  · rintro ⟨w, rfl, rfl⟩
    have := congr($(D.homOfLE_ιX0 n).base w)
    simpa [Scheme.Hom.comp_base] using this.symm

def openCover : D.glued.OpenCover :=
  Scheme.Cover.mkOfCovers (Option N) (fun o => Option.casesOn o ((D.X0 : X.Opens) : Scheme.{0}) D.Y)
    (fun o => match o with
      | none => D.ιX0
      | some n => D.ιY n)
    (fun y => by
      rcases D.ι_jointly_surjective y with ⟨x0, hx0⟩ | ⟨n, yn, hyn⟩
      · exact ⟨none, x0, hx0⟩
      · exact ⟨some n, yn, hyn⟩)
    (by rintro (_ | n) <;> dsimp <;> infer_instance)

@[simp] theorem openCover_f_none : D.openCover.f none = D.ιX0 := rfl
@[simp] theorem openCover_f_some (n : N) : D.openCover.f (some n) = D.ιY n := rfl

variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

theorem range_ιY (n : N) : Set.range (D.ιY n).base = D.toDR.base ⁻¹' (D.U n : Set X) := by
  apply le_antisymm
  · rintro _ ⟨yn, rfl⟩
    have : D.toDR.base ((D.ιY n).base yn) = ((D.q n).base yn).1 := by
      have h := congr($(D.ιY_toDR n).base yn)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      exact h.trans (by simp)
    show D.toDR.base _ ∈ (D.U n : Set X)
    rw [this]; exact ((D.q n).base yn).2
  · intro y hy

    have key : ∀ x0 : D.X0, D.toDR.base (D.ιX0.base x0) ∈ (D.U n : Set X) →
        D.ιX0.base x0 ∈ Set.range (D.ιY n).base := by
      intro x0 hx0
      have h0 := congr($(D.ιX0_toDR).base x0)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h0
      rw [h0] at hx0
      have h0' : (D.X0.ι.base x0) = x0.1 := by simp
      rw [h0'] at hx0
      refine ⟨(D.j n).base ⟨x0.1, hx0, x0.2⟩, ?_⟩
      have := congr($(D.homOfLE_ιX0 n).base ⟨x0.1, hx0, x0.2⟩)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
      rw [← this]
      have happ : (X.homOfLE (inf_le_right : D.U n ⊓ D.X0 ≤ D.X0)).base ⟨x0.1, hx0, x0.2⟩ = x0 :=
        Subtype.ext (by simpa using congr($(X.homOfLE_ι (inf_le_right : D.U n ⊓ D.X0 ≤ D.X0)).base ⟨x0.1, hx0, x0.2⟩))
      rw [happ]
    rcases D.ι_jointly_surjective y with ⟨x0, rfl⟩ | ⟨m, ym, rfl⟩
    · exact key x0 hy
    · by_cases hmn : m = n
      · subst hmn; exact ⟨ym, rfl⟩
      ·
        have h1 : D.toDR.base ((D.ιY m).base ym) = ((D.q m).base ym).1 := by
          have h := congr($(D.ιY_toDR m).base ym)
          simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
          exact h.trans (by simp)
        have hX0 : ((D.q m).base ym).1 ∈ D.X0 := by
          rw [D.mem_X0]
          intro k hk
          have hkU : D.x k ∈ D.U m ∧ D.x k ∈ D.U n := by
            constructor
            · rw [← hk]; exact ((D.q m).base ym).2
            · rw [← hk]; show ((D.q m).base ym).1 ∈ (D.U n : Set X); rw [← h1]; exact hy
          by_cases hkm : k = m
          · subst hkm; exact D.x_not_mem_U n k hmn hkU.2
          · exact D.x_not_mem_U m k hkm hkU.1
        obtain ⟨w, hw⟩ := hq m ym hX0
        have h2 := congr($(D.homOfLE_ιX0 m).base w)
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
        rw [← hw, ← h2]
        apply key
        rw [h2, hw]; exact hy

theorem range_ιX0 : Set.range D.ιX0.base = D.toDR.base ⁻¹' (D.X0 : Set X) := by
  apply le_antisymm
  · rintro _ ⟨x0, rfl⟩
    have : D.toDR.base (D.ιX0.base x0) = x0.1 := by
      have h := congr($(D.ιX0_toDR).base x0)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      exact h.trans (by simp)
    show D.toDR.base _ ∈ (D.X0 : Set X)
    rw [this]; exact x0.2
  · intro y hy
    rcases D.ι_jointly_surjective y with ⟨x0, rfl⟩ | ⟨m, ym, rfl⟩
    · exact ⟨x0, rfl⟩
    · have h1 : D.toDR.base ((D.ιY m).base ym) = ((D.q m).base ym).1 := by
        have h := congr($(D.ιY_toDR m).base ym)
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
        exact h.trans (by simp)
      have hX0 : ((D.q m).base ym).1 ∈ D.X0 := by
        show ((D.q m).base ym).1 ∈ (D.X0 : Set X); rw [← h1]; exact hy
      obtain ⟨w, hw⟩ := hq m ym hX0
      refine ⟨(X.homOfLE inf_le_right).base w, ?_⟩
      have h2 := congr($(D.homOfLE_ιX0 m).base w)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
      rw [h2, hw]

theorem opensRange_ιY (n : N) : (D.ιY n).opensRange = D.toDR ⁻¹ᵁ (D.U n) :=
  TopologicalSpace.Opens.ext (D.range_ιY hq n)

theorem opensRange_ιX0 : D.ιX0.opensRange = D.toDR ⁻¹ᵁ D.X0 :=
  TopologicalSpace.Opens.ext (D.range_ιX0 hq)

theorem isPullback_ιY (n : N) : IsPullback (D.q n) (D.ιY n) (D.U n).ι D.toDR :=
  IsOpenImmersion.isPullback _ _ _ _ (D.ιY_toDR n)
    (by rw [Scheme.Opens.opensRange_ι]; exact (D.opensRange_ιY hq n).symm)

theorem isPullback_ιX0 : IsPullback (𝟙 _) D.ιX0 D.X0.ι D.toDR :=
  IsOpenImmersion.isPullback _ _ _ _ (by rw [Category.id_comp, D.ιX0_toDR])
    (by rw [Scheme.Opens.opensRange_ι]; exact (D.opensRange_ιX0 hq).symm)

end GlueInput

end V3Glue

namespace V3Glue

structure ChartInput (X : Scheme.{0}) (N : Type) where

  x : N → X
  X0 : X.Opens
  mem_X0 : ∀ y : X, y ∈ X0 ↔ ∀ n, y ≠ x n

  S : N → Scheme.{0}
  Vc : ∀ n, (S n).Opens
  Res : N → Scheme.{0}
  ρ : ∀ n, Res n ⟶ S n

  isIso_ρ_restrict : ∀ n, IsIso (ρ n ∣_ Vc n)

  isProper_ρ : ∀ n, IsProper (ρ n)

  thick : N → ℕ
  one_le_thick : ∀ n, 1 ≤ thick n

  U : N → X.Opens
  x_mem_U : ∀ n, x n ∈ U n
  x_not_mem_U : ∀ n m, m ≠ n → x m ∉ U n
  f : ∀ n, ((U n : X.Opens) : Scheme.{0}) ⟶ S n

  f_mem_Vc_iff : ∀ n (y : U n), (f n).base y ∈ Vc n ↔ (y : X) ≠ x n

  f_etale : ∀ n, Etale (f n)

  f_node : ∀ n, ((f n).stalkMap ⟨x n, x_mem_U n⟩).hom.Flat ∧
    Ideal.map ((f n).stalkMap ⟨x n, x_mem_U n⟩).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
    IsIso ((f n).residueFieldMap ⟨x n, x_mem_U n⟩)

  B : Scheme.{0}
  πX : X ⟶ B
  σ : ∀ n, S n ⟶ B
  f_over : ∀ n, f n ≫ σ n = (U n).ι ≫ πX

  flat_ρ_σ : ∀ n, Flat (ρ n ≫ σ n)
  isLocallyNoetherian_Res : ∀ n, IsLocallyNoetherian (Res n)

  interior_preimage_vertex : ∀ n, interior ((ρ n).base ⁻¹' (Vc n : Set (S n))ᶜ) = ∅

attribute [instance] ChartInput.isIso_ρ_restrict ChartInput.isProper_ρ ChartInput.f_etale
  ChartInput.flat_ρ_σ ChartInput.isLocallyNoetherian_Res

namespace ChartInput

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

instance f_flat (n : N) : Flat (C.f n) := ((Etale.iff_flat_and_formallyUnramified).mp (C.f_etale n)).1

instance f_lfp (n : N) : LocallyOfFinitePresentation (C.f n) := ((Etale.iff_flat_and_formallyUnramified).mp (C.f_etale n)).2.2

theorem f_res (n : N) : IsIso ((C.f n).residueFieldMap ⟨C.x n, C.x_mem_U n⟩) := (C.f_node n).2.2

def Y (n : N) : Scheme.{0} := pullback (C.f n) (C.ρ n)

def q (n : N) : C.Y n ⟶ (C.U n : X.Opens) := pullback.fst (C.f n) (C.ρ n)

instance (n : N) : IsProper (C.q n) :=
  MorphismProperty.pullback_fst _ _ inferInstance

abbrev a (n : N) : ((C.U n ⊓ C.X0 : X.Opens) : Scheme.{0}) ⟶ (C.U n : X.Opens) := X.homOfLE inf_le_left

theorem range_a_f_subset (n : N) :
    Set.range (C.a n ≫ C.f n).base ⊆ Set.range (C.Vc n).ι.base := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  show (C.f n).base ((C.a n).base w) ∈ (C.Vc n : Set (C.S n))
  rw [SetLike.mem_coe, C.f_mem_Vc_iff]
  have hw : ((C.a n).base w).1 = w.1 := by
    simpa using congr($(X.homOfLE_ι (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n)).base w)
  rw [hw]
  exact ((C.mem_X0 _).mp w.2.2) n

def l (n : N) : ((C.U n ⊓ C.X0 : X.Opens) : Scheme.{0}) ⟶ (C.Vc n : Scheme.{0}) :=
  IsOpenImmersion.lift (C.Vc n).ι (C.a n ≫ C.f n) (C.range_a_f_subset n)

@[reassoc (attr := simp)]
theorem l_ι (n : N) : C.l n ≫ (C.Vc n).ι = C.a n ≫ C.f n := IsOpenImmersion.lift_fac _ _ _

instance isIso_pullback_fst_ι_ρ (n : N) : IsIso (pullback.fst (C.Vc n).ι (C.ρ n)) := by
  have : IsIso (pullback.snd (C.ρ n) (C.Vc n).ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have : pullback.fst (C.Vc n).ι (C.ρ n) = (pullbackSymmetry _ _).hom ≫ pullback.snd (C.ρ n) (C.Vc n).ι :=
    (pullbackSymmetry_hom_comp_snd _ _).symm
  rw [this]; infer_instance

instance isIso_pullback_fst_a_q (n : N) : IsIso (pullback.fst (C.a n) (C.q n)) := by

  let e₁ : pullback (C.a n) (C.q n) ≅ pullback (C.a n ≫ C.f n) (C.ρ n) :=
    pullbackRightPullbackFstIso (C.f n) (C.ρ n) (C.a n)
  let e₂ : pullback (C.a n ≫ C.f n) (C.ρ n) ≅ pullback (C.l n ≫ (C.Vc n).ι) (C.ρ n) :=
    pullback.congrHom (C.l_ι n).symm rfl
  let e₃ : pullback (C.l n ≫ (C.Vc n).ι) (C.ρ n) ≅ pullback (C.l n) (pullback.fst (C.Vc n).ι (C.ρ n)) :=
    (pullbackRightPullbackFstIso ((C.Vc n).ι) (C.ρ n) (C.l n)).symm
  have h3 : pullback.fst (C.l n ≫ (C.Vc n).ι) (C.ρ n) =
      e₃.hom ≫ pullback.fst (C.l n) (pullback.fst (C.Vc n).ι (C.ρ n)) := by
    simp only [e₃, Iso.symm_hom, pullbackRightPullbackFstIso_inv_fst]
  have h2 : pullback.fst (C.a n ≫ C.f n) (C.ρ n) = e₂.hom ≫ pullback.fst (C.l n ≫ (C.Vc n).ι) (C.ρ n) := by
    simp only [e₂, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  have h1 : pullback.fst (C.a n) (C.q n) = e₁.hom ≫ pullback.fst (C.a n ≫ C.f n) (C.ρ n) := by
    simp only [e₁, q]
    exact (pullbackRightPullbackFstIso_hom_fst _ _ _).symm
  rw [h1, h2, h3]
  infer_instance

def j (n : N) : ((C.U n ⊓ C.X0 : X.Opens) : Scheme.{0}) ⟶ C.Y n :=
  inv (pullback.fst (C.a n) (C.q n)) ≫ pullback.snd (C.a n) (C.q n)

instance (n : N) : IsOpenImmersion (C.j n) := by
  dsimp [j]; infer_instance

theorem j_q (n : N) : C.j n ≫ C.q n = X.homOfLE inf_le_left := by
  simp [j, ← pullback.condition]

def toGlueInput : GlueInput X N where
  x := C.x
  X0 := C.X0
  mem_X0 := C.mem_X0
  U := C.U
  x_mem_U := C.x_mem_U
  x_not_mem_U := C.x_not_mem_U
  Y := C.Y
  q := C.q
  j := C.j
  j_isOpenImmersion := inferInstance
  j_q := C.j_q

theorem hq (n : N) (y : C.Y n) (hy : ((C.q n).base y).1 ∈ C.X0) : y ∈ Set.range (C.j n).base := by
  have hw : (X.homOfLE (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n)).base ⟨((C.q n).base y).1, ((C.q n).base y).2, hy⟩ = (C.q n).base y :=
    Subtype.ext (by
      simpa using congr($(X.homOfLE_ι (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n)).base ⟨((C.q n).base y).1, ((C.q n).base y).2, hy⟩))
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.a n) (g := C.q n) _ y hw
  refine ⟨(pullback.fst (C.a n) (C.q n)).base z, ?_⟩
  rw [← hz2]
  show (pullback.snd (C.a n) (C.q n)).base _ = _
  have := congr($(IsIso.hom_inv_id (pullback.fst (C.a n) (C.q n))).base z)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] at this
  show (pullback.snd (C.a n) (C.q n)).base ((inv (pullback.fst (C.a n) (C.q n))).base ((pullback.fst (C.a n) (C.q n)).base z)) = _
  rw [this]

def g (n : N) : C.Y n ⟶ C.Res n := pullback.snd (C.f n) (C.ρ n)

instance (n : N) : Flat (C.g n) := MorphismProperty.pullback_snd _ _ inferInstance
instance (n : N) : LocallyOfFinitePresentation (C.g n) := MorphismProperty.pullback_snd _ _ inferInstance

@[reassoc]
theorem q_f (n : N) : C.q n ≫ C.f n = C.g n ≫ C.ρ n := pullback.condition

instance isLocallyNoetherian_Y (n : N) : IsLocallyNoetherian (C.Y n) :=
  LocallyOfFiniteType.isLocallyNoetherian (C.g n)

def toB (n : N) : C.Y n ⟶ C.B := C.g n ≫ C.ρ n ≫ C.σ n

theorem toB_eq (n : N) : C.toB n = C.q n ≫ (C.U n).ι ≫ C.πX := by
  rw [toB, ← C.f_over, ← Category.assoc, ← C.q_f, Category.assoc]

instance flat_toB (n : N) : Flat (C.toB n) := by
  dsimp [toB]; infer_instance

theorem flat_q_ι_πX (n : N) : Flat (C.q n ≫ (C.U n).ι ≫ C.πX) := C.toB_eq n ▸ C.flat_toB n

theorem setOf_q_eq (n : N) : {y : C.Y n | ((C.q n).base y).1 = C.x n} = (C.g n).base ⁻¹' ((C.ρ n).base ⁻¹' (C.Vc n : Set (C.S n))ᶜ) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
  have h := congr($(C.q_f n).base y)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  rw [← h, C.f_mem_Vc_iff, not_not]

theorem interior_setOf_q_eq (n : N) : interior {y : C.Y n | ((C.q n).base y).1 = C.x n} = ∅ := by
  rw [C.setOf_q_eq n, ← Set.subset_empty_iff]
  intro y hy
  have hopen : IsOpenMap (C.g n).base := (C.g n).isOpenMap
  have h1 : (C.g n).base '' interior ((C.g n).base ⁻¹' ((C.ρ n).base ⁻¹' (C.Vc n : Set _)ᶜ)) ⊆
      interior ((C.ρ n).base ⁻¹' (C.Vc n : Set _)ᶜ) :=
    interior_maximal ((Set.image_mono interior_subset).trans (Set.image_preimage_subset _ _)) (hopen _ isOpen_interior)
  rw [C.interior_preimage_vertex] at h1
  exact h1 ⟨y, hy, rfl⟩

end ChartInput

structure RawChartInput (X : Scheme.{0}) (N : Type) where
  x : N → X
  x_injective : Function.Injective x
  isClosed_x : ∀ n, IsClosed ({x n} : Set X)
  S : N → Scheme.{0}
  Vc : ∀ n, (S n).Opens
  Res : N → Scheme.{0}
  ρ : ∀ n, Res n ⟶ S n
  isIso_ρ_restrict : ∀ n, IsIso (ρ n ∣_ Vc n)
  isProper_ρ : ∀ n, IsProper (ρ n)
  thick : N → ℕ
  one_le_thick : ∀ n, 1 ≤ thick n
  U₀ : N → X.Opens
  x_mem_U₀ : ∀ n, x n ∈ U₀ n
  f₀ : ∀ n, ((U₀ n : X.Opens) : Scheme.{0}) ⟶ S n
  f₀_mem_Vc_iff : ∀ n (y : U₀ n), (f₀ n).base y ∈ Vc n ↔ (y : X) ≠ x n

  f₀_node : ∀ n (y : U₀ n), (y : X) = x n →
    ((f₀ n).stalkMap y).hom.Flat ∧
      Ideal.map ((f₀ n).stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      IsIso ((f₀ n).residueFieldMap y)

  f₀_lfp : ∀ n, LocallyOfFinitePresentation (f₀ n)
  B : Scheme.{0}
  πX : X ⟶ B
  σ : ∀ n, S n ⟶ B
  f₀_over : ∀ n, f₀ n ≫ σ n = (U₀ n).ι ≫ πX
  flat_ρ_σ : ∀ n, Flat (ρ n ≫ σ n)
  isLocallyNoetherian_Res : ∀ n, IsLocallyNoetherian (Res n)
  interior_preimage_vertex : ∀ n, interior ((ρ n).base ⁻¹' (Vc n : Set (S n))ᶜ) = ∅

attribute [instance] RawChartInput.isIso_ρ_restrict RawChartInput.isProper_ρ RawChartInput.f₀_lfp
  RawChartInput.flat_ρ_σ RawChartInput.isLocallyNoetherian_Res

namespace RawChartInput

variable {X : Scheme.{0}} {N : Type} [Finite N] (R : RawChartInput X N)

def X0 : X.Opens := ⟨(⋃ n, ({R.x n} : Set X))ᶜ, (isClosed_iUnion_of_finite R.isClosed_x).isOpen_compl⟩

theorem mem_X0 (y : X) : y ∈ R.X0 ↔ ∀ n, y ≠ R.x n := by
  simp only [X0, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff, Set.mem_iUnion,
    Set.mem_singleton_iff, not_exists]

def avoid (n : N) : X.Opens :=
  ⟨(⋃ m : {m : N // m ≠ n}, ({R.x m.1} : Set X))ᶜ,
    (isClosed_iUnion_of_finite fun m : {m : N // m ≠ n} => R.isClosed_x m.1).isOpen_compl⟩

theorem mem_avoid (n : N) (y : X) : y ∈ R.avoid n ↔ ∀ m, m ≠ n → y ≠ R.x m := by
  simp only [avoid, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff, Set.mem_iUnion,
    Set.mem_singleton_iff, not_exists]
  exact ⟨fun h m hm => h ⟨m, hm⟩, fun h m => h m.1 m.2⟩

theorem node_comp {V W S : Scheme.{0}} (ι : V ⟶ W) [IsOpenImmersion ι] (f : W ⟶ S) (v : V)
    (h : (f.stalkMap (ι.base v)).hom.Flat ∧
      Ideal.map (f.stalkMap (ι.base v)).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      IsIso (f.residueFieldMap (ι.base v))) :
    ((ι ≫ f).stalkMap v).hom.Flat ∧
      Ideal.map ((ι ≫ f).stalkMap v).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      IsIso ((ι ≫ f).residueFieldMap v) := by
  obtain ⟨hflat, hmax, hres⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Flat.comp hflat (RingHom.Flat.of_bijective (asIso (ι.stalkMap v)).commRingCatIsoToRingEquiv.bijective)
  · rw [Scheme.Hom.stalkMap_comp]
    change Ideal.map ((ι.stalkMap v).hom.comp (f.stalkMap (ι.base v)).hom)
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base (ι.base v)))) = _
    rw [← Ideal.map_map, hmax]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ (asIso (ι.stalkMap v)).commRingCatIsoToRingEquiv.surjective
  · rw [Scheme.residueFieldMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hres inferInstance

variable (hnbhd : ∀ n, ∃ V : ((R.U₀ n : X.Opens) : Scheme.{0}).Opens,
  (⟨R.x n, R.x_mem_U₀ n⟩ : R.U₀ n) ∈ V ∧ Etale (V.ι ≫ R.f₀ n))

def V (n : N) : ((R.U₀ n : X.Opens) : Scheme.{0}).Opens := (hnbhd n).choose

theorem x_mem_V (n : N) : (⟨R.x n, R.x_mem_U₀ n⟩ : R.U₀ n) ∈ R.V hnbhd n := (hnbhd n).choose_spec.1

theorem etale_V_ι_f₀ (n : N) : Etale ((R.V hnbhd n).ι ≫ R.f₀ n) := (hnbhd n).choose_spec.2

abbrev U₁ (n : N) : X.Opens := (R.U₀ n).ι ''ᵁ R.V hnbhd n

theorem U₁_le (n : N) : R.U₁ hnbhd n ≤ R.U₀ n := (R.U₀ n).ι_image_le _

theorem x_mem_U₁ (n : N) : R.x n ∈ R.U₁ hnbhd n := ⟨⟨R.x n, R.x_mem_U₀ n⟩, R.x_mem_V hnbhd n, rfl⟩

abbrev U (n : N) : X.Opens := R.U₁ hnbhd n ⊓ R.avoid n

theorem U_le (n : N) : R.U hnbhd n ≤ R.U₀ n := inf_le_left.trans (R.U₁_le hnbhd n)

theorem etale_homOfLE_U₁_f₀ (n : N) : Etale (X.homOfLE (R.U₁_le hnbhd n) ≫ R.f₀ n) := by
  have hfac : X.homOfLE (R.U₁_le hnbhd n) = ((R.U₀ n).ι.isoImage (R.V hnbhd n)).inv ≫ (R.V hnbhd n).ι := by
    rw [← cancel_mono (R.U₀ n).ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_inv_ι]
  rw [hfac]
  simp only [Category.assoc]
  haveI := R.etale_V_ι_f₀ hnbhd n
  infer_instance

theorem etale_homOfLE_f₀ (n : N) : Etale (X.homOfLE (R.U_le hnbhd n) ≫ R.f₀ n) := by
  have hfac : X.homOfLE (R.U_le hnbhd n) =
      X.homOfLE (inf_le_left : R.U hnbhd n ≤ R.U₁ hnbhd n) ≫ X.homOfLE (R.U₁_le hnbhd n) :=
    (Scheme.homOfLE_homOfLE X _ _).symm
  rw [hfac]
  simp only [Category.assoc]
  haveI := R.etale_homOfLE_U₁_f₀ hnbhd n
  infer_instance

theorem x_mem_U (n : N) : R.x n ∈ R.U hnbhd n :=
  ⟨R.x_mem_U₁ hnbhd n, (R.mem_avoid n _).mpr fun m hm h => hm (R.x_injective h.symm)⟩

theorem node_homOfLE_f₀ (n : N) (y : R.U hnbhd n) (hy : (y : X) = R.x n) :
    ((X.homOfLE (R.U_le hnbhd n) ≫ R.f₀ n).stalkMap y).hom.Flat ∧
      Ideal.map ((X.homOfLE (R.U_le hnbhd n) ≫ R.f₀ n).stalkMap y).hom (IsLocalRing.maximalIdeal _) =
        IsLocalRing.maximalIdeal _ ∧
      IsIso ((X.homOfLE (R.U_le hnbhd n) ≫ R.f₀ n).residueFieldMap y) := by
  have hy0 : ((X.homOfLE (R.U_le hnbhd n)).base y).1 = R.x n := by
    rw [← hy]; simpa using congr($(X.homOfLE_ι (R.U_le hnbhd n)).base y)
  exact node_comp (X.homOfLE (R.U_le hnbhd n)) (R.f₀ n) y (R.f₀_node n _ hy0)

def toChartInput : ChartInput X N where
  x := R.x
  X0 := R.X0
  mem_X0 := R.mem_X0
  S := R.S
  Vc := R.Vc
  Res := R.Res
  ρ := R.ρ
  isIso_ρ_restrict := inferInstance
  isProper_ρ := inferInstance
  thick := R.thick
  one_le_thick := R.one_le_thick
  U := R.U hnbhd
  x_mem_U := R.x_mem_U hnbhd
  x_not_mem_U n m hmn h := (R.mem_avoid n _).mp h.2 m hmn rfl
  f n := X.homOfLE (R.U_le hnbhd n) ≫ R.f₀ n
  f_mem_Vc_iff n y := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, R.f₀_mem_Vc_iff]
    have : ((X.homOfLE (R.U_le hnbhd n)).base y).1 = y.1 := by
      simpa using congr($(X.homOfLE_ι (R.U_le hnbhd n)).base y)
    exact Iff.of_eq (congrArg (fun z : X => z ≠ R.x n) this)
  f_etale n := R.etale_homOfLE_f₀ hnbhd n
  f_node n := R.node_homOfLE_f₀ hnbhd n ⟨R.x n, R.x_mem_U hnbhd n⟩ rfl
  B := R.B
  πX := R.πX
  σ := R.σ
  f_over n := by rw [Category.assoc, R.f₀_over, ← Category.assoc, Scheme.homOfLE_ι]
  flat_ρ_σ := inferInstance
  isLocallyNoetherian_Res := inferInstance
  interior_preimage_vertex := R.interior_preimage_vertex

omit [Finite N] in

theorem hnbhd_of
    (ET : ∀ {U S : Scheme.{0}} (f : U ⟶ S) [LocallyOfFinitePresentation f] (x : U),
      (f.stalkMap x).hom.Flat →
      Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f.base x))) =
        IsLocalRing.maximalIdeal (U.presheaf.stalk x) →
      ∀ [IsIso (f.residueFieldMap x)], ∃ V : U.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) :
    ∀ n, ∃ V : ((R.U₀ n : X.Opens) : Scheme.{0}).Opens, (⟨R.x n, R.x_mem_U₀ n⟩ : R.U₀ n) ∈ V ∧ Etale (V.ι ≫ R.f₀ n) := by
  intro n
  obtain ⟨hflat, hmax, hres⟩ := R.f₀_node n ⟨R.x n, R.x_mem_U₀ n⟩ rfl
  exact ET (R.f₀ n) ⟨R.x n, R.x_mem_U₀ n⟩ hflat hmax

theorem etale_toChartInput_f (n : N) : Etale ((R.toChartInput hnbhd).f n) := R.etale_homOfLE_f₀ hnbhd n

theorem toChartInput_f_node (n : N) (y : (R.toChartInput hnbhd).U n) (hy : (y : X) = R.x n) :
    (((R.toChartInput hnbhd).f n).stalkMap y).hom.Flat ∧
      Ideal.map (((R.toChartInput hnbhd).f n).stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      IsIso (((R.toChartInput hnbhd).f n).residueFieldMap y) :=
  R.node_homOfLE_f₀ hnbhd n y hy

end RawChartInput

end V3Glue

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

omit D in

theorem prop_morphismRestrict_of_isPullback {P : MorphismProperty Scheme.{0}} [P.RespectsIso]
    {V Y : Scheme.{0}} {U : X.Opens} {g : V ⟶ (U : Scheme.{0})} {i : V ⟶ Y} {f : Y ⟶ X}
    (h : IsPullback g i U.ι f) (hg : P g) : P (f ∣_ U) := by
  have h' := isPullback_morphismRestrict f U
  have he : (h.isoIsPullback _ _ h').hom ≫ (f ∣_ U) = g := IsPullback.isoIsPullback_hom_fst _ _ _ _
  rw [← he] at hg
  exact (P.cancel_left_of_respectsIso (h.isoIsPullback _ _ h').hom (f ∣_ U)).mp hg

theorem iSup_cover_eq_top : (⨆ o : Option N, o.elim D.X0 D.U) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  rw [TopologicalSpace.Opens.mem_iSup]
  by_cases hy : y ∈ D.X0
  · exact ⟨none, hy⟩
  · rw [D.mem_X0] at hy
    push Not at hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨some n, D.x_mem_U n⟩

variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

theorem isProper_toDR (hproper : ∀ n, IsProper (D.q n)) : IsProper D.toDR := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top _ D.iSup_cover_eq_top
  rintro (_ | n)
  · exact prop_morphismRestrict_of_isPullback (P := @IsProper) (D.isPullback_ιX0 hq) (MorphismProperty.id_mem _ _)
  · exact prop_morphismRestrict_of_isPullback (P := @IsProper) (D.isPullback_ιY hq n) (hproper n)

theorem prop_toDR_of_forall {P : MorphismProperty Scheme.{0}} [IsZariskiLocalAtTarget P] [P.ContainsIdentities]
    (hP : ∀ n, P (D.q n)) : P D.toDR := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top _ D.iSup_cover_eq_top
  rintro (_ | n)
  · exact prop_morphismRestrict_of_isPullback (D.isPullback_ιX0 hq) (P.id_mem _)
  · exact prop_morphismRestrict_of_isPullback (D.isPullback_ιY hq n) (hP n)

theorem isPullback_of_le_X0 {V : X.Opens} (hV : V ≤ D.X0) :
    IsPullback (𝟙 _) (X.homOfLE hV ≫ D.ιX0) V.ι D.toDR := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by rw [Category.id_comp, Category.assoc, D.ιX0_toDR, Scheme.homOfLE_ι]) ?_
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Opens.opensRange_ι, Scheme.Hom.coe_opensRange]
  apply le_antisymm
  · intro y hy
    have hy' : y ∈ D.toDR.base ⁻¹' (D.X0 : Set X) := hV hy
    rw [← D.range_ιX0 hq] at hy'
    obtain ⟨x0, rfl⟩ := hy'
    have hx0 : D.toDR.base (D.ιX0.base x0) = x0.1 := by
      have h := congr($(D.ιX0_toDR).base x0)
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
      exact h.trans (by simp)
    have hxV : x0.1 ∈ V := by
      have : D.toDR.base (D.ιX0.base x0) ∈ (V : Set X) := hy
      rwa [hx0] at this
    refine ⟨⟨x0.1, hxV⟩, ?_⟩
    show (X.homOfLE hV ≫ D.ιX0).base _ = _
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    congr 1
    exact Subtype.ext (by simpa using congr($(X.homOfLE_ι hV).base ⟨x0.1, hxV⟩))
  · rintro _ ⟨v, rfl⟩
    show D.toDR.base ((X.homOfLE hV ≫ D.ιX0).base v) ∈ (V : Set X)
    have h := congr($(D.ιX0_toDR).base ((X.homOfLE hV).base v))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h ⊢
    rw [h]
    have h2 := congr($(X.homOfLE_ι hV).base v)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    rw [h2]
    exact v.2

theorem isIso_toDR_restrict {V : X.Opens} (hV : V ≤ D.X0) : IsIso (D.toDR ∣_ V) := by
  have := prop_morphismRestrict_of_isPullback (P := MorphismProperty.isomorphisms Scheme.{0})
    (D.isPullback_of_le_X0 hq hV) (MorphismProperty.isomorphisms.infer_property _)
  exact this

omit hq in

theorem flat_toDR_comp {S : Scheme.{0}} (π : X ⟶ S) [Flat π] (hY : ∀ n, Flat (D.q n ≫ (D.U n).ι ≫ π)) :
    Flat (D.toDR ≫ π) := by
  apply IsZariskiLocalAtSource.of_openCover D.openCover
  rintro (_ | n)
  · change Flat (D.ιX0 ≫ D.toDR ≫ π)
    rw [D.ιX0_toDR_assoc]
    exact MorphismProperty.comp_mem @Flat _ _ inferInstance inferInstance
  · change Flat (D.ιY n ≫ D.toDR ≫ π)
    rw [D.ιY_toDR_assoc]
    exact hY n

omit hq in

theorem propSource_toDR_comp {P : MorphismProperty Scheme.{0}} [IsZariskiLocalAtSource P] {S : Scheme.{0}} (π : X ⟶ S)
    (h0 : P (D.X0.ι ≫ π)) (hY : ∀ n, P (D.q n ≫ (D.U n).ι ≫ π)) : P (D.toDR ≫ π) := by
  apply IsZariskiLocalAtSource.of_openCover D.openCover
  rintro (_ | n)
  · change P (D.ιX0 ≫ D.toDR ≫ π)
    rw [D.ιX0_toDR_assoc]; exact h0
  · change P (D.ιY n ≫ D.toDR ≫ π)
    rw [D.ιY_toDR_assoc]; exact hY n

theorem isProper_toDR_comp {S : Scheme.{0}} (π : X ⟶ S) [IsProper π] (hproper : ∀ n, IsProper (D.q n)) :
    IsProper (D.toDR ≫ π) := by
  haveI := D.isProper_toDR hq hproper
  infer_instance

omit hq in

theorem isLocallyNoetherian_glued [IsLocallyNoetherian X] (hY : ∀ n, IsLocallyNoetherian (D.Y n)) :
    IsLocallyNoetherian D.glued := by
  refine (isLocallyNoetherian_iff_openCover D.openCover).mpr ?_
  rintro (_ | n)
  · show IsLocallyNoetherian (D.X0 : Scheme.{0}); infer_instance
  · show IsLocallyNoetherian (D.Y n); exact hY n

omit hq in

theorem isReduced_glued [IsReduced X] (hY : ∀ n, IsReduced (D.Y n)) : IsReduced D.glued := by
  haveI : ∀ i, IsReduced (D.openCover.X i) := by
    rintro (_ | n)
    · show IsReduced (D.X0 : Scheme.{0}); infer_instance
    · show IsReduced (D.Y n); exact hY n
  exact IsReduced.of_openCover _ D.openCover

end V3Glue.GlueInput

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)

omit D in

theorem interior_iUnion_eq_empty_of_isClosed {T : Type*} [TopologicalSpace T] {ι : Type*} [Fintype ι]
    (s : ι → Set T) (hc : ∀ i, IsClosed (s i)) (he : ∀ i, interior (s i) = ∅) :
    interior (⋃ i, s i) = ∅ := by
  classical
  have key : ∀ F : Finset ι, interior (⋃ i ∈ F, s i) = ∅ := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp
    | insert a F ha ih =>
      rw [Finset.set_biUnion_insert, Set.union_comm,
        interior_union_isClosed_of_interior_empty (isClosed_biUnion_finset fun i _ => hc i) (he a), ih]
  have h := key Finset.univ
  simpa using h

variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

theorem range_ιY_diff_range_ιX0 (n : N) :
    Set.range (D.ιY n).base \ Set.range D.ιX0.base = D.toDR.base ⁻¹' {D.x n} := by
  rw [D.range_ιY hq n, D.range_ιX0 hq, ← Set.preimage_diff]
  congr 1
  ext z
  simp only [Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzU, hzX0⟩
    rw [D.mem_X0] at hzX0
    push Not at hzX0
    obtain ⟨m, rfl⟩ := hzX0
    by_contra hmn
    exact D.x_not_mem_U n m (fun h => hmn (congrArg D.x h)) hzU
  · rintro rfl
    refine ⟨D.x_mem_U n, fun h => ?_⟩
    rw [D.mem_X0] at h
    exact h n rfl

theorem closure_range_ιX0_eq_univ [Fintype N] (hx : ∀ n, IsClosed ({D.x n} : Set X))
    (hE : ∀ n, interior (D.toDR.base ⁻¹' {D.x n}) = ∅) :
    closure (Set.range D.ιX0.base) = Set.univ := by
  by_contra hne
  have hW : ((closure (Set.range D.ιX0.base))ᶜ).Nonempty := Set.nonempty_compl.mpr hne
  have hsub : (closure (Set.range D.ιX0.base))ᶜ ⊆ ⋃ n, D.toDR.base ⁻¹' {D.x n} := by
    intro y hy
    have hy' : y ∉ Set.range D.ιX0.base := fun h => hy (subset_closure h)
    rw [D.range_ιX0 hq] at hy'
    have h2 : ¬ ∀ n, D.toDR.base y ≠ D.x n := by rw [← D.mem_X0]; exact hy'
    push Not at h2
    obtain ⟨n, hn⟩ := h2
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hint : interior (⋃ n, D.toDR.base ⁻¹' {D.x n}) = ∅ :=
    interior_iUnion_eq_empty_of_isClosed _ (fun n => (hx n).preimage D.toDR.continuous) hE
  have h3 : (closure (Set.range D.ιX0.base))ᶜ ⊆ interior (⋃ n, D.toDR.base ⁻¹' {D.x n}) :=
    interior_maximal hsub isClosed_closure.isOpen_compl
  rw [hint, Set.subset_empty_iff] at h3
  exact hW.ne_empty h3

theorem irreducibleSpace_glued [IrreducibleSpace X] [Nonempty D.X0] [Fintype N]
    (hx : ∀ n, IsClosed ({D.x n} : Set X)) (hE : ∀ n, interior (D.toDR.base ⁻¹' {D.x n}) = ∅) :
    IrreducibleSpace D.glued := by
  haveI : IrreducibleSpace (D.X0 : Scheme.{0}) := by
    have h : IsIrreducible ((D.X0 : Set X)) :=
      ⟨let ⟨x⟩ := ‹Nonempty D.X0›; ⟨x.1, x.2⟩,
        (IrreducibleSpace.isIrreducible_univ X).2.open_subset D.X0.2 (Set.subset_univ _)⟩
    exact (Subtype.irreducibleSpace h)
  have hirr : IsIrreducible (Set.range D.ιX0.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ D.ιX0.continuous.continuousOn
  have huniv : IsIrreducible (Set.univ : Set D.glued) := by
    rw [← D.closure_range_ιX0_eq_univ hq hx hE]
    exact hirr.closure
  exact { isPreirreducible_univ := huniv.2, toNonempty := ⟨huniv.1.some⟩ }

theorem isIntegral_glued [IsIntegral X] [Nonempty D.X0] [Fintype N]
    (hx : ∀ n, IsClosed ({D.x n} : Set X)) (hE : ∀ n, interior (D.toDR.base ⁻¹' {D.x n}) = ∅)
    (hY : ∀ n, IsReduced (D.Y n)) : IsIntegral D.glued := by
  haveI := D.isReduced_glued hY
  haveI := D.irreducibleSpace_glued hq hx hE
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end V3Glue.GlueInput

end

noncomputable section

namespace V3Glue.GlueInput

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

variable {X : Scheme.{0}} {N : Type} (D : GlueInput X N)
variable (hq : ∀ n (y : D.Y n), ((D.q n).base y).1 ∈ D.X0 → y ∈ Set.range (D.j n).base)
include hq

theorem preimage_toDR_x_eq_image (n : N) :
    D.toDR.base ⁻¹' {D.x n} = (D.ιY n).base '' {y : D.Y n | ((D.q n).base y).1 = D.x n} := by
  ext y'
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Set.mem_setOf_eq]
  have key : ∀ y : D.Y n, D.toDR.base ((D.ιY n).base y) = ((D.q n).base y).1 := fun y => by
    have h := congr($(D.ιY_toDR n).base y)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h.trans (by simp)
  constructor
  · intro hy
    have hU : y' ∈ D.toDR.base ⁻¹' (D.U n : Set X) := by
      show D.toDR.base y' ∈ (D.U n : Set X); rw [hy]; exact D.x_mem_U n
    rw [← D.range_ιY hq n] at hU
    obtain ⟨y, rfl⟩ := hU
    exact ⟨y, (key y).symm.trans hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (key y).trans hy

theorem interior_preimage_toDR_x_eq_empty (n : N)
    (hE : interior {y : D.Y n | ((D.q n).base y).1 = D.x n} = ∅) :
    interior (D.toDR.base ⁻¹' {D.x n}) = ∅ := by
  rw [D.preimage_toDR_x_eq_image hq n]
  set T : Set (D.Y n) := {y : D.Y n | ((D.q n).base y).1 = D.x n}
  set e := (D.ιY n).base
  have hinj : Function.Injective e := (D.ιY n).isOpenEmbedding.injective
  have hcont : Continuous e := (D.ιY n).continuous

  have hsub : e ⁻¹' interior (e '' T) ⊆ interior T := by
    apply interior_maximal
    · intro y hy
      have : e y ∈ e '' T := interior_subset hy
      obtain ⟨y', hy', he⟩ := this
      rwa [← hinj he]
    · exact isOpen_interior.preimage hcont
  rw [hE, Set.subset_empty_iff] at hsub
  apply Set.eq_empty_of_forall_notMem
  intro z hz
  have hz' : z ∈ e '' T := interior_subset hz
  obtain ⟨y, -, rfl⟩ := hz'
  have : y ∈ e ⁻¹' interior (e '' T) := hz
  rw [hsub] at this
  exact this

theorem isIntegral_glued' [IsIntegral X] [Nonempty D.X0] [Fintype N]
    (hx : ∀ n, IsClosed ({D.x n} : Set X))
    (hE : ∀ n, interior {y : D.Y n | ((D.q n).base y).1 = D.x n} = ∅)
    (hY : ∀ n, IsReduced (D.Y n)) : IsIntegral D.glued :=
  D.isIntegral_glued hq hx (fun n => D.interior_preimage_toDR_x_eq_empty hq n (hE n)) hY

end V3Glue.GlueInput

end


