-- Prove2me | Definitions.Def_FormalGroup_FibreProductGluing
-- name    : FormalGroup_FibreProductGluing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/134c42dd-b478-582c-b6aa-cb4de754d39d
-- title:
--   Gluing formal group laws along jointly injective ring maps
-- statement:
--   Throughout, a `FormalGroup R` is a two-variable power series $F \in R[[X_0,X_1]]$ with zero constant term, with the coefficients of $X_0$ and of $X_1$ equal to $1$, and satisfying the associativity identity $F(F(X_0,X_1),X_2) = F(X_0,F(X_1,X_2))$; `IsComm` records $F = F(X_1,X_0)$, a `LawHom F G` is a one-variable series $s$ with $s(0)=0$ and $s(F(X_0,X_1)) = G(s(X_0),s(X_1))$, and a `LawIso` adds that the linear coefficient of $s$ is a unit. The first part of the module develops descent along a pair of ring homomorphisms $f_1 : P \to Q_1$, $f_2 : P \to Q_2$ which is jointly injective in the sense that $f_1x=f_1y$ and $f_2x=f_2y$ force $x=y$: `eq_of_map_eq_of_map_eq` says a multivariable power series over $P$ is determined by its two coefficientwise images, and `ofPair` assembles, from a series $F$ over $P$ with zero constant term and formal group laws $G_1$ over $Q_1$, $G_2$ over $Q_2$ with $f_{1*}F = G_1$ and $f_{2*}F = G_2$, a formal group law over $P$ whose underlying series is $F$; `map_ofPair_left`, `map_ofPair_right` and `isComm_ofPair` record its images and that commutativity descends. The same pattern yields `LawHom.ofPair` and `LawIso.ofPair` for a series $s$ over $P$ whose images are given morphisms (resp. isomorphisms) between the base changes, while `LawHom.map`, `LawIso.map`, `map_map`, `map_id`, `isComm_map` give the functoriality of base change, and `isBaseChange_iff_map_eq` identifies the predicate `IsBaseChange` with the equation $f_*F = G$.
--
--   The second part works with the ring $\{(a,b) \in T\times T : \sigma a = \sigma b\}$ attached to $\sigma : T \to S$: `pairRingHom` and `pairAlgHom` glue two maps into $T$ that agree after $\sigma$, and `jointlyInjective_fst_snd` gives joint injectivity of the two projections. Assuming $T$ local and $(\ker\sigma)\cdot\mathfrak m_T = 0$, `thetaFun`, `thetaLift` and `thetaLiftAlgHom` glue a map $g_1$ into $T$ with a map $g_2$ into the tangent quotient $(T\times_S T)/\Delta(\mathfrak m_T)$ whose residues agree, characterised by $\mathrm{fst}\circ\theta = g_1$ and $\mathrm{mk}\circ\theta = g_2$; `jointlyInjective_fst_mk` states that the pair (first projection, tangent quotient) is jointly injective.
--
--   **Relation to Mathlib.** The structure `FormalGroup`, its pushforward `FormalGroup.map` along a ring homomorphism and the class `FormalGroup.IsComm` are Mathlib's; the morphism structures [`FormalGroup.LawHom`](../def/FormalGroup_PointTransport.html#L15), [`FormalGroup.LawIso`](../def/FormalGroup_PointTransport.html#L24), the predicate [`FormalGroup.IsBaseChange`](../def/FormalGroup_PointTransport.html#L41), and the fibre-product ring and its tangent quotient for a ring homomorphism are the project's own.
--
--   **Where it is used.** These gluing constructions supply the fibre-product axioms, in the style of Schlessinger's conditions, for deformation problems of one-dimensional formal group laws over small extensions of local rings, where a lift over $T\times_S T$ is reconstructed from its two projections, or from its image in $T$ together with its image in the tangent quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FormalGroup_FibreProductGluing.lean

import Mathlib
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_IsLocalRing_SmallExtensionTangent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroup

section Descent

variable {P Q₁ Q₂ : Type} [CommRing P] [CommRing Q₁] [CommRing Q₂]

theorem eq_of_map_eq_of_map_eq {τ : Type} (f₁ : P →+* Q₁) (f₂ : P →+* Q₂)
    (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) {F G : MvPowerSeries τ P}
    (h₁ : MvPowerSeries.map f₁ F = MvPowerSeries.map f₁ G) (h₂ : MvPowerSeries.map f₂ F = MvPowerSeries.map f₂ G) :
    F = G := by
  ext d
  refine hf _ _ ?_ ?_
  · have := congrArg (MvPowerSeries.coeff d) h₁; rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at this
  · have := congrArg (MvPowerSeries.coeff d) h₂; rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at this

theorem map_assoc_aux {Q : Type} [CommRing Q] (f : P →+* Q) (F : MvPowerSeries (Fin 2) P) (hF0 : F.constantCoeff = 0)
    (G : FormalGroup Q) (hF : F.map f = G.toPowerSeries) :
    (F.subst ![F.subst ![(X 0 : MvPowerSeries (Fin 3) P), X 1], X 2]).map f =
        G.toPowerSeries.subst ![G.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) Q), X 1], X 2] ∧
      (F.subst ![(X 0 : MvPowerSeries (Fin 3) P), F.subst ![X 1, X 2]]).map f =
        G.toPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 3) Q), G.toPowerSeries.subst ![X 1, X 2]] := by
  have hvec : ∀ (g₁ g₂ : MvPowerSeries (Fin 3) P),
      (fun j => MvPowerSeries.map f (![g₁, g₂] j)) = ![g₁.map f, g₂.map f] := by
    intro g₁ g₂; ext1 j; fin_cases j <;> simp
  constructor
  · rw [MvPowerSeries.map_subst (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 hF0), hvec,
      MvPowerSeries.map_subst HasSubst.X_X, hvec, hF]
    simp only [MvPowerSeries.map_X]
  · rw [MvPowerSeries.map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 hF0), hvec,
      MvPowerSeries.map_subst HasSubst.X_X, hvec, hF]
    simp only [MvPowerSeries.map_X]

def ofPair (f₁ : P →+* Q₁) (f₂ : P →+* Q₂) (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    (F : MvPowerSeries (Fin 2) P) (hF0 : F.constantCoeff = 0)
    (G₁ : FormalGroup Q₁) (G₂ : FormalGroup Q₂)
    (h₁ : F.map f₁ = G₁.toPowerSeries) (h₂ : F.map f₂ = G₂.toPowerSeries) : FormalGroup P where
  toPowerSeries := F
  zero_constantCoeff := hF0
  lin_coeff_X := by
    refine hf _ _ ?_ ?_
    · have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h₁
      rw [MvPowerSeries.coeff_map, G₁.lin_coeff_X] at this; rw [this, map_one]
    · have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h₂
      rw [MvPowerSeries.coeff_map, G₂.lin_coeff_X] at this; rw [this, map_one]
  lin_coeff_Y := by
    refine hf _ _ ?_ ?_
    · have := congrArg (MvPowerSeries.coeff (Finsupp.single 1 1)) h₁
      rw [MvPowerSeries.coeff_map, G₁.lin_coeff_Y] at this; rw [this, map_one]
    · have := congrArg (MvPowerSeries.coeff (Finsupp.single 1 1)) h₂
      rw [MvPowerSeries.coeff_map, G₂.lin_coeff_Y] at this; rw [this, map_one]
  assoc := by
    apply eq_of_map_eq_of_map_eq f₁ f₂ hf
    · rw [(map_assoc_aux f₁ F hF0 G₁ h₁).1, (map_assoc_aux f₁ F hF0 G₁ h₁).2]; exact G₁.assoc
    · rw [(map_assoc_aux f₂ F hF0 G₂ h₂).1, (map_assoc_aux f₂ F hF0 G₂ h₂).2]; exact G₂.assoc

@[simp] theorem ofPair_toPowerSeries (f₁ : P →+* Q₁) (f₂ : P →+* Q₂)
    (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) (F : MvPowerSeries (Fin 2) P) (hF0 : F.constantCoeff = 0)
    (G₁ : FormalGroup Q₁) (G₂ : FormalGroup Q₂) (h₁ : F.map f₁ = G₁.toPowerSeries) (h₂ : F.map f₂ = G₂.toPowerSeries) :
    (ofPair f₁ f₂ hf F hF0 G₁ G₂ h₁ h₂).toPowerSeries = F := rfl

theorem map_ofPair_left (f₁ : P →+* Q₁) (f₂ : P →+* Q₂)
    (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) (F : MvPowerSeries (Fin 2) P) (hF0 : F.constantCoeff = 0)
    (G₁ : FormalGroup Q₁) (G₂ : FormalGroup Q₂) (h₁ : F.map f₁ = G₁.toPowerSeries) (h₂ : F.map f₂ = G₂.toPowerSeries) :
    (ofPair f₁ f₂ hf F hF0 G₁ G₂ h₁ h₂).map f₁ = G₁ := FormalGroup.ext h₁

theorem map_ofPair_right (f₁ : P →+* Q₁) (f₂ : P →+* Q₂)
    (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) (F : MvPowerSeries (Fin 2) P) (hF0 : F.constantCoeff = 0)
    (G₁ : FormalGroup Q₁) (G₂ : FormalGroup Q₂) (h₁ : F.map f₁ = G₁.toPowerSeries) (h₂ : F.map f₂ = G₂.toPowerSeries) :
    (ofPair f₁ f₂ hf F hF0 G₁ G₂ h₁ h₂).map f₂ = G₂ := FormalGroup.ext h₂

theorem isComm_ofPair (f₁ : P →+* Q₁) (f₂ : P →+* Q₂)
    (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) (F : MvPowerSeries (Fin 2) P) (hF0 : F.constantCoeff = 0)
    (G₁ : FormalGroup Q₁) (G₂ : FormalGroup Q₂) (h₁ : F.map f₁ = G₁.toPowerSeries) (h₂ : F.map f₂ = G₂.toPowerSeries)
    [G₁.IsComm] [G₂.IsComm] : (ofPair f₁ f₂ hf F hF0 G₁ G₂ h₁ h₂).IsComm := by
  refine ⟨?_⟩
  show F = F.subst ![X 1, X 0]
  have hX : HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) P) :=
    hasSubst_of_constantCoeff_zero (fun j => by fin_cases j <;> simp)
  have hvec : ∀ {Q : Type} [CommRing Q] (f : P →+* Q),
      (fun j => MvPowerSeries.map f ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) P) j)) =
        (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) Q) := by
    intro Q _ f; ext1 j; fin_cases j <;> simp
  apply eq_of_map_eq_of_map_eq f₁ f₂ hf
  · rw [MvPowerSeries.map_subst hX, hvec, h₁]; exact ‹G₁.IsComm›.comm
  · rw [MvPowerSeries.map_subst hX, hvec, h₂]; exact ‹G₂.IsComm›.comm

end Descent

section HomMap

variable {R S : Type} [CommRing R] [CommRing S]

theorem LawHom.constantCoeff_substX (i : Fin 2) (s : PowerSeries R) (hs : PowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (LawHom.substX i s) = 0 := by
  unfold LawHom.substX
  exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) s hs

theorem LawHom.hasSubst_substX (s : PowerSeries R) (hs : PowerSeries.constantCoeff s = 0) :
    HasSubst (![LawHom.substX 0 s, LawHom.substX 1 s] : Fin 2 → MvPowerSeries (Fin 2) R) :=
  hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨constantCoeff_substX 0 s hs, constantCoeff_substX 1 s hs⟩)

theorem LawHom.map_substX (f : R →+* S) (i : Fin 2) (s : PowerSeries R) :
    MvPowerSeries.map f (LawHom.substX i s) = LawHom.substX i (PowerSeries.map f s) := by
  unfold LawHom.substX
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)), MvPowerSeries.map_X]

theorem LawHom.map_comm_aux (f : R →+* S) (F G : FormalGroup R) (s : PowerSeries R)
    (hs : PowerSeries.constantCoeff s = 0) :
    MvPowerSeries.map f (PowerSeries.subst F.toPowerSeries s) =
        PowerSeries.subst (F.map f).toPowerSeries (PowerSeries.map f s) ∧
      MvPowerSeries.map f (MvPowerSeries.subst ![LawHom.substX 0 s, LawHom.substX 1 s] G.toPowerSeries) =
        MvPowerSeries.subst ![LawHom.substX 0 (PowerSeries.map f s), LawHom.substX 1 (PowerSeries.map f s)]
          (G.map f).toPowerSeries := by
  constructor
  · rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff)]; rfl
  · rw [MvPowerSeries.map_subst (LawHom.hasSubst_substX s hs)]
    have hvec : (fun j => MvPowerSeries.map f ((![LawHom.substX 0 s, LawHom.substX 1 s] : Fin 2 → _) j)) =
        ![LawHom.substX 0 (PowerSeries.map f s), LawHom.substX 1 (PowerSeries.map f s)] := by
      ext1 j; fin_cases j <;> simp [LawHom.map_substX f _ s]
    rw [hvec]; rfl

def LawHom.map (f : R →+* S) {F G : FormalGroup R} (θ : LawHom F G) : LawHom (F.map f) (G.map f) where
  series := PowerSeries.map f θ.series
  constantCoeff_series := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, θ.constantCoeff_series, map_zero]
  comm := by
    rw [← (LawHom.map_comm_aux f F G θ.series θ.constantCoeff_series).1,
      ← (LawHom.map_comm_aux f F G θ.series θ.constantCoeff_series).2, θ.comm]

@[simp] theorem LawHom.map_series (f : R →+* S) {F G : FormalGroup R} (θ : LawHom F G) :
    (θ.map f).series = PowerSeries.map f θ.series := rfl

def LawIso.map (f : R →+* S) {F G : FormalGroup R} (ψ : LawIso F G) : LawIso (F.map f) (G.map f) where
  toLawHom := ψ.toLawHom.map f
  isUnit_coeff_one := by
    show IsUnit (PowerSeries.coeff 1 (PowerSeries.map f ψ.series))
    rw [PowerSeries.coeff_map]; exact ψ.isUnit_coeff_one.map f

@[simp] theorem LawIso.map_series (f : R →+* S) {F G : FormalGroup R} (ψ : LawIso F G) :
    (ψ.map f).series = PowerSeries.map f ψ.series := rfl

end HomMap

section HomDescent

variable {P Q₁ Q₂ : Type} [CommRing P] [CommRing Q₁] [CommRing Q₂]

def LawHom.ofPair (f₁ : P →+* Q₁) (f₂ : P →+* Q₂) (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    {F G : FormalGroup P} (s : PowerSeries P) (hs : PowerSeries.constantCoeff s = 0)
    (θ₁ : LawHom (F.map f₁) (G.map f₁)) (θ₂ : LawHom (F.map f₂) (G.map f₂))
    (h₁ : PowerSeries.map f₁ s = θ₁.series) (h₂ : PowerSeries.map f₂ s = θ₂.series) : LawHom F G where
  series := s
  constantCoeff_series := hs
  comm := by
    apply eq_of_map_eq_of_map_eq f₁ f₂ hf
    · rw [(LawHom.map_comm_aux f₁ F G s hs).1, (LawHom.map_comm_aux f₁ F G s hs).2, h₁]; exact θ₁.comm
    · rw [(LawHom.map_comm_aux f₂ F G s hs).1, (LawHom.map_comm_aux f₂ F G s hs).2, h₂]; exact θ₂.comm

@[simp] theorem LawHom.ofPair_series (f₁ : P →+* Q₁) (f₂ : P →+* Q₂)
    (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) {F G : FormalGroup P} (s : PowerSeries P)
    (hs : PowerSeries.constantCoeff s = 0) (θ₁ : LawHom (F.map f₁) (G.map f₁)) (θ₂ : LawHom (F.map f₂) (G.map f₂))
    (h₁ : PowerSeries.map f₁ s = θ₁.series) (h₂ : PowerSeries.map f₂ s = θ₂.series) :
    (LawHom.ofPair f₁ f₂ hf s hs θ₁ θ₂ h₁ h₂).series = s := rfl

def LawIso.ofPair (f₁ : P →+* Q₁) (f₂ : P →+* Q₂) (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y)
    {F G : FormalGroup P} (s : PowerSeries P) (hs : PowerSeries.constantCoeff s = 0) (hu : IsUnit (PowerSeries.coeff 1 s))
    (θ₁ : LawHom (F.map f₁) (G.map f₁)) (θ₂ : LawHom (F.map f₂) (G.map f₂))
    (h₁ : PowerSeries.map f₁ s = θ₁.series) (h₂ : PowerSeries.map f₂ s = θ₂.series) : LawIso F G where
  toLawHom := LawHom.ofPair f₁ f₂ hf s hs θ₁ θ₂ h₁ h₂
  isUnit_coeff_one := hu

@[simp] theorem LawIso.ofPair_series (f₁ : P →+* Q₁) (f₂ : P →+* Q₂)
    (hf : ∀ x y : P, f₁ x = f₁ y → f₂ x = f₂ y → x = y) {F G : FormalGroup P} (s : PowerSeries P)
    (hs : PowerSeries.constantCoeff s = 0) (hu : IsUnit (PowerSeries.coeff 1 s))
    (θ₁ : LawHom (F.map f₁) (G.map f₁)) (θ₂ : LawHom (F.map f₂) (G.map f₂))
    (h₁ : PowerSeries.map f₁ s = θ₁.series) (h₂ : PowerSeries.map f₂ s = θ₂.series) :
    (LawIso.ofPair f₁ f₂ hf s hs hu θ₁ θ₂ h₁ h₂).series = s := rfl

end HomDescent

theorem map_map {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (F : FormalGroup R) (f : R →+* S) (g : S →+* U) :
    (F.map f).map g = F.map (g.comp f) := by
  apply FormalGroup.ext
  show MvPowerSeries.map g (MvPowerSeries.map f F.toPowerSeries) = MvPowerSeries.map (g.comp f) F.toPowerSeries
  rw [MvPowerSeries.map_comp]; rfl

theorem map_id {R : Type} [CommRing R] (F : FormalGroup R) : F.map (RingHom.id R) = F := by
  apply FormalGroup.ext
  show MvPowerSeries.map (RingHom.id R) F.toPowerSeries = F.toPowerSeries
  rw [MvPowerSeries.map_id]; rfl

theorem isComm_map {R S : Type} [CommRing R] [CommRing S] (F : FormalGroup R) [F.IsComm] (f : R →+* S) :
    (F.map f).IsComm := by
  refine ⟨?_⟩
  show MvPowerSeries.map f F.toPowerSeries = (MvPowerSeries.map f F.toPowerSeries).subst ![X 1, X 0]
  have hX : HasSubst (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) :=
    hasSubst_of_constantCoeff_zero (fun j => by fin_cases j <;> simp)
  have hvec : (fun j => MvPowerSeries.map f ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) j)) =
      (![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) S) := by
    ext1 j; fin_cases j <;> simp
  conv_lhs => rw [show F.toPowerSeries = F.toPowerSeries.subst ![X 1, X 0] from ‹F.IsComm›.comm]
  rw [MvPowerSeries.map_subst hX, hvec]

theorem isBaseChange_iff_map_eq {R S : Type} [CommRing R] [CommRing S] (F : FormalGroup R) (f : R →+* S) (G : FormalGroup S) :
    F.IsBaseChange f G ↔ F.map f = G :=
  ⟨fun h => FormalGroup.ext h.symm, fun h => by rw [← h]; rfl⟩

end FormalGroup

namespace IsLocalRing.SmallExtension

open IsLocalRing

variable {T S : Type} [CommRing T] [CommRing S] (σ : T →+* S)

def pairRingHom {A' : Type} [Semiring A'] (g₁ g₂ : A' →+* T) (h : ∀ r, σ (g₁ r) = σ (g₂ r)) :
    A' →+* fibreProd σ where
  toFun r := pair σ (g₁ r) (g₂ r) (h r)
  map_one' := (ext_iff σ).mpr ⟨map_one g₁, map_one g₂⟩
  map_mul' x y := (ext_iff σ).mpr ⟨map_mul g₁ x y, map_mul g₂ x y⟩
  map_zero' := (ext_iff σ).mpr ⟨map_zero g₁, map_zero g₂⟩
  map_add' x y := (ext_iff σ).mpr ⟨map_add g₁ x y, map_add g₂ x y⟩

@[simp] theorem fst_pairRingHom {A' : Type} [Semiring A'] (g₁ g₂ : A' →+* T) (h : ∀ r, σ (g₁ r) = σ (g₂ r)) (r : A') :
    fst σ (pairRingHom σ g₁ g₂ h r) = g₁ r := rfl
@[simp] theorem snd_pairRingHom {A' : Type} [Semiring A'] (g₁ g₂ : A' →+* T) (h : ∀ r, σ (g₁ r) = σ (g₂ r)) (r : A') :
    snd σ (pairRingHom σ g₁ g₂ h r) = g₂ r := rfl

def pairAlgHom {A A' : Type} [CommRing A] [Algebra A T] [Semiring A'] [Algebra A A'] (g₁ g₂ : A' →ₐ[A] T)
    (h : ∀ r, σ (g₁ r) = σ (g₂ r)) : A' →ₐ[A] fibreProd σ :=
  { pairRingHom σ g₁.toRingHom g₂.toRingHom h with
    commutes' := fun a => (ext_iff σ).mpr ⟨by
        show g₁.toRingHom (algebraMap A A' a) = fst σ (algebraMap A (fibreProd σ) a)
        rw [algebraMap_eq]; exact g₁.commutes a, by
        show g₂.toRingHom (algebraMap A A' a) = snd σ (algebraMap A (fibreProd σ) a)
        rw [algebraMap_eq]; exact g₂.commutes a⟩ }

@[simp] theorem fst_pairAlgHom {A A' : Type} [CommRing A] [Algebra A T] [Semiring A'] [Algebra A A']
    (g₁ g₂ : A' →ₐ[A] T) (h : ∀ r, σ (g₁ r) = σ (g₂ r)) (r : A') : fst σ (pairAlgHom σ g₁ g₂ h r) = g₁ r := rfl
@[simp] theorem snd_pairAlgHom {A A' : Type} [CommRing A] [Algebra A T] [Semiring A'] [Algebra A A']
    (g₁ g₂ : A' →ₐ[A] T) (h : ∀ r, σ (g₁ r) = σ (g₂ r)) (r : A') : snd σ (pairAlgHom σ g₁ g₂ h r) = g₂ r := rfl

theorem jointlyInjective_fst_snd : ∀ x y : fibreProd σ, fst σ x = fst σ y → snd σ x = snd σ y → x = y :=
  fun _ _ h1 h2 => (ext_iff σ).mpr ⟨h1, h2⟩

variable [IsLocalRing T]

def thetaFun (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A' : Type} (g₁ : A' → T) (g₂ : A' → Tangent σ)
    (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) : A' → fibreProd σ :=
  fun r => Classical.choose (exists_fst_eq_and_mk_eq σ hsmall (g₁ r) (g₂ r) (h r))

theorem fst_thetaFun (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A' : Type} (g₁ : A' → T) (g₂ : A' → Tangent σ)
    (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) (r : A') : fst σ (thetaFun σ hsmall g₁ g₂ h r) = g₁ r :=
  (Classical.choose_spec (exists_fst_eq_and_mk_eq σ hsmall (g₁ r) (g₂ r) (h r))).1

theorem mk_thetaFun (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A' : Type} (g₁ : A' → T) (g₂ : A' → Tangent σ)
    (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) (r : A') : mk σ (thetaFun σ hsmall g₁ g₂ h r) = g₂ r :=
  (Classical.choose_spec (exists_fst_eq_and_mk_eq σ hsmall (g₁ r) (g₂ r) (h r))).2

def thetaLift (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A' : Type} [Semiring A'] (g₁ : A' →+* T)
    (g₂ : A' →+* Tangent σ) (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) : A' →+* fibreProd σ where
  toFun := thetaFun σ hsmall g₁ g₂ h
  map_one' := eq_of_fst_eq_of_mk_eq σ hsmall (by rw [fst_thetaFun, map_one, map_one]) (by rw [mk_thetaFun, map_one, map_one])
  map_mul' x y := eq_of_fst_eq_of_mk_eq σ hsmall
    (by rw [fst_thetaFun, map_mul, map_mul, fst_thetaFun, fst_thetaFun])
    (by rw [mk_thetaFun, map_mul, map_mul, mk_thetaFun, mk_thetaFun])
  map_zero' := eq_of_fst_eq_of_mk_eq σ hsmall (by rw [fst_thetaFun, map_zero, map_zero]) (by rw [mk_thetaFun, map_zero, map_zero])
  map_add' x y := eq_of_fst_eq_of_mk_eq σ hsmall
    (by rw [fst_thetaFun, map_add, map_add, fst_thetaFun, fst_thetaFun])
    (by rw [mk_thetaFun, map_add, map_add, mk_thetaFun, mk_thetaFun])

@[simp] theorem fst_thetaLift (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A' : Type} [Semiring A'] (g₁ : A' →+* T)
    (g₂ : A' →+* Tangent σ) (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) (r : A') :
    fst σ (thetaLift σ hsmall g₁ g₂ h r) = g₁ r := fst_thetaFun σ hsmall g₁ g₂ h r

@[simp] theorem mk_thetaLift (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A' : Type} [Semiring A'] (g₁ : A' →+* T)
    (g₂ : A' →+* Tangent σ) (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) (r : A') :
    mk σ (thetaLift σ hsmall g₁ g₂ h r) = g₂ r := mk_thetaFun σ hsmall g₁ g₂ h r

def thetaLiftAlgHom (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A A' : Type} [CommRing A] [Algebra A T]
    [Semiring A'] [Algebra A A'] (g₁ : A' →ₐ[A] T) (g₂ : A' →ₐ[A] Tangent σ)
    (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) : A' →ₐ[A] fibreProd σ :=
  { thetaLift σ hsmall g₁.toRingHom g₂.toRingHom h with
    commutes' := fun a => by
      apply eq_of_fst_eq_of_mk_eq σ hsmall
      · show fst σ (thetaLift σ hsmall g₁.toRingHom g₂.toRingHom h (algebraMap A A' a)) = _
        rw [fst_thetaLift, algebraMap_eq]; exact g₁.commutes a
      · show mk σ (thetaLift σ hsmall g₁.toRingHom g₂.toRingHom h (algebraMap A A' a)) = mk σ (algebraMap A (fibreProd σ) a)
        rw [mk_thetaLift]
        exact g₂.commutes a }

@[simp] theorem fst_thetaLiftAlgHom (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A A' : Type} [CommRing A]
    [Algebra A T] [Semiring A'] [Algebra A A'] (g₁ : A' →ₐ[A] T) (g₂ : A' →ₐ[A] Tangent σ)
    (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) (r : A') : fst σ (thetaLiftAlgHom σ hsmall g₁ g₂ h r) = g₁ r :=
  fst_thetaFun σ hsmall _ _ h r

@[simp] theorem mk_thetaLiftAlgHom (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) {A A' : Type} [CommRing A]
    [Algebra A T] [Semiring A'] [Algebra A A'] (g₁ : A' →ₐ[A] T) (g₂ : A' →ₐ[A] Tangent σ)
    (h : ∀ r, residue T (g₁ r) = res σ (g₂ r)) (r : A') : mk σ (thetaLiftAlgHom σ hsmall g₁ g₂ h r) = g₂ r :=
  mk_thetaFun σ hsmall _ _ h r

theorem jointlyInjective_fst_mk (hsmall : RingHom.ker σ * maximalIdeal T = ⊥) :
    ∀ x y : fibreProd σ, fst σ x = fst σ y → mk σ x = mk σ y → x = y :=
  fun _ _ h1 h2 => eq_of_fst_eq_of_mk_eq σ hsmall h1 h2

end IsLocalRing.SmallExtension

end


