-- Prove2me | Definitions.Def_RPLib_S4_EtShFV
-- name    : RPLib_S4_EtShFV
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:36:55.767261+00:00
-- url     : https://prove2.me/theorems/9c38ea8e-1cbf-4165-9b69-895c7043308a
-- title:
--   The etale sheaf $F_V$ of a representation of a Galois group
-- statement:
--   For an etale sheaf $S$ and families $a, b : \iota \to \mathrm{End}(S)$, the subsheaf of sections $s$ with $a_i(s) = b_i(s)$ for all $i$ is constructed (glued inside $S$). For a Galois cover $\pi : Y = \mathrm{Spec}\,B \to X = \mathrm{Spec}\,A$ with group $G$ and a representation $\rho$ of $G$ on a $\Lambda$-module $V$, $G$ acts on $U \times_X Y$ over $X$ by $1 \times \sigma_Y$, hence on the sheaf $U \mapsto V_X(U \times_X Y)$, and on values by $\rho(\sigma^{-1})$; $F_V$ is the subsheaf where the two actions agree. For $T$ etale over $Y$, a section $s$ of $V_X$ over $T \times_X Y$ lies in $F_V(T)$ iff $s(\tau\sigma) = \rho(\sigma^{-1})\,s(\tau)$ for all $\sigma, \tau \in G$, where $s(\tau)$ is the restriction along $t \mapsto (t, \tau_Y t)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5

import Mathlib
import Definitions.Def_RPLib_S4_EtShTorSec

/-!
# S4-EtSheaves, part O10d-2(ii): the sheaf `F_V` of a representation of a Galois group

* `eqSh S a b`: for an etale sheaf `S` and families `a b : ι → (S ⟶ S)`, the subsheaf of sections `s` with
  `a i s = b i s` for all `i` (glued in `S`, membership by separatedness: `existsUnique_glueS`, `sep_eq`).
* For a Galois cover `C : GalCover A` (`π : Y = Spec B → X = Spec A`) and a representation `ρ` of `G` on `V`:
  `G` acts on `U ×_X Y` over `X` by `1 × σ_Y` (`tE`, natural in `U`), hence on `SV : U ↦ V_X(U ×_X Y)` (`aS`), and on
  values by `ρ(σ⁻¹)` (`th`, `bS`). `FV C Λ V ρ := eqSh (SV C Λ V) (aS C Λ V) (bS C Λ V ρ)`.
* `sec_tE`: `ι τ ≫ (1 × σ_Y) = ι (τ σ)`; `mem_FV_iff`: for `T` etale over `Y`, a section `s` of `V_X` over `T ×_X Y`
  lies in `F_V(T)` iff `s(τσ) = ρ(σ⁻¹) s(τ)` for all `σ τ`, where `s(τ)` is the restriction of `s` along `ι τ`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section EqSh

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

/-- **Gluing along a covering sieve** for sheaves of modules on the small etale site. -/
theorem existsUnique_glueS (F : EtSh Λ Z) {U : Z.Etale} (R : Sieve U) (hR : R ∈ Z.smallEtaleTopology U)
    (x : ∀ ⦃V : Z.Etale⦄ (f : V ⟶ U), R f → F.obj.obj (op V))
    (hx : ∀ ⦃V₁ V₂ W : Z.Etale⦄ (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (h₁ : R f₁) (h₂ : R f₂) (g₁ : W ⟶ V₁)
      (g₂ : W ⟶ V₂), g₁ ≫ f₁ = g₂ ≫ f₂ → (F.obj.map g₁.op).hom (x f₁ h₁) = (F.obj.map g₂.op).hom (x f₂ h₂)) :
    ∃! s, ∀ ⦃V : Z.Etale⦄ (f : V ⟶ U) (h : R f), (F.obj.map f.op).hom s = x f h := by
  let y : Presieve.FamilyOfElements (F.obj ⋙ coyoneda.obj (op (ModuleCat.of Λ Λ))) R.arrows := by
    intro V f h
    exact elt (x f h)
  have hy : y.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    change elt (x f₁ h₁) ≫ F.obj.map g₁.op = elt (x f₂ h₂) ≫ F.obj.map g₂.op
    rw [elt_comp, elt_comp, hx f₁ f₂ h₁ h₂ g₁ g₂ e]
  obtain ⟨t, ht, hu⟩ := F.property (ModuleCat.of Λ Λ) R hR y hy
  let t' : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) := t
  refine ⟨t'.hom 1, fun V f h => ?_, fun s hs => ?_⟩
  · have h1 : t' ≫ F.obj.map f.op = elt (x f h) := ht f h
    have h2 := congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op V) => φ.hom 1) h1
    simpa [elt] using h2
  · have e : elt s = t := hu _ (by
      intro V f h
      change elt s ≫ F.obj.map f.op = elt (x f h)
      rw [elt_comp, hs f h])
    change s = t'.hom 1
    rw [← elt_one s]
    exact congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) => φ.hom 1) e

theorem map_map_apply (F : EtSh Λ Z) {U V W : Z.Etale} (f : V ⟶ U) (g : W ⟶ V) (s : F.obj.obj (op U)) :
    (F.obj.map g.op).hom ((F.obj.map f.op).hom s) = (F.obj.map (g ≫ f).op).hom s := by
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- **Separatedness** along a covering sieve. -/
theorem sep_eq (F : EtSh Λ Z) {U : Z.Etale} (R : Sieve U) (hR : R ∈ Z.smallEtaleTopology U)
    (s t : F.obj.obj (op U))
    (h : ∀ ⦃V : Z.Etale⦄ (f : V ⟶ U), R f → (F.obj.map f.op).hom s = (F.obj.map f.op).hom t) : s = t := by
  obtain ⟨u, -, hu⟩ := existsUnique_glueS F R hR (fun V f _ => (F.obj.map f.op).hom t) (by
    intro V₁ V₂ W f₁ f₂ _ _ g₁ g₂ e
    rw [map_map_apply, map_map_apply, e])
  exact (hu s h).trans (hu t fun _ _ _ => rfl).symm

theorem app_map {F G : EtSh Λ Z} (φ : F ⟶ G) {U V : Z.Etale} (f : V ⟶ U) (s : F.obj.obj (op U)) :
    (φ.hom.app (op V)).hom ((F.obj.map f.op).hom s) = (G.obj.map f.op).hom ((φ.hom.app (op U)).hom s) :=
  congrArg (fun g => g.hom s) (φ.hom.naturality f.op)

variable (S : EtSh Λ Z) {ι : Type*} (a b : ι → (S ⟶ S))

/-- Sections on which `a i` and `b i` agree for every `i`. -/
def eqSecSub (U : Z.Etale) : Submodule Λ (S.obj.obj (op U)) where
  carrier := {s | ∀ i, ((a i).hom.app (op U)).hom s = ((b i).hom.app (op U)).hom s}
  add_mem' {s t} hs ht i := by
    simp only [Set.mem_ofPred_eq] at hs ht
    simp only [map_add, hs i, ht i]
  zero_mem' i := by simp
  smul_mem' c s hs i := by
    simp only [Set.mem_ofPred_eq] at hs
    simp only [map_smul, hs i]

theorem mem_eqSecSub {U : Z.Etale} (s : S.obj.obj (op U)) :
    s ∈ eqSecSub S a b U ↔ ∀ i, ((a i).hom.app (op U)).hom s = ((b i).hom.app (op U)).hom s := Iff.rfl

/-- Restriction of such sections. -/
def eqSecRes {U V : Z.Etale} (f : V ⟶ U) : eqSecSub S a b U →ₗ[Λ] eqSecSub S a b V where
  toFun s := ⟨(S.obj.map f.op).hom s.1, (mem_eqSecSub S a b _).2 fun i => by
    rw [app_map (a i) f, app_map (b i) f, (mem_eqSecSub S a b _).1 s.2 i]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- The presheaf of such sections. -/
def eqPre : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj U := ModuleCat.of Λ (eqSecSub S a b U.unop)
  map f := ModuleCat.ofHom (eqSecRes S a b f.unop)
  map_id U := ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (by
    change (S.obj.map (𝟙 U)).hom s.1 = s.1
    rw [CategoryTheory.Functor.map_id]
    rfl))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext (by
    change (S.obj.map (f ≫ g)).hom s.1 = (S.obj.map g).hom ((S.obj.map f).hom s.1)
    rw [CategoryTheory.Functor.map_comp]
    rfl))

theorem isSheaf_eqPre : Presheaf.IsSheaf (Scheme.smallEtaleTopology Z) (eqPre S a b) := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})
    ((isSheaf_iff_isSheaf_of_type (J := Scheme.smallEtaleTopology Z)
      (P := eqPre S a b ⋙ forget (ModuleCat.{u} Λ) ⋙ uliftFunctor.{u + 1, u})).2 ?_)
  intro U R hR x hx
  obtain ⟨s, hs, hu⟩ := existsUnique_glueS S R hR (fun V f h => (x f h).down.1) (by
    intro V₁ V₂ W f₁ f₂ h₁ h₂ g₁ g₂ e
    exact congrArg (fun t => t.down.1) (hx g₁ g₂ h₁ h₂ e))
  have hmem : s ∈ eqSecSub S a b U := (mem_eqSecSub S a b s).2 fun i =>
    sep_eq S R hR _ _ fun V f h => by
      rw [← app_map (a i) f, ← app_map (b i) f, hs f h]
      exact (mem_eqSecSub S a b _).1 (x f h).down.2 i
  refine ⟨ULift.up ⟨s, hmem⟩, fun V f h => ?_, fun t ht => ?_⟩
  · apply ULift.ext
    apply Subtype.ext
    exact hs f h
  · apply ULift.ext
    apply Subtype.ext
    exact hu t.down.1 fun V f h => congrArg (fun t => t.down.1) (ht f h)

/-- **The equaliser subsheaf** `U ↦ {s ∈ S(U) | ∀ i, a i s = b i s}`. -/
def eqSh : EtSh Λ Z := ⟨eqPre S a b, isSheaf_eqPre S a b⟩

/-- Its inclusion into `S`. -/
def eqι : eqSh S a b ⟶ S :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (eqSecSub S a b U.unop).subtype
      naturality := fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl) }

end EqSh

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

/-- The constant sheaf `V_X`. -/
abbrev VX (A : Type) [CommRing A] (Λ : Type) [CommRing Λ] (V : Type) [AddCommGroup V] [Module Λ V] :
    EtSh Λ (SX A) :=
  constSh Λ (SX A) (ModuleCat.of Λ V)

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

/-- `1 × σ_Y` on `U ×_X Y`, as a scheme map. -/
def tL (σ : C.G) (U : (SX A).Etale) : pullback U.hom (pr C) ⟶ pullback U.hom (pr C) :=
  pullback.lift (pullback.fst U.hom (pr C)) (pullback.snd U.hom (pr C) ≫ act C σ)
    (by rw [Category.assoc, act_pr]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem tL_fst (σ : C.G) (U : (SX A).Etale) :
    tL C σ U ≫ pullback.fst U.hom (pr C) = pullback.fst U.hom (pr C) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem tL_snd (σ : C.G) (U : (SX A).Etale) :
    tL C σ U ≫ pullback.snd U.hom (pr C) = pullback.snd U.hom (pr C) ≫ act C σ :=
  pullback.lift_snd _ _ _

/-- The scheme map of `U ×_X Y ⟶ U' ×_X Y` induced by `f : U ⟶ U'`. -/
def mL {U U' : (SX A).Etale} (f : U ⟶ U') : pullback U.hom (pr C) ⟶ pullback U'.hom (pr C) :=
  pullback.lift (pullback.fst U.hom (pr C) ≫ f.left) (pullback.snd U.hom (pr C)) (by
    rw [Category.assoc, MorphismProperty.Over.w f]
    exact pullback.condition)

theorem tL_naturality {U U' : (SX A).Etale} (f : U ⟶ U') (σ : C.G) :
    mL C f ≫ tL C σ U' = tL C σ U ≫ mL C f := by
  refine pullback.hom_ext (f := U'.hom) (g := pr C) ?_ ?_
  · calc (mL C f ≫ tL C σ U') ≫ pullback.fst U'.hom (pr C) = mL C f ≫ pullback.fst U'.hom (pr C) := by
          rw [Category.assoc, tL_fst]
      _ = pullback.fst U.hom (pr C) ≫ f.left := pullback.lift_fst _ _ _
      _ = tL C σ U ≫ pullback.fst U.hom (pr C) ≫ f.left := by rw [tL_fst_assoc]
      _ = (tL C σ U ≫ mL C f) ≫ pullback.fst U'.hom (pr C) := by
          rw [Category.assoc]
          exact congrArg (tL C σ U ≫ ·) (pullback.lift_fst _ _ _).symm
  · calc (mL C f ≫ tL C σ U') ≫ pullback.snd U'.hom (pr C)
        = mL C f ≫ pullback.snd U'.hom (pr C) ≫ act C σ := by rw [Category.assoc, tL_snd]
      _ = pullback.snd U.hom (pr C) ≫ act C σ := by
          rw [← Category.assoc]
          exact congrArg (· ≫ act C σ) (pullback.lift_snd _ _ _)
      _ = tL C σ U ≫ pullback.snd U.hom (pr C) := (tL_snd C σ U).symm
      _ = (tL C σ U ≫ mL C f) ≫ pullback.snd U'.hom (pr C) := by
          rw [Category.assoc]
          exact congrArg (tL C σ U ≫ ·) (pullback.lift_snd _ _ _).symm

/-- `1 × σ_Y` as an endomorphism of the etale `X`-scheme `U ×_X Y`. -/
def tE (σ : C.G) (U : (SX A).Etale) :
    (etComp (pr C)).obj ((etPull (pr C)).obj U) ⟶ (etComp (pr C)).obj ((etPull (pr C)).obj U) :=
  MorphismProperty.Over.homMk (tL C σ U) (by
    show tL C σ U ≫ pullback.snd U.hom (pr C) ≫ pr C = pullback.snd U.hom (pr C) ≫ pr C
    rw [tL_snd_assoc, act_pr]) trivial

theorem tE_left (σ : C.G) (U : (SX A).Etale) : (tE C σ U).left = tL C σ U := rfl

theorem tE_naturality {U U' : (SX A).Etale} (f : U ⟶ U') (σ : C.G) :
    (etComp (pr C)).map ((etPull (pr C)).map f) ≫ tE C σ U' =
      tE C σ U ≫ (etComp (pr C)).map ((etPull (pr C)).map f) :=
  MorphismProperty.Over.Hom.ext (tL_naturality C f σ)

variable (Λ : Type) [CommRing Λ] (V : Type) [AddCommGroup V] [Module Λ V]

/-- The sheaf `SV : U ↦ V_X(U ×_X Y)` (`= π_* π^* V_X`). -/
def SV : EtSh Λ (SX A) :=
  ⟨(etPull (pr C)).op ⋙ (etComp (pr C)).op ⋙ (VX A Λ V).obj,
    (etPull (pr C)).op_comp_isSheaf_of_isSheaf (SX A).smallEtaleTopology (SY C).smallEtaleTopology _
      ((etComp (pr C)).op_comp_isSheaf (SY C).smallEtaleTopology (SX A).smallEtaleTopology (VX A Λ V))⟩

/-- `G` acting on `SV` through `1 × σ_Y`. -/
def aS (σ : C.G) : SV C Λ V ⟶ SV C Λ V :=
  ObjectProperty.homMk
    { app := fun U => (VX A Λ V).obj.map (tE C σ U.unop).op
      naturality := fun U U' f => by
        change (VX A Λ V).obj.map ((etComp (pr C)).map ((etPull (pr C)).map f.unop)).op ≫
            (VX A Λ V).obj.map (tE C σ U'.unop).op =
          (VX A Λ V).obj.map (tE C σ U.unop).op ≫
            (VX A Λ V).obj.map ((etComp (pr C)).map ((etPull (pr C)).map f.unop)).op
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp,
          tE_naturality] }

variable {V} (ρ : Representation Λ C.G V)

/-- `ρ(σ⁻¹)` acting on `V_X`. -/
def th (σ : C.G) : VX A Λ V ⟶ VX A Λ V :=
  (constantSheaf (SX A).smallEtaleTopology (ModuleCat.{0} Λ)).map (ModuleCat.ofHom (ρ σ⁻¹))

theorem th_comp (σ τ : C.G) : th C Λ ρ τ ≫ th C Λ ρ σ = th C Λ ρ (τ * σ) := by
  have h : ModuleCat.ofHom (ρ τ⁻¹) ≫ ModuleCat.ofHom (ρ σ⁻¹) = ModuleCat.ofHom (ρ (τ * σ)⁻¹) := by
    ext v
    simp [mul_inv_rev]
  unfold th
  rw [← CategoryTheory.Functor.map_comp, h]

theorem th_one : th C Λ ρ 1 = 𝟙 _ := by
  have h : ModuleCat.ofHom (ρ (1 : C.G)⁻¹) = 𝟙 (ModuleCat.of Λ V) := by
    ext v
    simp
  unfold th
  rw [h, CategoryTheory.Functor.map_id]

theorem th_app_comp (σ τ : C.G) (U : ((SX A).Etale)ᵒᵖ) (v : (VX A Λ V).obj.obj U) :
    ((th C Λ ρ σ).hom.app U).hom (((th C Λ ρ τ).hom.app U).hom v) = ((th C Λ ρ (τ * σ)).hom.app U).hom v := by
  rw [← th_comp]
  rfl

theorem th_app_one (U : ((SX A).Etale)ᵒᵖ) (v : (VX A Λ V).obj.obj U) :
    ((th C Λ ρ 1).hom.app U).hom v = v := by
  rw [th_one]
  rfl

/-- `G` acting on the values of `SV` through `ρ(σ⁻¹)`. -/
def bS (σ : C.G) : SV C Λ V ⟶ SV C Λ V :=
  ObjectProperty.homMk
    { app := fun U => (th C Λ ρ σ).hom.app (op ((etComp (pr C)).obj ((etPull (pr C)).obj U.unop)))
      naturality := fun _ _ f =>
        (th C Λ ρ σ).hom.naturality ((etComp (pr C)).map ((etPull (pr C)).map f.unop)).op }

/-- **The sheaf `F_V`**: sections `s` of `V_X` over `U ×_X Y` with `(1 × σ_Y)^* s = ρ(σ⁻¹) s` for all `σ`. -/
def FV : EtSh Λ (SX A) := eqSh (SV C Λ V) (aS C Λ V) (bS C Λ ρ)

variable {C}

theorem secL_tL (T : (SY C).Etale) (σ τ : C.G) :
    secL T τ ≫ pullback.lift (pullback.fst (T.hom ≫ pr C) (pr C))
      (pullback.snd (T.hom ≫ pr C) (pr C) ≫ act C σ) (by rw [Category.assoc, act_pr]; exact pullback.condition) =
      secL T (τ * σ) := by
  refine pullback.hom_ext (f := T.hom ≫ pr C) (g := pr C) ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, secL_fst, secL_fst]
  · rw [Category.assoc, pullback.lift_snd, secL_snd_assoc, secL_snd, act_mul]

/-- **`ι τ ≫ (1 × σ_Y) = ι (τ σ)`.** -/
theorem sec_tE (T : (SY C).Etale) (σ τ : C.G) : sec T τ ≫ tE C σ (tx T) = sec T (τ * σ) :=
  MorphismProperty.Over.Hom.ext (secL_tL T σ τ)

/-- **Sections of `F_V` over `T` etale over `Y`**: `s(τσ) = ρ(σ⁻¹) s(τ)`. -/
theorem mem_FV_iff (T : (SY C).Etale) (s : (VX A Λ V).obj.obj (op (tp T))) :
    s ∈ eqSecSub (SV C Λ V) (aS C Λ V) (bS C Λ ρ) (tx T) ↔
      ∀ σ τ : C.G, ((VX A Λ V).obj.map (sec T (τ * σ)).op).hom s =
        ((th C Λ ρ σ).hom.app (op (tx T))).hom (((VX A Λ V).obj.map (sec T τ).op).hom s) := by
  constructor
  · intro hs σ τ
    have h := congrArg ((VX A Λ V).obj.map (sec T τ).op).hom
      ((mem_eqSecSub (U := tx T) (SV C Λ V) (aS C Λ V) (bS C Λ ρ) s).1 hs σ)
    calc ((VX A Λ V).obj.map (sec T (τ * σ)).op).hom s
        = ((VX A Λ V).obj.map (sec T τ).op).hom (((VX A Λ V).obj.map (tE C σ (tx T)).op).hom s) := by
          rw [map_map_apply (VX A Λ V) (tE C σ (tx T)) (sec T τ) s, sec_tE]
      _ = ((VX A Λ V).obj.map (sec T τ).op).hom (((th C Λ ρ σ).hom.app (op (tp T))).hom s) := h
      _ = _ := (app_map (th C Λ ρ σ) (sec T τ) s).symm
  · intro h
    refine (mem_eqSecSub (U := tx T) (SV C Λ V) (aS C Λ V) (bS C Λ ρ) s).2 fun σ => ?_
    change ((VX A Λ V).obj.map (tE C σ (tx T)).op).hom s = ((th C Λ ρ σ).hom.app (op (tp T))).hom s
    refine (secMap_bijective Λ (VX A Λ V) T).1 (funext fun τ => ?_)
    change ((VX A Λ V).obj.map (sec T τ).op).hom (((VX A Λ V).obj.map (tE C σ (tx T)).op).hom s) =
      ((VX A Λ V).obj.map (sec T τ).op).hom (((th C Λ ρ σ).hom.app (op (tp T))).hom s)
    rw [map_map_apply (VX A Λ V) (tE C σ (tx T)) (sec T τ) s, sec_tE, ← app_map (th C Λ ρ σ) (sec T τ) s]
    exact h σ τ

end TorSec

end RamanujanPetersson.EtSheaves


