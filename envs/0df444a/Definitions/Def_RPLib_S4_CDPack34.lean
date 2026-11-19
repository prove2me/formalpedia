-- Prove2me | Definitions.Def_RPLib_S4_CDPack34
-- name    : RPLib_S4_CDPack34
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:18:27.356348+00:00
-- url     : https://prove2.me/theorems/5c9e0c7f-36ed-48da-898d-77a352782be5
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 34 of 71
-- statement:
--   Part 34 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacChunkA_Dom`: Group chunk A3 (unit S4-JacChunkA): maximal domains, iso domains and the cocycle
--   * `Def_RP_JacChunkA_Glue`: Group chunk A4 (unit S4-JacChunkA): gluing copies of `X` from pointwise data
--   * `Def_RP_JacChunkA_G`: Group chunk A5 (unit S4-JacChunkA): the glued scheme `G`
--   * `Def_RP_JacChunkA_RC`: Group chunk A6, part 1 (unit S4-JacChunkA): re-charting
--   * `Def_RP_JacChunkA_Pt`: Group chunk A6, part 2 (unit S4-JacChunkA): the closed points of `G` are `H`
--   * `Def_RP_JacChunkA`: Group chunk theorem A (unit S4-JacChunkA), umbrella
--   * `Def_RP_JacChunkB_Ext`: Group chunk B0 (unit S4-JacChunkB): morphisms into `G` are determined by closed points and glue pointwise
--   * `Def_RP_JacChunkB_Act`: Group chunk B1 (unit S4-JacChunkB): the right action `act : G ×_k X ⟶ G`
--   * `Def_RP_JacChunkB_R`: Group chunk B2 (unit S4-JacChunkB): right translations of `G`
--   * `Def_RP_JacChunkB_Mul`: Group chunk B3 (unit S4-JacChunkB): the multiplication `μ : G ×_k G ⟶ G`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack26

/-!
# Curve-duality library package, part 34 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacChunkA_Dom`: Group chunk A3 (unit S4-JacChunkA): maximal domains, iso domains and the cocycle
* `Def_RP_JacChunkA_Glue`: Group chunk A4 (unit S4-JacChunkA): gluing copies of `X` from pointwise data
* `Def_RP_JacChunkA_G`: Group chunk A5 (unit S4-JacChunkA): the glued scheme `G`
* `Def_RP_JacChunkA_RC`: Group chunk A6, part 1 (unit S4-JacChunkA): re-charting
* `Def_RP_JacChunkA_Pt`: Group chunk A6, part 2 (unit S4-JacChunkA): the closed points of `G` are `H`
* `Def_RP_JacChunkA`: Group chunk theorem A (unit S4-JacChunkA), umbrella
* `Def_RP_JacChunkB_Ext`: Group chunk B0 (unit S4-JacChunkB): morphisms into `G` are determined by closed points and glue pointwise
* `Def_RP_JacChunkB_Act`: Group chunk B1 (unit S4-JacChunkB): the right action `act : G ×_k X ⟶ G`
* `Def_RP_JacChunkB_R`: Group chunk B2 (unit S4-JacChunkB): right translations of `G`
* `Def_RP_JacChunkB_Mul`: Group chunk B3 (unit S4-JacChunkB): the multiplication `μ : G ×_k G ⟶ G`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacChunkA_Dom =====
section

/-!
# Group chunk A3 (unit S4-JacChunkA): maximal domains, iso domains and the cocycle

For `σ : Bir k X`, `rep σ` is the representative of `σ` on its maximal domain of definition.
* `rep_of_rep` (KL): any representative of `σ` defined at `x` shows `x ∈ dom σ`, with the same value.
* `rep_comp_apply`: KL for a composite `τ ∘ σ`.
* `W σ`: the open where `σ` is defined and `σ⁻¹` is defined at the image; `tW σ τ h : W σ ⟶ W τ`
  (`τ = σ⁻¹`), `x ↦ σ x`.
* `mem_W_cocycle` / `apply_cocycle`: for `ρ = τσ` and `x ∈ W σ ∩ W ρ`: `σ x ∈ W τ` and `τ (σ x) = ρ x`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

omit [IsAlgClosed k] [IsReduced X] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
include k in
lemma isSeparated_X : X.IsSeparated :=
  ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩

omit [IsReduced X] in
lemma hom_congr {Y : Scheme.{u}} (f : X.PartialMap Y) {x y : X} (h : x = y) (hx : x ∈ f.domain)
    (hy : y ∈ f.domain) : f.hom ⟨x, hx⟩ = f.hom ⟨y, hy⟩ := by
  subst h; rfl

omit [IsReduced X] in
lemma homOfLE_comp_apply {Y : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (f : V.toScheme ⟶ Y) (x : U) :
    (X.homOfLE h ≫ f) x = f ⟨x.1, h x.2⟩ := by
  change f (X.homOfLE h x) = _
  exact congrArg f (Subtype.ext (val_eq_of_comp_ι (X.homOfLE_ι h) x))

variable [X.IsSeparated] [IrreducibleSpace X]

/-- The representative of `σ` on its maximal domain of definition. -/
noncomputable def rep (σ : Bir k X) : X.PartialMap X := σ.1.1.toPartialMap

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma rep_toRationalMap (σ : Bir k X) : (rep σ).toRationalMap = σ.1.1 :=
  Scheme.RationalMap.toRationalMap_toPartialMap _

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
instance rep_isDominant (σ : Bir k X) : IsDominant (rep σ).hom := by
  have := σ.1.2.1
  rw [← rep_toRationalMap σ, Scheme.PartialMap.isDominant_toRationalMap_iff] at this
  exact this

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
instance rep_isOver (σ : Bir k X) : (rep σ).IsOver (Spec (.of k)) :=
  haveI := σ.1.2.2; inferInstanceAs (σ.1.1.toPartialMap.IsOver (Spec (.of k)))

/-- KL: a representative of `σ` defined at `x` shows that `rep σ` is defined at `x`, with the same value. -/
lemma rep_of_rep (f : X.PartialMap X) [f.IsOver (Spec (.of k))] (σ : Bir k X)
    (e : f.toRationalMap = σ.1.1) (x : X) (hx : x ∈ f.domain) :
    ∃ h : x ∈ (rep σ).domain, (rep σ).hom ⟨x, h⟩ = f.hom ⟨x, hx⟩ := by
  have h : x ∈ (rep σ).domain := by
    have := f.le_domain_toRationalMap hx
    rw [e] at this
    exact this
  exact ⟨h, apply_eq_of_toRationalMap_eq (k := k) ((rep_toRationalMap σ).trans e.symm) x h hx⟩

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma comp_rep_toRationalMap (σ τ : Bir k X) :
    ((rep σ).comp (rep τ)).toRationalMap = (τ * σ).1.1 := by
  rw [← Scheme.RationalMap.toRationalMap_comp]
  have key : ∀ (f f' g g' : X ⤏ X) [f.IsDominant] [f'.IsDominant], f = f' → g = g' →
      f.comp g = f'.comp g' := by
    intro f f' g g' _ _ h h'; subst h h'; rfl
  haveI := σ.1.2.1
  exact key _ σ.1.1 _ τ.1.1 (rep_toRationalMap σ) (rep_toRationalMap τ)

/-- KL for a composite: if `σ` is defined at `x` and `τ` at `σ x`, then `ρ = τ σ` is defined at `x`. -/
lemma rep_comp_apply (σ τ ρ : Bir k X) (e : ρ = τ * σ) (x : X) (hx : x ∈ (rep σ).domain)
    (hx' : (rep σ).hom ⟨x, hx⟩ ∈ (rep τ).domain) :
    ∃ h : x ∈ (rep ρ).domain, (rep ρ).hom ⟨x, h⟩ = (rep τ).hom ⟨(rep σ).hom ⟨x, hx⟩, hx'⟩ := by
  haveI := comp_isOver (k := k) (rep σ) (rep τ)
  have h1 : x ∈ ((rep σ).comp (rep τ)).domain := (mem_comp_domain _ _).2 ⟨hx, hx'⟩
  obtain ⟨h, hv⟩ := rep_of_rep ((rep σ).comp (rep τ)) ρ (by rw [comp_rep_toRationalMap, e]) x h1
  exact ⟨h, hv.trans (comp_hom_apply _ _ ⟨x, h1⟩ hx hx')⟩

lemma rep_eq_one (ρ : Bir k X) (e : ρ = 1) (x : X) :
    ∃ h : x ∈ (rep ρ).domain, (rep ρ).hom ⟨x, h⟩ = x := by
  obtain ⟨h, hv⟩ := rep_of_rep (Scheme.PartialMap.id X) ρ (by rw [e]; rfl) x trivial
  exact ⟨h, hv.trans (id_hom_apply x _)⟩

/-- The open where `σ` is defined and `σ⁻¹` is defined at the image. -/
noncomputable def W (σ : Bir k X) : X.Opens := ((rep σ).comp (rep σ⁻¹)).domain

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma mem_W {σ : Bir k X} {x : X} :
    x ∈ W σ ↔ ∃ hx : x ∈ (rep σ).domain, (rep σ).hom ⟨x, hx⟩ ∈ (rep σ⁻¹).domain :=
  mem_comp_domain _ _

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma W_le (σ : Bir k X) : W σ ≤ (rep σ).domain := fun _ hx => (mem_W.1 hx).1

omit [IsAlgClosed k] [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] in
lemma dense_W (σ : Bir k X) : Dense ((W σ : X.Opens) : Set X) := ((rep σ).comp (rep σ⁻¹)).dense_domain

lemma inv_apply_apply (σ : Bir k X) (x : X) (hx : x ∈ (rep σ).domain)
    (hx' : (rep σ).hom ⟨x, hx⟩ ∈ (rep σ⁻¹).domain) : (rep σ⁻¹).hom ⟨(rep σ).hom ⟨x, hx⟩, hx'⟩ = x := by
  obtain ⟨h, hv⟩ := rep_comp_apply σ σ⁻¹ 1 (inv_mul_cancel σ).symm x hx hx'
  obtain ⟨h', hv'⟩ := rep_eq_one (1 : Bir k X) rfl x
  exact hv.symm.trans hv'

lemma mem_W_one (x : X) : x ∈ W (1 : Bir k X) := by
  obtain ⟨h, hv⟩ := rep_eq_one (1 : Bir k X) rfl x
  obtain ⟨h', -⟩ := rep_eq_one ((1 : Bir k X)⁻¹) inv_one x
  exact mem_W.2 ⟨h, by rw [hv]; exact h'⟩

/-- Cocycle, domain part: for `ρ = τ σ` and `x ∈ W σ ∩ W ρ`, `σ x ∈ W τ`. -/
lemma mem_W_cocycle (σ τ ρ : Bir k X) (e : ρ = τ * σ) (x : X) (hσ : x ∈ W σ) (hρ : x ∈ W ρ)
    (hx : x ∈ (rep σ).domain) : (rep σ).hom ⟨x, hx⟩ ∈ W τ := by
  obtain ⟨hx0, hy1⟩ := mem_W.1 hσ
  obtain ⟨hxρ, hz1⟩ := mem_W.1 hρ
  have hv1 := inv_apply_apply σ x hx hy1
  have hv2 := inv_apply_apply ρ x hxρ hz1
  obtain ⟨hyτ, hvτ⟩ := rep_comp_apply σ⁻¹ ρ τ (by rw [e, mul_inv_cancel_right]) _ hy1 (by rw [hv1]; exact hxρ)
  obtain ⟨hzτ, -⟩ := rep_comp_apply ρ⁻¹ σ τ⁻¹ (by rw [e, mul_inv_rev, mul_inv_cancel_left]) _ hz1
    (by rw [hv2]; exact hx)
  refine mem_W.2 ⟨hyτ, ?_⟩
  rw [hvτ, hom_congr (rep ρ) hv1 _ hxρ]
  exact hzτ

/-- Cocycle, value part: for `ρ = τ σ` and `x ∈ W σ ∩ W ρ`, `τ (σ x) = ρ x`. -/
lemma apply_cocycle (σ τ ρ : Bir k X) (e : ρ = τ * σ) (x : X) (hσ : x ∈ W σ) (hx : x ∈ (rep σ).domain)
    (hy : (rep σ).hom ⟨x, hx⟩ ∈ (rep τ).domain) (hxρ : x ∈ (rep ρ).domain) :
    (rep τ).hom ⟨(rep σ).hom ⟨x, hx⟩, hy⟩ = (rep ρ).hom ⟨x, hxρ⟩ := by
  obtain ⟨hx0, hy1⟩ := mem_W.1 hσ
  have hv1 := inv_apply_apply σ x hx hy1
  obtain ⟨hyτ, hvτ⟩ := rep_comp_apply σ⁻¹ ρ τ (by rw [e, mul_inv_cancel_right]) _ hy1 (by rw [hv1]; exact hxρ)
  exact hvτ.trans (hom_congr (rep ρ) hv1 _ hxρ)

/-- The transition map `W σ ⟶ W τ`, `x ↦ σ x`, for `τ = σ⁻¹`. -/
noncomputable def tW (σ τ : Bir k X) (h : τ = σ⁻¹) : (W σ).toScheme ⟶ (W τ).toScheme :=
  liftO (W τ) (X.homOfLE (W_le σ) ≫ (rep σ).hom) (fun x => by
    refine (congrArg (· ∈ W τ) (homOfLE_comp_apply (W_le σ) (rep σ).hom x)).mpr ?_
    subst h
    exact mem_W_cocycle σ σ⁻¹ 1 (inv_mul_cancel σ).symm x.1 x.2 (mem_W_one x.1) _)

lemma tW_apply (σ τ : Bir k X) (h : τ = σ⁻¹) (x : W σ) :
    (tW σ τ h x).1 = (rep σ).hom ⟨x.1, W_le σ x.2⟩ := by
  unfold tW
  refine (val_eq_of_comp_ι (ψ := X.homOfLE (W_le σ) ≫ (rep σ).hom) (liftO_ι _ _ _) x).trans ?_
  exact homOfLE_comp_apply (W_le σ) (rep σ).hom x

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkA_Glue =====
section

/-!
# Group chunk A4 (unit S4-JacChunkA): gluing copies of `X` from pointwise data

`PtGlue k X`: opens `V i j` of `X` (`V i i = ⊤`) and `k`-morphisms `t i j : V i j ⟶ V j i` with the
gluing identities checked at points. `PtGlue.toGlueData` turns it into a `Scheme.GlueData` whose charts are
all `X` (morphism identities follow from `ext_of_apply_eq`, since `X` is reduced, lft and separated over `k`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

omit [IsReduced X] in
/-- Morphisms into `X` from a reduced lft `k`-scheme are determined by their values at closed points. -/
lemma ext_X {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
    (f g : T ⟶ X) (hf : f ≫ X ↘ Spec (.of k) = sT) (hg : g ≫ X ↘ Spec (.of k) = sT)
    (h : ∀ x, IsClosed {x} → f x = g x) : f = g := by
  have : LocallyOfFiniteType (f ≫ X ↘ Spec (.of k)) := by rw [hf]; infer_instance
  exact ext_of_apply_eq (X ↘ Spec (.of k)) Set.univ isOpen_univ.isLocallyClosed dense_univ
    (fun x _ hx => h x hx) (hf.trans hg.symm)

variable (k X) in
/-- Pointwise gluing data for copies of `X`. -/
structure PtGlue where
  J : Type u
  V : J → J → X.Opens
  V_self : ∀ i, V i i = ⊤
  t : ∀ i j, (V i j).toScheme ⟶ (V j i).toScheme
  t_over : ∀ i j, t i j ≫ (V j i).ι ≫ X ↘ Spec (.of k) = (V i j).ι ≫ X ↘ Spec (.of k)
  t_self : ∀ i (x : V i i), (t i i x).1 = x.1
  t_mem : ∀ i j l (x : X) (hij : x ∈ V i j), x ∈ V i l → (t i j ⟨x, hij⟩).1 ∈ V j l
  t_cocycle : ∀ i j l (x : X) (hij : x ∈ V i j) (hil : x ∈ V i l) (h : (t i j ⟨x, hij⟩).1 ∈ V j l),
    (t j l ⟨(t i j ⟨x, hij⟩).1, h⟩).1 = (t i l ⟨x, hil⟩).1

namespace PtGlue

variable (D : PtGlue k X)

include D in
omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma P_val (i j l : D.J) (p : (pullback (D.V i j).ι (D.V i l).ι : Scheme.{u})) :
    (pullback.fst (D.V i j).ι (D.V i l).ι p).1 = (pullback.snd (D.V i j).ι (D.V i l).ι p).1 :=
  congrArg (fun φ => φ p) (pullback.condition (f := (D.V i j).ι) (g := (D.V i l).ι))

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma t_cocycle_val (i j l : D.J) (a : D.V i j) (b : D.V j l) (hil : a.1 ∈ D.V i l)
    (hb : b.1 = (D.t i j a).1) : (D.t j l b).1 = (D.t i l ⟨a.1, hil⟩).1 := by
  have hm : (D.t i j a).1 ∈ D.V j l := by rw [← hb]; exact b.2
  have e : b = ⟨(D.t i j a).1, hm⟩ := Subtype.ext hb
  rw [e]
  exact D.t_cocycle i j l a.1 a.2 hil hm

/-- The triple-overlap transition map. -/
noncomputable def t' (i j l : D.J) :
    pullback (D.V i j).ι (D.V i l).ι ⟶ pullback (D.V j l).ι (D.V j i).ι :=
  pullback.lift
    (liftO (D.V j l) (pullback.fst _ _ ≫ D.t i j ≫ (D.V j i).ι) (fun p => by
      have hil : (pullback.fst (D.V i j).ι (D.V i l).ι p).1 ∈ D.V i l := by
        rw [D.P_val]; exact (pullback.snd (D.V i j).ι (D.V i l).ι p).2
      exact D.t_mem i j l _ (pullback.fst (D.V i j).ι (D.V i l).ι p).2 hil))
    (pullback.fst _ _ ≫ D.t i j)
    ((liftO_ι _ _ _).trans (Category.assoc _ _ _).symm)

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
@[reassoc]
lemma t'_fst (i j l : D.J) :
    D.t' i j l ≫ pullback.fst _ _ ≫ (D.V j l).ι = pullback.fst _ _ ≫ D.t i j ≫ (D.V j i).ι := by
  unfold t'
  rw [pullback.lift_fst_assoc]
  exact liftO_ι _ _ _

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma t'_snd (i j l : D.J) : D.t' i j l ≫ pullback.snd _ _ = pullback.fst _ _ ≫ D.t i j :=
  pullback.lift_snd _ _ _

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
lemma t'_fst_val (i j l : D.J) (p : (pullback (D.V i j).ι (D.V i l).ι : Scheme.{u})) :
    (pullback.fst (D.V j l).ι (D.V j i).ι (D.t' i j l p)).1 = (D.t i j (pullback.fst (D.V i j).ι (D.V i l).ι p)).1 :=
  congrArg (fun φ => φ p) (D.t'_fst i j l)

omit [IsReduced X] [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] in
@[reassoc]
lemma t'_over (i j l : D.J) :
    D.t' i j l ≫ pullback.fst _ _ ≫ (D.V j l).ι ≫ X ↘ Spec (.of k) =
      pullback.fst _ _ ≫ (D.V i j).ι ≫ X ↘ Spec (.of k) := by
  rw [D.t'_fst_assoc, D.t_over]

@[reassoc]
lemma cocycle_fst (i j l : D.J) :
    D.t' i j l ≫ D.t' j l i ≫ D.t' l i j ≫ pullback.fst _ _ = pullback.fst _ _ := by
  haveI := isReduced_of_isOpenImmersion (pullback.fst (D.V i j).ι (D.V i l).ι ≫ (D.V i j).ι)
  refine (cancel_mono (D.V i j).ι).1 ?_
  refine ext_X (pullback.fst _ _ ≫ (D.V i j).ι ≫ X ↘ Spec (.of k)) _ _ ?_ ?_ ?_
  · simp only [Category.assoc, D.t'_over]
  · simp only [Category.assoc]
  · intro p _
    change (pullback.fst (D.V i j).ι (D.V i l).ι (D.t' l i j (D.t' j l i (D.t' i j l p)))).1 =
      (pullback.fst (D.V i j).ι (D.V i l).ι p).1
    have hil : (pullback.fst (D.V i j).ι (D.V i l).ι p).1 ∈ D.V i l := by
      rw [D.P_val]; exact (pullback.snd (D.V i j).ι (D.V i l).ι p).2
    have hii : (pullback.fst (D.V i j).ι (D.V i l).ι p).1 ∈ D.V i i := by
      rw [D.V_self i]; trivial
    have e1 := D.t'_fst_val i j l p
    have e2 := D.t'_fst_val j l i (D.t' i j l p)
    have e3 := D.t'_fst_val l i j (D.t' j l i (D.t' i j l p))
    have c1 := D.t_cocycle_val i j l _ _ hil e1
    have c2 := D.t_cocycle_val i l i ⟨_, hil⟩ _ hii (e2.trans c1)
    exact e3.trans (c2.trans (D.t_self i _))

/-- The glue data. -/
noncomputable def toGlueData : Scheme.GlueData.{u} where
  J := D.J
  U _ := X
  V p := (D.V p.1 p.2).toScheme
  f i j := (D.V i j).ι
  f_id i := by
    change IsIso (D.V i i).ι
    rw [D.V_self i]
    exact ⟨X.topIso.inv, Scheme.ι_toIso_inv X, Scheme.toIso_inv_ι X⟩
  t := D.t
  t_id i := by
    change D.t i i = 𝟙 _
    refine (cancel_mono (D.V i i).ι).1 ?_
    refine ext_X ((D.V i i).ι ≫ X ↘ Spec (.of k)) _ _ ?_ ?_ ?_
    · rw [Category.assoc, D.t_over]
    · rw [Category.id_comp]
    · intro x _
      exact D.t_self i x
  t' := D.t'
  t_fac i j l := D.t'_snd i j l
  cocycle i j l := by
    change D.t' i j l ≫ D.t' j l i ≫ D.t' l i j = 𝟙 _
    refine pullback.hom_ext ?_ ?_
    · rw [Category.id_comp, Category.assoc, Category.assoc]
      exact D.cocycle_fst i j l
    · refine (cancel_mono (D.V i l).ι).1 ?_
      simp only [Category.assoc, Category.id_comp]
      rw [← pullback.condition, D.cocycle_fst_assoc]
  f_open i j := inferInstance

end PtGlue

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkA_G =====
section

/-!
# Group chunk A5 (unit S4-JacChunkA): the glued scheme `G`

For a subgroup `H` of `Bir k X`: charts `X` indexed by `H`, overlaps `V σ τ := W (τ⁻¹ σ)` and transitions
`x ↦ (τ⁻¹ σ) x` form pointwise gluing data `gD H`. `G H` is the glued scheme, `ι H σ : X ⟶ G H` the charts
(open immersions), `sG H` the structure morphism to `Spec k` (lft), `G H` is reduced and irreducible, and
`L H h` (chart `σ ↦ h σ`) is the left action of `H`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

lemma tW_ι (σ τ : Bir k X) (h : τ = σ⁻¹) :
    tW σ τ h ≫ (W τ).ι = X.homOfLE (W_le σ) ≫ (rep σ).hom := liftO_ι _ _ _

lemma tW_over (σ τ : Bir k X) (h : τ = σ⁻¹) :
    tW σ τ h ≫ (W τ).ι ≫ X ↘ Spec (.of k) = (W σ).ι ≫ X ↘ Spec (.of k) := by
  rw [← Category.assoc, tW_ι, Category.assoc]
  refine (congrArg (X.homOfLE (W_le σ) ≫ ·)
    (HomIsOver.comp_over (f := (rep σ).hom) (S := Spec (.of k)))).trans ?_
  change X.homOfLE (W_le σ) ≫ (rep σ).domain.ι ≫ X ↘ Spec (.of k) = _
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- Transport of a gluing identity along an equality of group elements. -/
lemma tW_transport {Z : Scheme.{u}} (p q : X ⟶ Z) (c c' d d' : Bir k X) (e : c' = c) (hd : d = c⁻¹)
    (hd' : d' = c'⁻¹) (H' : tW c' d' hd' ≫ (W d').ι ≫ q = (W c').ι ≫ p) :
    tW c d hd ≫ (W d).ι ≫ q = (W c).ι ≫ p := by
  subst e hd hd'
  exact H'

lemma W_one_eq : W (1 : Bir k X) = ⊤ := top_unique fun x _ => mem_W_one x

lemma inv_mul_eq_inv (a b : Bir k X) : a⁻¹ * b = (b⁻¹ * a)⁻¹ := by rw [mul_inv_rev, inv_inv]

/-- The transition `W (b⁻¹ a) ⟶ W (a⁻¹ b)`, `x ↦ (b⁻¹ a) x`. -/
noncomputable def tH (a b : Bir k X) : (W (b⁻¹ * a)).toScheme ⟶ (W (a⁻¹ * b)).toScheme :=
  tW _ _ (inv_mul_eq_inv a b)

lemma tH_apply (a b : Bir k X) (x : W (b⁻¹ * a)) :
    (tH a b x).1 = (rep (b⁻¹ * a)).hom ⟨x.1, W_le _ x.2⟩ := tW_apply _ _ _ x

lemma tH_self (a : Bir k X) (x : W (a⁻¹ * a)) : (tH a a x).1 = x.1 := by
  rw [tH_apply]
  obtain ⟨_, hv⟩ := rep_eq_one (a⁻¹ * a) (inv_mul_cancel a) x.1
  exact hv

lemma tH_mem (a b c : Bir k X) (x : X) (h1 : x ∈ W (b⁻¹ * a)) (h2 : x ∈ W (c⁻¹ * a)) :
    (tH a b ⟨x, h1⟩).1 ∈ W (c⁻¹ * b) := by
  rw [tH_apply]
  exact mem_W_cocycle (b⁻¹ * a) (c⁻¹ * b) (c⁻¹ * a) (by rw [mul_assoc, mul_inv_cancel_left]) x h1 h2 _

lemma tH_cocycle (a b c : Bir k X) (x : X) (h1 : x ∈ W (b⁻¹ * a)) (h2 : x ∈ W (c⁻¹ * a))
    (h : (tH a b ⟨x, h1⟩).1 ∈ W (c⁻¹ * b)) :
    (tH b c ⟨(tH a b ⟨x, h1⟩).1, h⟩).1 = (tH a c ⟨x, h2⟩).1 := by
  have hy : (rep (b⁻¹ * a)).hom ⟨x, W_le _ h1⟩ ∈ (rep (c⁻¹ * b)).domain :=
    (congrArg (· ∈ (rep (c⁻¹ * b)).domain) (tH_apply a b ⟨x, h1⟩)).mp (W_le _ h)
  calc (tH b c ⟨(tH a b ⟨x, h1⟩).1, h⟩).1
      = (rep (c⁻¹ * b)).hom ⟨(tH a b ⟨x, h1⟩).1, W_le _ h⟩ := tH_apply b c _
    _ = (rep (c⁻¹ * b)).hom ⟨(rep (b⁻¹ * a)).hom ⟨x, W_le _ h1⟩, hy⟩ :=
        hom_congr _ (tH_apply a b _) _ _
    _ = (rep (c⁻¹ * a)).hom ⟨x, W_le _ h2⟩ :=
        apply_cocycle (b⁻¹ * a) (c⁻¹ * b) (c⁻¹ * a) (by rw [mul_assoc, mul_inv_cancel_left]) x h1
          (W_le _ h1) hy (W_le _ h2)
    _ = (tH a c ⟨x, h2⟩).1 := (tH_apply a c ⟨x, h2⟩).symm

variable (H : Subgroup (Bir k X))

/-- Overlaps: `V σ τ := W (τ⁻¹ σ)`. -/
noncomputable def VH (σ τ : H) : X.Opens := W ((τ : Bir k X)⁻¹ * (σ : Bir k X))

/-- Transitions `V σ τ ⟶ V τ σ`. -/
noncomputable def tHH (σ τ : H) : (VH H σ τ).toScheme ⟶ (VH H τ σ).toScheme := tH (σ : Bir k X) τ

lemma VH_self (σ : H) : VH H σ σ = ⊤ := (congrArg W (inv_mul_cancel (σ : Bir k X))).trans W_one_eq

lemma tHH_over (σ τ : H) :
    tHH H σ τ ≫ (VH H τ σ).ι ≫ X ↘ Spec (.of k) = (VH H σ τ).ι ≫ X ↘ Spec (.of k) :=
  tW_over ((τ : Bir k X)⁻¹ * (σ : Bir k X)) ((σ : Bir k X)⁻¹ * (τ : Bir k X)) (inv_mul_eq_inv _ _)

lemma tHH_self (σ : H) (x : VH H σ σ) : (tHH H σ σ x).1 = x.1 := tH_self (σ : Bir k X) x

lemma tHH_mem (σ τ ρ : H) (x : X) (h1 : x ∈ VH H σ τ) (h2 : x ∈ VH H σ ρ) :
    (tHH H σ τ ⟨x, h1⟩).1 ∈ VH H τ ρ := tH_mem (σ : Bir k X) τ ρ x h1 h2

lemma tHH_cocycle (σ τ ρ : H) (x : X) (h1 : x ∈ VH H σ τ) (h2 : x ∈ VH H σ ρ)
    (h : (tHH H σ τ ⟨x, h1⟩).1 ∈ VH H τ ρ) :
    (tHH H τ ρ ⟨(tHH H σ τ ⟨x, h1⟩).1, h⟩).1 = (tHH H σ ρ ⟨x, h2⟩).1 :=
  tH_cocycle (σ : Bir k X) τ ρ x h1 h2 h

/-- The pointwise gluing data of the charts indexed by `H`. -/
noncomputable def gD : PtGlue k X where
  J := H
  V := VH H
  V_self := VH_self H
  t := tHH H
  t_over := tHH_over H
  t_self := tHH_self H
  t_mem := tHH_mem H
  t_cocycle := tHH_cocycle H

/-- The glued scheme. -/
noncomputable abbrev G : Scheme.{u} := (gD H).toGlueData.glued

/-- The chart of index `σ`. -/
noncomputable abbrev ι (σ : H) : X ⟶ G H := (gD H).toGlueData.ι σ

lemma ι_glue (σ τ : H) : tHH H σ τ ≫ (VH H τ σ).ι ≫ ι H τ = (VH H σ τ).ι ≫ ι H σ :=
  (gD H).toGlueData.glue_condition σ τ

/-- The structure morphism of `G H`. -/
noncomputable def sG : G H ⟶ Spec (.of k) :=
  Multicoequalizer.desc _ _ (fun _ => X ↘ Spec (.of k)) (by
    rintro ⟨σ, τ⟩
    exact ((Category.assoc _ _ _).trans (tHH_over H σ τ)).symm)

lemma ι_sG (σ : H) : ι H σ ≫ sG H = X ↘ Spec (.of k) := Multicoequalizer.π_desc _ _ _ _ _

noncomputable instance : (G H).Over (Spec (.of k)) where
  hom := sG H

instance (σ : H) : (ι H σ).IsOver (Spec (.of k)) := ⟨ι_sG H σ⟩

instance (σ : H) : IsOpenImmersion (ι H σ) := Scheme.GlueData.ι_isOpenImmersion (gD H).toGlueData σ

instance : LocallyOfFiniteType (G H ↘ Spec (.of k)) := by
  have hP : ∀ σ : H, LocallyOfFiniteType (ι H σ ≫ sG H) := fun σ => by
    rw [ι_sG]
    all_goals infer_instance
  first
  | exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (gD H).toGlueData.openCover hP
  | exact (set_option backward.isDefEq.respectTransparency.types false in
      IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (gD H).toGlueData.openCover hP)

instance : IsReduced (G H) := by
  have : ∀ σ, IsReduced ((gD H).toGlueData.openCover.X σ) := fun _ => (inferInstance : IsReduced X)
  exact IsReduced.of_openCover _ (gD H).toGlueData.openCover

lemma ι_meet (σ τ : H) : ∃ x y, ι H σ x = ι H τ y := by
  obtain ⟨x, hx⟩ := (dense_W ((τ : Bir k X)⁻¹ * (σ : Bir k X))).nonempty
  refine ⟨x, (tHH H σ τ ⟨x, hx⟩).1, ?_⟩
  exact (congrArg (fun φ => φ ⟨x, hx⟩) (ι_glue H σ τ)).symm

instance : IrreducibleSpace (G H) := by
  rw [irreducibleSpace_def]
  have hirr : ∀ σ : H, IsIrreducible (Set.range (ι H σ)) := fun σ => by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ X).image _ (ι H σ).continuous.continuousOn
  have hcl : closure (Set.range (ι H 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨σ, x, rfl⟩ := (gD H).toGlueData.ι_jointly_surjective g
    obtain ⟨y, z, hyz⟩ := ι_meet H σ 1
    have hs := subset_closure_inter_of_isPreirreducible_of_isOpen (hirr σ).isPreirreducible
      (ι H 1).isOpenEmbedding.isOpen_range ⟨_, ⟨y, rfl⟩, ⟨z, hyz.symm⟩⟩
    exact closure_mono Set.inter_subset_right (hs ⟨x, rfl⟩)
  have h1 := isIrreducible_iff_closure.2 (hirr 1)
  rw [hcl] at h1
  exact h1

lemma ι_glue_transport (h σ τ : H) :
    (VH H σ τ).ι ≫ ι H (h * σ) = (tHH H σ τ ≫ (VH H τ σ).ι) ≫ ι H (h * τ) := by
  have e : ((h * τ : H) : Bir k X)⁻¹ * ((h * σ : H) : Bir k X) = (τ : Bir k X)⁻¹ * (σ : Bir k X) := by
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  rw [Category.assoc]
  exact (tW_transport (ι H (h * σ)) (ι H (h * τ)) _ _ _ _ e (inv_mul_eq_inv _ _) (inv_mul_eq_inv _ _)
    (ι_glue H (h * σ) (h * τ))).symm

/-- Left translation by `h ∈ H`: chart `σ` goes to chart `h σ`. -/
noncomputable def L (h : H) : G H ⟶ G H :=
  Multicoequalizer.desc _ _ (fun σ : H => ι H (h * σ)) (by
    rintro ⟨σ, τ⟩
    exact ι_glue_transport H h σ τ)

lemma ι_L (h σ : H) : ι H σ ≫ L H h = ι H (h * σ) := Multicoequalizer.π_desc _ _ _ _ _

lemma G_hom_ext {Z : Scheme.{u}} (f g : G H ⟶ Z) (e : ∀ σ, ι H σ ≫ f = ι H σ ≫ g) : f = g :=
  Multicoequalizer.hom_ext _ _ _ e

lemma L_one : L H 1 = 𝟙 _ :=
  G_hom_ext H _ _ fun σ => by rw [ι_L, one_mul, Category.comp_id]

lemma L_mul (h h' : H) : L H (h * h') = L H h' ≫ L H h :=
  G_hom_ext H _ _ fun σ => by rw [ι_L, ← Category.assoc, ι_L, ι_L, mul_assoc]

lemma L_over (h : H) : L H h ≫ sG H = sG H :=
  G_hom_ext H _ _ fun σ => by rw [← Category.assoc, ι_L, ι_sG, ι_sG]

/-- The left action of `h ∈ H` as an automorphism of `G H`. -/
noncomputable def Liso (h : H) : G H ≅ G H where
  hom := L H h
  inv := L H h⁻¹
  hom_inv_id := by rw [← L_mul, inv_mul_cancel, L_one]
  inv_hom_id := by rw [← L_mul, mul_inv_cancel, L_one]

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkA_RC =====
section

/-!
# Group chunk A6, part 1 (unit S4-JacChunkA): re-charting

`Takes σ x y` says that the maximal representative of `σ : Bir k X` is defined at `x` with value `y`.
For a strict chunk `C`, `σ ∈ C.H` and closed points `x y`:
* `RC_fwd`: `Takes σ x y → σ * λ_x = λ_y`;
* `RC_bwd`: `σ * λ_x = λ_y → Takes σ x y`;
* `RC_W`: `Takes σ x y → x ∈ W σ`, and `lamB_inj`: `λ_x = λ_y → x = y`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

/-- Two nonempty opens of an irreducible Jacobson space share a closed point. -/
lemma exists_closed_inter {T : Type*} [TopologicalSpace T] [JacobsonSpace T] [PreirreducibleSpace T]
    (U V : TopologicalSpace.Opens T) (hU : (U : Set T).Nonempty) (hV : (V : Set T).Nonempty) :
    ∃ z, z ∈ U ∧ z ∈ V ∧ IsClosed ({z} : Set T) := by
  obtain ⟨z, ⟨hzU, hzV⟩, hz⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter U.2 V.2 hU hV) (U.2.inter V.2).isLocallyClosed
  exact ⟨z, hzU, hzV, hz⟩

lemma pi_mem_target {X : Scheme.{u}} (f : X.PartialIso X) (u : X) (hu : u ∈ f.toPartialMap.domain) :
    f.toPartialMap.hom ⟨u, hu⟩ ∈ f.symm.toPartialMap.domain :=
  (congrArg (· ∈ f.target) (val_eq_of_comp_ι (φ := f.iso.hom) (ψ := f.toPartialMap.hom) rfl ⟨u, hu⟩)).mp
    (f.iso.hom ⟨u, hu⟩).2

lemma pi_symm_apply {X : Scheme.{u}} (f : X.PartialIso X) (u : X) (hu : u ∈ f.toPartialMap.domain)
    (h : f.toPartialMap.hom ⟨u, hu⟩ ∈ f.symm.toPartialMap.domain) :
    f.symm.toPartialMap.hom ⟨f.toPartialMap.hom ⟨u, hu⟩, h⟩ = u := by
  have h' := congrArg (fun φ => (φ ⟨u, hu⟩ : f.source.toScheme)) f.iso.hom_inv_id
  exact congrArg Subtype.val h'

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

/-- The maximal representative of `σ` is defined at `x`, with value `y`. -/
def Takes (σ : Bir k X) (x y : X) : Prop := ∃ h : x ∈ (rep σ).domain, (rep σ).hom ⟨x, h⟩ = y

lemma Takes.comp {σ τ ρ : Bir k X} {x v w : X} (h1 : Takes σ x v) (h2 : Takes τ v w) (e : ρ = τ * σ) :
    Takes ρ x w := by
  obtain ⟨hx, rfl⟩ := h1
  obtain ⟨hv, rfl⟩ := h2
  exact rep_comp_apply σ τ ρ e x hx hv

lemma Takes.unique {σ : Bir k X} {x w w' : X} (h1 : Takes σ x w) (h2 : Takes σ x w') : w = w' := by
  obtain ⟨h, rfl⟩ := h1
  obtain ⟨h', rfl⟩ := h2
  rfl

lemma Takes.of_eq {σ σ' : Bir k X} {x w : X} (e : σ = σ') (h : Takes σ x w) : Takes σ' x w := by
  subst e; exact h

lemma Takes.val_eq {σ : Bir k X} {x w w' : X} (h : Takes σ x w) (e : w = w') : Takes σ x w' := by
  subst e; exact h

lemma Takes.src_eq {σ : Bir k X} {v v' w : X} (h : Takes σ v w) (e : v = v') : Takes σ v' w := by
  subst e; exact h

lemma takes_one (x : X) : Takes (1 : Bir k X) x x := rep_eq_one 1 rfl x

lemma takes_self (σ : Bir k X) (x : X) (h : x ∈ (rep σ).domain) : Takes σ x ((rep σ).hom ⟨x, h⟩) := ⟨h, rfl⟩

lemma secL_eq_secR (x : X) (hx : IsClosed {x}) (z : X) (hz : IsClosed {z}) :
    secL (sX := X ↘ Spec (.of k)) x hx z = secR z hz x :=
  closedPoint_pullback_ext (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) _ _ (secL_isClosed x hx z hz)
    (secR_isClosed z hz x hx) ((secL_apply_fst x hx z).trans (secR_apply_fst z hz x).symm)
    ((secL_apply_snd x hx z).trans (secR_apply_snd z hz x).symm)

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

lemma lam_mem_rho (x : X) (hx : IsClosed {x}) (z : X) (hz : IsClosed {z})
    (h : z ∈ (C.lam x hx).toPartialMap.domain) : x ∈ (C.rho z hz).toPartialMap.domain := by
  have h' : secL x hx z ∈ C.Ω := (Scheme.Hom.mem_preimage _).1 h
  change x ∈ secR z hz ⁻¹ᵁ C.Ω
  rw [Scheme.Hom.mem_preimage, ← secL_eq_secR x hx z hz]
  exact h'

lemma lam_eq_rho (x : X) (hx : IsClosed {x}) (z : X) (hz : IsClosed {z})
    (h : z ∈ (C.lam x hx).toPartialMap.domain) :
    (C.rho z hz).toPartialMap.hom ⟨x, C.lam_mem_rho x hx z hz h⟩ = (C.lam x hx).toPartialMap.hom ⟨z, h⟩ :=
  (C.rho_apply z hz x _).trans (Eq.trans (congrArg C.m (Subtype.ext (secL_eq_secR x hx z hz).symm))
    (C.lam_apply x hx z h).symm)

lemma lamB_takes (a : X) (ha : IsClosed {a}) (z : X) (hz : z ∈ (C.lam a ha).toPartialMap.domain) :
    Takes (C.lamB a ha) z ((C.lam a ha).toPartialMap.hom ⟨z, hz⟩) := by
  haveI := pi_isOver _ (C.lam_isOver a ha)
  exact rep_of_rep _ (C.lamB a ha) rfl z hz

lemma rhoB_takes (b : X) (hb : IsClosed {b}) (z : X) (hz : z ∈ (C.rho b hb).toPartialMap.domain) :
    Takes (C.rhoB b hb) z ((C.rho b hb).toPartialMap.hom ⟨z, hz⟩) := by
  haveI := pi_isOver _ (C.rho_isOver b hb)
  exact rep_of_rep _ (C.rhoB b hb) rfl z hz

lemma lamB_inv_takes (a : X) (ha : IsClosed {a}) (z : X) (hz : z ∈ (C.lam a ha).toPartialMap.domain) :
    Takes (C.lamB a ha)⁻¹ ((C.lam a ha).toPartialMap.hom ⟨z, hz⟩) z := by
  haveI := pi_isOver _ (C.lam_isOver a ha).symm
  obtain ⟨h, e⟩ := rep_of_rep (C.lam a ha).symm.toPartialMap (C.lamB a ha)⁻¹ rfl _ (pi_mem_target _ z hz)
  exact ⟨h, e.trans (pi_symm_apply _ z hz _)⟩

lemma rhoB_inv_takes (b : X) (hb : IsClosed {b}) (z : X) (hz : z ∈ (C.rho b hb).toPartialMap.domain) :
    Takes (C.rhoB b hb)⁻¹ ((C.rho b hb).toPartialMap.hom ⟨z, hz⟩) z := by
  haveI := pi_isOver _ (C.rho_isOver b hb).symm
  obtain ⟨h, e⟩ := rep_of_rep (C.rho b hb).symm.toPartialMap (C.rhoB b hb)⁻¹ rfl _ (pi_mem_target _ z hz)
  exact ⟨h, e.trans (pi_symm_apply _ z hz _)⟩

/-- Re-charting, forward: if `σ ∈ H` sends the closed point `x` to `y`, then `σ λ_x = λ_y`. -/
theorem RC_fwd (σ : Bir k X) (hσ : σ ∈ C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y})
    (h : Takes σ x y) : σ * C.lamB x hx = C.lamB y hy := by
  haveI := pi_isDominant (C.lam x hx)
  haveI := pi_isOver _ (C.lam_isOver x hx)
  haveI := pi_isOver _ (C.lam_isOver y hy)
  haveI := comp_isOver (k := k) (C.lam x hx).toPartialMap (rep σ)
  refine Units.ext (Subtype.ext ?_)
  change (C.lam x hx).toPartialMap.toRationalMap.comp σ.1.1 = (C.lam y hy).toPartialMap.toRationalMap
  rw [← rep_toRationalMap σ, Scheme.RationalMap.toRationalMap_comp]
  refine toRationalMap_eq_of_apply (k := k) ?_
  intro z h1 h2 hz
  obtain ⟨hz1, hz2⟩ := (mem_comp_domain _ _).1 h1
  rw [comp_hom_apply _ _ ⟨z, h1⟩ hz1 hz2]
  have t1 : Takes (σ * C.rhoB z hz) x ((rep σ).hom ⟨_, hz2⟩) :=
    Takes.comp ((C.rhoB_takes z hz x (C.lam_mem_rho x hx z hz hz1)).val_eq (C.lam_eq_rho x hx z hz hz1))
      (takes_self σ _ hz2) rfl
  have t2 : Takes (C.rhoB z hz * σ) x ((C.lam y hy).toPartialMap.hom ⟨z, h2⟩) :=
    Takes.comp h ((C.rhoB_takes z hz y (C.lam_mem_rho y hy z hz h2)).val_eq (C.lam_eq_rho y hy z hz h2)) rfl
  exact Takes.unique t1 (t2.of_eq (C.H_comm_rhoB σ hσ z hz).symm)

/-- Re-charting, backward: if `σ ∈ H` and `σ λ_x = λ_y`, then `σ` sends `x` to `y`. -/
theorem RC_bwd (σ : Bir k X) (hσ : σ ∈ C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y})
    (h : σ * C.lamB x hx = C.lamB y hy) : Takes σ x y := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨u, hux, huy, hu⟩ := exists_closed_inter (C.lam x hx).toPartialMap.domain
    (C.lam y hy).toPartialMap.domain (C.lam_ne x hx) (C.lam_ne y hy)
  have tp : Takes σ ((C.lam x hx).toPartialMap.hom ⟨u, hux⟩) ((C.lam y hy).toPartialMap.hom ⟨u, huy⟩) :=
    Takes.comp (C.lamB_inv_takes x hx u hux) (C.lamB_takes y hy u huy) (eq_mul_inv_of_mul_eq h)
  have t1 : Takes (σ * C.rhoB u hu) x ((C.lam y hy).toPartialMap.hom ⟨u, huy⟩) :=
    Takes.comp ((C.rhoB_takes u hu x (C.lam_mem_rho x hx u hu hux)).val_eq (C.lam_eq_rho x hx u hu hux))
      tp rfl
  have t2 : Takes (C.rhoB u hu)⁻¹ ((C.lam y hy).toPartialMap.hom ⟨u, huy⟩) y :=
    (C.rhoB_inv_takes u hu y (C.lam_mem_rho y hy u hu huy)).src_eq (C.lam_eq_rho y hy u hu huy)
  refine Takes.comp t1 t2 ?_
  rw [C.H_comm_rhoB σ hσ u hu, inv_mul_cancel_left]

/-- A point sent to a closed point by `σ ∈ H` lies in `W σ`. -/
theorem RC_W (σ : Bir k X) (hσ : σ ∈ C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y})
    (h : Takes σ x y) : x ∈ W σ := by
  have e := C.RC_fwd σ hσ x hx y hy h
  have e' : σ⁻¹ * C.lamB y hy = C.lamB x hx := by rw [← e, inv_mul_cancel_left]
  obtain ⟨hy', -⟩ := C.RC_bwd σ⁻¹ (inv_mem hσ) y hy x hx e'
  obtain ⟨hd, hv⟩ := h
  exact mem_W.2 ⟨hd, by rw [hv]; exact hy'⟩

theorem RC_inv (σ : Bir k X) (hσ : σ ∈ C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y})
    (h : Takes σ x y) : Takes σ⁻¹ y x := by
  have e := C.RC_fwd σ hσ x hx y hy h
  exact C.RC_bwd σ⁻¹ (inv_mem hσ) y hy x hx (by rw [← e, inv_mul_cancel_left])

/-- Left translation is injective on closed points. -/
theorem lamB_inj (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y}) (h : C.lamB x hx = C.lamB y hy) :
    x = y :=
  Takes.unique (takes_one x) (C.RC_bwd 1 (one_mem _) x hx y hy (by rw [one_mul, h]))

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkA_Pt =====
section

/-!
# Group chunk A6, part 2 (unit S4-JacChunkA): the closed points of `G` are `H`

For a strict chunk `C` with `H := C.H` and `G := G C.H`:
* `ι_eq_iff_mul`: for closed `x y`, `ι σ x = ι τ y ↔ σ λ_x = τ λ_y`;
* `Pt C : {g : G // IsClosed {g}} → C.H`, `ι σ x ↦ σ λ_x` (`Pt_ι`), equivariant for the left action (`Pt_L`);
* `PtEquiv C : {g : G // IsClosed {g}} ≃ C.H`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

section Charts

variable (H : Subgroup (Bir k X))

lemma isClosed_ι (σ : H) (x : X) (hx : IsClosed {x}) : IsClosed {ι H σ x} :=
  isClosed_singleton_apply (X ↘ Spec (.of k)) (G H ↘ Spec (.of k)) (ι H σ) (ι_sG H σ) x hx

lemma isClosed_of_ι (σ : H) (x : X) (h : IsClosed {ι H σ x}) : IsClosed {x} := by
  have e : (ι H σ) ⁻¹' {ι H σ x} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (ι H σ).isOpenEmbedding.injective.eq_iff
  rw [← e]
  exact h.preimage (ι H σ).continuous

lemma exists_chart (g : G H) : ∃ σ : H, ∃ x : X, ι H σ x = g :=
  (gD H).toGlueData.ι_jointly_surjective g

lemma ι_eq_rel (σ τ : H) (x y : X) (h : ι H σ x = ι H τ y) :
    ∃ hW : x ∈ VH H σ τ, (tHH H σ τ ⟨x, hW⟩).1 = y := by
  obtain ⟨⟨x', hx'⟩, hz1, hz2⟩ := ((gD H).toGlueData.ι_eq_iff σ τ x y).1 h
  have e1 : x' = x := hz1
  have e2 : (tHH H σ τ ⟨x', hx'⟩).1 = y := hz2
  subst e1
  exact ⟨hx', e2⟩

lemma ι_eq_of_rel (σ τ : H) (x : X) (hW : x ∈ VH H σ τ) : ι H τ (tHH H σ τ ⟨x, hW⟩).1 = ι H σ x :=
  congrArg (fun φ => φ ⟨x, hW⟩) (ι_glue H σ τ)

variable (k) in
include k in
lemma exists_closedPoint : ∃ x : X, IsClosed ({x} : Set X) := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨x, -, -, hx⟩ := exists_closed_inter (⊤ : X.Opens) ⊤ ⟨Classical.arbitrary X, trivial⟩
    ⟨Classical.arbitrary X, trivial⟩
  exact ⟨x, hx⟩

end Charts

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- Two closed chart points agree in `G` iff the corresponding elements `σ λ_x` agree. -/
theorem ι_eq_iff_mul (σ τ : C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y}) :
    ι C.H σ x = ι C.H τ y ↔ (σ : Bir k X) * C.lamB x hx = (τ : Bir k X) * C.lamB y hy := by
  have hm : (τ : Bir k X)⁻¹ * (σ : Bir k X) ∈ C.H := mul_mem (inv_mem τ.2) σ.2
  constructor
  · intro h
    obtain ⟨hW, e⟩ := ι_eq_rel C.H σ τ x y h
    have t : Takes ((τ : Bir k X)⁻¹ * (σ : Bir k X)) x y := ⟨W_le _ hW, (tH_apply (σ : Bir k X) τ ⟨x, hW⟩).symm.trans e⟩
    have h' := C.RC_fwd _ hm x hx y hy t
    rw [mul_assoc] at h'
    exact inv_mul_eq_iff_eq_mul.1 h'
  · intro h
    have h' : ((τ : Bir k X)⁻¹ * (σ : Bir k X)) * C.lamB x hx = C.lamB y hy := by rw [mul_assoc, h, inv_mul_cancel_left]
    have t := C.RC_bwd _ hm x hx y hy h'
    have hW : x ∈ VH C.H σ τ := C.RC_W _ hm x hx y hy t
    have e : (tHH C.H σ τ ⟨x, hW⟩).1 = y :=
      (tH_apply (σ : Bir k X) τ ⟨x, hW⟩).trans (Takes.unique (takes_self _ x _) t)
    rw [← ι_eq_of_rel C.H σ τ x hW, e]

/-- The chart index of a point of `G`. -/
noncomputable def chS (g : G C.H) : C.H := (exists_chart C.H g).choose

/-- The chart coordinate of a point of `G`. -/
noncomputable def chX (g : G C.H) : X := (exists_chart C.H g).choose_spec.choose

lemma ch_spec (g : G C.H) : ι C.H (C.chS g) (C.chX g) = g := (exists_chart C.H g).choose_spec.choose_spec

lemma isClosed_chX (g : G C.H) (hg : IsClosed {g}) : IsClosed {C.chX g} :=
  isClosed_of_ι C.H _ _ (by rw [C.ch_spec]; exact hg)

/-- The element of `H` named by a closed point of `G`: `ι σ x ↦ σ λ_x`. -/
noncomputable def Pt (g : {g : G C.H // IsClosed {g}}) : C.H :=
  ⟨(C.chS g.1 : Bir k X) * C.lamB (C.chX g.1) (C.isClosed_chX g.1 g.2),
    mul_mem (C.chS g.1).2 (C.lamB_mem_H _ _)⟩

lemma Pt_ι (σ : C.H) (x : X) (hx : IsClosed {x}) :
    (C.Pt ⟨ι C.H σ x, isClosed_ι C.H σ x hx⟩ : Bir k X) = (σ : Bir k X) * C.lamB x hx :=
  (C.ι_eq_iff_mul _ _ _ (C.isClosed_chX _ (isClosed_ι C.H σ x hx)) x hx).1 (C.ch_spec _)

lemma Pt_injective : Function.Injective C.Pt := by
  intro g g' h
  apply Subtype.ext
  rw [← C.ch_spec g.1, ← C.ch_spec g'.1]
  exact (C.ι_eq_iff_mul _ _ _ (C.isClosed_chX g.1 g.2) _ (C.isClosed_chX g'.1 g'.2)).2
    (congrArg Subtype.val h)

lemma Pt_surjective : Function.Surjective C.Pt := by
  intro h
  obtain ⟨x, hx⟩ := exists_closedPoint k (X := X)
  let σ : C.H := ⟨(h : Bir k X) * (C.lamB x hx)⁻¹, mul_mem h.2 (inv_mem (C.lamB_mem_H x hx))⟩
  refine ⟨⟨ι C.H σ x, isClosed_ι C.H σ x hx⟩, Subtype.ext ?_⟩
  rw [C.Pt_ι σ x hx]
  exact inv_mul_cancel_right _ _

/-- Closed points of the glued scheme `G` are the elements of `H`. -/
noncomputable def PtEquiv : {g : G C.H // IsClosed {g}} ≃ C.H :=
  Equiv.ofBijective C.Pt ⟨C.Pt_injective, C.Pt_surjective⟩

lemma L_apply (h : C.H) (g : G C.H) : L C.H h g = ι C.H (h * C.chS g) (C.chX g) :=
  calc L C.H h g = L C.H h (ι C.H (C.chS g) (C.chX g)) := by rw [C.ch_spec]
    _ = ι C.H (h * C.chS g) (C.chX g) := congrArg (fun φ => φ (C.chX g)) (ι_L C.H h (C.chS g))

lemma isClosed_L (h : C.H) (g : G C.H) (hg : IsClosed {g}) : IsClosed {L C.H h g} := by
  rw [C.L_apply]
  exact isClosed_ι C.H _ _ (C.isClosed_chX g hg)

lemma Pt_congr (g g' : {g : G C.H // IsClosed {g}}) (e : g.1 = g'.1) : C.Pt g = C.Pt g' :=
  congrArg C.Pt (Subtype.ext e)

/-- `Pt` is equivariant: the left action of `h` on `G` is left multiplication by `h`. -/
lemma Pt_L (h : C.H) (g : {g : G C.H // IsClosed {g}}) :
    C.Pt ⟨L C.H h g.1, C.isClosed_L h g.1 g.2⟩ = h * C.Pt g := by
  have hx := C.isClosed_chX g.1 g.2
  rw [C.Pt_congr ⟨L C.H h g.1, C.isClosed_L h g.1 g.2⟩
    ⟨ι C.H (h * C.chS g.1) (C.chX g.1), isClosed_ι C.H _ _ hx⟩ (C.L_apply h g.1)]
  apply Subtype.ext
  rw [C.Pt_ι (h * C.chS g.1) (C.chX g.1) hx, Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc]
  rfl

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkA =====
section

/-!
# Group chunk theorem A (unit S4-JacChunkA), umbrella

Weil's construction over an algebraically closed field `k`, for a strict group chunk `C` on an integral,
separated, locally finite type `k`-scheme `X`:
* `Pts`: closed points of fibre products, opens decided on closed points;
* `Trans`: the `StrictChunk` structure, left/right translations `λ_a`, `ρ_b` as partial isomorphisms;
* `Val`, `Germ`: partial-map values, the germ group `Bir k X`, `lamB`/`rhoB`, the subgroup `C.H`;
* `Dom`: maximal domains `rep σ`, the overlaps `W σ`, the cocycle identities;
* `Glue`: pointwise gluing data `PtGlue` → `Scheme.GlueData`;
* `G`: the glued `k`-scheme `G H` (charts `ι H σ` open immersions, lft, reduced, irreducible), left action `L`;
* `RC`: re-charting `σ x = y ↔ σ λ_x = λ_y` (`RC_fwd`, `RC_bwd`, `RC_W`), `lamB_inj`;
* `Pt`: closed points of `G C.H` ≃ `C.H` (`PtEquiv`), `Pt_ι`, equivariance `Pt_L`.
-/

end

-- ===== S4.Def_RP_JacChunkB_Ext =====
section

/-!
# Group chunk B0 (unit S4-JacChunkB): morphisms into `G` are determined by closed points and glue pointwise

* `G_ext`: two `k`-morphisms from a reduced `k`-scheme locally of finite type into `G H` that agree on closed
  points are equal (the charts of `G H` are separated, `G H` itself need not be known separated);
* `glueG`: morphisms into `G H` on the members of a family of open immersions covering the closed points glue,
  once they agree on closed points;
* `PtT`, `lamT`: total versions of `Pt` and `lamB` (value `1` away from closed points).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

section Ext

variable (H : Subgroup (Bir k X))

/-- `k`-morphisms into `G H` from a reduced `k`-scheme locally of finite type agree once they agree on closed
points. -/
theorem G_ext {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
    (f g : T ⟶ G H) (hf : f ≫ sG H = sT) (hg : g ≫ sG H = sT)
    (h : ∀ t, IsClosed {t} → f t = g t) : f = g := by
  haveI : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace sT
  refine Scheme.hom_ext_of_forall f g fun t => ?_
  obtain ⟨σ, x, hx⟩ := exists_chart H (f t)
  have hle : f ⁻¹ᵁ (ι H σ).opensRange ≤ g ⁻¹ᵁ (ι H σ).opensRange := by
    refine opens_le_of_closedPoints _ _ fun s hs hsc => ?_
    have e : f s = g s := h s hsc
    refine (Scheme.Hom.mem_preimage _).2 ?_
    rw [← e]
    exact (Scheme.Hom.mem_preimage _).1 hs
  let U : T.Opens := f ⁻¹ᵁ (ι H σ).opensRange
  have hfU : Set.range (U.ι ≫ f) ⊆ Set.range (ι H σ) := by
    rintro _ ⟨s, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 ((Scheme.Hom.mem_preimage _).1 s.2)
  have hgU : Set.range (U.ι ≫ g) ⊆ Set.range (ι H σ) := by
    rintro _ ⟨s, rfl⟩
    exact Scheme.Hom.mem_opensRange.1 ((Scheme.Hom.mem_preimage _).1 (hle s.2))
  have efU : IsOpenImmersion.lift (ι H σ) (U.ι ≫ f) hfU ≫ ι H σ = U.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  have egU : IsOpenImmersion.lift (ι H σ) (U.ι ≫ g) hgU ≫ ι H σ = U.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have key : IsOpenImmersion.lift (ι H σ) (U.ι ≫ f) hfU = IsOpenImmersion.lift (ι H σ) (U.ι ≫ g) hgU := by
    refine ext_X (U.ι ≫ sT) _ _ ?_ ?_ ?_
    · rw [← ι_sG H σ, ← Category.assoc, efU, Category.assoc, hf]
    · rw [← ι_sG H σ, ← Category.assoc, egU, Category.assoc, hg]
    · intro s hs
      apply (ι H σ).isOpenEmbedding.injective
      have hs' : IsClosed {s.1} := isClosed_singleton_apply (U.ι ≫ sT) sT U.ι rfl s hs
      have e1 : (ι H σ) (IsOpenImmersion.lift (ι H σ) (U.ι ≫ f) hfU s) = f s.1 :=
        congrArg (fun φ => φ s) efU
      have e2 : (ι H σ) (IsOpenImmersion.lift (ι H σ) (U.ι ≫ g) hgU s) = g s.1 :=
        congrArg (fun φ => φ s) egU
      rw [e1, e2]
      exact h s.1 hs'
  refine ⟨U, (Scheme.Hom.mem_preimage _).2 (Scheme.Hom.mem_opensRange.2 ⟨x, hx⟩), ?_⟩
  rw [← efU, ← egU, key]

end Ext

section Glue

variable (H : Subgroup (Bir k X)) {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k))
  [LocallyOfFiniteType sT] {J : Type u} (P : J → Scheme.{u}) (j : ∀ i, P i ⟶ T) [∀ i, IsOpenImmersion (j i)]

/-- The open cover of `T` by the `j i`, when their ranges contain every closed point. -/
noncomputable def coverOfClosed (hcov : ∀ t, IsClosed {t} → ∃ i, ∃ p : P i, j i p = t) : T.OpenCover :=
  Scheme.Cover.mkOfCovers J P j (by
    haveI : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace sT
    have htop : (⨆ i, (j i).opensRange) = ⊤ := by
      refine top_unique (opens_le_of_closedPoints _ _ fun t _ ht => ?_)
      obtain ⟨i, p, hp⟩ := hcov t ht
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, Scheme.Hom.mem_opensRange.2 ⟨p, hp⟩⟩
    intro t
    have ht : t ∈ (⨆ i, (j i).opensRange) := by rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ht
    obtain ⟨p, hp⟩ := Scheme.Hom.mem_opensRange.1 hi
    exact ⟨i, p, hp⟩)

variable (φ : ∀ i, P i ⟶ G H) (hcov : ∀ t, IsClosed {t} → ∃ i, ∃ p : P i, j i p = t)
  (hφ : ∀ i, φ i ≫ sG H = j i ≫ sT)
  (hcomp : ∀ i i' (p : P i) (p' : P i'), IsClosed {p} → IsClosed {p'} → j i p = j i' p' → φ i p = φ i' p')

include hφ hcomp in
lemma glueG_compat (a b : J) :
    pullback.fst (j a) (j b) ≫ φ a = pullback.snd (j a) (j b) ≫ φ b := by
  haveI : IsReduced (pullback (j a) (j b)) := isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)
  refine G_ext H (pullback.fst (j a) (j b) ≫ j a ≫ sT) _ _ ?_ ?_ ?_
  · rw [Category.assoc, hφ]
  · rw [Category.assoc, hφ, pullback.condition_assoc]
  · intro r hr
    have h1 : IsClosed {pullback.fst (j a) (j b) r} :=
      isClosed_singleton_apply (pullback.fst (j a) (j b) ≫ j a ≫ sT) (j a ≫ sT) _ rfl r hr
    have h2 : IsClosed {pullback.snd (j a) (j b) r} :=
      isClosed_singleton_apply (pullback.fst (j a) (j b) ≫ j a ≫ sT) (j b ≫ sT) _
        (by rw [← pullback.condition_assoc]) r hr
    have e : j a (pullback.fst (j a) (j b) r) = j b (pullback.snd (j a) (j b) r) :=
      congrArg (fun ψ => ψ r) (pullback.condition (f := j a) (g := j b))
    exact hcomp a b _ _ h1 h2 e

/-- Pointwise gluing of morphisms into `G H`. -/
noncomputable def glueG : T ⟶ G H :=
  (coverOfClosed sT P j hcov).glueMorphisms φ (glueG_compat H sT P j φ hφ hcomp)

@[reassoc]
lemma glueG_fac (i : J) : j i ≫ glueG H sT P j φ hcov hφ hcomp = φ i :=
  Scheme.Cover.ι_glueMorphisms (coverOfClosed sT P j hcov) φ _ i

lemma glueG_over : glueG H sT P j φ hcov hφ hcomp ≫ sG H = sT :=
  Scheme.Cover.hom_ext (coverOfClosed sT P j hcov) _ _ fun (i : J) =>
    (glueG_fac_assoc H sT P j φ hcov hφ hcomp i (sG H)).trans (hφ i)

lemma glueG_apply (i : J) (p : P i) : glueG H sT P j φ hcov hφ hcomp (j i p) = φ i p :=
  congrArg (fun ψ => ψ p) (glueG_fac H sT P j φ hcov hφ hcomp i)

end Glue

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

open Classical in
/-- `lamB` as a total function (value `1` away from closed points). -/
noncomputable def lamT (x : X) : Bir k X := if hx : IsClosed {x} then C.lamB x hx else 1

lemma lamT_eq (x : X) (hx : IsClosed {x}) : C.lamT x = C.lamB x hx := by rw [lamT, dif_pos hx]

open Classical in
/-- `Pt` as a total function into `Bir k X` (value `1` away from closed points). -/
noncomputable def PtT (g : G C.H) : Bir k X := if hg : IsClosed {g} then (C.Pt ⟨g, hg⟩ : Bir k X) else 1

lemma PtT_eq (g : G C.H) (hg : IsClosed {g}) : C.PtT g = (C.Pt ⟨g, hg⟩ : Bir k X) := by rw [PtT, dif_pos hg]

lemma PtT_mem (g : G C.H) : C.PtT g ∈ C.H := by
  by_cases hg : IsClosed {g}
  · rw [C.PtT_eq g hg]; exact (C.Pt ⟨g, hg⟩).2
  · rw [PtT, dif_neg hg]; exact one_mem _

lemma PtT_ι (σ : C.H) (x : X) (hx : IsClosed {x}) : C.PtT (ι C.H σ x) = (σ : Bir k X) * C.lamT x := by
  rw [C.PtT_eq _ (isClosed_ι C.H σ x hx), C.Pt_ι σ x hx, C.lamT_eq x hx]

lemma PtT_inj (g g' : G C.H) (hg : IsClosed {g}) (hg' : IsClosed {g'}) (h : C.PtT g = C.PtT g') : g = g' := by
  rw [C.PtT_eq g hg, C.PtT_eq g' hg'] at h
  exact congrArg Subtype.val (C.Pt_injective (Subtype.ext h))

/-- `G_ext` in terms of `PtT` values. -/
theorem G_ext_Pt {T : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
    (f g : T ⟶ G C.H) (hf : f ≫ sG C.H = sT) (hg : g ≫ sG C.H = sT)
    (h : ∀ t, IsClosed {t} → C.PtT (f t) = C.PtT (g t)) : f = g :=
  G_ext C.H sT f g hf hg fun t ht =>
    C.PtT_inj _ _ (isClosed_singleton_apply sT (G C.H ↘ Spec (.of k)) f hf t ht)
      (isClosed_singleton_apply sT (G C.H ↘ Spec (.of k)) g hg t ht) (h t ht)

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Act =====
section

/-!
# Group chunk B1 (unit S4-JacChunkB): the right action `act : G ×_k X ⟶ G`

* `lamT_mul`: for a closed point `q` of `Ω`, `λ_{pr₁ q} λ_{pr₂ q} = λ_{m q}`;
* `act`: glued from the pieces `Ω ⟶ G ×_k X`, `(x, y) ↦ (ι σ x, y)` with value `ι σ (m(x, y))`;
  `PtT (act z) = PtT (pr₁ z) * lamT (pr₂ z)` at closed points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

lemma isClosed_Ω (q : C.Ω) (hq : IsClosed {q.1}) : IsClosed ({q} : Set C.Ω) := isClosed_mk' C.Ω q.1 q.2 hq

lemma isClosed_m (q : C.Ω) (hq : IsClosed {q.1}) : IsClosed {C.m q} :=
  isClosed_singleton_apply (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k))
    (X ↘ Spec (.of k)) C.m C.m_over q (C.isClosed_Ω q hq)

/-- `λ_a λ_b = λ_{ab}` for a closed point `(a, b)` of `Ω`. -/
lemma lamT_mul (q : C.Ω) (hq : IsClosed {q.1}) :
    C.lamT (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) * C.lamT (pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) = C.lamT (C.m q) := by
  have ha := isClosed_fst q.1 hq
  have hb := isClosed_snd q.1 hq
  have hm := C.isClosed_m q hq
  rw [C.lamT_eq _ ha, C.lamT_eq _ hb, C.lamT_eq _ hm]
  have hsec : secL (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) ha (pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) = q.1 :=
    closedPoint_pullback_ext (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) _ _
      (secL_isClosed _ ha _ hb) hq (secL_apply_fst _ ha _) (secL_apply_snd _ ha _)
  have hdom : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1 ∈ (C.lam _ ha).toPartialMap.domain :=
    (Scheme.Hom.mem_preimage _).2 (by rw [hsec]; exact q.2)
  have hval : (C.lam _ ha).toPartialMap.hom ⟨_, hdom⟩ = C.m q :=
    (C.lam_apply _ ha _ hdom).trans (congrArg C.m (Subtype.ext hsec))
  exact C.RC_fwd _ (C.lamB_mem_H _ ha) _ hb _ hm ((C.lamB_takes _ ha _ hdom).val_eq hval)

/-- The chart map `X ×_k X ⟶ G ×_k X`, `(x, y) ↦ (ι σ x, y)`. -/
noncomputable def jA (σ : C.H) : pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ⟶
    pullback (sG C.H) (X ↘ Spec (.of k)) :=
  pullback.map _ _ _ _ (ι C.H σ) (𝟙 X) (𝟙 _) (by rw [Category.comp_id, ι_sG]) (by simp)

instance (σ : C.H) : IsOpenImmersion (C.jA σ) := by unfold jA; infer_instance

@[reassoc (attr := simp)]
lemma jA_fst (σ : C.H) : C.jA σ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ι C.H σ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma jA_snd (σ : C.H) : C.jA σ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma jA_fst_apply (σ : C.H) (z : (pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) : Scheme.{u})) :
    pullback.fst (sG C.H) (X ↘ Spec (.of k)) (C.jA σ z) = ι C.H σ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z) := congrArg (fun φ => φ z) (C.jA_fst σ)

lemma jA_snd_apply (σ : C.H) (z : (pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) : Scheme.{u})) :
    pullback.snd (sG C.H) (X ↘ Spec (.of k)) (C.jA σ z) = pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z := congrArg (fun φ => φ z) (C.jA_snd σ)

/-- `ι_eq_iff_mul` with the total `lamT`. -/
lemma ι_eq_iff_mulT (σ τ : C.H) (x : X) (hx : IsClosed {x}) (y : X) (hy : IsClosed {y}) :
    ι C.H σ x = ι C.H τ y ↔ (σ : Bir k X) * C.lamT x = (τ : Bir k X) * C.lamT y := by
  rw [C.lamT_eq x hx, C.lamT_eq y hy]; exact C.ι_eq_iff_mul σ τ x hx y hy

lemma isClosed_Ωval (q : C.Ω) (hq : IsClosed ({q} : Set C.Ω.toScheme)) : IsClosed {q.1} :=
  isClosed_singleton_apply (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k))
    (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) C.Ω.ι rfl q hq

end StrictChunk

lemma isClosed_of_inj {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (f : A → B) (hf : Continuous f)
    (hi : Function.Injective f) (a : A) (h : IsClosed ({f a} : Set B)) : IsClosed ({a} : Set A) := by
  have e : f ⁻¹' {f a} = {a} := by
    ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hi.eq_iff
  rw [← e]; exact h.preimage hf

instance (H : Subgroup (Bir k X)) : LocallyOfFiniteType (sG H) :=
  (inferInstance : LocallyOfFiniteType (G H ↘ Spec (.of k)))

instance (H : Subgroup (Bir k X)) : IsLocallyNoetherian (G H) := LocallyOfFiniteType.isLocallyNoetherian (sG H)

variable [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- The structure map of `G ×_k X`. -/
noncomputable abbrev sGX : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ Spec (.of k) :=
  pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ sG C.H

lemma act_over (σ : C.H) : (C.m ≫ ι C.H σ) ≫ sG C.H = (C.Ω.ι ≫ C.jA σ) ≫ C.sGX := by
  simp only [sGX, Category.assoc, ι_sG, C.jA_fst_assoc, C.m_over]

lemma act_cov (t : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u})) (ht : IsClosed {t}) :
    ∃ σ : C.H, ∃ p : C.Ω.toScheme, (C.Ω.ι ≫ C.jA σ) p = t := by
  have hg : IsClosed {pullback.fst (sG C.H) (X ↘ Spec (.of k)) t} :=
    isClosed_singleton_apply C.sGX (G C.H ↘ Spec (.of k)) _ rfl t ht
  have hy : IsClosed {pullback.snd (sG C.H) (X ↘ Spec (.of k)) t} :=
    isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm t ht
  obtain ⟨σ, x, hx⟩ := exists_chart C.H (pullback.fst (sG C.H) (X ↘ Spec (.of k)) t)
  have hxc : IsClosed {x} := isClosed_of_ι C.H σ x (by rw [hx]; exact hg)
  obtain ⟨z, hzΩ, hz, hzy⟩ := C.fib_right _ hy
  have hu := isClosed_fst z hz
  let σ' : C.H := ⟨(σ : Bir k X) * C.lamB x hxc * (C.lamB _ hu)⁻¹,
    mul_mem (mul_mem σ.2 (C.lamB_mem_H x hxc)) (inv_mem (C.lamB_mem_H _ hu))⟩
  have e1 : ι C.H σ' (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z) = ι C.H σ x :=
    (C.ι_eq_iff_mul σ' σ _ hu x hxc).2 (inv_mul_cancel_right _ _)
  refine ⟨σ', ⟨z, hzΩ⟩, ?_⟩
  have hc : IsClosed {C.jA σ' z} :=
    isClosed_singleton_apply (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) C.sGX
      (C.jA σ') (by simp only [sGX, C.jA_fst_assoc, ι_sG]) z hz
  exact closedPoint_pullback_ext (sG C.H) (X ↘ Spec (.of k)) (C.jA σ' z) t hc ht
    ((C.jA_fst_apply σ' z).trans (e1.trans hx)) ((C.jA_snd_apply σ' z).trans hzy)

lemma act_comp (σ τ : C.H) (p p' : C.Ω.toScheme) (hp : IsClosed {p}) (hp' : IsClosed {p'})
    (e : (C.Ω.ι ≫ C.jA σ) p = (C.Ω.ι ≫ C.jA τ) p') : (C.m ≫ ι C.H σ) p = (C.m ≫ ι C.H τ) p' := by
  have hq := C.isClosed_Ωval p hp
  have hq' := C.isClosed_Ωval p' hp'
  have e1 : ι C.H σ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1) =
      ι C.H τ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p'.1) :=
    (C.jA_fst_apply σ p.1).symm.trans
      ((congrArg (pullback.fst (sG C.H) (X ↘ Spec (.of k))) e).trans (C.jA_fst_apply τ p'.1))
  have e2 : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1 =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p'.1 :=
    (C.jA_snd_apply σ p.1).symm.trans
      ((congrArg (pullback.snd (sG C.H) (X ↘ Spec (.of k))) e).trans (C.jA_snd_apply τ p'.1))
  have h1 := (C.ι_eq_iff_mulT σ τ _ (isClosed_fst _ hq) _ (isClosed_fst _ hq')).1 e1
  show ι C.H σ (C.m p) = ι C.H τ (C.m p')
  rw [C.ι_eq_iff_mulT σ τ _ (C.isClosed_m p hq) _ (C.isClosed_m p' hq'), ← C.lamT_mul p hq,
    ← C.lamT_mul p' hq', e2, ← mul_assoc, ← mul_assoc, h1]

/-- The right action `G ×_k X ⟶ G`, `(ι σ x, y) ↦ ι σ (m(x, y))`. -/
noncomputable def act : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ G C.H :=
  glueG C.H C.sGX (fun _ : C.H => C.Ω.toScheme) (fun σ => C.Ω.ι ≫ C.jA σ) (fun σ => C.m ≫ ι C.H σ)
    C.act_cov C.act_over C.act_comp

lemma act_over' : C.act ≫ sG C.H = C.sGX :=
  glueG_over C.H C.sGX (fun _ : C.H => C.Ω.toScheme) (fun σ => C.Ω.ι ≫ C.jA σ) (fun σ => C.m ≫ ι C.H σ)
    C.act_cov C.act_over C.act_comp

lemma act_fac (σ : C.H) : C.Ω.ι ≫ C.jA σ ≫ C.act = C.m ≫ ι C.H σ := by
  rw [← Category.assoc]; exact glueG_fac C.H C.sGX (fun _ : C.H => C.Ω.toScheme) (fun σ => C.Ω.ι ≫ C.jA σ) (fun σ => C.m ≫ ι C.H σ)
      C.act_cov C.act_over C.act_comp σ

/-- The value of `act` at a closed point: `PtT (act z) = PtT (pr₁ z) * λ_{pr₂ z}`. -/
theorem PtT_act (t : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u})) (ht : IsClosed {t}) :
    C.PtT (C.act t) = C.PtT (pullback.fst (sG C.H) (X ↘ Spec (.of k)) t) *
      C.lamT (pullback.snd (sG C.H) (X ↘ Spec (.of k)) t) := by
  obtain ⟨σ, p, rfl⟩ := C.act_cov t ht
  have hp : IsClosed {p} := isClosed_of_inj _ (C.Ω.ι ≫ C.jA σ).continuous
    (C.Ω.ι ≫ C.jA σ).isOpenEmbedding.injective p ht
  have hq := C.isClosed_Ωval p hp
  have e : C.act ((C.Ω.ι ≫ C.jA σ) p) = ι C.H σ (C.m p) :=
    glueG_apply C.H C.sGX (fun _ : C.H => C.Ω.toScheme) (fun σ => C.Ω.ι ≫ C.jA σ) (fun σ => C.m ≫ ι C.H σ)
      C.act_cov C.act_over C.act_comp σ p
  have e1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) ((C.Ω.ι ≫ C.jA σ) p) =
      ι C.H σ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1) := C.jA_fst_apply σ p.1
  have e2 : pullback.snd (sG C.H) (X ↘ Spec (.of k)) ((C.Ω.ι ≫ C.jA σ) p) =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) p.1 := C.jA_snd_apply σ p.1
  rw [e, e1, e2, C.PtT_ι σ _ (C.isClosed_m p hq), C.PtT_ι σ _ (isClosed_fst _ hq), mul_assoc, C.lamT_mul p hq]

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_R =====
section

/-!
# Group chunk B2 (unit S4-JacChunkB): right translations of `G`

* `Rb b`: `g ↦ act (g, b)`, value `PtT g * λ_b`;
* `Rinv b`: glued from `ι σ ∘ ρ_b⁻¹` on the target of `ρ_b`, value `PtT g * λ_b⁻¹`;
* `exists_R`: for every `τ ∈ H` a `k`-endomorphism `R` of `G` with `PtT (R g) = PtT g * τ` at closed points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

section Rinv

variable (b : X) (hb : IsClosed {b})

/-- `ρ_b⁻¹ y` is a closed point with `λ_{ρ_b⁻¹ y} = λ_y λ_b⁻¹`. -/
lemma rhoInv_spec (y : (C.rho b hb).symm.toPartialMap.domain) (hyc : IsClosed {y.1}) :
    IsClosed {(C.rho b hb).symm.toPartialMap.hom y} ∧
    C.lamT ((C.rho b hb).symm.toPartialMap.hom y) = C.lamT y.1 * (C.lamB b hb)⁻¹ := by
  haveI := pi_isOver _ (C.rho_isOver b hb).symm
  have hw : IsClosed {(C.rho b hb).symm.toPartialMap.hom y} :=
    isClosed_hom_apply (k := k) (C.rho b hb).symm.toPartialMap y.1 y.2 hyc
  refine ⟨hw, ?_⟩
  have hdom : (C.rho b hb).symm.toPartialMap.hom y ∈ (C.rho b hb).toPartialMap.domain :=
    pi_mem_target (C.rho b hb).symm y.1 y.2
  have hback : (C.rho b hb).toPartialMap.hom ⟨_, hdom⟩ = y.1 :=
    pi_symm_apply (C.rho b hb).symm y.1 y.2 hdom
  have hq : IsClosed {secR b hb ((C.rho b hb).symm.toPartialMap.hom y)} := secR_isClosed (sX := X ↘ Spec (.of k)) b hb _ hw
  have hm := C.lamT_mul ⟨secR b hb ((C.rho b hb).symm.toPartialMap.hom y), hdom⟩ hq
  have e3 : C.m ⟨secR b hb ((C.rho b hb).symm.toPartialMap.hom y), hdom⟩ = y.1 :=
    (C.rho_apply b hb _ hdom).symm.trans hback
  dsimp only at hm
  rw [secR_apply_fst, secR_apply_snd, e3, C.lamT_eq b hb] at hm
  rw [← hm, mul_inv_cancel_right]

lemma rinv_over (σ : C.H) : ((C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) ≫ sG C.H =
    ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) ≫ sG C.H := by
  haveI := pi_isOver _ (C.rho_isOver b hb).symm
  simp only [Category.assoc, ι_sG]
  exact HomIsOver.comp_over (f := (C.rho b hb).symm.toPartialMap.hom) (S := Spec (.of k))

lemma rinv_cov (g : G C.H) (hg : IsClosed {g}) :
    ∃ σ : C.H, ∃ p : (C.rho b hb).symm.toPartialMap.domain.toScheme,
      ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) p = g := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨σ, x, hx⟩ := exists_chart C.H g
  have hxc : IsClosed {x} := isClosed_of_ι C.H σ x (by rw [hx]; exact hg)
  have hne : (((C.rho b hb).symm.toPartialMap.domain : X.Opens) : Set X).Nonempty :=
    (C.rho b hb).dense_target.nonempty
  obtain ⟨y, hy, -, hyc⟩ := exists_closed_inter _ _ hne hne
  let σ' : C.H := ⟨(σ : Bir k X) * C.lamB x hxc * (C.lamB y hyc)⁻¹,
    mul_mem (mul_mem σ.2 (C.lamB_mem_H x hxc)) (inv_mem (C.lamB_mem_H y hyc))⟩
  exact ⟨σ', ⟨y, hy⟩, ((C.ι_eq_iff_mul σ' σ y hyc x hxc).2 (inv_mul_cancel_right _ _)).trans hx⟩

lemma rinv_comp (σ τ : C.H) (p p' : (C.rho b hb).symm.toPartialMap.domain.toScheme)
    (hp : IsClosed {p}) (hp' : IsClosed {p'})
    (e : ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) p =
      ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H τ) p') :
    ((C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) p = ((C.rho b hb).symm.toPartialMap.hom ≫ ι C.H τ) p' := by
  have hq : IsClosed {p.1} := isClosed_val (k := k) _ p hp
  have hq' : IsClosed {p'.1} := isClosed_val (k := k) _ p' hp'
  obtain ⟨hw, hl⟩ := C.rhoInv_spec b hb p hq
  obtain ⟨hw', hl'⟩ := C.rhoInv_spec b hb p' hq'
  have h1 := (C.ι_eq_iff_mulT σ τ _ hq _ hq').1 e
  show ι C.H σ ((C.rho b hb).symm.toPartialMap.hom p) = ι C.H τ ((C.rho b hb).symm.toPartialMap.hom p')
  rw [C.ι_eq_iff_mulT σ τ _ hw _ hw', hl, hl', ← mul_assoc, ← mul_assoc, h1]

/-- Right translation by `λ_b⁻¹`. -/
noncomputable def Rinv : G C.H ⟶ G C.H :=
  glueG C.H (sG C.H) (fun _ : C.H => (C.rho b hb).symm.toPartialMap.domain.toScheme)
    (fun σ => (C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ)
    (fun σ => (C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) (C.rinv_cov b hb) (C.rinv_over b hb) (C.rinv_comp b hb)

lemma Rinv_over : C.Rinv b hb ≫ sG C.H = sG C.H :=
  glueG_over C.H (sG C.H) (fun _ : C.H => (C.rho b hb).symm.toPartialMap.domain.toScheme)
    (fun σ => (C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ)
    (fun σ => (C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) (C.rinv_cov b hb) (C.rinv_over b hb) (C.rinv_comp b hb)

lemma PtT_Rinv (g : G C.H) (hg : IsClosed {g}) : C.PtT (C.Rinv b hb g) = C.PtT g * (C.lamB b hb)⁻¹ := by
  obtain ⟨σ, p, rfl⟩ := C.rinv_cov b hb g hg
  have hp : IsClosed {p} := isClosed_of_inj _ ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ).continuous
    ((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ).isOpenEmbedding.injective p hg
  have hq : IsClosed {p.1} := isClosed_val (k := k) _ p hp
  obtain ⟨hw, hl⟩ := C.rhoInv_spec b hb p hq
  have e : C.Rinv b hb (((C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ) p) =
      ι C.H σ ((C.rho b hb).symm.toPartialMap.hom p) :=
    glueG_apply C.H (sG C.H) (fun _ : C.H => (C.rho b hb).symm.toPartialMap.domain.toScheme)
      (fun σ => (C.rho b hb).symm.toPartialMap.domain.ι ≫ ι C.H σ)
      (fun σ => (C.rho b hb).symm.toPartialMap.hom ≫ ι C.H σ) (C.rinv_cov b hb) (C.rinv_over b hb)
      (C.rinv_comp b hb) σ p
  rw [e]
  show C.PtT (ι C.H σ _) = C.PtT (ι C.H σ p.1) * _
  rw [C.PtT_ι σ _ hw, C.PtT_ι σ _ hq, hl, mul_assoc]

end Rinv

variable [GeometricallyReduced (X ↘ Spec (.of k))]

/-- `g ↦ (g, b)`. -/
noncomputable def liftb (b : X) (hb : IsClosed {b}) : G C.H ⟶ pullback (sG C.H) (X ↘ Spec (.of k)) :=
  pullback.lift (𝟙 _) (sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb) (by simp)

/-- Right translation by `λ_b`: `g ↦ act (g, b)`. -/
noncomputable def Rb (b : X) (hb : IsClosed {b}) : G C.H ⟶ G C.H := C.liftb b hb ≫ C.act

lemma liftb_fst (b : X) (hb : IsClosed {b}) :
    C.liftb b hb ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) = 𝟙 _ := pullback.lift_fst _ _ _

lemma liftb_snd (b : X) (hb : IsClosed {b}) : C.liftb b hb ≫ pullback.snd (sG C.H) (X ↘ Spec (.of k)) =
    sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb := pullback.lift_snd _ _ _

lemma liftb_sGX (b : X) (hb : IsClosed {b}) : C.liftb b hb ≫ C.sGX = sG C.H := by
  show C.liftb b hb ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ sG C.H = sG C.H
  rw [← Category.assoc, C.liftb_fst b hb, Category.id_comp]

lemma Rb_over (b : X) (hb : IsClosed {b}) : C.Rb b hb ≫ sG C.H = sG C.H := by
  rw [Rb, Category.assoc, act_over']; exact C.liftb_sGX b hb

lemma PtT_Rb (b : X) (hb : IsClosed {b}) (g : G C.H) (hg : IsClosed {g}) :
    C.PtT (C.Rb b hb g) = C.PtT g * C.lamB b hb := by
  have hl : IsClosed {C.liftb b hb g} :=
    isClosed_singleton_apply (sG C.H) C.sGX (C.liftb b hb) (C.liftb_sGX b hb) g hg
  have e1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) (C.liftb b hb g) = g := by
    have := congrArg (fun φ => φ g) (C.liftb_fst b hb)
    exact this
  have e2 : pullback.snd (sG C.H) (X ↘ Spec (.of k)) (C.liftb b hb g) = b := by
    have h1 : (C.liftb b hb ≫ pullback.snd (sG C.H) (X ↘ Spec (.of k))) g =
        (sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb) g := by rw [C.liftb_snd b hb]
    have h2 : (sG C.H ≫ pointOfClosedPoint (X ↘ Spec (.of k)) b hb) g = b :=
      pointOfClosedPoint_apply (X ↘ Spec (.of k)) b hb _
    exact h1.trans h2
  show C.PtT (C.act (C.liftb b hb g)) = _
  rw [C.PtT_act _ hl, e1, e2, C.lamT_eq b hb]

/-- Right translations by all elements of `H`. -/
theorem exists_R (τ : Bir k X) (hτ : τ ∈ C.H) :
    ∃ R : G C.H ⟶ G C.H, R ≫ sG C.H = sG C.H ∧ ∀ g, IsClosed {g} → C.PtT (R g) = C.PtT g * τ := by
  unfold H at hτ
  induction hτ using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    exact ⟨C.Rb a ha, C.Rb_over a ha, C.PtT_Rb a ha⟩
  | inv_mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    exact ⟨C.Rinv a ha, C.Rinv_over a ha, C.PtT_Rinv a ha⟩
  | one => exact ⟨𝟙 _, Category.id_comp _, fun g _ => (mul_one _).symm⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨R1, h1, v1⟩ := ihx
    obtain ⟨R2, h2, v2⟩ := ihy
    refine ⟨R1 ≫ R2, by rw [Category.assoc, h2, h1], fun g hg => ?_⟩
    have hc := isClosed_singleton_apply (sG C.H) (sG C.H) R1 h1 g hg
    show C.PtT (R2 (R1 g)) = _
    rw [v2 _ hc, v1 g hg, mul_assoc]

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Mul =====
section

/-!
# Group chunk B3 (unit S4-JacChunkB): the multiplication `μ : G ×_k G ⟶ G`

* `G` is geometrically reduced over `k` (its charts are copies of `X`);
* `Rt τ`: a chosen right translation by `τ ∈ H`;
* `mu`: glued over the charts `G ×_k X ⟶ G ×_k G`, `(g, x) ↦ (g, ι τ x)`, from `(g, x) ↦ act (R_τ g, x)`;
  `PtT (mu t) = PtT (pr₁ t) * PtT (pr₂ t)` at closed points.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

/-- `G` is geometrically reduced over `k`: base changes of its charts are base changes of `X`. -/
instance geometricallyReduced_sG (H : Subgroup (Bir k X)) : GeometricallyReduced (sG H) := by
  constructor
  intro K _ y Z fst snd h
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := (gD H).toGlueData.openCover.pullback₁ fst)
  intro σ
  have hl : IsPullback (pullback.fst fst (ι H σ)) (pullback.snd fst (ι H σ)) fst (ι H σ) :=
    IsPullback.of_hasPullback _ _
  have hp := (hl.paste_horiz h.flip).flip
  exact GeometricallyReduced.geometrically_isReduced (f := X ↘ Spec (.of k)) y _ _
    (by rw [← ι_sG H σ]; exact hp)

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- A chosen right translation by `τ ∈ H`. -/
noncomputable def Rt (τ : C.H) : G C.H ⟶ G C.H := Classical.choose (C.exists_R τ τ.2)

lemma Rt_over (τ : C.H) : C.Rt τ ≫ sG C.H = sG C.H := (Classical.choose_spec (C.exists_R τ τ.2)).1

lemma PtT_Rt (τ : C.H) (g : G C.H) (hg : IsClosed {g}) : C.PtT (C.Rt τ g) = C.PtT g * τ :=
  (Classical.choose_spec (C.exists_R τ τ.2)).2 g hg

/-- `(g, x) ↦ (R_τ g, x)`. -/
noncomputable def mapR (τ : C.H) : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ pullback (sG C.H) (X ↘ Spec (.of k)) :=
  pullback.map _ _ _ _ (C.Rt τ) (𝟙 X) (𝟙 _) (by rw [Category.comp_id, C.Rt_over])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc]
lemma mapR_fst (τ : C.H) : C.mapR τ ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) =
    pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ C.Rt τ := pullback.lift_fst _ _ _

@[reassoc]
lemma mapR_snd (τ : C.H) : C.mapR τ ≫ pullback.snd (sG C.H) (X ↘ Spec (.of k)) =
    pullback.snd (sG C.H) (X ↘ Spec (.of k)) := (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma mapR_sGX (τ : C.H) : C.mapR τ ≫ C.sGX = C.sGX := by
  show C.mapR τ ≫ pullback.fst (sG C.H) (X ↘ Spec (.of k)) ≫ sG C.H = pullback.fst _ _ ≫ sG C.H
  rw [C.mapR_fst_assoc, C.Rt_over]

lemma mapR_act_over (τ : C.H) : (C.mapR τ ≫ C.act) ≫ sG C.H = C.sGX := by
  rw [Category.assoc, C.act_over', C.mapR_sGX]

/-- The chart `(g, x) ↦ (g, ι τ x)` of `G ×_k G`. -/
noncomputable def jB (τ : C.H) : pullback (sG C.H) (X ↘ Spec (.of k)) ⟶ pullback (sG C.H) (sG C.H) :=
  pullback.map _ _ _ _ (𝟙 _) (ι C.H τ) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ι_sG])

instance (τ : C.H) : IsOpenImmersion (C.jB τ) := by unfold jB; infer_instance

@[reassoc]
lemma jB_fst (τ : C.H) : C.jB τ ≫ pullback.fst (sG C.H) (sG C.H) = pullback.fst (sG C.H) (X ↘ Spec (.of k)) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma jB_snd (τ : C.H) : C.jB τ ≫ pullback.snd (sG C.H) (sG C.H) =
    pullback.snd (sG C.H) (X ↘ Spec (.of k)) ≫ ι C.H τ := pullback.lift_snd _ _ _

/-- The structure map of `G ×_k G`. -/
noncomputable abbrev sGG : pullback (sG C.H) (sG C.H) ⟶ Spec (.of k) := pullback.fst (sG C.H) (sG C.H) ≫ sG C.H

lemma jB_sGG (τ : C.H) : C.jB τ ≫ C.sGG = C.sGX := by
  show C.jB τ ≫ pullback.fst (sG C.H) (sG C.H) ≫ sG C.H = pullback.fst _ _ ≫ sG C.H
  rw [C.jB_fst_assoc]

lemma mu_over (τ : C.H) : (C.mapR τ ≫ C.act) ≫ sG C.H = C.jB τ ≫ C.sGG :=
  (C.mapR_act_over τ).trans (C.jB_sGG τ).symm

lemma mu_cov (t : (pullback (sG C.H) (sG C.H) : Scheme.{u})) (ht : IsClosed {t}) :
    ∃ τ : C.H, ∃ p : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u}), C.jB τ p = t := by
  have h1 : IsClosed {pullback.fst (sG C.H) (sG C.H) t} :=
    isClosed_singleton_apply C.sGG (sG C.H) _ rfl t ht
  have h2 : IsClosed {pullback.snd (sG C.H) (sG C.H) t} :=
    isClosed_singleton_apply C.sGG (sG C.H) _ pullback.condition.symm t ht
  obtain ⟨τ, x, hx⟩ := exists_chart C.H (pullback.snd (sG C.H) (sG C.H) t)
  have hxc : IsClosed {x} := isClosed_of_ι C.H τ x (by rw [hx]; exact h2)
  obtain ⟨p, hp, hp1, hp2⟩ := exists_closedPoint_pullback (sG C.H) (X ↘ Spec (.of k)) _ h1 x hxc
  refine ⟨τ, p, ?_⟩
  have hc : IsClosed {C.jB τ p} := isClosed_singleton_apply C.sGX C.sGG (C.jB τ) (C.jB_sGG τ) p hp
  have f1 : pullback.fst (sG C.H) (sG C.H) (C.jB τ p) = pullback.fst (sG C.H) (X ↘ Spec (.of k)) p :=
    congrArg (fun φ => φ p) (C.jB_fst τ)
  have f2 : pullback.snd (sG C.H) (sG C.H) (C.jB τ p) = ι C.H τ (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p) :=
    congrArg (fun φ => φ p) (C.jB_snd τ)
  exact closedPoint_pullback_ext (sG C.H) (sG C.H) _ t hc ht (f1.trans hp1)
    (f2.trans ((congrArg (ι C.H τ) hp2).trans hx))

lemma PtT_mapR_act (τ : C.H) (p : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u})) (hp : IsClosed {p}) :
    IsClosed {C.act (C.mapR τ p)} ∧ C.PtT (C.act (C.mapR τ p)) =
      C.PtT (pullback.fst (sG C.H) (X ↘ Spec (.of k)) p) *
        ((τ : Bir k X) * C.lamT (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p)) := by
  have hg := isClosed_singleton_apply C.sGX (sG C.H) _ rfl p hp
  have hm := isClosed_singleton_apply C.sGX C.sGX (C.mapR τ) (C.mapR_sGX τ) p hp
  refine ⟨isClosed_singleton_apply C.sGX (sG C.H) (C.mapR τ ≫ C.act) (C.mapR_act_over τ) p hp, ?_⟩
  have f1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) (C.mapR τ p) = C.Rt τ (pullback.fst (sG C.H) (X ↘ Spec (.of k)) p) :=
    congrArg (fun φ => φ p) (C.mapR_fst τ)
  have f2 : pullback.snd (sG C.H) (X ↘ Spec (.of k)) (C.mapR τ p) = pullback.snd (sG C.H) (X ↘ Spec (.of k)) p :=
    congrArg (fun φ => φ p) (C.mapR_snd τ)
  rw [C.PtT_act _ hm, f1, f2, C.PtT_Rt τ _ hg, mul_assoc]

lemma mu_comp (τ τ' : C.H) (p p' : (pullback (sG C.H) (X ↘ Spec (.of k)) : Scheme.{u}))
    (hp : IsClosed {p}) (hp' : IsClosed {p'}) (e : C.jB τ p = C.jB τ' p') :
    (C.mapR τ ≫ C.act) p = (C.mapR τ' ≫ C.act) p' := by
  have e1 : pullback.fst (sG C.H) (X ↘ Spec (.of k)) p = pullback.fst (sG C.H) (X ↘ Spec (.of k)) p' :=
    (congrArg (fun φ => φ p) (C.jB_fst τ)).symm.trans
      ((congrArg (pullback.fst (sG C.H) (sG C.H)) e).trans (congrArg (fun φ => φ p') (C.jB_fst τ')))
  have e2 : ι C.H τ (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p) =
      ι C.H τ' (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p') :=
    (congrArg (fun φ => φ p) (C.jB_snd τ)).symm.trans
      ((congrArg (pullback.snd (sG C.H) (sG C.H)) e).trans (congrArg (fun φ => φ p') (C.jB_snd τ')))
  have hx := isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm p hp
  have hx' := isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm p' hp'
  have h3 := (C.ι_eq_iff_mulT τ τ' _ hx _ hx').1 e2
  obtain ⟨c, v⟩ := C.PtT_mapR_act τ p hp
  obtain ⟨c', v'⟩ := C.PtT_mapR_act τ' p' hp'
  refine C.PtT_inj _ _ c c' ?_
  show C.PtT (C.act (C.mapR τ p)) = C.PtT (C.act (C.mapR τ' p'))
  rw [v, v', e1, h3]

/-- The multiplication `G ×_k G ⟶ G`. -/
noncomputable def mu : pullback (sG C.H) (sG C.H) ⟶ G C.H :=
  glueG C.H C.sGG (fun _ : C.H => pullback (sG C.H) (X ↘ Spec (.of k))) C.jB (fun τ => C.mapR τ ≫ C.act)
    C.mu_cov C.mu_over C.mu_comp

lemma mu_over' : C.mu ≫ sG C.H = C.sGG :=
  glueG_over C.H C.sGG (fun _ : C.H => pullback (sG C.H) (X ↘ Spec (.of k))) C.jB (fun τ => C.mapR τ ≫ C.act)
    C.mu_cov C.mu_over C.mu_comp

/-- The value of `μ` at a closed point: `PtT (μ t) = PtT (pr₁ t) * PtT (pr₂ t)`. -/
theorem PtT_mu (t : (pullback (sG C.H) (sG C.H) : Scheme.{u})) (ht : IsClosed {t}) :
    C.PtT (C.mu t) = C.PtT (pullback.fst (sG C.H) (sG C.H) t) * C.PtT (pullback.snd (sG C.H) (sG C.H) t) := by
  obtain ⟨τ, p, rfl⟩ := C.mu_cov t ht
  have hp : IsClosed {p} := isClosed_of_inj _ (C.jB τ).continuous (C.jB τ).isOpenEmbedding.injective p ht
  have hx := isClosed_singleton_apply C.sGX (X ↘ Spec (.of k)) _ pullback.condition.symm p hp
  have e : C.mu (C.jB τ p) = C.act (C.mapR τ p) :=
    glueG_apply C.H C.sGG (fun _ : C.H => pullback (sG C.H) (X ↘ Spec (.of k))) C.jB
      (fun τ => C.mapR τ ≫ C.act) C.mu_cov C.mu_over C.mu_comp τ p
  have f1 : pullback.fst (sG C.H) (sG C.H) (C.jB τ p) = pullback.fst (sG C.H) (X ↘ Spec (.of k)) p :=
    congrArg (fun φ => φ p) (C.jB_fst τ)
  have f2 : pullback.snd (sG C.H) (sG C.H) (C.jB τ p) = ι C.H τ (pullback.snd (sG C.H) (X ↘ Spec (.of k)) p) :=
    congrArg (fun φ => φ p) (C.jB_snd τ)
  rw [e, (C.PtT_mapR_act τ p hp).2, f1, f2, C.PtT_ι τ _ hx]

end StrictChunk

end RamanujanPetersson.JacChunk

end


