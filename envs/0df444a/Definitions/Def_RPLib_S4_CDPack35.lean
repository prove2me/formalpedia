-- Prove2me | Definitions.Def_RPLib_S4_CDPack35
-- name    : RPLib_S4_CDPack35
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:24:10.790194+00:00
-- url     : https://prove2.me/theorems/9c3ede1b-c0d1-47e6-9d1a-43fd3ce5bf30
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 35 of 71
-- statement:
--   Part 35 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacChunkB_Inv`: Group chunk B3, part 2 (unit S4-JacChunkB): the inverse `G ⟶ G` and the unit point
--   * `Def_RP_JacChunkB_Grp`: Group chunk B4 (unit S4-JacChunkB): `G` is a group object over `Spec k`
--   * `Def_RP_JacChunkB_Smooth`: Group chunk B5, part 1 (unit S4-JacChunkB): smoothness, transitivity, the dense open `X`
--   * `Def_RP_JacChunkB_Sep`: Group chunk B5, part 2 (unit S4-JacChunkB): `G` is separated
--   * `Def_RP_JacChunkB_Uniq`: Group chunk B6, part 1 (unit S4-JacChunkB): uniqueness of maps out of `G`
--   * `Def_RP_JacChunkB_GPt`: Group chunk B6, part 2a (unit S4-JacChunkB): `k`-points and translations of a group scheme `G'` over `k`
--   * `Def_RP_JacChunkB_Theta`: Group chunk B6, part 2b (unit S4-JacChunkB): the comparison map `Θ : H → G'(k)`
--   * `Def_RP_JacChunkB_Iso`: Group chunk B6, part 2c (unit S4-JacChunkB): `G` is unique up to unique isomorphism
--   * `Def_RP_JacChunkB`: Group chunk theorem B (unit S4-JacChunkB), umbrella
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack34

/-!
# Curve-duality library package, part 35 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacChunkB_Inv`: Group chunk B3, part 2 (unit S4-JacChunkB): the inverse `G ⟶ G` and the unit point
* `Def_RP_JacChunkB_Grp`: Group chunk B4 (unit S4-JacChunkB): `G` is a group object over `Spec k`
* `Def_RP_JacChunkB_Smooth`: Group chunk B5, part 1 (unit S4-JacChunkB): smoothness, transitivity, the dense open `X`
* `Def_RP_JacChunkB_Sep`: Group chunk B5, part 2 (unit S4-JacChunkB): `G` is separated
* `Def_RP_JacChunkB_Uniq`: Group chunk B6, part 1 (unit S4-JacChunkB): uniqueness of maps out of `G`
* `Def_RP_JacChunkB_GPt`: Group chunk B6, part 2a (unit S4-JacChunkB): `k`-points and translations of a group scheme `G'` over `k`
* `Def_RP_JacChunkB_Theta`: Group chunk B6, part 2b (unit S4-JacChunkB): the comparison map `Θ : H → G'(k)`
* `Def_RP_JacChunkB_Iso`: Group chunk B6, part 2c (unit S4-JacChunkB): `G` is unique up to unique isomorphism
* `Def_RP_JacChunkB`: Group chunk theorem B (unit S4-JacChunkB), umbrella
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacChunkB_Inv =====
section

/-!
# Group chunk B3, part 2 (unit S4-JacChunkB): the inverse `G ⟶ G` and the unit point

* `Uv v`: the open `{x | (v, x) ∈ range Ψ}` of `X`; on it `sv v := trS (secL v) Ψ` picks `z ∈ Ω` with
  `m z = v`, `pr₂ z = x`, so `λ_{pr₁ z} = λ_v λ_x⁻¹`;
* `ginv`: glued over the charts `ι σ` restricted to `Uv v`, from `x ↦ R_{σ⁻¹} (ι λ_v⁻¹ (pr₁ z))`;
  `PtT (ginv g) = (PtT g)⁻¹` at closed points;
* `ptH h`: the closed point of `G` named by `h ∈ H`; `eta`: the `k`-point at `ptH 1`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- The open of the `x` with `(v, x)` in the range of `Ψ`. -/
noncomputable abbrev Uv (v : X) (hv : IsClosed {v}) : X.Opens :=
  secL (sX := X ↘ Spec (.of k)) v hv ⁻¹ᵁ C.Ψ.opensRange

/-- `x ↦ z ∈ Ω` with `Ψ z = (v, x)`. -/
noncomputable abbrev sv (v : X) (hv : IsClosed {v}) : (C.Uv v hv).toScheme ⟶ C.Ω.toScheme :=
  trS (secL (sX := X ↘ Spec (.of k)) v hv) C.Ψ

lemma sv_over (v : X) (hv : IsClosed {v}) :
    C.sv v hv ≫ C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k) =
      (C.Uv v hv).ι ≫ X ↘ Spec (.of k) := by
  rw [pullback.condition (f := X ↘ Spec (.of k)) (g := X ↘ Spec (.of k)), ← C.Ψ_snd_assoc, trS_Φ_assoc,
    secL_snd_assoc]

/-- At a closed point `p` of `Uv v`, `z := sv v p` is closed and `λ_{pr₁ z} = λ_v λ_p⁻¹`. -/
lemma sv_spec (v : X) (hv : IsClosed {v}) (p : (C.Uv v hv).toScheme) (hp : IsClosed {p}) :
    IsClosed {(C.sv v hv p).1} ∧
    C.lamT (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1) =
      C.lamB v hv * (C.lamT p.1)⁻¹ := by
  have hz : IsClosed {C.sv v hv p} :=
    isClosed_singleton_apply ((C.Uv v hv).ι ≫ X ↘ Spec (.of k))
      (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) (C.sv v hv)
      (C.sv_over v hv) p hp
  have hz1 := C.isClosed_Ωval _ hz
  refine ⟨hz1, ?_⟩
  have hΨ : C.Ψ (C.sv v hv p) = secL (sX := X ↘ Spec (.of k)) v hv p.1 :=
    congrArg (fun φ => φ p) (trS_Φ (secL (sX := X ↘ Spec (.of k)) v hv) C.Ψ)
  have e1 : C.m (C.sv v hv p) = pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ (C.sv v hv p)) :=
    (congrArg (fun φ => φ (C.sv v hv p)) C.Ψ_fst).symm
  have hm : C.m (C.sv v hv p) = v := by rw [e1, hΨ, secL_apply_fst]
  have e2 : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1 =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ (C.sv v hv p)) :=
    (congrArg (fun φ => φ (C.sv v hv p)) C.Ψ_snd).symm
  have hs : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1 = p.1 := by
    rw [e2, hΨ, secL_apply_snd]
  have hl := C.lamT_mul (C.sv v hv p) hz1
  rw [hs, hm, C.lamT_eq v hv] at hl
  exact eq_mul_inv_of_mul_eq hl

/-- The charts of the inverse: `Uv v` for `v` closed, inside the chart `ι σ`. -/
noncomputable abbrev invP (i : C.H × {v : X // IsClosed ({v} : Set X)}) : Scheme.{u} :=
  (C.Uv i.2.1 i.2.2).toScheme

/-- `x ↦ ι σ x` on `Uv v`. -/
noncomputable def invj (i : C.H × {v : X // IsClosed ({v} : Set X)}) : C.invP i ⟶ G C.H :=
  (C.Uv i.2.1 i.2.2).ι ≫ ι C.H i.1

instance (i : C.H × {v : X // IsClosed ({v} : Set X)}) : IsOpenImmersion (C.invj i) := by
  unfold invj; infer_instance

/-- `x ↦ R_{σ⁻¹} (ι λ_v⁻¹ (pr₁ (sv v x)))`, of value `λ_x⁻¹ σ⁻¹`. -/
noncomputable def invφ (i : C.H × {v : X // IsClosed ({v} : Set X)}) : C.invP i ⟶ G C.H :=
  C.sv i.2.1 i.2.2 ≫ C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫
    ι C.H ⟨(C.lamB i.2.1 i.2.2)⁻¹, inv_mem (C.lamB_mem_H _ _)⟩ ≫ C.Rt i.1⁻¹

lemma ginv_over (i : C.H × {v : X // IsClosed ({v} : Set X)}) :
    C.invφ i ≫ sG C.H = C.invj i ≫ sG C.H := by
  simp only [invφ, invj, Category.assoc, C.Rt_over, ι_sG]
  exact C.sv_over i.2.1 i.2.2

lemma ginv_cov (g : G C.H) (hg : IsClosed {g}) :
    ∃ i : C.H × {v : X // IsClosed ({v} : Set X)}, ∃ p : C.invP i, C.invj i p = g := by
  obtain ⟨σ, x, hx⟩ := exists_chart C.H g
  have hxc : IsClosed {x} := isClosed_of_ι C.H σ x (by rw [hx]; exact hg)
  obtain ⟨z, hzΩ, hzc, hz2⟩ := C.fib_right x hxc
  have hq : IsClosed {C.m ⟨z, hzΩ⟩} := C.isClosed_m ⟨z, hzΩ⟩ hzc
  have hΨc : IsClosed {C.Ψ ⟨z, hzΩ⟩} :=
    isClosed_singleton_apply (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k))
      (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) C.Ψ
      (by rw [C.Ψ_fst_assoc, C.m_over]) ⟨z, hzΩ⟩ (C.isClosed_Ω ⟨z, hzΩ⟩ hzc)
  have f1 : pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ ⟨z, hzΩ⟩) = C.m ⟨z, hzΩ⟩ :=
    congrArg (fun φ => φ ⟨z, hzΩ⟩) C.Ψ_fst
  have f2 : pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.Ψ ⟨z, hzΩ⟩) =
      pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) z :=
    congrArg (fun φ => φ ⟨z, hzΩ⟩) C.Ψ_snd
  have hsec : secL (sX := X ↘ Spec (.of k)) (C.m ⟨z, hzΩ⟩) hq x = C.Ψ ⟨z, hzΩ⟩ :=
    closedPoint_pullback_ext (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) _ _ (secL_isClosed _ hq x hxc) hΨc
      ((secL_apply_fst _ hq x).trans f1.symm) ((secL_apply_snd _ hq x).trans (hz2.symm.trans f2.symm))
  have hmem : x ∈ C.Uv (C.m ⟨z, hzΩ⟩) hq :=
    (Scheme.Hom.mem_preimage _).2 (Scheme.Hom.mem_opensRange.2 ⟨⟨z, hzΩ⟩, hsec.symm⟩)
  exact ⟨(σ, ⟨_, hq⟩), ⟨x, hmem⟩, hx⟩

/-- The value of a chart of the inverse: `PtT (invφ i p) = (PtT (invj i p))⁻¹`. -/
lemma ginv_val (i : C.H × {v : X // IsClosed ({v} : Set X)}) (p : C.invP i) (hp : IsClosed {p}) :
    IsClosed {C.invφ i p} ∧ C.PtT (C.invφ i p) = (C.PtT (C.invj i p))⁻¹ := by
  obtain ⟨σ, v, hv⟩ := i
  have hq : IsClosed {p.1} := isClosed_val (k := k) _ p hp
  obtain ⟨hz, hl⟩ := C.sv_spec v hv p hp
  have hw := isClosed_fst _ hz
  let τ : C.H := ⟨(C.lamB v hv)⁻¹, inv_mem (C.lamB_mem_H v hv)⟩
  have hι := isClosed_ι C.H τ _ hw
  refine ⟨?_, ?_⟩
  · show IsClosed {C.Rt σ⁻¹ (ι C.H τ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1))}
    exact isClosed_singleton_apply (sG C.H) (sG C.H) _ (C.Rt_over _) _ hι
  · show C.PtT (C.Rt σ⁻¹ (ι C.H τ (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) (C.sv v hv p).1))) =
      (C.PtT (ι C.H σ p.1))⁻¹
    rw [C.PtT_Rt _ _ hι, C.PtT_ι τ _ hw, C.PtT_ι σ _ hq, hl, Subgroup.coe_inv, mul_inv_rev]
    show (C.lamB v hv)⁻¹ * (C.lamB v hv * (C.lamT p.1)⁻¹) * (σ : Bir k X)⁻¹ = (C.lamT p.1)⁻¹ * (σ : Bir k X)⁻¹
    rw [inv_mul_cancel_left]

lemma ginv_comp (i i' : C.H × {v : X // IsClosed ({v} : Set X)}) (p : C.invP i) (p' : C.invP i')
    (hp : IsClosed {p}) (hp' : IsClosed {p'}) (e : C.invj i p = C.invj i' p') : C.invφ i p = C.invφ i' p' := by
  obtain ⟨c, v⟩ := C.ginv_val i p hp
  obtain ⟨c', v'⟩ := C.ginv_val i' p' hp'
  exact C.PtT_inj _ _ c c' (by rw [v, v', e])

/-- The inverse `G ⟶ G`. -/
noncomputable def ginv : G C.H ⟶ G C.H :=
  glueG C.H (sG C.H) C.invP C.invj C.invφ C.ginv_cov C.ginv_over C.ginv_comp

lemma ginv_over' : C.ginv ≫ sG C.H = sG C.H :=
  glueG_over C.H (sG C.H) C.invP C.invj C.invφ C.ginv_cov C.ginv_over C.ginv_comp

/-- The value of the inverse at a closed point: `PtT (ginv g) = (PtT g)⁻¹`. -/
theorem PtT_ginv (g : G C.H) (hg : IsClosed {g}) : C.PtT (C.ginv g) = (C.PtT g)⁻¹ := by
  obtain ⟨i, p, rfl⟩ := C.ginv_cov g hg
  have hp : IsClosed {p} := isClosed_of_inj _ (C.invj i).continuous (C.invj i).isOpenEmbedding.injective p hg
  have e : C.ginv (C.invj i p) = C.invφ i p :=
    glueG_apply C.H (sG C.H) C.invP C.invj C.invφ C.ginv_cov C.ginv_over C.ginv_comp i p
  rw [e]
  exact (C.ginv_val i p hp).2

/-- The closed point of `G` named by `h ∈ H`. -/
noncomputable def ptH (h : C.H) : G C.H := (C.PtEquiv.symm h).1

lemma isClosed_ptH (h : C.H) : IsClosed {C.ptH h} := (C.PtEquiv.symm h).2

lemma PtT_ptH (h : C.H) : C.PtT (C.ptH h) = h := by
  rw [C.PtT_eq _ (C.isClosed_ptH h)]
  exact congrArg Subtype.val (C.PtEquiv.apply_symm_apply h)

/-- The unit `k`-point of `G`. -/
noncomputable def eta : Spec (.of k) ⟶ G C.H := pointOfClosedPoint (sG C.H) (C.ptH 1) (C.isClosed_ptH 1)

lemma eta_over : C.eta ≫ sG C.H = 𝟙 _ := pointOfClosedPoint_comp (sG C.H) (C.ptH 1) (C.isClosed_ptH 1)

lemma eta_apply (s : Spec (.of k)) : C.eta s = C.ptH 1 :=
  pointOfClosedPoint_apply (sG C.H) (C.ptH 1) (C.isClosed_ptH 1) s

lemma PtT_eta (s : Spec (.of k)) : C.PtT (C.eta s) = 1 := by
  rw [C.eta_apply, C.PtT_ptH, Subgroup.coe_one]

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Grp =====
section

/-!
# Group chunk B4 (unit S4-JacChunkB): `G` is a group object over `Spec k`

* `GO := Over.mk (sG H)`; `kval a := PtT (a (closed point))` for a `k`-point `a : 𝟙_ ⟶ GO`;
* `hom_ext_kpt`: maps `B ⟶ GO` out of a reduced `B` locally of finite type agree once they agree on `k`-points;
* `kval_mul`, `kval_inv`, `kval_one'`: the values of `μ`, `ginv`, `η` on `k`-points;
* `grpObj`: `GrpObj GO` with `one := η`, `mul := μ`, `inv := ginv`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

lemma isClosed_specPt (s : Spec (.of k)) : IsClosed ({s} : Set (Spec (.of k))) := by
  rw [show ({s} : Set (Spec (.of k))) = Set.univ from Set.eq_univ_of_forall fun x => Subsingleton.elim x s]
  exact isClosed_univ

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- `G` as an object over `Spec k`. -/
noncomputable abbrev GO : Over (Spec (.of k)) := Over.mk (sG C.H)

/-- The value in `H` of a `k`-point of `G`. -/
noncomputable def kval (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : Bir k X :=
  C.PtT (a.left (IsLocalRing.closedPoint k))

lemma isClosed_kpt (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : IsClosed {a.left (IsLocalRing.closedPoint k)} :=
  isClosed_singleton_apply (𝟙 (Spec (.of k))) (sG C.H) a.left (Over.w a) _ (isClosed_specPt _)

lemma kpt_ext (a b : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) (h : C.kval a = C.kval b) : a = b :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq (sG C.H) (Over.w a) (Over.w b)
    (C.PtT_inj _ _ (C.isClosed_kpt a) (C.isClosed_kpt b) h))

/-- Maps out of a reduced `B` locally of finite type over `k` are determined on `k`-points. -/
lemma hom_ext_kpt {B : Over (Spec (.of k))} (hB : IsReduced B.left) (hB' : LocallyOfFiniteType B.hom)
    (f g : B ⟶ C.GO) (h : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ B, C.kval (p ≫ f) = C.kval (p ≫ g)) : f = g := by
  refine Over.OverMorphism.ext (C.G_ext_Pt B.hom f.left g.left (Over.w f) (Over.w g) fun t ht => ?_)
  have e := h (Over.homMk (U := 𝟙_ (Over (Spec (.of k)))) (V := B) (pointOfClosedPoint B.hom t ht)
    (pointOfClosedPoint_comp B.hom t ht))
  have e2 : ∀ φ : B ⟶ C.GO, C.kval (Over.homMk (U := 𝟙_ (Over (Spec (.of k)))) (V := B)
      (pointOfClosedPoint B.hom t ht) (pointOfClosedPoint_comp B.hom t ht) ≫ φ) = C.PtT (φ.left t) := by
    intro φ
    exact congrArg (fun x => C.PtT (φ.left x)) (pointOfClosedPoint_apply B.hom t ht _)
  rwa [e2 f, e2 g] at e

/-- The unit of `GO`. -/
noncomputable def oneO : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO := Over.homMk C.eta C.eta_over

/-- The multiplication of `GO`. -/
noncomputable def mulO : C.GO ⊗ C.GO ⟶ C.GO := Over.homMk C.mu C.mu_over'

/-- The inverse of `GO`. -/
noncomputable def invO : C.GO ⟶ C.GO := Over.homMk C.ginv C.ginv_over'

lemma kval_one' (q : 𝟙_ (Over (Spec (.of k))) ⟶ 𝟙_ (Over (Spec (.of k)))) : C.kval (q ≫ C.oneO) = 1 :=
  C.PtT_eta _

lemma kval_inv (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : C.kval (a ≫ C.invO) = (C.kval a)⁻¹ :=
  C.PtT_ginv _ (C.isClosed_kpt a)

lemma kval_mul (p : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO ⊗ C.GO) :
    C.kval (p ≫ C.mulO) = C.kval (p ≫ fst _ _) * C.kval (p ≫ snd _ _) := by
  have hs : IsClosed {p.left (IsLocalRing.closedPoint k)} :=
    isClosed_singleton_apply (𝟙 (Spec (.of k))) C.sGG p.left (Over.w p) _ (isClosed_specPt _)
  exact C.PtT_mu _ hs

lemma oneO_mul : C.oneO ▷ C.GO ≫ C.mulO = (λ_ C.GO).hom := by
  refine C.hom_ext_kpt (by show IsReduced (pullback (𝟙 _) (sG C.H)); infer_instance)
    (by show LocallyOfFiniteType (pullback.fst (𝟙 _) (sG C.H) ≫ 𝟙 _); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ C.oneO ▷ C.GO)
  have h2 := C.kval_one' (p ≫ fst _ _)
  simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd] at h1 h2
  rw [h1, h2, _root_.one_mul, leftUnitor_hom]

lemma mul_oneO : C.GO ◁ C.oneO ≫ C.mulO = (ρ_ C.GO).hom := by
  refine C.hom_ext_kpt (by show IsReduced (pullback (sG C.H) (𝟙 _)); infer_instance)
    (by show LocallyOfFiniteType (pullback.fst (sG C.H) (𝟙 _) ≫ sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ C.GO ◁ C.oneO)
  have h2 := C.kval_one' (p ≫ snd _ _)
  simp only [Category.assoc, whiskerLeft_fst, whiskerLeft_snd] at h1 h2
  rw [h1, h2, _root_.mul_one, rightUnitor_hom]

lemma mulO_assoc : C.mulO ▷ C.GO ≫ C.mulO = (α_ C.GO C.GO C.GO).hom ≫ C.GO ◁ C.mulO ≫ C.mulO := by
  refine C.hom_ext_kpt
    (by show IsReduced (pullback (pullback.fst (sG C.H) (sG C.H) ≫ sG C.H) (sG C.H)); infer_instance)
    (by show LocallyOfFiniteType (pullback.fst (pullback.fst (sG C.H) (sG C.H) ≫ sG C.H) (sG C.H) ≫
      pullback.fst (sG C.H) (sG C.H) ≫ sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ C.mulO ▷ C.GO)
  have h2 := C.kval_mul (p ≫ fst _ _)
  have h3 := C.kval_mul (p ≫ (α_ C.GO C.GO C.GO).hom ≫ C.GO ◁ C.mulO)
  have h4 := C.kval_mul (p ≫ (α_ C.GO C.GO C.GO).hom ≫ snd _ _)
  simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, whiskerLeft_fst, whiskerLeft_snd,
    associator_hom_fst, associator_hom_snd_fst, associator_hom_snd_snd] at h1 h2 h3 h4
  rw [h1, h2, h3, h4, _root_.mul_assoc]

lemma invO_left : lift C.invO (𝟙 C.GO) ≫ C.mulO = toUnit _ ≫ C.oneO := by
  refine C.hom_ext_kpt (by show IsReduced (G C.H); infer_instance)
    (by show LocallyOfFiniteType (sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ lift C.invO (𝟙 C.GO))
  have h2 := C.kval_one' (p ≫ toUnit _)
  simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd,
    Category.comp_id] at h1 h2
  rw [h1, h2, C.kval_inv, inv_mul_cancel]

lemma invO_right : lift (𝟙 C.GO) C.invO ≫ C.mulO = toUnit _ ≫ C.oneO := by
  refine C.hom_ext_kpt (by show IsReduced (G C.H); infer_instance)
    (by show LocallyOfFiniteType (sG C.H); infer_instance) _ _ fun p => ?_
  have h1 := C.kval_mul (p ≫ lift (𝟙 C.GO) C.invO)
  have h2 := C.kval_one' (p ≫ toUnit _)
  simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd,
    Category.comp_id] at h1 h2
  rw [h1, h2, C.kval_inv, mul_inv_cancel]

/-- `G` is a group scheme over `k`: `GrpObj (Over.mk (sG H))`. -/
noncomputable instance grpObj : GrpObj C.GO where
  one := C.oneO
  mul := C.mulO
  inv := C.invO
  one_mul := C.oneO_mul
  mul_one := C.mul_oneO
  mul_assoc := C.mulO_assoc
  left_inv := C.invO_left
  right_inv := C.invO_right

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Smooth =====
section

/-!
# Group chunk B5, part 1 (unit S4-JacChunkB): smoothness, transitivity, the dense open `X`

* `smooth_sG`: `G` is smooth over `k` (Mathlib `smooth_of_grpObj`);
* `kptH h`: the `k`-point named by `h ∈ H`; `transitive`: right translations act transitively on `G(k)`;
* `denseRange_ι1`: the chart `ι 1 : X ⟶ G` is an open immersion with dense range;
* `mu_ι1`: on `Ω`, `μ ∘ (ι 1 × ι 1) = ι 1 ∘ m` (the group law extends the chunk law).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- `G` is smooth over `k`. -/
theorem smooth_sG : Smooth (sG C.H) := by
  haveI := C.grpObj
  exact smooth_of_grpObj (sG C.H)

/-- The `k`-point of `G` named by `h ∈ H`. -/
noncomputable def kptH (h : C.H) : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO :=
  Over.homMk (pointOfClosedPoint (sG C.H) (C.ptH h) (C.isClosed_ptH h)) (pointOfClosedPoint_comp _ _ _)

lemma kval_kptH (h : C.H) : C.kval (C.kptH h) = h :=
  (congrArg C.PtT (pointOfClosedPoint_apply (sG C.H) (C.ptH h) (C.isClosed_ptH h) _)).trans (C.PtT_ptH h)

lemma kval_mem (a : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : C.kval a ∈ C.H := C.PtT_mem _

/-- Translations act transitively on the `k`-points of `G`. -/
theorem transitive (a b : 𝟙_ (Over (Spec (.of k))) ⟶ C.GO) : ∃ g, lift g a ≫ C.mulO = b := by
  refine ⟨C.kptH ⟨C.kval b * (C.kval a)⁻¹, mul_mem (C.kval_mem b) (inv_mem (C.kval_mem a))⟩, C.kpt_ext _ _ ?_⟩
  rw [C.kval_mul, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd, C.kval_kptH]
  exact inv_mul_cancel_right _ _

/-- The chart `ι 1 : X ⟶ G` has dense range. -/
theorem denseRange_ι1 : DenseRange (ι C.H 1) :=
  (ι C.H 1).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

/-- `ι 1 × ι 1 : X ×_k X ⟶ G ×_k G`. -/
noncomputable def jm : pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ⟶ pullback (sG C.H) (sG C.H) :=
  pullback.map _ _ _ _ (ι C.H 1) (ι C.H 1) (𝟙 _) (by rw [Category.comp_id, ι_sG]) (by rw [Category.comp_id, ι_sG])

@[reassoc]
lemma jm_fst : C.jm ≫ pullback.fst (sG C.H) (sG C.H) =
    pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ ι C.H 1 := pullback.lift_fst _ _ _

@[reassoc]
lemma jm_snd : C.jm ≫ pullback.snd (sG C.H) (sG C.H) =
    pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ ι C.H 1 := pullback.lift_snd _ _ _

/-- The group law of `G` extends the chunk law: `μ (ι 1 a, ι 1 b) = ι 1 (m (a, b))` on `Ω`. -/
theorem mu_ι1 : C.Ω.ι ≫ C.jm ≫ C.mu = C.m ≫ ι C.H 1 := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  haveI : IsReduced C.Ω.toScheme := isReduced_of_isOpenImmersion C.Ω.ι
  refine C.G_ext_Pt (C.Ω.ι ≫ pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) _ _ ?_ ?_
    fun q hq => ?_
  · simp only [Category.assoc, C.mu_over', sGG, C.jm_fst_assoc, ι_sG]
  · simp only [Category.assoc, ι_sG, C.m_over]
  · have hq1 := C.isClosed_Ωval q hq
    have hz : IsClosed {C.jm q.1} :=
      isClosed_singleton_apply (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k)) C.sGG C.jm
        (by simp only [sGG, C.jm_fst_assoc, ι_sG]) q.1 hq1
    have f1 : pullback.fst (sG C.H) (sG C.H) (C.jm q.1) =
        ι C.H 1 (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) := congrArg (fun φ => φ q.1) C.jm_fst
    have f2 : pullback.snd (sG C.H) (sG C.H) (C.jm q.1) =
        ι C.H 1 (pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) := congrArg (fun φ => φ q.1) C.jm_snd
    show C.PtT (C.mu (C.jm q.1)) = C.PtT (ι C.H 1 (C.m q))
    rw [C.PtT_mu _ hz, f1, f2, C.PtT_ι 1 _ (isClosed_fst _ hq1), C.PtT_ι 1 _ (isClosed_snd _ hq1),
      C.PtT_ι 1 _ (C.isClosed_m q hq1), ← C.lamT_mul q hq1]
    simp only [OneMemClass.coe_one, _root_.one_mul]

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Sep =====
section

/-!
# Group chunk B5, part 2 (unit S4-JacChunkB): `G` is separated

* `grpDiv G : G ⊗ G ⟶ G`, `(a, b) ↦ a b⁻¹`, for a group object `G` of a cartesian monoidal category;
* `isPullback_diag_grp`: the diagonal of `G` is the pullback of the unit `η` along `grpDiv`;
* `isSeparated_sG`: `G → Spec k` is separated (its diagonal is a base change of the closed immersion `η`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

section General

variable {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] (G : 𝒞) [GrpObj G]

/-- `(a, b) ↦ a b⁻¹` on a group object. -/
noncomputable def grpDiv : G ⊗ G ⟶ G := lift (fst G G) (snd G G ≫ GrpObj.inv) ≫ MonObj.mul

lemma lift_grpDiv {T : 𝒞} (a b : T ⟶ G) : lift a b ≫ grpDiv G = a * b⁻¹ := by
  rw [grpDiv, ← Category.assoc, comp_lift, lift_fst, lift_snd_assoc]
  rfl

/-- The diagonal of a group object is the pullback of the unit along `grpDiv`. -/
lemma isPullback_diag_grp :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G) (grpDiv G) MonObj.one := by
  have key : ∀ {T : 𝒞} (s : T ⟶ G ⊗ G) (t : T ⟶ 𝟙_ 𝒞), s ≫ grpDiv G = t ≫ MonObj.one →
      s ≫ fst G G = s ≫ snd G G := by
    intro T s t h
    have h1 : (s ≫ fst G G) * (s ≫ snd G G)⁻¹ = 1 := by
      rw [← lift_grpDiv, lift_comp_fst_snd, h, toUnit_unique t (toUnit T)]
      rfl
    exact mul_inv_eq_one.mp h1
  have w : lift (𝟙 G) (𝟙 G) ≫ grpDiv G = toUnit G ≫ MonObj.one := by
    rw [lift_grpDiv]
    exact mul_inv_cancel (𝟙 G)
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w (fun s => s.fst ≫ fst G G) (fun s => ?_)
    (fun s => toUnit_unique _ _) (fun s m h₁ _ => ?_)⟩⟩
  · refine hom_ext _ _ (by simp) ?_
    simpa using key s.fst s.snd s.condition
  · rw [← h₁]
    simp

end General

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- `G` is separated over `k`: its diagonal is the base change of the unit section (a closed immersion) along
`(a, b) ↦ a b⁻¹`. -/
theorem isSeparated_sG : IsSeparated (sG C.H) := by
  letI := C.grpObj
  have hP := (isPullback_diag_grp C.GO).map (Over.forget (Spec (.of k)))
  have hη : IsClosedImmersion ((Over.forget (Spec (.of k))).map (MonObj.one : 𝟙_ _ ⟶ C.GO)) :=
    inferInstanceAs (IsClosedImmersion (MonObj.one : 𝟙_ _ ⟶ C.GO).left)
  have hΔ : IsClosedImmersion ((Over.forget (Spec (.of k))).map (lift (𝟙 C.GO) (𝟙 C.GO))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) hP.flip hη
  exact ⟨hΔ⟩

/-- `G` is a separated scheme. -/
theorem isSeparated_G : (G C.H).IsSeparated := by
  haveI := C.isSeparated_sG
  exact ⟨by rw [terminal.hom_ext (terminal.from (G C.H)) (sG C.H ≫ terminal.from _)]; infer_instance⟩

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Uniq =====
section

/-!
# Group chunk B6, part 1 (unit S4-JacChunkB): uniqueness of maps out of `G`

* `Y_ext`: `k`-maps from a reduced lft `k`-scheme to a separated lft `k`-scheme agreeing on closed points agree;
* `glueY`: pointwise gluing of `k`-maps into a separated lft `k`-scheme `Y` (the `glueG` of B0 for any target);
* `hom_ext_ι1`: `k`-maps from `G` to a separated lft `k`-scheme are determined on the dense open `ι 1 : X ⟶ G`;
* `iso_ext_ι1`, `eq_id_of_ι1`: an isomorphism out of `G` is unique given its restriction to `X`, and a `k`-endomorphism
  of `G` fixing `X` is the identity ("unique up to unique isomorphism").
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

section GlueY

variable {T Y : Scheme.{u}} [IsReduced T] (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT]
  (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY]

/-- `k`-maps from a reduced lft `k`-scheme to a separated lft `k`-scheme agreeing on closed points agree. -/
lemma Y_ext (f g : T ⟶ Y) (hf : f ≫ sY = sT) (hg : g ≫ sY = sT) (h : ∀ t, IsClosed {t} → f t = g t) :
    f = g := by
  haveI : LocallyOfFiniteType (f ≫ sY) := by rw [hf]; infer_instance
  exact ext_of_apply_eq sY Set.univ isOpen_univ.isLocallyClosed dense_univ (fun t _ ht => h t ht)
    (hf.trans hg.symm)

variable {J : Type u} (P : J → Scheme.{u}) (j : ∀ i, P i ⟶ T) [∀ i, IsOpenImmersion (j i)]
  (φ : ∀ i, P i ⟶ Y) (hcov : ∀ t, IsClosed {t} → ∃ i, ∃ p : P i, j i p = t)
  (hφ : ∀ i, φ i ≫ sY = j i ≫ sT)
  (hcomp : ∀ i i' (p : P i) (p' : P i'), IsClosed {p} → IsClosed {p'} → j i p = j i' p' → φ i p = φ i' p')

include hφ hcomp in
lemma glueY_compat (a b : J) :
    pullback.fst (j a) (j b) ≫ φ a = pullback.snd (j a) (j b) ≫ φ b := by
  haveI : IsReduced (pullback (j a) (j b)) := isReduced_of_isOpenImmersion (pullback.fst (j a) (j b) ≫ j a)
  refine Y_ext (pullback.fst (j a) (j b) ≫ j a ≫ sT) sY _ _ ?_ ?_ ?_
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

/-- Pointwise gluing of `k`-morphisms into a separated lft `k`-scheme `Y`. -/
noncomputable def glueY : T ⟶ Y :=
  (coverOfClosed sT P j hcov).glueMorphisms φ (glueY_compat sT sY P j φ hφ hcomp)

@[reassoc]
lemma glueY_fac (i : J) : j i ≫ glueY sT sY P j φ hcov hφ hcomp = φ i :=
  Scheme.Cover.ι_glueMorphisms (coverOfClosed sT P j hcov) φ _ i

lemma glueY_over : glueY sT sY P j φ hcov hφ hcomp ≫ sY = sT :=
  Scheme.Cover.hom_ext (coverOfClosed sT P j hcov) _ _ fun (i : J) =>
    (glueY_fac_assoc sT sY P j φ hcov hφ hcomp i sY).trans (hφ i)

lemma glueY_apply (i : J) (p : P i) : glueY sT sY P j φ hcov hφ hcomp (j i p) = φ i p :=
  congrArg (fun ψ => ψ p) (glueY_fac sT sY P j φ hcov hφ hcomp i)

end GlueY

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

/-- `k`-morphisms from `G` to a separated lft `k`-scheme are determined on the dense open `ι 1 : X ⟶ G`. -/
theorem hom_ext_ι1 {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY]
    (f g : G C.H ⟶ Y) (hf : f ≫ sY = sG C.H) (hg : g ≫ sY = sG C.H) (h : ι C.H 1 ≫ f = ι C.H 1 ≫ g) :
    f = g := by
  haveI : LocallyOfFiniteType (f ≫ sY) := by rw [hf]; infer_instance
  refine ext_of_apply_eq sY (Set.range (ι C.H 1)) (ι C.H 1).isOpenEmbedding.isOpen_range.isLocallyClosed
    C.denseRange_ι1 ?_ (hf.trans hg.symm)
  rintro _ ⟨x, rfl⟩ _
  exact congrArg (fun φ => φ x) h

/-- Uniqueness of the isomorphism: an isomorphism over `k` from `G` onto a separated lft `k`-scheme is determined
by its restriction to the dense open `X`. -/
theorem iso_ext_ι1 {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY]
    (e e' : G C.H ≅ Y) (he : e.hom ≫ sY = sG C.H) (he' : e'.hom ≫ sY = sG C.H)
    (h : ι C.H 1 ≫ e.hom = ι C.H 1 ≫ e'.hom) : e = e' :=
  Iso.ext (C.hom_ext_ι1 sY _ _ he he' h)

/-- A `k`-endomorphism of `G` that fixes the dense open `X` is the identity. -/
theorem eq_id_of_ι1 (f : G C.H ⟶ G C.H) (hf : f ≫ sG C.H = sG C.H) (h : ι C.H 1 ≫ f = ι C.H 1) : f = 𝟙 _ := by
  haveI := C.isSeparated_sG
  exact C.hom_ext_ι1 (sG C.H) f (𝟙 _) hf (Category.id_comp _) (h.trans (Category.comp_id _).symm)

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_GPt =====
section

/-!
# Group chunk B6, part 2a (unit S4-JacChunkB): `k`-points and translations of a group scheme `G'` over `k`

For `G' : Over (Spec k)` locally of finite type (`k` algebraically closed), `k`-points `𝟙_ ⟶ G'` form a group when
`G'` is a group object (`open MonObj`). This file gives:
* `ev a`: the closed point named by a `k`-point; `ev_inj`, `kp` (the `k`-point at a closed point), `ev_kp`, `kp_ev`;
* `ev_mul`: the product of `k`-points is `μ` at the closed point of `G' ×_k G'` with the two coordinates;
* `tr θ = (toUnit ≫ θ) * 𝟙 : G' ⟶ G'` (left translation), `kp_tr : a ≫ tr θ = θ * a`, `tr_tr`, `tr_one`, `trIso`,
  `tr_ev : (tr θ).left (ev a) = ev (θ * a)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace GrpPt

variable (G' : Over (Spec (.of k))) [LocallyOfFiniteType G'.hom]

/-- The closed point named by a `k`-point. -/
noncomputable def ev (a : 𝟙_ (Over (Spec (.of k))) ⟶ G') : G'.left := a.left (IsLocalRing.closedPoint k)

lemma isClosed_ev (a : 𝟙_ (Over (Spec (.of k))) ⟶ G') : IsClosed {ev G' a} :=
  isClosed_singleton_apply (𝟙 (Spec (.of k))) G'.hom a.left (Over.w a) _ (isClosed_specPt _)

lemma ev_inj {a b : 𝟙_ (Over (Spec (.of k))) ⟶ G'} (h : ev G' a = ev G' b) : a = b :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq G'.hom (Over.w a) (Over.w b) h)

lemma ev_comp {B : Over (Spec (.of k))} (a : 𝟙_ (Over (Spec (.of k))) ⟶ B) (f : B ⟶ G') :
    ev G' (a ≫ f) = f.left (a.left (IsLocalRing.closedPoint k)) := rfl

/-- The `k`-point at a closed point. -/
noncomputable def kp (g : G'.left) (hg : IsClosed {g}) : 𝟙_ (Over (Spec (.of k))) ⟶ G' :=
  Over.homMk (pointOfClosedPoint G'.hom g hg) (pointOfClosedPoint_comp _ _ _)

lemma ev_kp (g : G'.left) (hg : IsClosed {g}) : ev G' (kp G' g hg) = g :=
  pointOfClosedPoint_apply G'.hom g hg _

lemma kp_ev (a : 𝟙_ (Over (Spec (.of k))) ⟶ G') : kp G' (ev G' a) (isClosed_ev G' a) = a :=
  ev_inj G' (ev_kp G' _ _)

variable [GrpObj G']

lemma ev_mul (a b : 𝟙_ (Over (Spec (.of k))) ⟶ G') (p : (pullback G'.hom G'.hom : Scheme.{u}))
    (hp : IsClosed {p}) (h1 : pullback.fst G'.hom G'.hom p = ev G' a)
    (h2 : pullback.snd G'.hom G'.hom p = ev G' b) :
    ev G' (a * b) = (MonObj.mul : G' ⊗ G' ⟶ G').left p := by
  have e1 : (lift a b).left ≫ pullback.fst G'.hom G'.hom = a.left := congrArg CommaMorphism.left (lift_fst a b)
  have e2 : (lift a b).left ≫ pullback.snd G'.hom G'.hom = b.left := congrArg CommaMorphism.left (lift_snd a b)
  have hq : IsClosed {(lift a b).left (IsLocalRing.closedPoint k)} :=
    isClosed_singleton_apply (𝟙 (Spec (.of k))) (pullback.fst G'.hom G'.hom ≫ G'.hom) (lift a b).left
      (Over.w (lift a b)) _ (isClosed_specPt _)
  have e : (lift a b).left (IsLocalRing.closedPoint k) = p :=
    closedPoint_pullback_ext G'.hom G'.hom _ p hq hp
      ((congrArg (fun φ => φ (IsLocalRing.closedPoint k)) e1).trans h1.symm)
      ((congrArg (fun φ => φ (IsLocalRing.closedPoint k)) e2).trans h2.symm)
  exact congrArg (MonObj.mul : G' ⊗ G' ⟶ G').left e

/-- Left translation by a `k`-point: `g ↦ θ g`. -/
noncomputable def tr (θ : 𝟙_ (Over (Spec (.of k))) ⟶ G') : G' ⟶ G' := (toUnit G' ≫ θ) * 𝟙 G'

lemma comp_tr {T : Over (Spec (.of k))} (a : T ⟶ G') (θ : 𝟙_ (Over (Spec (.of k))) ⟶ G') :
    a ≫ tr G' θ = (toUnit T ≫ θ) * a := by
  rw [tr, MonObj.comp_mul, ← Category.assoc, toUnit_unique (a ≫ toUnit G') (toUnit T), Category.comp_id]

lemma kp_tr (a θ : 𝟙_ (Over (Spec (.of k))) ⟶ G') : a ≫ tr G' θ = θ * a := by
  rw [comp_tr, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

lemma tr_tr (θ θ' : 𝟙_ (Over (Spec (.of k))) ⟶ G') : tr G' θ ≫ tr G' θ' = tr G' (θ' * θ) := by
  rw [comp_tr]
  simp only [tr, MonObj.comp_mul]
  exact (mul_assoc _ _ _).symm

lemma tr_one : tr G' 1 = 𝟙 G' := by
  rw [tr, MonObj.comp_one, _root_.one_mul]

/-- Left translation as an isomorphism. -/
noncomputable def trIso (θ : 𝟙_ (Over (Spec (.of k))) ⟶ G') : G' ≅ G' where
  hom := tr G' θ
  inv := tr G' θ⁻¹
  hom_inv_id := by rw [tr_tr, inv_mul_cancel, tr_one]
  inv_hom_id := by rw [tr_tr, mul_inv_cancel, tr_one]

instance isIso_tr_left (θ : 𝟙_ (Over (Spec (.of k))) ⟶ G') : IsIso (tr G' θ).left :=
  inferInstanceAs (IsIso ((Over.forget _).map (trIso G' θ).hom))

lemma tr_ev (θ a : 𝟙_ (Over (Spec (.of k))) ⟶ G') : (tr G' θ).left (ev G' a) = ev G' (θ * a) := by
  rw [← kp_tr]
  rfl

end GrpPt

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Theta =====
section

/-!
# Group chunk B6, part 2b (unit S4-JacChunkB): the comparison map `Θ : H → G'(k)`

Setting: a group scheme `G'` over `k` (lft) and `j : X ⟶ G'` over `k` with `μ' ∘ (j × j) = j ∘ m` on `Ω`.
* `JT x`: the `k`-point `j x` (total; `1` off closed points); `JT_mul`: `J(m(a, b)) = J a * J b` on closed points of `Ω`;
* `common_pt`: for closed `z, u, z', u'` there are closed `t, t'` with `(z,t), (u,t), (z',t'), (u',t') ∈ Ω` and
  `m(z,t) = m(z',t')` (Jacobson + irreducible, images of opens under the open immersions `λ_z`);
* `Th_wd`: `σ λ_z = λ_u`, `σ λ_z' = λ_u'` imply `J u (J z)⁻¹ = J u' (J z')⁻¹`;
* `Th σ := J u (J z)⁻¹` for any such pair; `Th_spec`, `Th_mul`, `Th_one`, `Th_lam : Th λ_x = J x`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]

lemma takes_closed {σ : Bir k X} {x y : X} (h : Takes σ x y) (hx : IsClosed {x}) : IsClosed {y} := by
  obtain ⟨h, rfl⟩ := h
  exact isClosed_hom_apply (k := k) (rep σ) x h hx

variable (G' : Over (Spec (.of k))) [LocallyOfFiniteType G'.hom] [GrpObj G'] (j : X ⟶ G'.left)
  (hj : j ≫ G'.hom = X ↘ Spec (.of k))

/-- `j × j : X ×_k X ⟶ G' ×_k G'`. -/
noncomputable def jmap : pullback (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ⟶ pullback G'.hom G'.hom :=
  pullback.map _ _ _ _ j j (𝟙 _) (by rw [hj, Category.comp_id]) (by rw [hj, Category.comp_id])

@[reassoc]
lemma jmap_fst : jmap G' j hj ≫ pullback.fst G'.hom G'.hom =
    pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ j := pullback.lift_fst _ _ _

@[reassoc]
lemma jmap_snd : jmap G' j hj ≫ pullback.snd G'.hom G'.hom =
    pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ j := pullback.lift_snd _ _ _

open Classical in
/-- The `k`-point `j x` of `G'` (value `1` away from closed points). -/
noncomputable def JT (x : X) : 𝟙_ (Over (Spec (.of k))) ⟶ G' :=
  if hx : IsClosed {x} then GrpPt.kp G' (j x) (isClosed_singleton_apply (X ↘ Spec (.of k)) G'.hom j hj x hx) else 1

lemma ev_JT (x : X) (hx : IsClosed {x}) : GrpPt.ev G' (JT G' j hj x) = j x := by
  rw [JT, dif_pos hx, GrpPt.ev_kp]

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))

lemma lamT_inj (a b : X) (ha : IsClosed {a}) (hb : IsClosed {b}) (h : C.lamT a = C.lamT b) : a = b := by
  rw [C.lamT_eq a ha, C.lamT_eq b hb] at h
  exact C.lamB_inj a ha b hb h

/-- `λ_a (dom λ_a ∩ dom λ_b)`, an open subset of `X`. -/
noncomputable def img (a b : X) (ha : IsClosed {a}) (hb : IsClosed {b}) : TopologicalSpace.Opens X :=
  ⟨(C.lam a ha).toPartialMap.hom ''
      ((C.lam a ha).toPartialMap.domain.ι ⁻¹' ((C.lam b hb).toPartialMap.domain : Set X)), by
    haveI : IsOpenImmersion (C.lam a ha).toPartialMap.hom :=
      inferInstanceAs (IsOpenImmersion ((C.lam a ha).iso.hom ≫ (C.lam a ha).target.ι))
    exact (C.lam a ha).toPartialMap.hom.isOpenEmbedding.isOpenMap _
      ((C.lam b hb).toPartialMap.domain.isOpen.preimage (Scheme.Hom.continuous _))⟩

/-- A common value `m(z,t) = m(z',t')` with `(z,t), (u,t), (z',t'), (u',t') ∈ Ω`, all points closed. -/
lemma common_pt (z u z' u' : X) (hz : IsClosed {z}) (hu : IsClosed {u}) (hz' : IsClosed {z'})
    (hu' : IsClosed {u'}) :
    ∃ t t' : X, IsClosed {t} ∧ IsClosed {t'} ∧ ∃ (h1 : t ∈ (C.lam z hz).toPartialMap.domain)
      (_ : t ∈ (C.lam u hu).toPartialMap.domain) (h3 : t' ∈ (C.lam z' hz').toPartialMap.domain)
      (_ : t' ∈ (C.lam u' hu').toPartialMap.domain), C.m ⟨secL z hz t, h1⟩ = C.m ⟨secL z' hz' t', h3⟩ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  have ne : ∀ (a b : X) (ha : IsClosed {a}) (hb : IsClosed {b}), ((C.img a b ha hb : X.Opens) : Set X).Nonempty := by
    intro a b ha hb
    obtain ⟨t, h1, h2, -⟩ := exists_closed_inter _ _ (C.lam_ne a ha) (C.lam_ne b hb)
    exact ⟨_, ⟨t, h1⟩, h2, rfl⟩
  obtain ⟨p, ⟨⟨t, h1⟩, h2, rfl⟩, ⟨⟨t', h3⟩, h4, e⟩, hp⟩ :=
    exists_closed_inter _ _ (ne z u hz hu) (ne z' u' hz' hu')
  have ht := takes_closed (C.lamB_inv_takes z hz t h1) hp
  have ht' := takes_closed (C.lamB_inv_takes z' hz' t' h3) (by rw [e]; exact hp)
  exact ⟨t, t', ht, ht', h1, h2, h3, h4,
    ((C.lam_apply z hz t h1).symm.trans e.symm).trans (C.lam_apply z' hz' t' h3)⟩

variable (hjm : C.Ω.ι ≫ jmap G' j hj ≫ (MonObj.mul : G' ⊗ G' ⟶ G').left = C.m ≫ j)

include hjm in
/-- `J (m (a, b)) = J a * J b` at closed points of `Ω`. -/
lemma JT_mul (q : C.Ω) (hq : IsClosed {q.1}) :
    JT G' j hj (C.m q) = JT G' j hj (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) *
      JT G' j hj (pullback.snd (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) q.1) := by
  have hp : IsClosed {jmap G' j hj q.1} :=
    isClosed_singleton_apply (pullback.fst (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) ≫ X ↘ Spec (.of k))
      (pullback.fst G'.hom G'.hom ≫ G'.hom) (jmap G' j hj) (by rw [jmap_fst_assoc, hj]) q.1 hq
  refine GrpPt.ev_inj G' ((ev_JT G' j hj _ (C.isClosed_m q hq)).trans ?_)
  rw [GrpPt.ev_mul G' _ _ (jmap G' j hj q.1) hp
    ((congrArg (fun φ => φ q.1) (jmap_fst G' j hj)).trans (ev_JT G' j hj _ (isClosed_fst q.1 hq)).symm)
    ((congrArg (fun φ => φ q.1) (jmap_snd G' j hj)).trans (ev_JT G' j hj _ (isClosed_snd q.1 hq)).symm)]
  exact (congrArg (fun φ => φ q) hjm).symm

include hjm in
lemma shift (σ : Bir k X) (z u t : X) (hz : IsClosed {z}) (hu : IsClosed {u}) (ht : IsClosed {t})
    (h1 : t ∈ (C.lam z hz).toPartialMap.domain) (h2 : t ∈ (C.lam u hu).toPartialMap.domain)
    (h : σ * C.lamT z = C.lamT u) :
    σ * C.lamT (C.m ⟨secL z hz t, h1⟩) = C.lamT (C.m ⟨secL u hu t, h2⟩) ∧
      JT G' j hj u * (JT G' j hj z)⁻¹ =
        JT G' j hj (C.m ⟨secL u hu t, h2⟩) * (JT G' j hj (C.m ⟨secL z hz t, h1⟩))⁻¹ := by
  have c1 : IsClosed {(⟨secL z hz t, h1⟩ : C.Ω).1} := secL_isClosed (sX := X ↘ Spec (.of k)) z hz t ht
  have c2 : IsClosed {(⟨secL u hu t, h2⟩ : C.Ω).1} := secL_isClosed (sX := X ↘ Spec (.of k)) u hu t ht
  have l1 := C.lamT_mul _ c1
  have l2 := C.lamT_mul _ c2
  have j1 := C.JT_mul G' j hj hjm _ c1
  have j2 := C.JT_mul G' j hj hjm _ c2
  simp only [secL_apply_fst, secL_apply_snd] at l1 l2 j1 j2
  refine ⟨by rw [← l1, ← l2, ← _root_.mul_assoc, h], ?_⟩
  rw [j1, j2, _root_.mul_inv_rev, _root_.mul_assoc, _root_.mul_inv_cancel_left]

include hjm in
/-- Well-definedness of `Θ`. -/
theorem Th_wd (σ : Bir k X) (z u z' u' : X) (hz : IsClosed {z}) (hu : IsClosed {u}) (hz' : IsClosed {z'})
    (hu' : IsClosed {u'}) (h : σ * C.lamT z = C.lamT u) (h' : σ * C.lamT z' = C.lamT u') :
    JT G' j hj u * (JT G' j hj z)⁻¹ = JT G' j hj u' * (JT G' j hj z')⁻¹ := by
  obtain ⟨t, t', ht, ht', h1, h2, h3, h4, e⟩ := C.common_pt z u z' u' hz hu hz' hu'
  obtain ⟨A1, A2⟩ := C.shift G' j hj hjm σ z u t hz hu ht h1 h2 h
  obtain ⟨B1, B2⟩ := C.shift G' j hj hjm σ z' u' t' hz' hu' ht' h3 h4 h'
  rw [e] at A1 A2
  have e2 := C.lamT_inj _ _ (C.isClosed_m _ (secL_isClosed (sX := X ↘ Spec (.of k)) u hu t ht))
    (C.isClosed_m _ (secL_isClosed (sX := X ↘ Spec (.of k)) u' hu' t' ht')) (A1.symm.trans B1)
  rw [A2, B2, e2]

lemma exists_pair (σ : Bir k X) (hσ : σ ∈ C.H) :
    ∃ z u : X, IsClosed {z} ∧ IsClosed {u} ∧ σ * C.lamT z = C.lamT u := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨z, hz1, -, hz⟩ := exists_closed_inter (rep σ).domain (rep σ).domain (rep σ).dense_domain.nonempty
    (rep σ).dense_domain.nonempty
  have hu := isClosed_hom_apply (k := k) (rep σ) z hz1 hz
  exact ⟨z, _, hz, hu, by rw [C.lamT_eq z hz, C.lamT_eq _ hu]; exact C.RC_fwd σ hσ z hz _ hu (takes_self σ z hz1)⟩

/-- `Θ σ = J u (J z)⁻¹` for any closed `z, u` with `σ λ_z = λ_u`. -/
noncomputable def Th (σ : C.H) : 𝟙_ (Over (Spec (.of k))) ⟶ G' :=
  JT G' j hj (C.exists_pair σ σ.2).choose_spec.choose * (JT G' j hj (C.exists_pair σ σ.2).choose)⁻¹

include hjm in
lemma Th_spec (σ : C.H) (z u : X) (hz : IsClosed {z}) (hu : IsClosed {u}) (h : (σ : Bir k X) * C.lamT z = C.lamT u) :
    C.Th G' j hj σ = JT G' j hj u * (JT G' j hj z)⁻¹ := by
  obtain ⟨hz0, hu0, h0⟩ := (C.exists_pair σ σ.2).choose_spec.choose_spec
  exact C.Th_wd G' j hj hjm σ _ _ z u hz0 hu0 hz hu h0 h

include hjm in
lemma Th_mul (σ τ : C.H) : C.Th G' j hj (σ * τ) = C.Th G' j hj σ * C.Th G' j hj τ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨v, hv1, hv2, hv⟩ := exists_closed_inter (rep (σ : Bir k X)).domain (rep (τ : Bir k X)⁻¹).domain
    (rep _).dense_domain.nonempty (rep _).dense_domain.nonempty
  have hu := isClosed_hom_apply (k := k) (rep (σ : Bir k X)) v hv1 hv
  have hz := isClosed_hom_apply (k := k) (rep (τ : Bir k X)⁻¹) v hv2 hv
  have e1 : (σ : Bir k X) * C.lamT v = C.lamT ((rep (σ : Bir k X)).hom ⟨v, hv1⟩) := by
    rw [C.lamT_eq v hv, C.lamT_eq _ hu]; exact C.RC_fwd _ σ.2 v hv _ hu (takes_self _ v hv1)
  have e2 : (τ : Bir k X)⁻¹ * C.lamT v = C.lamT ((rep (τ : Bir k X)⁻¹).hom ⟨v, hv2⟩) := by
    rw [C.lamT_eq v hv, C.lamT_eq _ hz]; exact C.RC_fwd _ (inv_mem τ.2) v hv _ hz (takes_self _ v hv2)
  have e3 : (τ : Bir k X) * C.lamT ((rep (τ : Bir k X)⁻¹).hom ⟨v, hv2⟩) = C.lamT v := by
    rw [← e2, _root_.mul_inv_cancel_left]
  rw [C.Th_spec G' j hj hjm (σ * τ) _ _ hz hu (by rw [Subgroup.coe_mul, _root_.mul_assoc, e3, e1]),
    C.Th_spec G' j hj hjm σ v _ hv hu e1, C.Th_spec G' j hj hjm τ _ v hz hv e3, _root_.mul_assoc,
    _root_.inv_mul_cancel_left]

include hjm in
lemma Th_one : C.Th G' j hj 1 = 1 := by
  obtain ⟨x, hx⟩ := exists_closedPoint (X := X) k
  rw [C.Th_spec G' j hj hjm 1 x x hx hx (by simp), _root_.mul_inv_cancel]

include hjm in
lemma Th_lam (x : X) (hx : IsClosed {x}) : C.Th G' j hj ⟨C.lamB x hx, C.lamB_mem_H x hx⟩ = JT G' j hj x := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  obtain ⟨t, h1, -, ht⟩ := exists_closed_inter _ _ (C.lam_ne x hx) (C.lam_ne x hx)
  have c1 : IsClosed {(⟨secL x hx t, h1⟩ : C.Ω).1} := secL_isClosed (sX := X ↘ Spec (.of k)) x hx t ht
  have l1 := C.lamT_mul _ c1
  have j1 := C.JT_mul G' j hj hjm _ c1
  simp only [secL_apply_fst, secL_apply_snd] at l1 j1
  rw [C.Th_spec G' j hj hjm _ t _ ht (C.isClosed_m _ c1) (by rw [← l1, C.lamT_eq x hx]), j1,
    _root_.mul_inv_cancel_right]

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB_Iso =====
section

/-!
# Group chunk B6, part 2c (unit S4-JacChunkB): `G` is unique up to unique isomorphism

Let `G'` be a group scheme over `k` (separated, lft, reduced, irreducible) with an open immersion `j : X ⟶ G'` over `k`
compatible with the chunk law (`μ' ∘ (j × j) = j ∘ m` on `Ω`). With `Θ : H → G'(k)` of part 2b:
* `Th_inj`, `Th_surj`: `Θ` is bijective; `trj σ := j ≫ (left translation by Θ σ)`;
* `phi : G ⟶ G'` glued from `trj σ` on the charts `ι σ`, `psi : G' ⟶ G` glued from `ι σ` on the charts `trj σ`;
* `existsUnique_iso`: there is a unique isomorphism `G ≅ G'` over `k` restricting to `j` on `X`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacChunk

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsReduced X]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] [X.IsSeparated]
  [IrreducibleSpace X] [GeometricallyReduced (X ↘ Spec (.of k))]
  (G' : Over (Spec (.of k))) [LocallyOfFiniteType G'.hom] [GrpObj G'] (j : X ⟶ G'.left)
  (hj : j ≫ G'.hom = X ↘ Spec (.of k))

namespace StrictChunk

variable (C : StrictChunk (X ↘ Spec (.of k)))
  (hjm : C.Ω.ι ≫ jmap G' j hj ≫ (MonObj.mul : G' ⊗ G' ⟶ G').left = C.m ≫ j)

/-- The chart `x ↦ Θ σ · j x` of `G'`. -/
noncomputable def trj (σ : C.H) : X ⟶ G'.left := j ≫ (GrpPt.tr G' (C.Th G' j hj σ)).left

lemma trj_over (σ : C.H) : C.trj G' j hj σ ≫ G'.hom = X ↘ Spec (.of k) := by
  rw [trj, Category.assoc, Over.w (GrpPt.tr G' (C.Th G' j hj σ)), hj]

include hjm in
lemma trj_apply (σ : C.H) (x : X) (hx : IsClosed {x}) :
    C.trj G' j hj σ x = GrpPt.ev G' (C.Th G' j hj (σ * ⟨C.lamB x hx, C.lamB_mem_H x hx⟩)) := by
  rw [C.Th_mul G' j hj hjm, C.Th_lam G' j hj hjm x hx, ← GrpPt.tr_ev, ev_JT G' j hj x hx]
  rfl

include hjm in
lemma trj_one : C.trj G' j hj 1 = j := by
  rw [trj, C.Th_one G' j hj hjm, GrpPt.tr_one, Over.id_left, Category.comp_id]

variable [IsOpenImmersion j]

instance (σ : C.H) : IsOpenImmersion (C.trj G' j hj σ) := by unfold trj; infer_instance

include hjm in
lemma Th_eq_one (σ : C.H) (h : C.Th G' j hj σ = 1) : σ = 1 := by
  obtain ⟨z, u, hz, hu, e⟩ := C.exists_pair σ σ.2
  rw [C.Th_spec G' j hj hjm σ z u hz hu e, _root_.mul_inv_eq_one] at h
  have hzu : u = z := j.isOpenEmbedding.injective
    ((ev_JT G' j hj u hu).symm.trans ((congrArg (GrpPt.ev G') h).trans (ev_JT G' j hj z hz)))
  subst hzu
  exact Subtype.ext (_root_.mul_right_cancel (e.trans (_root_.one_mul _).symm))

include hjm in
lemma Th_inj (σ τ : C.H) (h : C.Th G' j hj σ = C.Th G' j hj τ) : σ = τ := by
  have h1 : C.Th G' j hj τ⁻¹ * C.Th G' j hj τ = 1 := by
    rw [← C.Th_mul G' j hj hjm, _root_.inv_mul_cancel, C.Th_one G' j hj hjm]
  exact (_root_.inv_mul_eq_one.1 (C.Th_eq_one G' j hj hjm (τ⁻¹ * σ) (by rw [C.Th_mul G' j hj hjm, h, h1]))).symm

variable [IsSeparated G'.hom] [IsReduced G'.left] [IrreducibleSpace G'.left]

include hjm in
lemma Th_surj (θ : 𝟙_ (Over (Spec (.of k))) ⟶ G') : ∃ σ : C.H, C.Th G' j hj σ = θ := by
  have : JacobsonSpace G'.left := LocallyOfFiniteType.jacobsonSpace G'.hom
  obtain ⟨x0, -⟩ := exists_closedPoint (X := X) k
  obtain ⟨g, ⟨u, rfl⟩, ⟨z, e⟩, hg⟩ := exists_closed_inter ⟨_, j.isOpenEmbedding.isOpen_range⟩
    ⟨_, (j ≫ (GrpPt.tr G' θ).left).isOpenEmbedding.isOpen_range⟩ ⟨_, x0, rfl⟩ ⟨_, x0, rfl⟩
  have hu := isClosed_of_inj j j.continuous j.isOpenEmbedding.injective u hg
  have hz := isClosed_of_inj _ (j ≫ (GrpPt.tr G' θ).left).continuous
    (j ≫ (GrpPt.tr G' θ).left).isOpenEmbedding.injective z (by rw [e]; exact hg)
  have e' : JT G' j hj u = θ * JT G' j hj z := GrpPt.ev_inj G' (by
    rw [ev_JT G' j hj u hu, ← GrpPt.tr_ev, ev_JT G' j hj z hz]; exact e.symm)
  refine ⟨⟨C.lamB u hu * (C.lamB z hz)⁻¹, mul_mem (C.lamB_mem_H u hu) (inv_mem (C.lamB_mem_H z hz))⟩, ?_⟩
  rw [C.Th_spec G' j hj hjm _ z u hz hu
      (by rw [C.lamT_eq z hz, C.lamT_eq u hu]; exact _root_.inv_mul_cancel_right _ _),
    e', _root_.mul_inv_cancel_right]

lemma phi_over (σ : C.H) : C.trj G' j hj σ ≫ G'.hom = JacChunk.ι C.H σ ≫ sG C.H :=
  (C.trj_over G' j hj σ).trans (ι_sG C.H σ).symm

include hjm in
lemma phi_comp (σ τ : C.H) (x y : X) (hx : IsClosed {x}) (hy : IsClosed {y}) (e : JacChunk.ι C.H σ x = JacChunk.ι C.H τ y) :
    C.trj G' j hj σ x = C.trj G' j hj τ y := by
  have e2 : σ * (⟨C.lamB x hx, C.lamB_mem_H x hx⟩ : C.H) = τ * ⟨C.lamB y hy, C.lamB_mem_H y hy⟩ :=
    Subtype.ext ((C.ι_eq_iff_mul σ τ x hx y hy).1 e)
  rw [C.trj_apply G' j hj hjm σ x hx, C.trj_apply G' j hj hjm τ y hy, e2]

/-- The comparison morphism `G ⟶ G'`. -/
noncomputable def phi : G C.H ⟶ G'.left :=
  glueY (sG C.H) G'.hom (fun _ : C.H => X) (JacChunk.ι C.H) (C.trj G' j hj) (fun g _ => exists_chart C.H g)
    (C.phi_over G' j hj) (C.phi_comp G' j hj hjm)

lemma phi_fac (σ : C.H) : JacChunk.ι C.H σ ≫ C.phi G' j hj hjm = C.trj G' j hj σ :=
  glueY_fac (sG C.H) G'.hom (fun _ : C.H => X) (JacChunk.ι C.H) (C.trj G' j hj) (fun g _ => exists_chart C.H g)
    (C.phi_over G' j hj) (C.phi_comp G' j hj hjm) σ

lemma phi_over_k : C.phi G' j hj hjm ≫ G'.hom = sG C.H :=
  glueY_over (sG C.H) G'.hom (fun _ : C.H => X) (JacChunk.ι C.H) (C.trj G' j hj) (fun g _ => exists_chart C.H g)
    (C.phi_over G' j hj) (C.phi_comp G' j hj hjm)

lemma ι_phi : JacChunk.ι C.H 1 ≫ C.phi G' j hj hjm = j := (C.phi_fac G' j hj hjm 1).trans (C.trj_one G' j hj hjm)

include hjm in
lemma psi_cov (g : G'.left) (hg : IsClosed {g}) : ∃ σ : C.H, ∃ x : X, C.trj G' j hj σ x = g := by
  obtain ⟨x, hx⟩ := exists_closedPoint (X := X) k
  obtain ⟨σ, hσ⟩ := C.Th_surj G' j hj hjm (GrpPt.kp G' g hg * (JT G' j hj x)⁻¹)
  refine ⟨σ, x, ?_⟩
  change (GrpPt.tr G' (C.Th G' j hj σ)).left (j x) = g
  rw [hσ, ← ev_JT G' j hj x hx, GrpPt.tr_ev, _root_.inv_mul_cancel_right, GrpPt.ev_kp]

lemma psi_over (σ : C.H) : JacChunk.ι C.H σ ≫ sG C.H = C.trj G' j hj σ ≫ G'.hom :=
  (ι_sG C.H σ).trans (C.trj_over G' j hj σ).symm

include hjm in
lemma psi_comp (σ τ : C.H) (x y : X) (hx : IsClosed {x}) (hy : IsClosed {y})
    (e : C.trj G' j hj σ x = C.trj G' j hj τ y) : JacChunk.ι C.H σ x = JacChunk.ι C.H τ y :=
  (C.ι_eq_iff_mul σ τ x hx y hy).2 (congrArg Subtype.val (C.Th_inj G' j hj hjm _ _
    (GrpPt.ev_inj G' ((C.trj_apply G' j hj hjm σ x hx).symm.trans (e.trans (C.trj_apply G' j hj hjm τ y hy))))))

/-- The inverse comparison morphism `G' ⟶ G`. -/
noncomputable def psi : G'.left ⟶ G C.H :=
  haveI := C.isSeparated_sG
  glueY G'.hom (sG C.H) (fun _ : C.H => X) (C.trj G' j hj) (JacChunk.ι C.H) (C.psi_cov G' j hj hjm)
    (C.psi_over G' j hj) (C.psi_comp G' j hj hjm)

lemma psi_fac (σ : C.H) : C.trj G' j hj σ ≫ C.psi G' j hj hjm = JacChunk.ι C.H σ :=
  haveI := C.isSeparated_sG
  glueY_fac G'.hom (sG C.H) (fun _ : C.H => X) (C.trj G' j hj) (JacChunk.ι C.H) (C.psi_cov G' j hj hjm)
    (C.psi_over G' j hj) (C.psi_comp G' j hj hjm) σ

lemma psi_over_k : C.psi G' j hj hjm ≫ sG C.H = G'.hom :=
  haveI := C.isSeparated_sG
  glueY_over G'.hom (sG C.H) (fun _ : C.H => X) (C.trj G' j hj) (JacChunk.ι C.H) (C.psi_cov G' j hj hjm)
    (C.psi_over G' j hj) (C.psi_comp G' j hj hjm)

lemma phi_psi : C.phi G' j hj hjm ≫ C.psi G' j hj hjm = 𝟙 _ := by
  refine C.eq_id_of_ι1 _ (by rw [Category.assoc, C.psi_over_k G' j hj hjm, C.phi_over_k G' j hj hjm]) ?_
  rw [← Category.assoc, C.phi_fac G' j hj hjm 1]
  exact C.psi_fac G' j hj hjm 1

lemma psi_phi : C.psi G' j hj hjm ≫ C.phi G' j hj hjm = 𝟙 _ := by
  refine Y_ext G'.hom G'.hom _ _ (by rw [Category.assoc, C.phi_over_k G' j hj hjm, C.psi_over_k G' j hj hjm]) (Category.id_comp _)
    fun g hg => ?_
  obtain ⟨σ, x, rfl⟩ := C.psi_cov G' j hj hjm g hg
  exact (congrArg (C.phi G' j hj hjm) (congrArg (fun φ => φ x) (C.psi_fac G' j hj hjm σ))).trans
    (congrArg (fun φ => φ x) (C.phi_fac G' j hj hjm σ))

include hjm in
/-- **Uniqueness up to unique isomorphism.** A separated, reduced, irreducible group scheme `G'` over `k` (lft) with an
open immersion `j : X ⟶ G'` over `k` compatible with the chunk law is isomorphic to `G` by a unique isomorphism over `k`
restricting to `j` on the dense open `X`. -/
theorem existsUnique_iso : ∃! e : G C.H ≅ G'.left, e.hom ≫ G'.hom = sG C.H ∧ JacChunk.ι C.H 1 ≫ e.hom = j :=
  ⟨⟨C.phi G' j hj hjm, C.psi G' j hj hjm, C.phi_psi G' j hj hjm, C.psi_phi G' j hj hjm⟩,
    ⟨C.phi_over_k G' j hj hjm, C.ι_phi G' j hj hjm⟩,
    fun e he => C.iso_ext_ι1 G'.hom e _ he.1 (C.phi_over_k G' j hj hjm) (he.2.trans (C.ι_phi G' j hj hjm).symm)⟩

end StrictChunk

end RamanujanPetersson.JacChunk

end

-- ===== S4.Def_RP_JacChunkB =====
section

/-!
# Group chunk theorem B (unit S4-JacChunkB), umbrella

For a strict group chunk `C` on a geometrically reduced, integral, separated, lft `k`-scheme `X` (`k` algebraically
closed), the glued scheme `G C.H` of part A is a group variety containing `X` as a dense open:
* `Ext`, `Act`, `R`, `Mul`, `Inv`: pointwise gluing into `G`, the action `G ×_k X ⟶ G`, right translations,
  multiplication `μ`, inverse and unit;
* `Grp`: `GrpObj (Over.mk (sG C.H))`; `Smooth`: `G` smooth, translations transitive on `G(k)`, `ι 1` dense, `mu_ι1`;
* `Sep`: `G` separated (diagonal = base change of the unit section);
* `Uniq`: maps out of `G` are determined on `X`; `GPt`: `k`-points and translations of another group scheme;
* `Theta`: the comparison `Θ : H → G'(k)`; `Iso`: `existsUnique_iso` (unique up to unique isomorphism).
-/

end


