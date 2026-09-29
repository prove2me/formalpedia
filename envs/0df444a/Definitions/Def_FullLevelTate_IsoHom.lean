-- Prove2me | Definitions.Def_FullLevelTate_IsoHom
-- name    : FullLevelTate_IsoHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/6e1b101a-4271-5b1b-889d-12e5519021c7
-- title:
--   Isotypic Hom-spaces of a full-level-q Tate datum
-- statement:
--   Throughout, $D$ is a [`FullLevelTate.Datum`](../def/FullLevelTate_Datum.html#L11) for a prime $q$, a level $M'$ and a local coefficient ring $O'$: a finite free $O'$-module $V$ carrying a Galois action `gal` of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ (adically continuous), an action `gl2` of $\mathrm{GL}_2(\mathbb{Z}/q)$ and a ring action `hecke` of the polynomial Hecke ring $\mathbb{Z}[T_\ell]$, the three pairwise commuting, subject to the unramifiedness and Eichler–Shimura clauses of that structure. Further data: a field $K$ that is an $O'$-algebra, a subgroup $H \le \mathrm{GL}_2(\mathbb{Z}/q)$ and a representation $\chi$ of $H$ on a $K$-vector space $W$.
--
--   `isoHom` is the $K$-subspace of $\mathrm{Hom}_K(W, K \otimes_{O'} V)$ consisting of the $H$-equivariant maps, i.e. those $f$ with $f \circ \chi(h) = (\mathrm{gl2}(h) \otimes K) \circ f$ for all $h \in H$; `mem_isoHom_iff` records this criterion. Post-composition with the base change of $\mathrm{gal}(\sigma)$ preserves this subspace and yields a monoid homomorphism `isoHomGal` from $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_K(\mathrm{isoHom})$; post-composition with the base change of $\mathrm{hecke}(t)$ yields a ring homomorphism `isoHomHecke` from the Hecke ring to the same endomorphism ring, and `isoHomGal_comm_isoHomHecke` states that the two commute. For a ring homomorphism $\varphi$ from the Hecke ring to $K$, `eigenIsoHom` is the subspace of $f$ with $\mathrm{isoHomHecke}(t)f = \varphi(t)\,f$ for all $t$, and `eigenIsoHomGal` is the restricted Galois action on it; formulas for the underlying maps accompany each.
--
--   Independently, `borel q` is the subgroup of $\mathrm{GL}_2(\mathbb{Z}/q)$ of matrices with vanishing $(1,0)$ entry; for monoid homomorphisms $\mu_1, \mu_2 : (\mathbb{Z}/q)^\times \to K^\times$ over a commutative ring $K$, `borelChar` sends $g$ to $\mu_1(g_{00})\mu_2(g_{11})$ (the diagonal entries being units, as the determinant is), with evaluation formula `borelChar_apply`; over a field, `borelRep` is the associated one-dimensional representation of `borel q` on $K$ by multiplication through this character. Two examples instantiate the eigen-space Galois action on a zero datum and `borelRep` for $q = 2$.
--
--   **Relation to Mathlib.** Built on Mathlib's `Representation`, base change of linear maps along $O' \to K$, and `Matrix.GeneralLinearGroup`; the `Datum`, its $\chi$-isotypic and Hecke-eigen Hom-spaces, the upper-triangular subgroup of $\mathrm{GL}_2(\mathbb{Z}/q)$ and its diagonal characters are the project's own notions.
--
--   **Where it is used.** These spaces isolate, inside the base-changed full-level-$q$ Tate module of the datum, the part of a prescribed type at $q$ on which Galois acts compatibly with a Hecke eigensystem $\varphi$. The two intended types are a representation of the whole group $\mathrm{GL}_2(\mathbb{Z}/q)$ (cuspidal case) and a character of the upper-triangular subgroup built from $\mu_1, \mu_2$ (principal series), as used in the comparison of Galois representations at level $q$ in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FullLevelTate_IsoHom.lean

import Definitions.Def_FullLevelTate_Datum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FullLevelTate

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} {O' : Type} [CommRing O'] [IsLocalRing O']

namespace Datum

variable (D : Datum q M' O') (K : Type) [Field K] [Algebra O' K]
  {H : Subgroup (CuspidalType.GL2 q)} {W : Type} [AddCommGroup W] [Module K W]
  (χ : Representation K H W)

def isoHom : Submodule K (W →ₗ[K] K ⊗[O'] D.V) where
  carrier := {f | ∀ h : H, f ∘ₗ χ h = ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ f}
  add_mem' {f g} hf hg h := by rw [LinearMap.add_comp, LinearMap.comp_add, hf h, hg h]
  zero_mem' h := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  smul_mem' c f hf h := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hf h]

theorem mem_isoHom_iff (f : W →ₗ[K] K ⊗[O'] D.V) :
    f ∈ D.isoHom K χ ↔ ∀ h : H, f ∘ₗ χ h = ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ f :=
  Iff.rfl

def isoHomGal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K (D.isoHom K χ) where
  toFun σ :=
    { toFun := fun f => ⟨((D.gal σ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V), fun h => by
        have hc : ((D.gal σ).baseChange K) ∘ₗ ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) =
            ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ ((D.gal σ).baseChange K) := by
          rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp,
            ← Module.End.mul_eq_comp, D.gal_comm_gl2]
        rw [LinearMap.comp_assoc, f.2 h, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.comp_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (by
    change ((D.gal 1).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = f
    rw [map_one, LinearMap.baseChange_one, Module.End.one_eq_id, LinearMap.id_comp])
  map_mul' σ τ := LinearMap.ext fun f => Subtype.ext (by
    change ((D.gal (σ * τ)).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.gal σ).baseChange K) ∘ₗ (((D.gal τ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V))
    rw [map_mul, LinearMap.baseChange_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc])

theorem coe_isoHomGal_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : D.isoHom K χ) :
    ((D.isoHomGal K χ σ f : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.gal σ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) :=
  rfl

def isoHomHecke : ModularCurve.HeckeAlg →+* Module.End K (D.isoHom K χ) where
  toFun t :=
    { toFun := fun f => ⟨((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V), fun h => by
        have hc : ((D.hecke t).baseChange K) ∘ₗ ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) =
            ((D.gl2 (h : CuspidalType.GL2 q)).baseChange K) ∘ₗ ((D.hecke t).baseChange K) := by
          rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp,
            ← Module.End.mul_eq_comp, D.hecke_comm_gl2]
        rw [LinearMap.comp_assoc, f.2 h, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]⟩
      map_add' := fun f g => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c f => Subtype.ext (LinearMap.comp_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke 1).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = f
    rw [map_one, LinearMap.baseChange_one, Module.End.one_eq_id, LinearMap.id_comp])
  map_mul' s t := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke (s * t)).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.hecke s).baseChange K) ∘ₗ (((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V))
    rw [map_mul, LinearMap.baseChange_mul, Module.End.mul_eq_comp, LinearMap.comp_assoc])
  map_zero' := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke 0).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = 0
    rw [map_zero, LinearMap.baseChange_zero, LinearMap.zero_comp])
  map_add' s t := LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke (s + t)).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.hecke s).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) +
        ((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V)
    rw [map_add, LinearMap.baseChange_add, LinearMap.add_comp])

theorem coe_isoHomHecke_apply (t : ModularCurve.HeckeAlg) (f : D.isoHom K χ) :
    ((D.isoHomHecke K χ t f : D.isoHom K χ) : W →ₗ[K] K ⊗[O'] D.V) =
      ((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) :=
  rfl

theorem isoHomGal_comm_isoHomHecke (t : ModularCurve.HeckeAlg)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    D.isoHomHecke K χ t * D.isoHomGal K χ σ = D.isoHomGal K χ σ * D.isoHomHecke K χ t :=
  LinearMap.ext fun f => Subtype.ext (by
    change ((D.hecke t).baseChange K) ∘ₗ (((D.gal σ).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V)) =
      ((D.gal σ).baseChange K) ∘ₗ (((D.hecke t).baseChange K) ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V))
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, D.hecke_comm_gal])

def eigenIsoHom (φ : ModularCurve.HeckeAlg →+* K) : Submodule K (D.isoHom K χ) where
  carrier := {f | ∀ t : ModularCurve.HeckeAlg, D.isoHomHecke K χ t f = φ t • f}
  add_mem' {f g} hf hg t := by rw [map_add, hf t, hg t, smul_add]
  zero_mem' t := by rw [map_zero, smul_zero]
  smul_mem' c f hf t := by rw [map_smul, hf t, smul_comm]

theorem mem_eigenIsoHom_iff (φ : ModularCurve.HeckeAlg →+* K) (f : D.isoHom K χ) :
    f ∈ D.eigenIsoHom K χ φ ↔ ∀ t : ModularCurve.HeckeAlg, D.isoHomHecke K χ t f = φ t • f :=
  Iff.rfl

def eigenIsoHomGal (φ : ModularCurve.HeckeAlg →+* K) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End K (D.eigenIsoHom K χ φ) where
  toFun σ :=
    { toFun := fun f => ⟨D.isoHomGal K χ σ (f : D.isoHom K χ), fun t => by
        have hc := congrArg (fun T => T (f : D.isoHom K χ)) (D.isoHomGal_comm_isoHomHecke K χ t σ)
        simp only [Module.End.mul_apply] at hc
        rw [hc, f.2 t, map_smul]⟩
      map_add' := fun f g => Subtype.ext (map_add _ _ _)
      map_smul' := fun c f => Subtype.ext (map_smul _ _ _) }
  map_one' := LinearMap.ext fun f => Subtype.ext (by
    change D.isoHomGal K χ 1 (f : D.isoHom K χ) = f
    rw [map_one, Module.End.one_apply])
  map_mul' σ τ := LinearMap.ext fun f => Subtype.ext (by
    change D.isoHomGal K χ (σ * τ) (f : D.isoHom K χ) = D.isoHomGal K χ σ (D.isoHomGal K χ τ (f : D.isoHom K χ))
    rw [map_mul, Module.End.mul_apply])

theorem coe_eigenIsoHomGal_apply (φ : ModularCurve.HeckeAlg →+* K)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : D.eigenIsoHom K χ φ) :
    ((D.eigenIsoHomGal K χ φ σ f : D.eigenIsoHom K χ φ) : D.isoHom K χ) = D.isoHomGal K χ σ f :=
  rfl

end Datum

def borel (q : ℕ) [Fact q.Prime] : Subgroup (CuspidalType.GL2 q) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0}
  mul_mem' {x y} hx hy := by
    have hx' : (x : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := hx
    have hy' : (y : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := hy
    show ((x * y : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx', hy']
    ring
  one_mem' := by
    show ((1 : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_one]
    exact Matrix.one_apply_ne (by decide)
  inv_mem' {x} hx := by
    have hx' : (x : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := hx
    show ((x⁻¹ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0
    rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def]
    simp [Matrix.adjugate_fin_two, hx']

theorem mem_borel_iff {q : ℕ} [Fact q.Prime] (g : CuspidalType.GL2 q) :
    g ∈ borel q ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 :=
  Iff.rfl

def borelChar {q : ℕ} [Fact q.Prime] {K : Type} [CommRing K] (μ₁ μ₂ : (ZMod q)ˣ →* Kˣ) :
    borel q →* Kˣ where
  toFun g :=
    have hg : ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 *
        ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 ≠ 0 := by
      have hdet : ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
      rwa [Matrix.det_fin_two, (mem_borel_iff _).1 g.2, mul_zero, sub_zero] at hdet
    μ₁ (Units.mk0 _ (mul_ne_zero_iff.mp hg).1) * μ₂ (Units.mk0 _ (mul_ne_zero_iff.mp hg).2)
  map_one' := by
    have h1 : ∀ h, Units.mk0 ((((1 : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h = 1 :=
      fun h => Units.ext (by simp)
    have h2 : ∀ h, Units.mk0 ((((1 : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) h = 1 :=
      fun h => Units.ext (by simp)
    show μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _) = 1
    rw [h1, h2, map_one, map_one, one_mul]
  map_mul' x y := by
    have hx : ((x : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := (mem_borel_iff _).1 x.2
    have hy : ((y : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := (mem_borel_iff _).1 y.2
    have hdx : ((x : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    have hdy : ((y : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_fin_two, hx, mul_zero, sub_zero] at hdx
    rw [Matrix.det_fin_two, hy, mul_zero, sub_zero] at hdy
    have e0 : ∀ h, Units.mk0 ((((x * y : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h =
        Units.mk0 _ (mul_ne_zero_iff.mp hdx).1 * Units.mk0 _ (mul_ne_zero_iff.mp hdy).1 :=
      fun h => Units.ext (by
        rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, Subgroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hy, mul_zero, add_zero])
    have e1 : ∀ h, Units.mk0 ((((x * y : borel q) : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) h =
        Units.mk0 _ (mul_ne_zero_iff.mp hdx).2 * Units.mk0 _ (mul_ne_zero_iff.mp hdy).2 :=
      fun h => Units.ext (by
        rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, Subgroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx, zero_mul, zero_add])
    show μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _) =
      (μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _)) * (μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _))
    rw [e0, e1, map_mul, map_mul, mul_mul_mul_comm]

theorem borelChar_apply {q : ℕ} [Fact q.Prime] {K : Type} [CommRing K] (μ₁ μ₂ : (ZMod q)ˣ →* Kˣ)
    (g : borel q) (a d : (ZMod q)ˣ)
    (ha : (a : ZMod q) = ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0)
    (hd : (d : ZMod q) = ((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) :
    borelChar μ₁ μ₂ g = μ₁ a * μ₂ d := by
  have ea : ∀ h, Units.mk0 (((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h = a :=
    fun h => Units.ext (by rw [Units.val_mk0, ha])
  have ed : ∀ h, Units.mk0 (((g : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1) h = d :=
    fun h => Units.ext (by rw [Units.val_mk0, hd])
  show μ₁ (Units.mk0 _ _) * μ₂ (Units.mk0 _ _) = _
  rw [ea, ed]

def borelRep {q : ℕ} [Fact q.Prime] {K : Type} [Field K] (μ₁ μ₂ : (ZMod q)ˣ →* Kˣ) :
    Representation K (borel q) K :=
  (Algebra.lmul K K).toRingHom.toMonoidHom.comp ((Units.coeHom K).comp (borelChar μ₁ μ₂))

example (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' K : Type) [CommRing O'] [IsLocalRing O'] [Field K] [Algebra O' K]
    (φ : ModularCurve.HeckeAlg →+* K) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End K (Datum.eigenIsoHom
        ({ V := Fin 0 → O'
           gal := 1
           gal_isAdicContinuous := fun n =>
             ⟨⊥, inferInstance, fun σ _ v => by
               rw [MonoidHom.one_apply, Module.End.one_apply, sub_self]; exact zero_mem _⟩
           gl2 := 1
           hecke := (algebraMap O' (Module.End O' (Fin 0 → O'))).comp
             (MvPolynomial.eval₂Hom (Int.castRingHom O') 0)
           gal_comm_gl2 := fun σ x => by rw [MonoidHom.one_apply, MonoidHom.one_apply]
           hecke_comm_gal := fun t σ => by rw [MonoidHom.one_apply, mul_one, one_mul]
           hecke_comm_gl2 := fun t x => by rw [MonoidHom.one_apply, mul_one, one_mul]
           unramified := fun _ _ _ _ _ _ _ _ _ => MonoidHom.one_apply _
           eichlerShimura := fun _ _ _ _ _ _ _ _ _ => LinearMap.ext fun v => Subsingleton.elim _ _ } : Datum q M' O')
        K (Representation.trivial K (⊤ : Subgroup (CuspidalType.GL2 q)) K) φ) :=
  Datum.eigenIsoHomGal _ K _ φ

example {K : Type} [Field K] : Representation K (borel 2) K :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  borelRep (1 : (ZMod 2)ˣ →* Kˣ) 1

end FullLevelTate

end


