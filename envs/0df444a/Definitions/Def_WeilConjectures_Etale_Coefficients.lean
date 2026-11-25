-- Prove2me | Definitions.Def_WeilConjectures_Etale_Coefficients
-- name    : WeilConjectures_Etale_Coefficients
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T12:05:57.381996+00:00
-- url     : https://prove2.me/theorems/c72e1090-755c-4154-834c-1a50fd2001f5
-- title:
--   $\ell$-adic cohomology $H^i(X,\mathbb Z_\ell)=\varprojlim_\nu H^i(X,\mathbb Z/\ell^{\nu+1})$ and $H^i(X,\mathbb Q_\ell)$
-- statement:
--   Fix a prime $\ell$ and a scheme $X$.
--
--   * $H^i_{\mathrm{fin}}(X,\nu)=H^i(X_{\mathrm{et}},\mathbb Z/\ell^{\nu+1})$, with the transition maps $H^i(X,\mathbb Z/\ell^{\nu+2})\to H^i(X,\mathbb Z/\ell^{\nu+1})$ induced by reduction. These groups are killed by $\ell^{\nu+1}$, hence are $\mathbb Z/\ell^{\nu+1}$-modules and $\mathbb Z_\ell$-modules.
--   * $H^i(X,\mathbb Z_\ell)$ is the $\mathbb Z_\ell$-module of compatible families $(x_\nu)_\nu$, i.e. the inverse limit $\varprojlim_\nu H^i(X_{\mathrm{et}},\mathbb Z/\ell^{\nu+1})$.
--   * $H^i(X,\mathbb Q_\ell)=\mathbb Q_\ell\otimes_{\mathbb Z_\ell}H^i(X,\mathbb Z_\ell)$.
--   * A morphism $g\colon Y\to X$ induces pullbacks $g^*$ at each finite level, compatible with the transition maps, hence $\mathbb Z_\ell$-linear and $\mathbb Q_\ell$-linear maps $g^*$ on $H^i(-,\mathbb Z_\ell)$ and $H^i(-,\mathbb Q_\ell)$.
-- source:
--   P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), §1 (definition of $H^i(\bar X,\mathbb Q_\ell)$); E. Freitag, R. Kiehl, Étale Cohomology and the Weil Conjecture, Chapter I (ℓ-adic sheaves).

import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_ConstantPullback
import Definitions.Def_FiniteFields_Etale_ExactPullback
import Definitions.Def_FiniteFields_Etale_FiniteCoefficients
import Definitions.Def_FiniteFields_Etale_Functoriality
import Definitions.Def_FiniteFields_Etale_Sites
import Definitions.Def_WeilConjectures_Etale_Pullback

noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian AlgebraicGeometry FiniteFields.Etale

namespace WeilConjectures.Etale

universe u

set_option backward.isDefEq.respectTransparency.types false

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Le groupe `ℤ/ℓ^{ν+1}`, dans `Ab.{u+1}`. -/
abbrev Lam (ν : ℕ) : Ab.{u + 1} :=
  AddCommGrpCat.uliftFunctor.{u + 1, 0}.obj (finiteEllAdicCoefficientGroup ℓ ν)

/-- La réduction `ℤ/ℓ^{ν+2} → ℤ/ℓ^{ν+1}`. -/
abbrev redLam (ν : ℕ) : Lam.{u} ℓ (ν + 1) ⟶ Lam.{u} ℓ ν :=
  AddCommGrpCat.uliftFunctor.{u + 1, 0}.map (finiteEllAdicReduction ℓ (Nat.le_succ ν))

/-- `Hⁱ(X_ét, ℤ/ℓ^{ν+1})`. -/
def Hfin (X : Scheme.{u}) (ν i : ℕ) : Type (u + 1) :=
  SmallEtaleCohomology X (const X (Lam.{u} ℓ ν)) i

instance (X : Scheme.{u}) (ν i : ℕ) : AddCommGroup (Hfin ℓ X ν i) :=
  inferInstanceAs (AddCommGroup (SmallEtaleCohomology X _ i))

/-- La transition `Hⁱ(ℤ/ℓ^{ν+2}) → Hⁱ(ℤ/ℓ^{ν+1})`. -/
def redH (X : Scheme.{u}) (ν i : ℕ) : Hfin ℓ X (ν + 1) i →+ Hfin ℓ X ν i :=
  Sheaf.H.map ((constantSheaf (smallEtaleSiteTopology X) Ab.{u + 1}).map (redLam ℓ ν)) i

/-- `g^*` au niveau `ν`. -/
def pullbackFin {X Y : Scheme.{u}} (g : Y ⟶ X) (ν i : ℕ) : Hfin ℓ X ν i →+ Hfin ℓ Y ν i :=
  pullbackH g (Lam.{u} ℓ ν) i

theorem pullbackFin_redH {X Y : Scheme.{u}} (g : Y ⟶ X) (ν i : ℕ) (x : Hfin ℓ X (ν + 1) i) :
    pullbackFin ℓ g ν i (redH ℓ X ν i x) = redH ℓ Y ν i (pullbackFin ℓ g (ν + 1) i x) :=
  pullbackH_naturality g (redLam ℓ ν) i x


/-- Le faisceau constant est additif (adjoint à gauche). -/
instance constantSheaf_additive (X : Scheme.{u}) :
    (constantSheaf (smallEtaleSiteTopology X) Ab.{u + 1}).Additive :=
  rightExactFunctor_le_additiveFunctor _ _ _ (by
    simp only [rightExactFunctor_iff]
    infer_instance)

/-- `n • 𝟙_{A_X}` induit `n •` sur la cohomologie. -/
theorem nsmul_eq_H_map {X : Scheme.{u}} {A : Ab.{u + 1}} (i n : ℕ)
    (x : SmallEtaleCohomology X (const X A) i) :
    n • x = Sheaf.H.map ((constantSheaf (smallEtaleSiteTopology X) Ab.{u + 1}).map (n • 𝟙 A)) i x := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  let φ : (const X A ⟶ const X A) →+ SmallEtaleCohomology X (const X A) i :=
    { toFun := fun f ↦ Sheaf.H.map f i x
      map_zero' := by simp [Sheaf.H.map_apply, Ext.mk₀_zero]
      map_add' := fun f g ↦ by simp [Sheaf.H.map_apply, Ext.mk₀_add, Ext.comp_add] }
  have := map_nsmul φ n (𝟙 _)
  simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sheaf.H.map_id_apply] at this
  exact this.symm

theorem torsion (X : Scheme.{u}) (ν i : ℕ) (x : Hfin ℓ X ν i) : (ℓ ^ (ν + 1)) • x = 0 := by
  have h0 : (ℓ ^ (ν + 1)) • 𝟙 (Lam.{u} ℓ ν) = 0 := by
    ext ⟨a⟩
    simp only [AddCommGrpCat.hom_nsmul, AddCommGrpCat.hom_id, AddMonoidHom.nsmul_apply,
      AddMonoidHom.id_apply, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
    apply ULift.ext
    change (ℓ ^ (ν + 1)) • (a : ZMod (ℓ ^ (ν + 1))) = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  calc (ℓ ^ (ν + 1)) • x
      = Sheaf.H.map ((constantSheaf (smallEtaleSiteTopology X) Ab.{u + 1}).map
          ((ℓ ^ (ν + 1)) • 𝟙 (Lam.{u} ℓ ν))) i x := nsmul_eq_H_map i _ x
    _ = 0 := by
      rw [h0, Functor.map_zero]
      simp [Sheaf.H.map_apply, Ext.mk₀_zero]

instance (X : Scheme.{u}) (ν i : ℕ) : Module (ZMod (ℓ ^ (ν + 1))) (Hfin ℓ X ν i) :=
  AddCommGroup.zmodModule (torsion ℓ X ν i)

/-- Une application additive entre groupes de torsion compatibles est `ZMod`-linéaire, à la
réduction près. -/
theorem map_zmod_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N] {a b : ℕ}
    [NeZero a] [Module (ZMod a) M] [Module (ZMod b) N] (h : b ∣ a) (f : M →+ N) (c : ZMod a) (y : M) :
    f (c • y) = (ZMod.castHom h (ZMod b) c) • f y := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ZMod a) = c := ⟨c.val, ZMod.natCast_zmod_val c⟩
  rw [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]


instance (k : ℕ) : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

instance (X : Scheme.{u}) (ν i : ℕ) : Module ℤ_[ℓ] (Hfin ℓ X ν i) :=
  Module.compHom _ (PadicInt.toZModPow (ν + 1))

theorem padic_smul_def (X : Scheme.{u}) (ν i : ℕ) (a : ℤ_[ℓ]) (y : Hfin ℓ X ν i) :
    a • y = (PadicInt.toZModPow (ν + 1) a) • y := rfl

theorem redH_padic_smul (X : Scheme.{u}) (ν i : ℕ) (a : ℤ_[ℓ]) (y : Hfin ℓ X (ν + 1) i) :
    redH ℓ X ν i (a • y) = a • redH ℓ X ν i y := by
  rw [padic_smul_def, padic_smul_def,
    map_zmod_smul (pow_dvd_pow ℓ (Nat.succ_le_succ (Nat.le_succ ν))) (redH ℓ X ν i)]
  congr 1
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow (ν + 1) (ν + 1 + 1) (by omega)) a

theorem pullbackFin_padic_smul {X Y : Scheme.{u}} (g : Y ⟶ X) (ν i : ℕ) (a : ℤ_[ℓ])
    (y : Hfin ℓ X ν i) : pullbackFin ℓ g ν i (a • y) = a • pullbackFin ℓ g ν i y := by
  rw [padic_smul_def, padic_smul_def, map_zmod_smul (dvd_refl _) (pullbackFin ℓ g ν i)]
  simp


/-- Les familles compatibles `(x_ν)` avec `red x_{ν+1} = x_ν`. -/
def compatible (X : Scheme.{u}) (i : ℕ) : Submodule ℤ_[ℓ] (∀ ν, Hfin ℓ X ν i) where
  carrier := {x | ∀ ν, redH ℓ X ν i (x (ν + 1)) = x ν}
  add_mem' {x y} hx hy ν := by simp [map_add, hx ν, hy ν]
  zero_mem' ν := by simp
  smul_mem' a x hx ν := by simp [redH_padic_smul, hx ν]

/-- **D5.** `Hⁱ(X_ét, ℤ_ℓ) = lim_ν Hⁱ(X_ét, ℤ/ℓ^{ν+1})`. -/
abbrev Hint (X : Scheme.{u}) (i : ℕ) : Type (u + 1) := compatible ℓ X i

/-- `g^*` sur `Hⁱ(−, ℤ_ℓ)`. -/
def pullbackInt {X Y : Scheme.{u}} (g : Y ⟶ X) (i : ℕ) : Hint ℓ X i →ₗ[ℤ_[ℓ]] Hint ℓ Y i where
  toFun x := ⟨fun ν ↦ pullbackFin ℓ g ν i (x.1 ν), fun ν ↦ by
    rw [← pullbackFin_redH, x.2 ν]⟩
  map_add' x y := by ext ν; simp
  map_smul' a x := by ext ν; simp [pullbackFin_padic_smul]


/-- **D6.** `Hⁱ(X_ét, ℚ_ℓ) = ℚ_ℓ ⊗_{ℤ_ℓ} Hⁱ(X_ét, ℤ_ℓ)`. -/
abbrev Hrat (X : Scheme.{u}) (i : ℕ) : Type (u + 1) := TensorProduct ℤ_[ℓ] ℚ_[ℓ] (Hint ℓ X i)

/-- `g^*` sur `Hⁱ(−, ℚ_ℓ)`. -/
def pullbackRat {X Y : Scheme.{u}} (g : Y ⟶ X) (i : ℕ) : Hrat ℓ X i →ₗ[ℚ_[ℓ]] Hrat ℓ Y i :=
  (pullbackInt ℓ g i).baseChange ℚ_[ℓ]

end WeilConjectures.Etale


