-- Prove2me | Definitions.Def_ModularCurve_FullLevelJacobian
-- name    : ModularCurve_FullLevelJacobian
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/20cd7574-5c1a-5387-9771-7e822c6f355d
-- title:
--   Full-level-q modular Jacobian with Galois, Hecke and GL2​(Fq​) operators
-- statement:
--   Throughout, $q$ is a prime and $M'$ a natural number. The level group `levelH q M'` is the kernel of the reduction map $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, i.e. the units congruent to $1$ mod $q$; `fieldBar` is the corresponding base-changed function field `xHFunctionFieldBar (q^2*M') (levelH q M')` inside the Laurent series over $\overline{\mathbb Q}$, and `jacComp` is the associated divisor class group `JH (q^2*M') (levelH q M')`. The index type `Idx q` is the set of primitive $q$-th roots of unity in $\overline{\mathbb Q}$; it is finite, carries the action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ by evaluation, and `Idx.pow d` raises $\zeta$ to the exponent given by the representative of $d \in (\mathbb Z/q)^\times$ in $\{0,\dots,q-1\}$. The carrier `Jac q M'` is the type of functions $\mathrm{Idx}(q) \to$ `jacComp`, with pointwise addition, components read off by `Jac.eval`; `Jac.mapIdx T s` is the endomorphism $x \mapsto (\zeta \mapsto T_\zeta(x(s\zeta)))$ for a family of additive endomorphisms $T$ and a self-map $s$ of the index set.
--
--   On this carrier: `galJac` sends $\sigma$ to $x \mapsto (\zeta \mapsto \sigma\cdot x(\sigma^{-1}\zeta))$, combining the semilinear Galois action on each component with the permutation of components. `conjElem γ` is the real matrix $\begin{pmatrix} a & b/q \\ qc & d\end{pmatrix}$ attached to $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in \mathrm{SL}_2(\mathbb Z)$, i.e. the conjugate of $\gamma$ by $\mathrm{diag}(1,q)$, of determinant $1$. The predicate `IsLevelAutBar q M' ζ γ τ` says of a $\overline{\mathbb Q}$-algebra automorphism $\tau$ of `fieldBar`: for every weight $k$, all modular forms $f,g$ for $\Gamma_H(q^2M')$ with integral $q$-expansions $p_f,p_g$ and $p_g \neq 0$ as a rational series, and every ring embedding $\iota : \overline{\mathbb Q}\to\mathbb C$ with $\iota(\zeta)=e^{2\pi i/q}$, the $\iota$-image of $\tau$ applied to the class of $p_f/p_g$, multiplied by the $q$-expansion of $g|_k\,\mathrm{conjElem}(\gamma)$, equals the $q$-expansion of $f|_k\,\mathrm{conjElem}(\gamma)$. `levelAutBar ζ γ` is a choice of such $\tau$ when one exists and the identity otherwise; `levelOp ζ γ` transports it to an additive endomorphism of `jacComp` via the semilinear automorphism action, and equals the identity when no such $\tau$ exists. `LevelAutInputs` asserts existence of such $\tau$ for all $\zeta$ and all $\gamma \in \Gamma_0(M')$.
--
--   The $\mathrm{GL}_2(\mathbb Z/q)$-side: `redQ` is entrywise reduction $\mathrm{SL}_2(\mathbb Z)\to \mathrm{GL}_2(\mathbb Z/q)$, `diagOneElem d` is $\mathrm{diag}(1,d)$, `slJac γ` acts on the $\zeta$-component by `levelOp ζ γ⁻¹` without moving components, and `diagJac d` permutes components by $\zeta \mapsto \zeta^{d^{-1}}$. `GL2Laws` asserts the existence of a monoid homomorphism $\mathrm{GL}_2(\mathbb Z/q)\to \mathrm{End}(\mathrm{Jac})$ matching `slJac` on reductions of elements of $\Gamma_0(M')$ and `diagJac` on the elements $\mathrm{diag}(1,d)$; `gl2Jac` is such a homomorphism if one exists and trivial otherwise. For a prime $\ell \nmid qM'$, `heckeGenJac ℓ` applies on each component the inverse diamond operator at the class of $\ell$ in $(\mathbb Z/q^2M')^\times$ composed after `heckeOperatorHAlong … ℓ`, while shifting components by $\zeta\mapsto\zeta^{\ell^{-1}}$; it is $0$ when $\ell$ is not prime or divides $qM'$. Under `HeckeGenCommute` (pairwise commutation of these operators) `heckeJacAux` is the induced $\mathbb Z$-algebra map from `HeckeAlg` $=\mathbb Z[X_\ell : \ell \text{ prime}]$ into the commutative subalgebra they generate, and `heckeJac` is the resulting ring homomorphism to $\mathrm{End}(\mathrm{Jac})$; failing commutation, `heckeJac` sends each generator to $0$, acting by the constant term. Finally `tateEnd` is the ring homomorphism from $\mathrm{End}(\mathrm{Jac})$ to $\mathbb Z_\lambda$-linear endomorphisms of the $\lambda$-adic Tate module [`TateModule lam (Jac q M')`](../def/EllipticCurve_TateModule.html#L15), and `tateGal`, `tateHecke`, `tateGL2` are the compositions with `galJac`, `heckeJac`, `gl2Jac`, each acting termwise on the sequences presenting the Tate module.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient ingredients used here (primitive roots, `ZMod.unitsMap`, modular forms with the slash action, Laurent series, matrix groups); the modular function fields, their divisor class groups, the diamond and Hecke operators, the abstract Hecke ring `HeckeAlg` and the Tate module are the project's own notions.
--
--   **Where it is used.** The full level-$q$ Jacobian assembled here is the module on which the Galois group, the Hecke ring and $\mathrm{GL}_2(\mathbb F_q)$ act simultaneously, as needed for the analysis of the representation at $q$ in the level-lowering step; the imported notion of a representation cuspidal of a given type is what this action is tested against.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelJacobian.lean

import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve.FullLevel

section Level

variable (q M' : ℕ)

theorem dvd_sq_mul : q ∣ q ^ 2 * M' :=
  Dvd.dvd.mul_right (dvd_pow_self q two_ne_zero) M'

def levelH : Subgroup (ZMod (q ^ 2 * M'))ˣ :=
  (ZMod.unitsMap (dvd_sq_mul q M')).ker

theorem mem_levelH_iff (u : (ZMod (q ^ 2 * M'))ˣ) :
    u ∈ levelH q M' ↔ ZMod.unitsMap (dvd_sq_mul q M') u = 1 :=
  MonoidHom.mem_ker

abbrev fieldBar : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  xHFunctionFieldBar (q ^ 2 * M') (levelH q M')

abbrev jacComp : Type := JH (q ^ 2 * M') (levelH q M')

end Level

section Idx

variable (q : ℕ)

def Idx : Type := ↥(primitiveRoots q (AlgebraicClosure ℚ))

instance : Fintype (Idx q) := inferInstanceAs (Fintype ↥(primitiveRoots q (AlgebraicClosure ℚ)))

instance : DecidableEq (Idx q) := Classical.decEq _

variable {q}

def Idx.val (ζ : Idx q) : AlgebraicClosure ℚ := (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).1

theorem Idx.ext {ζ ζ' : Idx q} (h : ζ.val = ζ'.val) : ζ = ζ' :=
  Subtype.ext h

variable [Fact q.Prime]

theorem Idx.isPrimitiveRoot (ζ : Idx q) : IsPrimitiveRoot ζ.val q :=
  (mem_primitiveRoots (Fact.out : q.Prime).pos).1 (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).2

def Idx.mk (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z q) : Idx q :=
  ⟨z, (mem_primitiveRoots (Fact.out : q.Prime).pos).2 hz⟩

@[simp] theorem Idx.val_mk (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z q) : (Idx.mk z hz).val = z :=
  rfl

instance : MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Idx q) where
  smul σ ζ := Idx.mk (σ ζ.val) (ζ.isPrimitiveRoot.map_of_injective σ.injective)
  one_smul _ := Idx.ext rfl
  mul_smul _ _ _ := Idx.ext rfl

@[simp] theorem Idx.val_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : Idx q) :
    (σ • ζ).val = σ ζ.val :=
  rfl

def Idx.pow (d : (ZMod q)ˣ) (ζ : Idx q) : Idx q :=
  Idx.mk (ζ.val ^ (d : ZMod q).val) (ζ.isPrimitiveRoot.pow_of_coprime _ (ZMod.val_coe_unit_coprime d))

@[simp] theorem Idx.val_pow (d : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow d).val = ζ.val ^ (d : ZMod q).val :=
  rfl

end Idx

section Carrier

variable (q : ℕ) (M' : ℕ)

def Jac : Type := Idx q → jacComp q M'

instance : AddCommGroup (Jac q M') := inferInstanceAs (AddCommGroup (Idx q → jacComp q M'))

variable {q M'}

def Jac.eval (x : Jac q M') (ζ : Idx q) : jacComp q M' := (id x : Idx q → jacComp q M') ζ

def Jac.mk (f : Idx q → jacComp q M') : Jac q M' := (id f : Jac q M')

@[simp] theorem Jac.eval_mk (f : Idx q → jacComp q M') (ζ : Idx q) : (Jac.mk f).eval ζ = f ζ := rfl

theorem Jac.ext {x y : Jac q M'} (h : ∀ ζ, x.eval ζ = y.eval ζ) : x = y := funext h

@[simp] theorem Jac.eval_add (x y : Jac q M') (ζ : Idx q) : (x + y).eval ζ = x.eval ζ + y.eval ζ := rfl
@[simp] theorem Jac.eval_zero (ζ : Idx q) : (0 : Jac q M').eval ζ = 0 := rfl
@[simp] theorem Jac.eval_neg (x : Jac q M') (ζ : Idx q) : (-x).eval ζ = -x.eval ζ := rfl
@[simp] theorem Jac.eval_sub (x y : Jac q M') (ζ : Idx q) : (x - y).eval ζ = x.eval ζ - y.eval ζ := rfl
@[simp] theorem Jac.eval_zsmul (n : ℤ) (x : Jac q M') (ζ : Idx q) : (n • x).eval ζ = n • x.eval ζ := rfl
@[simp] theorem Jac.eval_nsmul (n : ℕ) (x : Jac q M') (ζ : Idx q) : (n • x).eval ζ = n • x.eval ζ := rfl

def Jac.mapIdx (T : Idx q → (jacComp q M' →+ jacComp q M')) (s : Idx q → Idx q) : Jac q M' →+ Jac q M' where
  toFun x := Jac.mk fun ζ => T ζ (x.eval (s ζ))
  map_zero' := Jac.ext fun ζ => by simp only [Jac.eval_mk, Jac.eval_zero, map_zero]
  map_add' x y := Jac.ext fun ζ => by simp only [Jac.eval_mk, Jac.eval_add, map_add]

@[simp] theorem Jac.mapIdx_eval (T : Idx q → (jacComp q M' →+ jacComp q M')) (s : Idx q → Idx q)
    (x : Jac q M') (ζ : Idx q) : (Jac.mapIdx T s x).eval ζ = T ζ (x.eval (s ζ)) := rfl

end Carrier

section Galois

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def galJac : Gal →* AddMonoid.End (Jac q M') where
  toFun σ :=
    { toFun := fun x => Jac.mk fun ζ => σ • x.eval (σ⁻¹ • ζ)
      map_zero' := Jac.ext fun ζ => by
        simp only [Jac.eval_mk, Jac.eval_zero]
        exact smul_zero (A := jacComp q M') σ
      map_add' := fun x y => Jac.ext fun ζ => by
        simp only [Jac.eval_mk, Jac.eval_add]
        exact smul_add (A := jacComp q M') σ _ _ }
  map_one' := by
    refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
    show (1 : Gal) • x.eval ((1 : Gal)⁻¹ • ζ) = x.eval ζ
    rw [inv_one, one_smul, one_smul]
  map_mul' σ τ := by
    refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
    show (σ * τ) • x.eval ((σ * τ)⁻¹ • ζ) = σ • (τ • x.eval (τ⁻¹ • (σ⁻¹ • ζ)))
    rw [mul_smul, mul_inv_rev, mul_smul]

theorem galJac_eval (σ : Gal) (x : Jac q M') (ζ : Idx q) :
    (galJac q M' σ x).eval ζ = σ • x.eval (σ⁻¹ • ζ) :=
  rfl

end Galois

section LevelAut

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

def conjElem (γ : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / q; (q : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)]
    (by
      have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
      have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe γ
        rw [Matrix.det_fin_two] at h
        exact_mod_cast h
      rw [Matrix.det_fin_two_of]
      have : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) / q * ((q : ℝ) * ((γ 1 0 : ℤ) : ℝ)) =
          ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
        field_simp
      rw [this, hdet]
      exact one_ne_zero)

def IsLevelAutBar (ζ : Idx q) (γ : SL(2, ℤ))
    (τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (ι : AlgebraicClosure ℚ →+* ℂ),
    ι ζ.val = Complex.exp (2 * Real.pi * Complex.I / q) →
      coeffMap ι
          ((τ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : fieldBar q M') :
            LaurentSeries (AlgebraicClosure ℚ)) *
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] conjElem q γ)) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] conjElem q γ))

def levelAutBar (ζ : Idx q) (γ : SL(2, ℤ)) :
    fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M' :=
  haveI := Classical.dec (∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M',
    IsLevelAutBar q M' ζ γ τ)
  if h : ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ
  then h.choose else AlgEquiv.refl

variable {q M'}

theorem isLevelAutBar_levelAutBar {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ) :
    IsLevelAutBar q M' ζ γ (levelAutBar q M' ζ γ) := by
  rw [levelAutBar, dif_pos h]
  exact h.choose_spec

theorem levelAutBar_of_not {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ¬ ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ) :
    levelAutBar q M' ζ γ = AlgEquiv.refl := by
  rw [levelAutBar, dif_neg h]

variable (q M')

def levelOp (ζ : Idx q) (γ : SL(2, ℤ)) : jacComp q M' →+ jacComp q M' :=
  DistribSMul.toAddMonoidHom (jacComp q M') (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ))

theorem levelOp_apply (ζ : Idx q) (γ : SL(2, ℤ)) (x : jacComp q M') :
    levelOp q M' ζ γ x = SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) • x :=
  rfl

variable {q M'} in

theorem levelOp_of_not {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ¬ ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ)
    (x : jacComp q M') : levelOp q M' ζ γ x = x := by
  rw [levelOp_apply, levelAutBar_of_not h]
  have : SemilinearAut.ofAlgAut
      (AlgEquiv.refl : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') = 1 :=
    map_one _
  rw [this, one_smul]

def LevelAutInputs : Prop :=
  ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
    ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ

end LevelAut

section Operators

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

def redQ : SL(2, ℤ) →* CuspidalType.GL2 q :=
  (Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))))

def diagOneElem (d : (ZMod q)ˣ) : CuspidalType.GL2 q :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, (d : ZMod q)]
    (by rw [Matrix.det_fin_two_of]; simp [d.ne_zero])

@[simp] theorem coe_diagOneElem (d : (ZMod q)ˣ) :
    ((diagOneElem q d : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, 0; 0, (d : ZMod q)] :=
  rfl

def slJac (γ : SL(2, ℤ)) : Jac q M' →+ Jac q M' :=
  Jac.mapIdx (fun ζ => levelOp q M' ζ γ⁻¹) id

@[simp] theorem slJac_eval (γ : SL(2, ℤ)) (x : Jac q M') (ζ : Idx q) :
    (slJac q M' γ x).eval ζ = levelOp q M' ζ γ⁻¹ (x.eval ζ) :=
  rfl

def diagJac (d : (ZMod q)ˣ) : Jac q M' →+ Jac q M' :=
  Jac.mapIdx (fun _ => AddMonoidHom.id _) (Idx.pow d⁻¹)

@[simp] theorem diagJac_eval (d : (ZMod q)ˣ) (x : Jac q M') (ζ : Idx q) :
    (diagJac q M' d x).eval ζ = x.eval (ζ.pow d⁻¹) :=
  rfl

def GL2Laws : Prop :=
  ∃ G : CuspidalType.GL2 q →* AddMonoid.End (Jac q M'),
    (∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → G (redQ q γ) = slJac q M' γ) ∧
      ∀ d : (ZMod q)ˣ, G (diagOneElem q d) = diagJac q M' d

def gl2Jac : CuspidalType.GL2 q →* AddMonoid.End (Jac q M') :=
  haveI := Classical.dec (GL2Laws q M')
  if h : GL2Laws q M' then h.choose else 1

variable {q M'}

theorem gl2Jac_redQ (h : GL2Laws q M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    gl2Jac q M' (redQ q γ) = slJac q M' γ := by
  rw [gl2Jac, dif_pos h]
  exact h.choose_spec.1 γ hγ

theorem gl2Jac_diagOneElem (h : GL2Laws q M') (d : (ZMod q)ˣ) :
    gl2Jac q M' (diagOneElem q d) = diagJac q M' d := by
  rw [gl2Jac, dif_pos h]
  exact h.choose_spec.2 d

theorem gl2Jac_of_not (h : ¬ GL2Laws q M') : gl2Jac q M' = 1 := by
  rw [gl2Jac, dif_neg h]

variable (q M')

def heckeGenJac (ℓ : ℕ) : AddMonoid.End (Jac q M') :=
  haveI := Classical.dec (ℓ.Prime ∧ ¬ ℓ ∣ q * M')
  if h : ℓ.Prime ∧ ¬ ℓ ∣ q * M' then
    haveI : NeZero ℓ := ⟨h.1.ne_zero⟩
    have hq : ℓ.Coprime q := (Nat.Prime.coprime_iff_not_dvd h.1).2 fun hd => h.2 (hd.mul_right M')
    have hqM : ℓ.Coprime (q ^ 2 * M') := by
      refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 hq) ?_
      exact (Nat.Prime.coprime_iff_not_dvd h.1).2 fun hd => h.2 (hd.mul_left q)
    (Jac.mapIdx
      (fun _ => (diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹).comp
        (heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ))
      (Idx.pow (ZMod.unitOfCoprime ℓ hq)⁻¹) : Jac q M' →+ Jac q M')
  else 0

variable {q M'}

theorem heckeGenJac_of_dvd {ℓ : ℕ} (h : ℓ ∣ q * M') : heckeGenJac q M' ℓ = 0 := by
  rw [heckeGenJac, dif_neg (fun h' => h'.2 h)]

theorem heckeGenJac_of_not_prime {ℓ : ℕ} (h : ¬ ℓ.Prime) : heckeGenJac q M' ℓ = 0 := by
  rw [heckeGenJac, dif_neg (fun h' => h h'.1)]

theorem heckeGenJac_eval {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓqM : ¬ ℓ ∣ q * M') (hq : ℓ.Coprime q)
    (hqM : ℓ.Coprime (q ^ 2 * M')) (x : Jac q M') (ζ : Idx q) :
    (heckeGenJac q M' ℓ x).eval ζ =
      diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ
            (x.eval (ζ.pow (ZMod.unitOfCoprime ℓ hq)⁻¹))) := by
  rw [heckeGenJac, dif_pos ⟨hℓ, hℓqM⟩]
  rfl

variable (q M')

def HeckeGenCommute : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeGenJac q M' ℓ * heckeGenJac q M' ℓ' = heckeGenJac q M' ℓ' * heckeGenJac q M' ℓ

variable {q M'}

theorem isMulCommutative_adjoin_heckeGenJac (h : HeckeGenCommute q M') :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ)) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact h ℓ ℓ')

open scoped IsMulCommutative in

def heckeJacAux (h : HeckeGenCommute q M') :
    HeckeAlg →ₐ[ℤ] (Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ) :
      Subalgebra ℤ (AddMonoid.End (Jac q M'))) :=
  haveI := isMulCommutative_adjoin_heckeGenJac h
  MvPolynomial.aeval fun ℓ =>
    (⟨heckeGenJac q M' ℓ, Algebra.subset_adjoin (Set.mem_range_self ℓ)⟩ :
      Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ))

open scoped IsMulCommutative in
theorem heckeJacAux_heckeGen (h : HeckeGenCommute q M') (ℓ : Nat.Primes) :
    (heckeJacAux h (heckeGen ℓ) : AddMonoid.End (Jac q M')) = heckeGenJac q M' ℓ := by
  haveI := isMulCommutative_adjoin_heckeGenJac h
  rw [heckeJacAux, heckeGen, MvPolynomial.aeval_X]

variable (q M')

def heckeJac : HeckeAlg →+* AddMonoid.End (Jac q M') :=
  haveI := Classical.dec (HeckeGenCommute q M')
  if h : HeckeGenCommute q M' then
    ((Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ)).val.comp (heckeJacAux h)).toRingHom
  else (Int.castRingHom (AddMonoid.End (Jac q M'))).comp
    (MvPolynomial.eval₂Hom (Int.castRingHom ℤ) (0 : Nat.Primes → ℤ))

variable {q M'}

theorem heckeJac_heckeGen (h : HeckeGenCommute q M') (ℓ : Nat.Primes) :
    heckeJac q M' (heckeGen ℓ) = heckeGenJac q M' ℓ := by
  rw [heckeJac, dif_pos h]
  exact heckeJacAux_heckeGen h ℓ

theorem heckeJac_heckeGen_of_not (h : ¬ HeckeGenCommute q M') (ℓ : Nat.Primes) :
    heckeJac q M' (heckeGen ℓ) = 0 := by
  rw [heckeJac, dif_neg h, heckeGen, RingHom.comp_apply, MvPolynomial.eval₂Hom_zero_apply,
    MvPolynomial.constantCoeff_X, map_zero, map_zero]

theorem heckeJac_heckeGen_of_dvd (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ∣ q * M') :
    heckeJac q M' (heckeGen ℓ) = 0 := by
  by_cases h : HeckeGenCommute q M'
  · rw [heckeJac_heckeGen h, heckeGenJac_of_dvd hℓ]
  · exact heckeJac_heckeGen_of_not h ℓ

end Operators

section Tate

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

example : DistribMulAction (AddMonoid.End (Jac q M')) (Jac q M') := inferInstance

def tateEnd : AddMonoid.End (Jac q M') →+* Module.End ℤ_[lam] (TateModule lam (Jac q M')) where
  toFun := TateModule.rep lam (Jac q M') (AddMonoid.End (Jac q M'))
  map_one' := map_one _
  map_mul' f g := map_mul _ f g
  map_zero' := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

omit [Fact q.Prime] in
theorem tateEnd_apply_coe (f : AddMonoid.End (Jac q M')) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateEnd q M' lam f x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = f ((x : ℕ → Jac q M') n) :=
  rfl

def tateGal : Gal →* Module.End ℤ_[lam] (TateModule lam (Jac q M')) :=
  (tateEnd q M' lam).toMonoidHom.comp (galJac q M')

def tateHecke : HeckeAlg →+* Module.End ℤ_[lam] (TateModule lam (Jac q M')) :=
  (tateEnd q M' lam).comp (heckeJac q M')

def tateGL2 : CuspidalType.GL2 q →* Module.End ℤ_[lam] (TateModule lam (Jac q M')) :=
  (tateEnd q M' lam).toMonoidHom.comp (gl2Jac q M')

theorem tateGal_apply_coe (σ : Gal) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateGal q M' lam σ x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = galJac q M' σ ((x : ℕ → Jac q M') n) :=
  rfl

theorem tateHecke_apply_coe (t : HeckeAlg) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateHecke q M' lam t x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = heckeJac q M' t ((x : ℕ → Jac q M') n) :=
  rfl

theorem tateGL2_apply_coe (g : CuspidalType.GL2 q) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateGL2 q M' lam g x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = gl2Jac q M' g ((x : ℕ → Jac q M') n) :=
  rfl

theorem tateHecke_heckeGen_of_dvd (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ∣ q * M') :
    tateHecke q M' lam (heckeGen ℓ) = 0 := by
  rw [tateHecke, RingHom.comp_apply, heckeJac_heckeGen_of_dvd ℓ hℓ, map_zero]

end Tate

end ModularCurve.FullLevel

end


