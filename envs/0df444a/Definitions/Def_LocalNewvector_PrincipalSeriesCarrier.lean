-- Prove2me | Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
-- name    : LocalNewvector_PrincipalSeriesCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/76872d82-ca4f-59f9-bf3e-fda1fc9e79d4
-- title:
--   Principal series of GL₂(ℚ_p): function model and carrier
-- statement:
--   Fix a prime $p$ and write $G=\mathrm{GL}_2(\mathbb{Q}_p)$. For units $a_1,a_2\in\mathbb{Q}_p^\times$ and $x\in\mathbb{Q}_p$, `borelElem p a₁ a₂ x` is the upper triangular element $\begin{pmatrix} a_1 & x\\ 0 & a_2\end{pmatrix}$ of $G$, given together with its explicit inverse; the accompanying lemmas record the product rule $(a_1,a_2,x)\cdot(b_1,b_2,y)=(a_1b_1,a_2b_2,a_1y+xb_2)$, the inverse, and that $(1,1,0)$ is the identity. `halfModulus p a₁ a₂` is the complex number $\sqrt{\lVert a_1\rVert/\lVert a_2\rVert}$, obtained from the real square root of the ratio of $p$-adic norms; it depends only on the two norms, equals $1$ when both are $1$, and is multiplicative in $(a_1,a_2)$.
--
--   Given monoid homomorphisms $\mu_1,\mu_2:\mathbb{Q}_p^\times\to\mathbb{C}^\times$, `principalSeries p μ₁ μ₂` is the $\mathbb{C}$-submodule of all functions $f:G\to\mathbb{C}$ that are locally constant and satisfy $f(b\,g)=\mu_1(a_1)\mu_2(a_2)\sqrt{\lVert a_1\rVert/\lVert a_2\rVert}\,f(g)$ for every Borel element $b=$ `borelElem p a₁ a₂ x` and every $g\in G$: a concrete model of the normalised induced representation, with no further support or growth condition. Membership is characterised, and the space is stable under right translation $f\mapsto f(\cdot\,g)$. For a subgroup $U\le G$, `rightInvariantFunctions p U` is the submodule of $f$ with $f(xu)=f(x)$ for all $u\in U$, $x\in G$ (local constancy is not required here).
--
--   `PSCarrier p μ₁ μ₂` is the underlying type of `principalSeries p μ₁ μ₂`, equipped with its complex vector space structure and with the $G$-action $(g\bullet f)(y)=f(yg)$, commuting with scalars, plus a small interface (`mk`, `toSub`, `toFn`, `ext`, `toSubEquiv`). Finally `PSCarrier.fixedEquiv U` is the $\mathbb{C}$-linear isomorphism between `fixedSubmodule U (PSCarrier p μ₁ μ₂)`, the vectors fixed by every element of $U$, and the intersection `principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U` inside the function space, and `finrank_fixed_eq` transports complex dimensions across it.
--
--   **Relation to Mathlib.** Local constancy is Mathlib's `IsLocallyConstant`; Mathlib has no principal series or normalised induction for $p$-adic groups, so the function-space model, its carrier type and the fixed-space identification are the project's own.
--
--   **Where it is used.** These definitions give the working model of the principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$ used in the project's local newvector theory, where conductors are defined through the fixed spaces of the congruence subgroups $K_1(p^n)$; `fixedEquiv` and `finrank_fixed_eq` let such fixed spaces be computed inside the space of functions on the group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalNewvector_PrincipalSeriesCarrier.lean

import Definitions.Def_LocalNewvector_ConductorDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]

section BorelElements

def borelElem (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  ⟨!![(a₁ : ℚ_[p]), x; 0, (a₂ : ℚ_[p])],
   !![((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]), -(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]));
      0, ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])],
   by
    have h1 : (a₁ : ℚ_[p]) ≠ 0 := a₁.ne_zero
    have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, mul_assoc, h1, h2],
   by
    have h1 : (a₁ : ℚ_[p]) ≠ 0 := a₁.ne_zero
    have h2 : (a₂ : ℚ_[p]) ≠ 0 := a₂.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val, mul_assoc, h1, h2]⟩

@[simp] lemma coe_borelElem (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (borelElem p a₁ a₂ x : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![(a₁ : ℚ_[p]), x; 0, (a₂ : ℚ_[p])] :=
  rfl

@[simp] lemma coe_borelElem_inv (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (((borelElem p a₁ a₂ x)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])
      = !![((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]),
            -(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]));
          0, ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p])] :=
  rfl

theorem borelElem_mul (a₁ a₂ b₁ b₂ : ℚ_[p]ˣ) (x y : ℚ_[p]) :
    borelElem p a₁ a₂ x * borelElem p b₁ b₂ y
      = borelElem p (a₁ * b₁) (a₂ * b₂) ((a₁ : ℚ_[p]) * y + x * (b₂ : ℚ_[p])) := by
  apply Units.ext
  show (borelElem p a₁ a₂ x : Matrix (Fin 2) (Fin 2) ℚ_[p])
      * (borelElem p b₁ b₂ y : Matrix (Fin 2) (Fin 2) ℚ_[p]) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem borelElem_inv (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) :
    (borelElem p a₁ a₂ x)⁻¹
      = borelElem p a₁⁻¹ a₂⁻¹
          (-(((a₁⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * x * ((a₂⁻¹ : ℚ_[p]ˣ) : ℚ_[p]))) :=
  Units.ext rfl

@[simp] theorem borelElem_one : borelElem p 1 1 0 = 1 := by
  apply Units.ext
  show (borelElem p 1 1 0 : Matrix (Fin 2) (Fin 2) ℚ_[p]) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end BorelElements

section HalfModulus

def halfModulus (a₁ a₂ : ℚ_[p]ˣ) : ℂ :=
  (Real.sqrt (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) : ℝ)

theorem halfModulus_eq_one_of_norm_eq_one {a₁ a₂ : ℚ_[p]ˣ}
    (h₁ : ‖(a₁ : ℚ_[p])‖ = 1) (h₂ : ‖(a₂ : ℚ_[p])‖ = 1) : halfModulus p a₁ a₂ = 1 := by
  simp only [halfModulus, h₁, h₂, div_one, Real.sqrt_one, Complex.ofReal_one]

@[simp] theorem halfModulus_one : halfModulus p 1 1 = 1 :=
  halfModulus_eq_one_of_norm_eq_one p (by simp) (by simp)

theorem halfModulus_congr {a₁ a₂ b₁ b₂ : ℚ_[p]ˣ}
    (h₁ : ‖(a₁ : ℚ_[p])‖ = ‖(b₁ : ℚ_[p])‖) (h₂ : ‖(a₂ : ℚ_[p])‖ = ‖(b₂ : ℚ_[p])‖) :
    halfModulus p a₁ a₂ = halfModulus p b₁ b₂ := by
  simp only [halfModulus, h₁, h₂]

theorem halfModulus_mul (a₁ a₂ b₁ b₂ : ℚ_[p]ˣ) :
    halfModulus p (a₁ * b₁) (a₂ * b₂) = halfModulus p a₁ a₂ * halfModulus p b₁ b₂ := by
  have hquot : ‖((a₁ * b₁ : ℚ_[p]ˣ) : ℚ_[p])‖ / ‖((a₂ * b₂ : ℚ_[p]ˣ) : ℚ_[p])‖
      = (‖(a₁ : ℚ_[p])‖ / ‖(a₂ : ℚ_[p])‖) * (‖(b₁ : ℚ_[p])‖ / ‖(b₂ : ℚ_[p])‖) := by
    rw [Units.val_mul, Units.val_mul, norm_mul, norm_mul, div_mul_div_comm]
  simp only [halfModulus, hquot]
  rw [Real.sqrt_mul (by positivity), Complex.ofReal_mul]

end HalfModulus

section PrincipalSeries

def principalSeries (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ) where
  carrier := {f | IsLocallyConstant f ∧
    ∀ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]),
      f (borelElem p a₁ a₂ x * g)
        = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun a₁ a₂ x g => by simp⟩
  add_mem' := by
    intro f g hf hg
    obtain ⟨hf_lc, hf_tr⟩ := hf
    obtain ⟨hg_lc, hg_tr⟩ := hg
    refine ⟨hf_lc.comp₂ hg_lc (· + ·), fun a₁ a₂ x g₀ => ?_⟩
    show f _ + g _ = _ * (f g₀ + g g₀)
    rw [hf_tr, hg_tr]
    ring
  smul_mem' := by
    intro c f hf
    obtain ⟨hf_lc, hf_tr⟩ := hf
    refine ⟨hf_lc.comp (c * ·), fun a₁ a₂ x g₀ => ?_⟩
    show c * f _ = _ * (c * f g₀)
    rw [hf_tr]
    ring

theorem mem_principalSeries_iff {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ} {f : GL (Fin 2) ℚ_[p] → ℂ} :
    f ∈ principalSeries p μ₁ μ₂
      ↔ IsLocallyConstant f ∧
          ∀ (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]),
            f (borelElem p a₁ a₂ x * g)
              = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g :=
  Iff.rfl

theorem isLocallyConstant_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) : IsLocallyConstant f :=
  ((mem_principalSeries_iff p).mp hf).1

theorem apply_borelElem_mul_of_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂)
    (a₁ a₂ : ℚ_[p]ˣ) (x : ℚ_[p]) (g : GL (Fin 2) ℚ_[p]) :
    f (borelElem p a₁ a₂ x * g)
      = (μ₁ a₁ : ℂ) * (μ₂ a₂ : ℂ) * halfModulus p a₁ a₂ * f g :=
  ((mem_principalSeries_iff p).mp hf).2 a₁ a₂ x g

theorem rightTranslate_mem_principalSeries {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {f : GL (Fin 2) ℚ_[p] → ℂ} (hf : f ∈ principalSeries p μ₁ μ₂) (g : GL (Fin 2) ℚ_[p]) :
    (fun y => f (y * g)) ∈ principalSeries p μ₁ μ₂ := by
  obtain ⟨hlc, htr⟩ := (mem_principalSeries_iff p).mp hf
  refine (mem_principalSeries_iff p).mpr
    ⟨hlc.comp_continuous (continuous_id.mul continuous_const), fun a₁ a₂ x g₀ => ?_⟩
  show f (borelElem p a₁ a₂ x * g₀ * g) = _ * f (g₀ * g)
  rw [mul_assoc, htr]

end PrincipalSeries

section RightInvariant

def rightInvariantFunctions (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    Submodule ℂ (GL (Fin 2) ℚ_[p] → ℂ) where
  carrier := {f | ∀ u ∈ U, ∀ x, f (x * u) = f x}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro f g hf hg u hu x
    show f (x * u) + g (x * u) = f x + g x
    rw [hf u hu x, hg u hu x]
  smul_mem' := by
    intro c f hf u hu x
    show c * f (x * u) = c * f x
    rw [hf u hu x]

theorem mem_rightInvariantFunctions_iff {U : Subgroup (GL (Fin 2) ℚ_[p])}
    {f : GL (Fin 2) ℚ_[p] → ℂ} :
    f ∈ rightInvariantFunctions p U ↔ ∀ u ∈ U, ∀ x, f (x * u) = f x :=
  Iff.rfl

end RightInvariant

section PrincipalSeriesCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

def PSCarrier : Type := ↥(principalSeries p μ₁ μ₂)

namespace PSCarrier

def mk (f : ↥(principalSeries p μ₁ μ₂)) : PSCarrier p μ₁ μ₂ := f

def toSub (f : PSCarrier p μ₁ μ₂) : ↥(principalSeries p μ₁ μ₂) := f

def toFn (f : PSCarrier p μ₁ μ₂) : GL (Fin 2) ℚ_[p] → ℂ :=
  (toSub p μ₁ μ₂ f : GL (Fin 2) ℚ_[p] → ℂ)

theorem toFn_mem (f : PSCarrier p μ₁ μ₂) : toFn p μ₁ μ₂ f ∈ principalSeries p μ₁ μ₂ :=
  (toSub p μ₁ μ₂ f).property

theorem ext {f g : PSCarrier p μ₁ μ₂}
    (h : ∀ y, toFn p μ₁ μ₂ f y = toFn p μ₁ μ₂ g y) : f = g :=
  Subtype.ext (funext h)

instance : AddCommGroup (PSCarrier p μ₁ μ₂) :=
  inferInstanceAs (AddCommGroup ↥(principalSeries p μ₁ μ₂))

instance : Module ℂ (PSCarrier p μ₁ μ₂) :=
  inferInstanceAs (Module ℂ ↥(principalSeries p μ₁ μ₂))

def toSubEquiv : PSCarrier p μ₁ μ₂ ≃ₗ[ℂ] ↥(principalSeries p μ₁ μ₂) where
  toFun := toSub p μ₁ μ₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := mk p μ₁ μ₂
  left_inv _ := rfl
  right_inv _ := rfl

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (PSCarrier p μ₁ μ₂) where
  smul g f := mk p μ₁ μ₂
    ⟨fun y => toFn p μ₁ μ₂ f (y * g),
     rightTranslate_mem_principalSeries p (toFn_mem p μ₁ μ₂ f) g⟩
  one_smul f := ext p μ₁ μ₂ fun y => congrArg (toFn p μ₁ μ₂ f) (mul_one y)
  mul_smul g h f := ext p μ₁ μ₂ fun y => congrArg (toFn p μ₁ μ₂ f) (mul_assoc y g h).symm
  smul_zero _ := ext p μ₁ μ₂ fun _ => rfl
  smul_add _ _ _ := ext p μ₁ μ₂ fun _ => rfl

@[simp] theorem toFn_smul (g : GL (Fin 2) ℚ_[p]) (f : PSCarrier p μ₁ μ₂)
    (y : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (g • f) y = toFn p μ₁ μ₂ f (y * g) := rfl

@[simp] theorem toFn_csmul (c : ℂ) (f : PSCarrier p μ₁ μ₂) (y : GL (Fin 2) ℚ_[p]) :
    toFn p μ₁ μ₂ (c • f) y = c * toFn p μ₁ μ₂ f y := rfl

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (PSCarrier p μ₁ μ₂) where
  smul_comm _ _ _ := ext p μ₁ μ₂ fun _ => rfl

def fixedEquiv (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    ↥(LocalNewvector.fixedSubmodule U (PSCarrier p μ₁ μ₂)) ≃ₗ[ℂ]
      ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U) where
  toFun v := ⟨toFn p μ₁ μ₂ v.val, Submodule.mem_inf.mpr
    ⟨toFn_mem p μ₁ μ₂ v.val, by
      rw [mem_rightInvariantFunctions_iff]
      intro u hu y
      exact congrArg (fun z => toFn p μ₁ μ₂ z y)
        ((LocalNewvector.mem_fixedSubmodule_iff.mp v.property) u hu)⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  invFun w := ⟨mk p μ₁ μ₂ ⟨w.val, (Submodule.mem_inf.mp w.property).1⟩, by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro u hu
    refine ext p μ₁ μ₂ fun y => ?_
    exact (mem_rightInvariantFunctions_iff p).mp
      (Submodule.mem_inf.mp w.property).2 u hu y⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem finrank_fixed_eq (U : Subgroup (GL (Fin 2) ℚ_[p])) :
    Module.finrank ℂ ↥(LocalNewvector.fixedSubmodule U (PSCarrier p μ₁ μ₂))
      = Module.finrank ℂ ↥(principalSeries p μ₁ μ₂ ⊓ rightInvariantFunctions p U) :=
  (fixedEquiv p μ₁ μ₂ U).finrank_eq

end PSCarrier

end PrincipalSeriesCarrier

end LocalNewvector

end


