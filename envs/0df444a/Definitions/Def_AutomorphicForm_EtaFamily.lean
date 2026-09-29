-- Prove2me | Definitions.Def_AutomorphicForm_EtaFamily
-- name    : AutomorphicForm_EtaFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/4730ba3d-70a9-5e46-87ab-4c7bfda8d094
-- title:
--   Complex powers of positive idele characters; the eta family
-- statement:
--   Throughout, $R$ is a Dedekind domain with field of fractions $K$, and the group in play is the unit group $(\mathbb{A}_{R,K})^\times$ of Mathlib's adele ring of this pair. Given a homomorphism $\alpha : (\mathbb{A}_{R,K})^\times \to \mathbb{R}^\times$ whose values are everywhere positive (the hypothesis `hα`) and a complex number $s$, `cpowChar` is the homomorphism $x \mapsto \alpha(x)^s$ into $\mathbb{C}^\times$, the complex power being the principal one of the positive real $\alpha(x)$; positivity supplies both non-vanishing and the multiplicativity $(ab)^s = a^s b^s$. Its modulus is computed in `norm_cpowChar_apply` as $\|\alpha(x)^s\| = \alpha(x)^{\operatorname{Re} s}$; consequently `cpowChar` is unitary in the sense of `IsUnitaryChar` whenever $\operatorname{Re} s = 0$. The predicate `IsPrincipalTrivial` on $\alpha$ asserts that $\alpha$ kills the principal ideles, i.e. $\alpha(\iota(u)) = 1$ for every $u \in K^\times$, where $\iota$ is induced by $K \to \mathbb{A}_{R,K}$; under it, `cpowChar α hα s` satisfies `IsIdeleClassChar`, the corresponding triviality condition for $\mathbb{C}^\times$-valued characters, for every $s$.
--
--   For complex characters $\mu, \nu$ of the idele group, `etaFst` and `etaSnd` are the shifted pair $\mu\,\alpha^{s+1/2}$ and $\nu\,\alpha^{-(s+1/2)}$, formed as products in the monoid of homomorphisms to $\mathbb{C}^\times$. The accompanying lemmas record: the pointwise defining formulas; that each member is trivial on principal ideles as soon as $\mu$ (resp. $\nu$) is and $\alpha$ is `IsPrincipalTrivial`; the cancellation $\eta_1(x)\eta_2(x) = \mu(x)\nu(x)$ for all $x$, independent of $s$; and, for unitary $\mu$, the modulus $\|\eta_1(x)\| = \alpha(x)^{\operatorname{Re} s + 1/2}$, with `re_add_half` the elementary identity $\operatorname{Re}(s + 1/2) = \operatorname{Re} s + 1/2$. No convergence, measure-theoretic or automorphy assertion is made, and the intended positive character (an adelic absolute value) is not constructed here.
--
--   **Relation to Mathlib.** The adele ring and its unit group, and the complex power function `Complex.cpow`, are Mathlib's; the characters `IsIdeleClassChar`, `IsUnitaryChar` used here, together with `IsPrincipalTrivial`, `cpowChar` and the shifted pair `etaFst`/`etaSnd`, are the project's own notions, Mathlib having no theory of quasi-characters of the idele class group.
--
--   **Where it is used.** These quasi-characters provide the parameter $s$ along which the adelic $L^2(\xi)$ spaces of the project's $GL_2$ automorphic-forms layer are twisted: `etaFst`/`etaSnd` is the pair of characters attached to a principal-series-type family, normalised so that the product of the two members is the fixed central character $\mu\nu$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_EtaFamily.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AutomorphicForm

section EtaFamily

open NumberField

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem re_add_half (s : ℂ) : (s + 1 / 2).re = s.re + 1 / 2 := by
  have h : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [← h, Complex.add_re, Complex.ofReal_re]

def cpowChar (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) :
    (AdeleRing R K)ˣ →* ℂˣ where
  toFun x := Units.mk0 ((((α x : ℝˣ) : ℝ) : ℂ) ^ s)
    (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (hα x).ne')))
  map_one' := by
    apply Units.ext
    show ((((α 1 : ℝˣ) : ℝ) : ℂ)) ^ s = 1
    rw [map_one, Units.val_one, Complex.ofReal_one, Complex.one_cpow]
  map_mul' x y := by
    apply Units.ext
    show ((((α (x * y) : ℝˣ) : ℝ) : ℂ)) ^ s
        = ((((α x : ℝˣ) : ℝ) : ℂ)) ^ s * ((((α y : ℝˣ) : ℝ) : ℂ)) ^ s
    rw [map_mul, Units.val_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (hα x).le (hα y).le s

@[simp] theorem cpowChar_apply_val (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ((cpowChar α hα s x : ℂˣ) : ℂ) = (((α x : ℝˣ) : ℝ) : ℂ) ^ s := rfl

theorem norm_cpowChar_apply (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ‖((cpowChar α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (hα x) s

def IsPrincipalTrivial (α : (AdeleRing R K)ˣ →* ℝˣ) : Prop :=
  ∀ u : Kˣ, α (Units.map (algebraMap K (AdeleRing R K)) u) = 1

theorem cpowChar_isIdeleClassChar {α : (AdeleRing R K)ˣ →* ℝˣ}
    {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} (hprin : IsPrincipalTrivial (R := R) (K := K) α) (s : ℂ) :
    IsIdeleClassChar R K (cpowChar α hα s) := by
  intro u
  apply Units.ext
  show ((((α (Units.map (algebraMap K (AdeleRing R K)) u) : ℝˣ) : ℝ) : ℂ)) ^ s = 1
  rw [hprin u, Units.val_one, Complex.ofReal_one, Complex.one_cpow]

theorem cpowChar_isUnitaryChar_of_re_eq_zero {α : (AdeleRing R K)ˣ →* ℝˣ}
    {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)} {s : ℂ} (hs : s.re = 0) :
    IsUnitaryChar R K (cpowChar α hα s) := by
  intro x
  rw [norm_cpowChar_apply, hs, Real.rpow_zero]

def etaFst (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) : (AdeleRing R K)ˣ →* ℂˣ :=
  μ * cpowChar α hα (s + 1 / 2)

def etaSnd (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) : (AdeleRing R K)ˣ →* ℂˣ :=
  ν * cpowChar α hα (-(s + 1 / 2))

theorem etaFst_apply (μ : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    etaFst μ α hα s x = μ x * cpowChar α hα (s + 1 / 2) x := rfl

theorem etaSnd_apply (ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    etaSnd ν α hα s x = ν x * cpowChar α hα (-(s + 1 / 2)) x := rfl

theorem etaFst_isIdeleClassChar {μ : (AdeleRing R K)ˣ →* ℂˣ} (hμ : IsIdeleClassChar R K μ)
    {α : (AdeleRing R K)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)}
    (hprin : IsPrincipalTrivial (R := R) (K := K) α) (s : ℂ) :
    IsIdeleClassChar R K (etaFst μ α hα s) := by
  intro u
  rw [etaFst_apply, hμ u, cpowChar_isIdeleClassChar hprin (s + 1 / 2) u, one_mul]

theorem etaSnd_isIdeleClassChar {ν : (AdeleRing R K)ˣ →* ℂˣ} (hν : IsIdeleClassChar R K ν)
    {α : (AdeleRing R K)ˣ →* ℝˣ} {hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)}
    (hprin : IsPrincipalTrivial (R := R) (K := K) α) (s : ℂ) :
    IsIdeleClassChar R K (etaSnd ν α hα s) := by
  intro u
  rw [etaSnd_apply, hν u, cpowChar_isIdeleClassChar hprin (-(s + 1 / 2)) u, one_mul]

theorem etaFst_mul_etaSnd (μ ν : (AdeleRing R K)ˣ →* ℂˣ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    etaFst μ α hα s x * etaSnd ν α hα s x = μ x * ν x := by
  rw [etaFst_apply, etaSnd_apply]
  have hcancel : cpowChar α hα (s + 1 / 2) x * cpowChar α hα (-(s + 1 / 2)) x = 1 := by
    apply Units.ext
    rw [Units.val_mul, cpowChar_apply_val, cpowChar_apply_val, Units.val_one]
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne'), add_neg_cancel,
      Complex.cpow_zero]
  calc μ x * cpowChar α hα (s + 1 / 2) x * (ν x * cpowChar α hα (-(s + 1 / 2)) x)
      = μ x * ν x * (cpowChar α hα (s + 1 / 2) x * cpowChar α hα (-(s + 1 / 2)) x) :=
        mul_mul_mul_comm _ _ _ _
    _ = μ x * ν x := by rw [hcancel, mul_one]

theorem norm_etaFst_apply_of_unitary {μ : (AdeleRing R K)ˣ →* ℂˣ}
    (hμ : IsUnitaryChar R K μ) (α : (AdeleRing R K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing R K)ˣ) :
    ‖((etaFst μ α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (s.re + 1 / 2) := by
  rw [etaFst_apply, Units.val_mul, norm_mul, hμ x, one_mul, norm_cpowChar_apply, re_add_half]

end EtaFamily

end AutomorphicForm


