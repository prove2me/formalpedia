-- Prove2me | Definitions.Def_LanglandsTunnell_ArchPlace
-- name    : LanglandsTunnell_ArchPlace
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/eb6d980c-50c1-5aa3-b073-37e1e32f4e03
-- title:
--   Archimedean carriers for Tate's local zeta integrals and γ-factors
-- statement:
--   Working at the two archimedean completions, this module fixes additive characters, quasi-characters, test functions, zeta integrals and γ-factors, all as total functions of the data they depend on. Over $\mathbb{C}$: `psiComplex` is the bundled additive character $z \mapsto \exp(-2\pi i(z + \bar z))$; `anglePhase` sends a unit $z$ to $z/\lVert z\rVert$, with helper lemmas giving that it has modulus one, is nonzero, and is multiplicative; `complexCharFun u k` is the monoid homomorphism $\mathbb{C}^\times \to \mathbb{C}^\times$ given by $z \mapsto \lVert z\rVert^{2u}\,(z/\lVert z\rVert)^k$ for $u \in \mathbb{C}$, $k \in \mathbb{Z}$; and `complexTestFun k` is the function $z \mapsto \bar z^{\,\max(k,0)} z^{\,\max(-k,0)} e^{-2\pi\lVert z\rVert^2}$ (the exponents are the truncations of $k$ and $-k$ to $\mathbb{N}$), which at $k=0$ is the Gaussian, takes the value $1$ at the origin and is not the zero function. Over $\mathbb{R}$: `psiReal` is $x \mapsto \exp(-2\pi i x)$, `realSign` is $x \mapsto x/\lvert x\rvert$ viewed in $\mathbb{C}^\times$ (multiplicative), `realCharFun u a` is $x \mapsto \lvert x\rvert^{u}\,\mathrm{sgn}(x)^{a}$ for $u \in \mathbb{C}$ and $a \in \mathbb{Z}/2$ acting through its natural-number value, and `realTestFun a` is $x \mapsto x^{a} e^{-\pi x^2}$, again with the $a=0$ case computed and shown nonzero.
--
--   The zeta integrals are taken against an arbitrary measure on the completion: `complexZeta μ f χ s` is $\int f(z)\,\chi(z)\,\lVert z\rVert^{2s-2}\,d\mu$ and `realZeta μ f χ s` is $\int f(x)\,\chi(x)\,\lvert x\rvert^{s-1}\,d\mu$, where $\chi$ is extended from units to the whole field by $0$ at the origin via [`LanglandsTunnell.TateLocal.charExt`](../def/LanglandsTunnell_TateLocalZeta.html#L99); the exponents are the normalised absolute values $\lvert z\rvert_{\mathbb{C}}^{s-1}$ and $\lvert x\rvert_{\mathbb{R}}^{s-1}$. The γ-factors `complexGammaAt` and `realGammaAt` are defined, at a chosen test function $f_0$, as the ratio of the zeta integral of [`LanglandsTunnell.TateLocal.tateFourier ψ μ f₀`](../def/LanglandsTunnell_TateLocalZeta.html#L85) against $\chi^{-1}$ at $1-s$ to that of $f_0$ against $\chi$ at $s$; there is no existential quantifier, and the division is the total division of $\mathbb{C}$.
--
--   **Relation to Mathlib.** Mathlib supplies the bundled `AddChar`, complex `cpow` and the measure-theoretic integral, but has no Tate local zeta integrals or archimedean γ-factors; these, like the general carriers of `LanglandsTunnell.TateLocal`, are the project's own definitions.
--
--   **Where it is used.** These archimedean carriers serve the local harmonic analysis underlying the Langlands–Tunnell theorem, which supplies modularity of the mod-$3$ representation attached to a Frey curve and thereby the starting point of the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArchPlace.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Real MeasureTheory LanglandsTunnell.TateLocal

namespace LanglandsTunnell.ArchPlace

def psiComplex : AddChar ℂ ℂ where
  toFun z := Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z)))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← Complex.exp_add, map_add]; ring_nf

theorem psiComplex_apply (z : ℂ) :
    psiComplex z = Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z))) := rfl

def anglePhase (z : ℂˣ) : ℂ := (z : ℂ) / (‖(z : ℂ)‖ : ℂ)

@[simp] theorem norm_anglePhase (z : ℂˣ) : ‖anglePhase z‖ = 1 := by
  rw [anglePhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr z.ne_zero)]

theorem anglePhase_ne_zero (z : ℂˣ) : anglePhase z ≠ 0 := fun h => by
  have := norm_anglePhase z; rw [h, norm_zero] at this; exact one_ne_zero this.symm

theorem anglePhase_mul (z w : ℂˣ) : anglePhase (z * w) = anglePhase z * anglePhase w := by
  simp only [anglePhase, Units.val_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv]
  ring

def complexCharFun (u : ℂ) (k : ℤ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 (((‖(z : ℂ)‖ : ℂ) ^ (2 * u)) * anglePhase z ^ k)
    (mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))))
      (zpow_ne_zero _ (anglePhase_ne_zero z)))
  map_one' := by ext; simp [anglePhase]
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0]
    push_cast [norm_mul, anglePhase_mul, mul_zpow]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

theorem complexCharFun_apply (u : ℂ) (k : ℤ) (z : ℂˣ) :
    ((complexCharFun u k z : ℂˣ) : ℂ) = (‖(z : ℂ)‖ : ℂ) ^ (2 * u) * anglePhase z ^ k := rfl

def complexTestFun (k : ℤ) : ℂ → ℂ :=
  fun z => (starRingEnd ℂ z) ^ k.toNat * z ^ (-k).toNat * Complex.exp (-(2 * π * ‖z‖ ^ 2))

@[simp] theorem complexTestFun_zero_apply (z : ℂ) :
    complexTestFun 0 z = Complex.exp (-(2 * π * ‖z‖ ^ 2)) := by
  simp [complexTestFun]

theorem complexTestFun_zero_at_zero : complexTestFun 0 0 = 1 := by simp

theorem complexTestFun_zero_ne_zero : complexTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def complexZeta (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ z, f z * charExt χ z * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2)) ∂μ

def complexGammaAt (μ : Measure ℂ) (ψ : AddChar ℂ ℂ) (f₀ : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  complexZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / complexZeta μ f₀ χ s

theorem psiComplex_mul_eq (z w : ℂ) :
    psiComplex (z * w)
      = Complex.exp (-(2 * π * Complex.I * (z * w + starRingEnd ℂ z * starRingEnd ℂ w))) := by
  rw [psiComplex_apply, map_mul]

def psiReal : AddChar ℝ ℂ where
  toFun x := Complex.exp (-(2 * π * Complex.I * x))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by push_cast; rw [← Complex.exp_add]; ring_nf

theorem psiReal_apply (x : ℝ) : psiReal x = Complex.exp (-(2 * π * Complex.I * x)) := rfl

def realSign (x : ℝˣ) : ℂˣ :=
  Units.mk0 ((x : ℝ) / (‖(x : ℝ)‖ : ℝ) : ℂ) (by
    have hx : (x : ℝ) ≠ 0 := x.ne_zero
    simp only [ne_eq, Complex.ofReal_eq_zero, div_eq_zero_iff, hx, norm_eq_zero, or_self,
      not_false_eq_true])

theorem realSign_mul (x y : ℝˣ) : realSign (x * y) = realSign x * realSign y := by
  ext
  simp only [realSign, Units.val_mk0, Units.val_mul, norm_mul]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring

def realCharFun (u : ℂ) (a : ZMod 2) : ℝˣ →* ℂˣ where
  toFun x := Units.mk0 ((‖(x : ℝ)‖ : ℂ) ^ u)
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))))
    * realSign x ^ (a.val : ℕ)
  map_one' := by ext; simp [realSign]
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val, realSign_mul, mul_pow]
    push_cast [norm_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

def realTestFun (a : ZMod 2) : ℝ → ℂ :=
  fun x => ((x : ℂ) ^ (a.val : ℕ)) * Complex.exp (-(π * x ^ 2))

@[simp] theorem realTestFun_zero_apply (x : ℝ) :
    realTestFun 0 x = Complex.exp (-(π * x ^ 2)) := by simp [realTestFun]

theorem realTestFun_zero_at_zero : realTestFun 0 0 = 1 := by simp

theorem realTestFun_zero_ne_zero : realTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def realZeta (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((‖x‖ : ℂ) ^ (s - 1)) ∂μ

def realGammaAt (μ : Measure ℝ) (ψ : AddChar ℝ ℂ) (f₀ : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  realZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / realZeta μ f₀ χ s

end LanglandsTunnell.ArchPlace


