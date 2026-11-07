-- Prove2me | Definitions.Def_ModFormPIR_CharForms
-- name    : ModFormPIR_CharForms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:00:00.011364+00:00
-- url     : https://prove2.me/theorems/afb01fa1-5d34-4e10-b070-382cfbeccc89
-- title:
--   Modular forms for $\Gamma(q)$ with a character, and their orders at cusps
-- statement:
--   A holomorphic $f:\mathbb H\to\mathbb C$ is **weakly modular of weight $k$ for $\Gamma(q)$ with a finite-order character** if $f(g*\tau)=\chi(g)G(g,\tau)^kf(\tau)$ on $\Gamma(q)$, for a character $\chi$ with $\chi^j=1$, some $j\ge1$.
--
--   For $g\in SL_2(\mathbb Z)$ put $f_g(\tau)=G(g,\tau)^{-k}f(g*\tau)$. The **order at the cusp** $g*\infty$ is the supremum, in the extended reals, of the real $r$ such that $f_g(\tau)e^{-2\pi ir\tau/q}$ is bounded as $\operatorname{Im}\tau\to\infty$; $f$ is **holomorphic at the cusp** if $r=0$ qualifies, and a **modular form** if this holds at every cusp. The **classes of cusps** are the first columns of $g$ modulo $q$, up to sign.
--
--   **Formalization Note** The paper defines the order from the Fourier expansion in $e^{2\pi i\tau/q}$ with exponents $n+\alpha$. For a scalar with a finite-order character, the leading exponent is the supremum above, and $f=0$ has order $+\infty$. The sanity file proves that the order of the discriminant at $\infty$ is $q$, its exact leading exponent in these units.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Definitions 10.19, 10.25, 10.27, 10.29, 10.33, pp.43–48; Proposition 12.23, p.71

import Mathlib
import Definitions.Def_ModFormPIR_Weil

open Complex Matrix
open scoped UpperHalfPlane
open scoped MatrixGroups Real

set_option autoImplicit false

namespace ModFormPIR

/-!
# Scalar modular forms for `Γ(q)` with a finite-order character, and their orders at cusps

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Definitions 10.19, 10.25, 10.27, 10.29, 10.33, pp.43–48; Proposition 12.23,
p.71.

**Formalization Note.**
* *Cusp order.* The paper defines `ord_∞` from the Fourier expansion in `e^{2πiτ/h}`, twisted by the eigenvalue of
  `ρ(T^h)`. Here the width is `h = q` (Proposition 12.23), and for a scalar with a finite-order character the order is
  the analytic form: `ord_g f` is the supremum in `EReal` of the real `r` such that `f_g(τ) e^{-2πirτ/q}` is bounded
  as `Im τ → ∞`, where `f_g(τ) = G(g,τ)^{-k} f(g∗τ)`. For a series with exponents `n + α` the supremum is the leading
  exponent, and `f = 0` has order `⊤`, as in (25). The sanity file checks the normalization on an explicit form.
* *Holomorphy at a cusp* is `r = 0` in the same test: `f_g` is bounded as `Im τ → ∞`, i.e. no negative exponents.
* *Cusps.* A cusp is `g∗∞`, named by `g ∈ SL₂(ℤ)`; its `Γ(q)`-class is the first column of `g` modulo `q`, up to sign
  (Proposition 12.23).
-/

variable (q : ℕ)

/-- `f : ℍ → ℂ` is holomorphic. -/
def IsHolo (f : ℍ → ℂ) : Prop :=
  DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im}

/-- Definition 10.19 for `N = 1`, with Lemma 10.20's form of finite order: `f` is holomorphic and
`f(g∗τ) = χ(g) G(g,τ)^k f(τ)` on `Γ(q)` for a character `χ` with `χ^j = 1`, some `j ≥ 1`. -/
def IsWeaklyModularChar (k : ℕ) (f : ℍ → ℂ) : Prop :=
  IsHolo f ∧ ∃ χ : CongruenceSubgroup.Gamma q →* ℂˣ, (∃ j : ℕ, 0 < j ∧ χ ^ j = 1) ∧
    ∀ (g : CongruenceSubgroup.Gamma q) (τ : ℍ),
      f ((g : SL(2, ℤ)) • τ) = (χ g : ℂ) * denomG (g : SL(2, ℤ)) τ ^ k * f τ

/-- (26): `f_g(τ) = G(g,τ)^{-k} f(g∗τ)`. -/
noncomputable def slashG (k : ℕ) (f : ℍ → ℂ) (g : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  (denomG g τ ^ k)⁻¹ * f (g • τ)

/-- `F(τ) e^{-2πirτ/q}` is bounded as `Im τ → ∞`, with `F` a function on `ℍ`. -/
def BoundedAtScale (F : ℍ → ℂ) (r : ℝ) : Prop :=
  ∃ C A : ℝ, ∀ τ : ℍ, A ≤ τ.im → ‖F τ * exp (-(2 * π * I * r * τ / q))‖ ≤ C

/-- `ord_{g∗∞}(f)`, in units of `e^{2πiτ/q}` (width `q`), in `EReal`. -/
noncomputable def cuspOrd (k : ℕ) (f : ℍ → ℂ) (g : SL(2, ℤ)) : EReal :=
  sSup ((fun r : ℝ => (r : EReal)) '' {r : ℝ | BoundedAtScale q (slashG k f g) r})

/-- `f` is holomorphic at the cusp `g∗∞`. -/
def IsHolomorphicAtCusp (k : ℕ) (f : ℍ → ℂ) (g : SL(2, ℤ)) : Prop :=
  BoundedAtScale q (slashG k f g) 0

/-- Definition 10.29: a scalar modular form of weight `k` for `Γ(q)` with a one-dimensional representation of finite
order. -/
def IsModularFormChar (k : ℕ) (f : ℍ → ℂ) : Prop :=
  IsWeaklyModularChar q k f ∧ ∀ g : SL(2, ℤ), IsHolomorphicAtCusp q k f g

/-- The first column of `g` modulo `q`, which names the cusp `g∗∞`. -/
def firstColumn (g : SL(2, ℤ)) : ZMod q × ZMod q :=
  (((g 0 0 : ℤ) : ZMod q), ((g 1 0 : ℤ) : ZMod q))

/-- `g∗∞` and `h∗∞` are `Γ(q)`-equivalent: their first columns agree modulo `q` up to sign (Proposition 12.23). -/
def cuspSetoid : Setoid SL(2, ℤ) where
  r g h := firstColumn q g = firstColumn q h ∨ firstColumn q g = -firstColumn q h
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        rintro g h (h1 | h1)
        · exact Or.inl h1.symm
        · exact Or.inr (by rw [h1, neg_neg])
      trans := by
        rintro g h l (h1 | h1) (h2 | h2)
        · exact Or.inl (h1.trans h2)
        · exact Or.inr (h1.trans h2)
        · exact Or.inr (by rw [h1, h2])
        · exact Or.inl (by rw [h1, h2, neg_neg]) }

/-- The `Γ(q)`-equivalence classes of cusps. -/
abbrev CuspClass : Type := Quotient (cuspSetoid q)

/-- The `Γ(q)`-orbits of points of `ℍ`. -/
abbrev PointClass : Type := MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma q) ℍ

/-- Definition 10.33: the order of vanishing of `f` at `τ₀`, as a natural (`0` for `f` flat there, a case
excluded by `f ≢ 0`). -/
noncomputable def pointOrd (f : ℍ → ℂ) (τ₀ : ℍ) : ℕ :=
  (analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ)).toNat

end ModFormPIR


