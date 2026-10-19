-- Prove2me | Definitions.Def_ArtinHeckeSModel
-- name    : ArtinHeckeSModel
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T08:39:06.586134+00:00
-- url     : https://prove2.me/theorems/0a769a0a-4ec1-4be8-889d-e3a137365d59
-- title:
--   A model of F_S^× modulo principal units at S, with log-moduli, arguments and finite parts, for §§3 and 5 of OpenAI's Primitive roots paper
-- statement:
--   Objects for §3 (p. 9) and §5.3 (p. 23) of OpenAI, *Primitive roots for every admissible integer base* (2026). They are built on the bundle `Def_ArtinHeckeTheta` (`placesOf 𝔪`, `SInt 𝔪`). Here $F$ is a number field, $\mathfrak m$ is an ideal of $\mathcal O_F$, $k \ge 0$ is a natural number, $|\cdot|_v$ = `NumberField.HeightOneSpectrum.adicAbv F v` is the $v$-adic absolute value normalized by $|x|_v = (\mathrm N v)^{-\operatorname{ord}_v x}$, and $W$ is the set of infinite places of $F$.
--
--   - `adicAbv_eq_one_of_sub_lt`: if $|x - 1|_v < 1$ then $|x|_v = 1$. `absNorm_zpow_neg_lt_one`: $(\mathrm N v)^{-(k+1)} < 1$. These two lemmas are used to build the definitions below.
--   - `SLevel 𝔪 k`: the subgroup of $F^\times$ of the $x$ with $|x - 1|_v \le (\mathrm N v)^{-(k+1)}$ for every $v$ in `placesOf 𝔪`.
--   - `SFin 𝔪 k`: the quotient $F^\times/$`SLevel 𝔪 k`, written additively (`Additive`), with the measurable space in which every set is measurable. `SFin.mk 𝔪 k x` is the class of $x \in F^\times$.
--   - `SFin.norm y`: for the class $y$ of $x$, the finite product $\prod_{v \in \texttt{placesOf } \mathfrak m}|x|_v$ (`finprod`); it does not depend on the representative.
--   - `SModel 𝔪 k`: the triples $(x, \theta, y)$ with $x : W \to \mathbb R$, $\theta : W \to \mathbb R/2\pi\mathbb Z$ (`AddCircle (2 * Real.pi)`) and $y \in$ `SFin 𝔪 k`, with the componentwise addition.
--   - `sEmb 𝔪 k a` for $a \in F$: $0$ if $a = 0$, and otherwise the triple $\big(w \mapsto m_w\log w(a),\ w \mapsto \arg \sigma_w(a) \bmod 2\pi,\ \texttt{SFin.mk}\ a\big)$, where $w(a)$ is the absolute value at $w$, $m_w$ = `w.mult` its multiplicity, and $\sigma_w$ = `w.embedding`.
--   - `SFinCls 𝔪 k`: the quotient of `SFin 𝔪 k` by its subgroup of multiples of $6$.
--
--   In the paper's notation, with $S$ the complex places together with `placesOf 𝔪`, `SModel 𝔪 k` stands for $F_S^\times/\prod_{v \in S_f}(1 + \mathfrak p_v^{k+1})$: for $y \in F_S^\times$ it records $\log|y_w|_w$ (with $|y_w|_w$ the square of the ordinary modulus), $\arg y_w$ and the finite part. `sEmb` is the diagonal embedding of $F^\times$, and `SFinCls 𝔪 k` stands for $\mathcal V = F_S^\times/F_S^{\times 6}$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 9: “On $\mathcal V = F_S^\times/F_S^{\times6}$ define $H_S(x, y) = \prod_{v\in S}(x_v, y_v)_{6,v}$, and let $E$ be the image of $U_S$ in $\mathcal V$.” and p. 23: “Recall that $r = \#S_\infty = [F : \mathbb Q]/2$, and define $X_u = \{y \in F_S^\times : |y|_S = u\}$ $(u > 0)$.”
--
--   **Formalization note.** No completions are used: the finite part is $F^\times$ modulo the congruence subgroup `SLevel 𝔪 k`, in place of $\prod_{v \in S_f}F_v^\times/(1 + \mathfrak p_v^{k+1})$.
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 9, 23, §§3, 5.3 (a model of F_S^× modulo principal units at S, its diagonal embedding of F^×, the finite norm, and 𝒱 = F_S^×/F_S^{×6})

import Mathlib
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F]

theorem adicAbv_eq_one_of_sub_lt {v : HeightOneSpectrum (𝓞 F)} {x : F}
    (h : NumberField.HeightOneSpectrum.adicAbv F v (x - 1) < 1) :
    NumberField.HeightOneSpectrum.adicAbv F v x = 1 := by
  have h1 := NumberField.HeightOneSpectrum.adicAbv_add_le_max F v (x - 1) 1
  have h2 := NumberField.HeightOneSpectrum.adicAbv_add_le_max F v x (-(x - 1))
  rw [sub_add_cancel, map_one] at h1
  rw [show x + -(x - 1) = 1 by ring, map_one, AbsoluteValue.map_neg] at h2
  refine le_antisymm (h1.trans (max_le h.le le_rfl)) ?_
  rcases le_max_iff.1 h2 with h' | h'
  · exact h'
  · exact absurd (h'.trans_lt h) (lt_irrefl _)

theorem absNorm_zpow_neg_lt_one (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1)) < 1 := by
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact zpow_lt_one_of_neg₀ hq (by omega)

def SLevel (𝔪 : Ideal (𝓞 F)) (k : ℕ) : Subgroup Fˣ where
  carrier := {x | ∀ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v ((x : F) - 1) ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1))}
  one_mem' := by
    intro v _
    simp only [Units.val_one, sub_self, map_zero]
    positivity
  mul_mem' := by
    intro x y hx hy v hv
    have hx1 := adicAbv_eq_one_of_sub_lt ((hx v hv).trans_lt (absNorm_zpow_neg_lt_one v k))
    have hxy : ((x * y : Fˣ) : F) - 1 = (x : F) * ((y : F) - 1) + ((x : F) - 1) := by
      push_cast; ring
    rw [hxy]
    refine (NumberField.HeightOneSpectrum.adicAbv_add_le_max F v _ _).trans (max_le ?_ (hx v hv))
    rw [map_mul, hx1, one_mul]
    exact hy v hv
  inv_mem' := by
    intro x hx v hv
    have hx1 := adicAbv_eq_one_of_sub_lt ((hx v hv).trans_lt (absNorm_zpow_neg_lt_one v k))
    have hx0 : (x : F) ≠ 0 := x.ne_zero
    have : ((x⁻¹ : Fˣ) : F) - 1 = -((x : F) - 1) * (x : F)⁻¹ := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [this, map_mul, AbsoluteValue.map_neg, map_inv₀, hx1, inv_one, mul_one]
    exact hx v hv

def SFin (𝔪 : Ideal (𝓞 F)) (k : ℕ) : Type _ := Additive (Fˣ ⧸ SLevel 𝔪 k)

noncomputable instance (𝔪 : Ideal (𝓞 F)) (k : ℕ) : AddCommGroup (SFin 𝔪 k) :=
  inferInstanceAs (AddCommGroup (Additive (Fˣ ⧸ SLevel 𝔪 k)))

instance (𝔪 : Ideal (𝓞 F)) (k : ℕ) : MeasurableSpace (SFin 𝔪 k) := ⊤

def SFin.mk (𝔪 : Ideal (𝓞 F)) (k : ℕ) (x : Fˣ) : SFin 𝔪 k :=
  Additive.ofMul (QuotientGroup.mk x)

noncomputable def SFin.norm {𝔪 : Ideal (𝓞 F)} {k : ℕ} (y : SFin 𝔪 k) : ℝ :=
  Quotient.liftOn' (Additive.toMul y)
    (fun x : Fˣ => ∏ᶠ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v (x : F)) (by
      intro x y hxy
      have hmem : x⁻¹ * y ∈ SLevel 𝔪 k := QuotientGroup.leftRel_apply.mp hxy
      refine finprod_mem_congr rfl fun v hv => ?_
      set u : Fˣ := x⁻¹ * y
      have hu1 := adicAbv_eq_one_of_sub_lt ((hmem v hv).trans_lt (absNorm_zpow_neg_lt_one v k))
      have : (y : F) = (x : F) * (u : F) := by
        simp only [u, Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
      rw [this, map_mul, hu1, mul_one])

abbrev SModel (𝔪 : Ideal (𝓞 F)) (k : ℕ) : Type _ :=
  (InfinitePlace F → ℝ) × (InfinitePlace F → AddCircle (2 * Real.pi)) × SFin 𝔪 k

open Classical in
noncomputable def sEmb (𝔪 : Ideal (𝓞 F)) (k : ℕ) (x : F) : SModel 𝔪 k :=
  if hx : x = 0 then 0 else
    (fun w => (w.mult : ℝ) * Real.log (w x),
      fun w => ((Complex.arg (w.embedding x) : ℝ) : AddCircle (2 * Real.pi)), SFin.mk 𝔪 k (Units.mk0 x hx))

abbrev SFinCls (𝔪 : Ideal (𝓞 F)) (k : ℕ) : Type _ :=
  SFin 𝔪 k ⧸ (nsmulAddMonoidHom 6 : SFin 𝔪 k →+ SFin 𝔪 k).range

end ArtinPrimitiveRoots


