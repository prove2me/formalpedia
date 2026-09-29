-- Prove2me | Definitions.Def_AutomorphicForm_WeylSelectors
-- name    : AutomorphicForm_WeylSelectors
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c89c3d89-0657-5861-83b9-fc5fbf5eb8a6
-- title:
--   Adelic selector idempotents, units and Haar modulus
-- statement:
--   Over a number field $F$ with adele ring $\mathbb{A}=\mathbb{A}_\infty\times\mathbb{A}_f$, this module sets up a placewise "big part" decomposition of an adele and the Haar-measure modulus attached to it. First, for four elements $\varepsilon,y,z,x$ of a commutative ring $A$ the structure `SelRel` records four equations as fields: $\varepsilon^2=\varepsilon$, $yz=1$, $(1-\varepsilon)y=1-\varepsilon$ and $\varepsilon y=\varepsilon x$. From such data `yUnit` produces the element $y$ as a unit of $A$, with inverse $\varepsilon z+(1-\varepsilon)$; `coe_yUnit` and `coe_yUnit_inv` identify the underlying element and its inverse. Secondly, an infinite place $w$ is declared big for $a\in\mathbb{A}_\infty$ when $\|a_w\|>1$ (`BigInf`), and a finite place $v$ big for $b\in\mathbb{A}_f$ when $b_v\notin\mathcal{O}_v$ (`BigFin`); auxiliary lemmas show that a big component is nonzero and that at a big finite place $b_v^{-1}$ is integral. Using `toAdele'` (pairing an infinite and a finite adele) and `finOfIntegral` (assembling a finite adele from a placewise family that is integral at every finite place), one defines, for $a\in\mathbb{A}_\infty$ and $b\in\mathbb{A}_f$: the idempotent `selE`, with component $1$ at the big places and $0$ elsewhere; `selY`, with component $a_w$ resp. $b_v$ at the big places and $1$ elsewhere; and `selZ`, with component $a_w^{-1}$ resp. $b_v^{-1}$ at the big places and $1$ elsewhere. The theorem `selRel` asserts that these four data, together with the adele $(a,b)$, satisfy `SelRel`, so `selY` is a unit of $\mathbb{A}$. Further, `intLattice` is $\prod_v\mathcal{O}_v$ as an additive subgroup of $\mathbb{A}_f$, `dilate` its image under multiplication by a finite idele $y$ (identified with $y\cdot\prod_v\mathcal{O}_v$ in `coe_dilate`), and `finPart` the finite part of a unit of $\mathbb{A}$ as a unit of $\mathbb{A}_f$. Finally, `Dy x` is the real number given by the distributive Haar character of $\mathbb{A}$ evaluated at the unit built from the selectors of $x$, i.e. the factor by which multiplication by the big part of $x$ scales an additive Haar measure. Elementary placewise rewriting lemmas for products, differences, $1$ and extensionality of adeles accompany these definitions.
--
--   **Relation to Mathlib.** The predicate `SelRel` and the selector constructions are the project's own; `Dy` is expressed through Mathlib's `distribHaarChar`, and `intLattice` packages the project's set `integralFiniteAdeles` as an additive subgroup.
--
--   **Where it is used.** The vocabulary is used by statements about automorphic forms on $\mathrm{GL}_2$ over the adeles, where functions are estimated along the big Bruhat cell in terms of the modulus $D(x)$ of the big part of an adele $x$, and where the dilated lattice attached to the finite part of $x$ is identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WeylSelectors.lean

import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical Pointwise

namespace AutomorphicForm.WeylIntegrable

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}

structure SelRel (ε y z x : A) : Prop where
  idem : ε * ε = ε
  yz : y * z = 1
  small : (1 - ε) * y = 1 - ε
  big : ε * y = ε * x

def yUnit (h : SelRel ε y z x) : Aˣ :=
  ⟨y, ε * z + (1 - ε), by linear_combination ε * h.yz + h.small, by linear_combination ε * h.yz + h.small⟩

@[simp] theorem coe_yUnit (h : SelRel ε y z x) : (yUnit h : A) = y := rfl
theorem coe_yUnit_inv (h : SelRel ε y z x) : (((yUnit h)⁻¹ : Aˣ) : A) = ε * z + (1 - ε) := rfl

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def toAdele' (a : 𝔸∞) (b : 𝔸f) : 𝔸 := (a, b)

def finOfIntegral (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : 𝔸f :=
  show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk f (.of_forall hf)

@[simp] theorem finOfIntegral_apply (f : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : finOfIntegral F f hf v = f v := rfl

def BigInf (a : 𝔸∞) (w : InfinitePlace F) : Prop := 1 < ‖a w‖

def BigFin (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : Prop := b v ∉ v.adicCompletionIntegers F

omit [NumberField F] in
theorem ne_zero_of_bigInf {a : 𝔸∞} {w : InfinitePlace F} (h : BigInf F a w) : a w ≠ 0 := by
  intro h0; rw [BigInf, h0, norm_zero] at h; exact (not_lt.mpr zero_le_one) h

theorem one_lt_valued_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : 1 < Valued.v (b v) := by
  rw [BigFin, HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at h; exact h

theorem ne_zero_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : b v ≠ 0 := by
  intro h0; have := one_lt_valued_of_bigFin F h; rw [h0, map_zero] at this; exact (not_lt.mpr zero_le_one) this

theorem inv_mem_of_bigFin {b : 𝔸f} {v : HeightOneSpectrum (𝓞 F)} (h : BigFin F b v) : (b v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact ((Valuation.one_lt_val_iff _ (ne_zero_of_bigFin F h)).mp (one_lt_valued_of_bigFin F h)).le

def selE (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then 1 else 0)
  (finOfIntegral F (fun v => if BigFin F b v then 1 else 0) fun v => by split_ifs <;> simp [one_mem, zero_mem])

def selZ (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then (a w)⁻¹ else 1)
  (finOfIntegral F (fun v => if BigFin F b v then (b v)⁻¹ else 1) fun v => by
    split_ifs with h
    · exact inv_mem_of_bigFin F h
    · exact one_mem _)

def selY (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then a w else 1)
  (show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from
    RestrictedProduct.mk (fun v => if BigFin F b v then b v else 1)
      ((show RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite from b).eventually.mono
        fun v hv => by
          rw [if_neg (show ¬ BigFin F b v from not_not.mpr hv)]
          exact one_mem _))

theorem selE_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selE F a b).1 w = if BigInf F a w then 1 else 0 := rfl
theorem selE_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selE F a b).2 v = if BigFin F b v then 1 else 0 := rfl
theorem selY_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selY F a b).1 w = if BigInf F a w then a w else 1 := rfl
theorem selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selY F a b).2 v = if BigFin F b v then b v else 1 := rfl
theorem selZ_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : (selZ F a b).1 w = if BigInf F a w then (a w)⁻¹ else 1 := rfl
theorem selZ_snd (a : 𝔸∞) (b : 𝔸f) (v : HeightOneSpectrum (𝓞 F)) : (selZ F a b).2 v = if BigFin F b v then (b v)⁻¹ else 1 := rfl
theorem toAdele'_fst (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).1 = a := rfl
theorem toAdele'_snd (a : 𝔸∞) (b : 𝔸f) : (toAdele' F a b).2 = b := rfl

theorem mul_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u * u').1 w = u.1 w * u'.1 w := rfl
theorem mul_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u * u').2 v = u.2 v * u'.2 v := rfl
theorem sub_fst_apply (u u' : 𝔸) (w : InfinitePlace F) : (u - u').1 w = u.1 w - u'.1 w := rfl
theorem sub_snd_apply (u u' : 𝔸) (v : HeightOneSpectrum (𝓞 F)) : (u - u').2 v = u.2 v - u'.2 v := rfl
theorem one_fst_apply (w : InfinitePlace F) : (1 : 𝔸).1 w = 1 := rfl
theorem one_snd_apply (v : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸).2 v = 1 := rfl

theorem adele_ext {u u' : 𝔸} (h1 : ∀ w, u.1 w = u'.1 w) (h2 : ∀ v, u.2 v = u'.2 v) : u = u' :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

theorem selRel (a : 𝔸∞) (b : 𝔸f) : SelRel (selE F a b) (selY F a b) (selZ F a b) (toAdele' F a b) where
  idem := adele_ext F (fun w => by rw [mul_fst_apply, selE_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, selE_snd]; split_ifs <;> simp)
  yz := adele_ext F
    (fun w => by
      rw [mul_fst_apply, selY_fst, selZ_fst, one_fst_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigInf F h)
      · exact mul_one 1)
    (fun v => by
      rw [mul_snd_apply, selY_snd, selZ_snd, one_snd_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (ne_zero_of_bigFin F h)
      · exact mul_one 1)
  small := adele_ext F
    (fun w => by rw [mul_fst_apply, sub_fst_apply, one_fst_apply, selE_fst, selY_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, sub_snd_apply, one_snd_apply, selE_snd, selY_snd]; split_ifs <;> simp)
  big := adele_ext F
    (fun w => by rw [mul_fst_apply, mul_fst_apply, selE_fst, selY_fst, toAdele'_fst]; split_ifs <;> simp)
    (fun v => by rw [mul_snd_apply, mul_snd_apply, selE_snd, selY_snd, toAdele'_snd]; split_ifs <;> simp)

end Adelic

section Lattice

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def intLattice : AddSubgroup 𝔸f where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' hx hy := fun v => add_mem (hx v) (hy v)
  neg_mem' hx := fun v => neg_mem (hx v)

@[simp] theorem coe_intLattice : (intLattice F : Set 𝔸f) = integralFiniteAdeles (𝓞 F) F := rfl

def dilate (y : (𝔸f)ˣ) : AddSubgroup 𝔸f := (intLattice F).map (DistribSMul.toAddMonoidHom 𝔸f (y : 𝔸f))

theorem coe_dilate (y : (𝔸f)ˣ) : (dilate F y : Set 𝔸f) = (y : 𝔸f) • integralFiniteAdeles (𝓞 F) F := by
  ext z; simp [dilate, Set.mem_smul_set]

theorem snd_mul (x y : 𝔸) : (x * y).2 = x.2 * y.2 := rfl

def finPart (Y : (𝔸)ˣ) : (𝔸f)ˣ where
  val := (Y : 𝔸).2
  inv := ((Y⁻¹ : (𝔸)ˣ) : 𝔸).2
  val_inv := by rw [← snd_mul, Units.mul_inv]; rfl
  inv_val := by rw [← snd_mul, Units.inv_mul]; rfl

end Lattice

section Modulus

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def Dy (x : 𝔸) : ℝ := (distribHaarChar 𝔸 (yUnit (selRel F x.1 x.2)) : ℝ)

end Modulus

end AutomorphicForm.WeylIntegrable

end


