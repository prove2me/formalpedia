-- Prove2me | Definitions.Def_ArtinKPB004
-- name    : ArtinKPB004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:10.943451+00:00
-- url     : https://prove2.me/theorems/28b49223-16e8-44f3-a968-aa5deda3f0ff
-- title:
--   Definitions bundle ArtinKPB004 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 15 declarations of that development: 6 definitions, 1 inductive type or structure and 8 theorems. The definitions and types are `ArtinKP.S2.Coc`, `ArtinKP.S2.IsSteinbergSymbol`, `ArtinKP.S2.cj00`, `ArtinKP.S2.cj01`, `ArtinKP.S2.cj10`, `ArtinKP.S2.cj11`, `ArtinKP.S2.tS`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.S2_Cocycle`, `KP.S2_Sig`, `KP.S_Basic`.
--
--   **Imports.** It imports the published bundles `Def_ArtinHeckeProbe`, `Def_ArtinHeckeSModel`, `Def_ArtinHeckeTheta`, `Def_DedekindDomain_Completion_BaseChange`, `Def_ExtCitation_LocalLevelResidues`, `Def_IsDedekindDomain_FiniteUnitIdeles`, `Def_IsDedekindDomain_FiniteUnitIdelesOutside`, `Def_LanglandsTunnell_ArtinCoreCTM`, `Def_M4aHerbrand_GenuineDescent`, `Def_M4aHerbrand_IdeleClassVocab`, `Def_M4aHerbrand_SIdeleClassGroup`, `Def_NormIndex_AdmissibleExpOfDegree`, `Def_NumberField_ArchimedeanIdeleModule` and `Def_NumberField_PlaceDecompositionAction`; the bundle `ArtinKPB002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB015`; the statement `ArtinKP.S2.exists_level_sig_mul_sig_conj_eq`; the proof of `ArtinKP.S2.exists_level_sig_mul_sig_conj_eq`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ArtinKPB002

section
-- module Solutions.Artin.KP.S2_Cocycle
attribute [-simp] _root_.ArtinKP.S.Xs_zero
/-!
# WP-S2, part 1: Kubota's cocycle identity for a Steinberg symbol

`F` is any field and `t : Fˣ → Fˣ → A` a bi-additive symbol with `t a (-a) = 0`, `t (-1) a = 0`
and the Steinberg relation `a + b = 1 → t a b = 0` (`IsSteinbergSymbol`; no valuation, no
tameness).  With `X(c, d) = c` if `c ≠ 0`, else `d`, and for a row `p` and a matrix `h`

  `σ(p, h) = t (X(ph)/X(p)) (X(ph)/X(h))`     (`X(h)` = `X` of the bottom row),

`cocycle_scalar` is Kubota's 2-cocycle identity on all of `SL₂(F)`, in row form:

  `σ(p, h) + σ(ph, k) = σ(p, hk) + σ(bot h, k)`.

Proof.  Put `P = (p₂, -p₁)ᵀ`, `E = e₁`, `A = h e₁`, `B = hk e₁`.  The six `X`-values are the
"brackets" `[U, V] = U ∧ V` (or the ratio `U/V` when `U ∥ V`) of the four vectors, and the
identity is the 4-point relation

  `t([P,A]/[P,E], [P,A]/[E,A]) + t([P,B]/[P,A], [P,B]/[A,B])
      = t([P,B]/[P,E], [P,B]/[E,B]) + t([E,B]/[E,A], [E,B]/[A,B])`.

In general position it is *equivalent* (by bi-additivity, `t x x = 0`, skew-symmetry) to the
Steinberg relation for the Plücker identity `[P,E][A,B] + [P,B][E,A] = [P,A][E,B]`
(`coc_generic`); the eight degenerate configurations are bi-additive identities.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A

variable {F : Type*} [Field F] {A : Type*} [AddCommGroup A]

/-- A bi-additive Steinberg symbol on `Fˣ` with `t a (-a) = 0` and `t (-1) a = 0`. -/
structure IsSteinbergSymbol (t : Fˣ → Fˣ → A) : Prop where
  mul_left : ∀ a b c : Fˣ, t (a * b) c = t a c + t b c
  mul_right : ∀ a b c : Fˣ, t a (b * c) = t a b + t a c
  steinberg : ∀ a : Fˣ, t a (-a) = 0
  neg_one_left : ∀ a : Fˣ, t (-1) a = 0
  add_eq_one : ∀ a b : Fˣ, (a : F) + b = 1 → t a b = 0

/-- The 4-point relation for six bracket values. -/
def Coc (t : Fˣ → Fˣ → A) (x x₁ x₂ y y₁ z : F) : Prop :=
  tz t (x₁ / x) (x₁ / y) + tz t (x₂ / x₁) (x₂ / z) = tz t (x₂ / x) (x₂ / y₁) + tz t (y₁ / y) (y₁ / z)

theorem Xs_ne {c : F} (d : F) (hc : c ≠ 0) : Xs c d = c := by
  simp [Xs, hc]

theorem Xs_zero_left (d : F) : Xs 0 d = d := by simp [Xs]

theorem Xs_smul {l : F} (hl : l ≠ 0) (c d : F) : Xs (l * c) (l * d) = l * Xs c d := by
  by_cases hc : c = 0
  · simp [hc, Xs_zero_left]
  · rw [Xs_ne _ hc, Xs_ne _ (mul_ne_zero hl hc)]

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 1: `S_f`-adic smallness, norms, the pairing `⟨·,·⟩` on `F`, rows of `SL₂(R)`

* `Small 𝔪 N x`: `v(x) ≤ exp(-N)` at every `v ∣ 𝔪` (`N : ℤ`; `N < 0` means "bounded").
* `absS 𝔪 x = |x|_{S_f}`, `normS 𝔪 c d = ‖(c,d)‖ = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`.
* `brk ι P 𝔪 x y = ⟨x, y⟩ = ι (x, y)_S` for `x, y ≠ 0`, and `1` if `x = 0` or `y = 0`.
  With WP-A's orientation `⟨c, d⟩ = (d/c)(c/d)⁻¹` on coprime elements of `R` (`brk_reciprocity`).
* `sig`: Kubota's `σ_S` evaluated on a pair and a matrix, through `ι`.
* `Row 𝔪`: primitive pairs of `R = SInt 𝔪`; right action of `SL₂(R)`; scaling by `Rˣ`;
  `kappaRow` and its transformation laws (`kappaRow_act` is Lemma A5 on rows).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-! ### Smallness at the places of `S_f` -/

/-! ### Absolute values at `S_f` -/

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

section brk

variable {ι : F →+* ℂ} {P : CubicPkg F} {𝔪 : Ideal (𝓞 F)}

theorem brk_mul_left {x x' : F} (y : F) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    brk ι P 𝔪 (x * x') y = brk ι P 𝔪 x y * brk ι P 𝔪 x' y := by
  by_cases hy : y = 0
  · simp [hy]
  lift x to Fˣ using IsUnit.mk0 x hx
  lift x' to Fˣ using IsUnit.mk0 x' hx'
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [← Units.val_mul, brk_units, brk_units, brk_units, map_mul, MonoidHom.mul_apply, map_mul]

theorem brk_mul_right (x : F) {y y' : F} (hy : y ≠ 0) (hy' : y' ≠ 0) :
    brk ι P 𝔪 x (y * y') = brk ι P 𝔪 x y * brk ι P 𝔪 x y' := by
  by_cases hx : x = 0
  · simp [hx]
  lift x to Fˣ using IsUnit.mk0 x hx
  lift y to Fˣ using IsUnit.mk0 y hy
  lift y' to Fˣ using IsUnit.mk0 y' hy'
  rw [← Units.val_mul, brk_units, brk_units, brk_units, map_mul, map_mul]

theorem brk_inv_right (x y : F) : brk ι P 𝔪 x y⁻¹ = (brk ι P 𝔪 x y)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  lift x to Fˣ using IsUnit.mk0 x hx
  lift y to Fˣ using IsUnit.mk0 y hy
  rw [← Units.val_inv_eq_inv_val, brk_units, brk_units, map_inv, iota3_inv]

/-- Deep units lie in the radical (right slot). -/
theorem brk_deep_right (hG : Good 𝔪) {N : ℕ} (hN : P.IsDeepLevel 𝔪 N) (x : F) {y : F}
    (hy : Small 𝔪 N (y - 1)) : brk ι P 𝔪 x y = 1 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  lift x to Fˣ using IsUnit.mk0 x hx0
  lift y to Fˣ using IsUnit.mk0 y hy0
  rw [brk_units, P.HS_deep_right hG.ne_bot hN x y fun v hv => hy v hv, map_one]

/-- Deep units lie in the radical (left slot). -/
theorem brk_deep_left (hG : Good 𝔪) {N : ℕ} (hN : P.IsDeepLevel 𝔪 N) {x : F} (y : F)
    (hx : Small 𝔪 N (x - 1)) : brk ι P 𝔪 x y = 1 := by
  rw [brk_skew, brk_deep_right hG hN y hx, inv_one]

end brk

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-! ### Primitive rows -/

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S2_Sig
/-!
# WP-S2, part 2: Kubota's cocycle identity for `σ_S` on `SL₂(F)`

* `isSteinberg`: `(·,·)_S` is a Steinberg symbol in the sense of `S2_Cocycle`.
* `sig_cocycle`: `σ_S(p, h) σ_S(ph, k) = σ_S(p, hk) σ_S(bot h, k)` for every non-zero pair
  `p ∈ F²` and all `h, k ∈ SL₂(F)` (no integrality, no depth).
* `sigmaS_cocycle`: the same on `Matrix.SpecialLinearGroup (Fin 2) F`.
* `sig_smul`: `σ_S(lp, h) = σ_S(p, h) ⟨X(ph)/X(p), l⟩`.
* `sig_conj`: for `σ ∈ SL₂(F)` and `k` deep enough (depending on `σ`),
  `σ_S(bot σ, σ⁻¹kσ) = σ_S(bot k, σ)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- `(·,·)_S`, additively. -/
def tS (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) : Fˣ → Fˣ → Additive (rootsOfUnity 3 F) :=
  fun a b => Additive.ofMul (P.HS 𝔪 a b)

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- The entries of `σ⁻¹ k σ`, `σ = [[α,β],[γ,δ]]`, `k = [[a,b],[c',d']]`. -/
def cj00 (α β γ δ a b c' d' : F) : F := δ * (a * α + b * γ) - β * (c' * α + d' * γ)
/-- upper right entry of `σ⁻¹ k σ` -/
def cj01 (α β γ δ a b c' d' : F) : F := δ * (a * β + b * δ) - β * (c' * β + d' * δ)
/-- lower left entry of `σ⁻¹ k σ` -/
def cj10 (α β γ δ a b c' d' : F) : F := -γ * (a * α + b * γ) + α * (c' * α + d' * γ)
/-- lower right entry of `σ⁻¹ k σ` -/
def cj11 (α β γ δ a b c' d' : F) : F := -γ * (a * β + b * δ) + α * (c' * β + d' * δ)

end ArtinKP.S2
end
end


