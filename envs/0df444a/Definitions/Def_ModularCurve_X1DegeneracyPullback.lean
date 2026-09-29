-- Prove2me | Definitions.Def_ModularCurve_X1DegeneracyPullback
-- name    : ModularCurve_X1DegeneracyPullback
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/e28314ef-d3e6-5d80-8488-5a1a4fd6a152
-- title:
--   Degeneracy pullbacks from J1​(N) to J1​(N′)
-- statement:
--   Fix natural numbers $N$, $N'$, $t$ with $t \neq 0$. The module first records the containment $\Gamma_1(N') \le \Gamma_1(N) \cap \Gamma_0(Nt)$ whenever $Nt \mid N'$ (`Gamma1_le_inf_Gamma0_of_mul_dvd`) and deduces, by the monotonicity of the project's $q$-expansion function fields, the field containment `x1x0FunctionFieldC K N (N * t) ≤ x1FunctionFieldC K N'` inside $K((q))$ for any field $K$. Over a field $L$ containing $\mathbb{Q}$, `laurentBaseChange L` carries an intermediate field of $\mathbb{Q}((q))$ to the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image; this operation is monotone, and the resulting inclusions of base-changed fields are packaged as two $L$-algebra maps: `x1LevelInclBar L h` for $N \mid N'$, the inclusion $L\cdot F(\Gamma_1(N)) \hookrightarrow L\cdot F(\Gamma_1(N'))$, and `x1x0LevelInclBar L t h` for $Nt \mid N'$, the inclusion of $L \cdot F(\Gamma_1(N)\cap\Gamma_0(Nt))$ into $L\cdot F(\Gamma_1(N'))$. Composing the substitution $q \mapsto q^t$ of `heckeBetaOneBar L N t` with the latter gives `x1LevelSubstBar L t h`; on underlying Laurent series it is the identity composed with `heckeBetaOneBar`, and equals $q\mapsto q^{t}$ substitution `qExpand L t` as soon as `HeckeBetaOneDefined N t` holds, i.e. as soon as $q \mapsto q^{t}$ maps $F(\Gamma_1(N))$ into $F(\Gamma_1(N)\cap\Gamma_0(Nt))$.
--
--   The predicate `JOne.DegeneracyPullbackInputs N N' t` asserts the existence of: a divisibility $Nt \mid N'$; `HeckeBetaOneDefined N t`; integrality of the ring homomorphisms underlying `x1LevelInclBar` and `x1LevelSubstBar` over $\overline{\mathbb{Q}}$; the instance `HasPrincipalDivisors` for `x1FunctionFieldBar N'`; and `FundamentalIdentityAlong` for each of the two maps (the hypothesis under which pullback of divisors multiplies degrees by the relative degree, so preserves degree zero). Under these inputs `JOne.degeneracyPullbackPair N N' t` is the pair, indexed by `Fin 2`, of homomorphisms $J_1(N) \to J_1(N')$ obtained as `Pic0.pullbackAlongHom` along `x1LevelInclBar` and along `x1LevelSubstBar`; when the inputs fail it is the zero pair. Auxiliary lemmas introduce the predicate from its components, project out the divisibility and `HeckeBetaOneDefined`, compute the pair under given inputs and record that it vanishes otherwise. Here $J_1(N)$ is the degree-zero divisor class group `Pic0` of the base change to $\overline{\mathbb{Q}}$ of $F(\Gamma_1(N))$, so the two maps play the role of the pullbacks $\pi_1^*$ and $\pi_t^*$ along the degeneracy coverings $X_1(N') \to X_1(N)$ given by $\tau \mapsto \tau$ and $\tau \mapsto t\tau$.
--
--   **Relation to Mathlib.** Mathlib provides the congruence subgroups `CongruenceSubgroup.Gamma0`/`Gamma1`, Laurent series and `IntermediateField.inclusion`; the $q$-expansion function fields, divisors, the degree-zero class group `Pic0` and its functoriality under integral algebra maps are the project's own, as is the notion of degeneracy pullback used here.
--
--   **Where it is used.** The pair of maps defined here realises, on divisor class groups of the Laurent-series function fields, the two degeneracy pullbacks whose images span the $t$-old part of $J_1(N')$; this is the mechanism by which oldforms at level $N'$ are compared with forms of level $N$ in the level-lowering step of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_X1DegeneracyPullback.lean

import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_ShimuraKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups

section PrivateSupply

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem laurentBaseChange_mono₃ {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

end PrivateSupply

section Containments

variable {N N' : ℕ}

theorem Gamma1_le_inf_Gamma0_of_mul_dvd {t : ℕ} (h : N * t ∣ N') :
    Gamma1 N' ≤ Gamma1 N ⊓ Gamma0 (N * t) := by
  refine le_inf (Gamma1_le_of_dvd ((dvd_mul_right N t).trans h)) ?_
  intro A hA
  rw [Gamma1_mem] at hA
  rw [Gamma0_mem]
  have := congrArg (ZMod.castHom h (ZMod (N * t))) hA.2.2
  rwa [map_intCast, map_zero] at this

theorem x1x0FunctionFieldC_le_x1FunctionFieldC_of_mul_dvd (K : Type*) [Field K] {t : ℕ}
    (h : N * t ∣ N') : x1x0FunctionFieldC K N (N * t) ≤ x1FunctionFieldC K N' :=
  qExpFunctionFieldC_mono K (Gamma1_le_inf_Gamma0_of_mul_dvd h)

end Containments

section Embeddings

variable (L : Type*) [Field L] [Algebra ℚ L] {N N' : ℕ}

def x1LevelInclBar (h : N ∣ N') :
    laurentBaseChange L (x1FunctionField N) →ₐ[L] laurentBaseChange L (x1FunctionField N') :=
  IntermediateField.inclusion (laurentBaseChange_mono₃ L (x1FunctionFieldC_le_of_dvd ℚ h))

@[simp]
theorem coe_x1LevelInclBar (h : N ∣ N') (x : laurentBaseChange L (x1FunctionField N)) :
    (x1LevelInclBar L h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem x1LevelInclBar_eq_inclusion (h : N ∣ N')
    (h' : laurentBaseChange L (x1FunctionField N) ≤ laurentBaseChange L (x1FunctionField N')) :
    x1LevelInclBar L h = IntermediateField.inclusion h' :=
  rfl

def x1x0LevelInclBar (t : ℕ) (h : N * t ∣ N') :
    laurentBaseChange L (x1x0FunctionFieldC ℚ N (N * t)) →ₐ[L]
      laurentBaseChange L (x1FunctionField N') :=
  IntermediateField.inclusion
    (laurentBaseChange_mono₃ L (x1x0FunctionFieldC_le_x1FunctionFieldC_of_mul_dvd ℚ h))

@[simp]
theorem coe_x1x0LevelInclBar (t : ℕ) (h : N * t ∣ N')
    (x : laurentBaseChange L (x1x0FunctionFieldC ℚ N (N * t))) :
    (x1x0LevelInclBar L t h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem x1x0LevelInclBar_eq_inclusion (t : ℕ) (h : N * t ∣ N')
    (h' : laurentBaseChange L (x1x0FunctionFieldC ℚ N (N * t)) ≤
      laurentBaseChange L (x1FunctionField N')) :
    x1x0LevelInclBar L t h = IntermediateField.inclusion h' :=
  rfl

def x1LevelSubstBar (t : ℕ) [NeZero t] (h : N * t ∣ N') :
    laurentBaseChange L (x1FunctionField N) →ₐ[L] laurentBaseChange L (x1FunctionField N') :=
  (x1x0LevelInclBar L t h).comp (heckeBetaOneBar L N t)

theorem x1LevelSubstBar_apply (t : ℕ) [NeZero t] (h : N * t ∣ N')
    (x : laurentBaseChange L (x1FunctionField N)) :
    x1LevelSubstBar L t h x = x1x0LevelInclBar L t h (heckeBetaOneBar L N t x) :=
  rfl

@[simp]
theorem coe_x1LevelSubstBar (t : ℕ) [NeZero t] (h : N * t ∣ N')
    (x : laurentBaseChange L (x1FunctionField N)) :
    (x1LevelSubstBar L t h x : LaurentSeries L) = (heckeBetaOneBar L N t x : LaurentSeries L) := by
  rw [x1LevelSubstBar_apply, coe_x1x0LevelInclBar]

theorem coe_x1LevelSubstBar_of (t : ℕ) [NeZero t] (h : N * t ∣ N') (hβ : HeckeBetaOneDefined N t)
    (x : laurentBaseChange L (x1FunctionField N)) :
    (x1LevelSubstBar L t h x : LaurentSeries L) = qExpand L t (x : LaurentSeries L) := by
  rw [coe_x1LevelSubstBar, coe_heckeBetaOneBar N t hβ]

end Embeddings

namespace JOne

section Total

variable (N N' t : ℕ) [NeZero t]

def DegeneracyPullbackInputs : Prop :=
  ∃ (h : N * t ∣ N') (_ : HeckeBetaOneDefined N t)
    (h₁ : (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)).toRingHom.IsIntegral)
    (h₂ : (x1LevelSubstBar (AlgebraicClosure ℚ) t h).toRingHom.IsIntegral)
    (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) (x1FunctionFieldBar N')),
    FundamentalIdentityAlong (AlgebraicClosure ℚ)
        (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁ ∧
      FundamentalIdentityAlong (AlgebraicClosure ℚ) (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂

open Classical in

def degeneracyPullbackPair : Fin 2 → (JOne N →+ JOne N') :=
  if h : DegeneracyPullbackInputs N N' t then
    haveI := h.snd.snd.snd.snd.fst
    ![Pic0.pullbackAlongHom
        (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h.fst))
        h.snd.snd.fst h.snd.snd.snd.snd.snd.1,
      Pic0.pullbackAlongHom (x1LevelSubstBar (AlgebraicClosure ℚ) t h.fst)
        h.snd.snd.snd.fst h.snd.snd.snd.snd.snd.2]
  else 0

variable {N N' t}

theorem degeneracyPullbackInputs_intro (h : N * t ∣ N') (hβ : HeckeBetaOneDefined N t)
    (h₁ : (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)).toRingHom.IsIntegral)
    (h₂ : (x1LevelSubstBar (AlgebraicClosure ℚ) t h).toRingHom.IsIntegral)
    [hP : HasPrincipalDivisors (AlgebraicClosure ℚ) (x1FunctionFieldBar N')]
    (hFI₁ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁)
    (hFI₂ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂) :
    DegeneracyPullbackInputs N N' t :=
  ⟨h, hβ, h₁, h₂, hP, hFI₁, hFI₂⟩

theorem DegeneracyPullbackInputs.mul_dvd (h : DegeneracyPullbackInputs N N' t) : N * t ∣ N' :=
  h.fst

theorem DegeneracyPullbackInputs.betaOneDefined (h : DegeneracyPullbackInputs N N' t) :
    HeckeBetaOneDefined N t :=
  h.snd.fst

theorem degeneracyPullbackPair_eq (h : N * t ∣ N') (hβ : HeckeBetaOneDefined N t)
    (h₁ : (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)).toRingHom.IsIntegral)
    (h₂ : (x1LevelSubstBar (AlgebraicClosure ℚ) t h).toRingHom.IsIntegral)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (x1FunctionFieldBar N')]
    (hFI₁ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁)
    (hFI₂ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂) :
    degeneracyPullbackPair N N' t =
      ![Pic0.pullbackAlongHom
          (x1LevelInclBar (AlgebraicClosure ℚ) ((dvd_mul_right N t).trans h)) h₁ hFI₁,
        Pic0.pullbackAlongHom (x1LevelSubstBar (AlgebraicClosure ℚ) t h) h₂ hFI₂] := by
  have hi : DegeneracyPullbackInputs N N' t := degeneracyPullbackInputs_intro h hβ h₁ h₂ hFI₁ hFI₂
  rw [degeneracyPullbackPair, dif_pos hi]

theorem degeneracyPullbackPair_of_not (h : ¬ DegeneracyPullbackInputs N N' t) :
    degeneracyPullbackPair N N' t = 0 := by
  rw [degeneracyPullbackPair, dif_neg h]

theorem degeneracyPullbackPair_apply_of_not (h : ¬ DegeneracyPullbackInputs N N' t) (i : Fin 2)
    (x : JOne N) : degeneracyPullbackPair N N' t i x = 0 := by
  rw [degeneracyPullbackPair_of_not h]
  rfl

end Total

end JOne

end ModularCurve

end


