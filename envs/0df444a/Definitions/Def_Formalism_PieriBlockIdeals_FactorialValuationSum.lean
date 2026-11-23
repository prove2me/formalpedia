-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
-- name    : Formalism_PieriBlockIdeals_FactorialValuationSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:16.036377+00:00
-- url     : https://prove2.me/theorems/baf52a5c-b951-45a3-bf73-16ef4c39913d
-- title:
--   Factorial Valuation Sum
-- statement:
--   Definitions and structural lemmas for Factorial Valuation Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/FactorialValuationSum.lean

import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
def U (k j t : ℕ) (lam : Fin (k + j) → ℕ) (a : Fin (k + j)) : ℤ :=
  (lam a : ℤ) + ((k : ℤ) + (j : ℤ) + (t : ℤ) - 1 - (a.val : ℤ))
def maxB (t w : ℕ) : ℤ := (w : ℤ) + (t : ℤ) - 1
def dual {r : ℕ} (M : ℕ) (lam : Fin r → ℕ) : Fin r → ℕ := fun b => M - lam (Fin.rev b)
def label (k j t M : ℕ) (lam : Fin (k + j) → ℕ) (b : Fin (k + j)) (col : ℕ) : ℤ :=
  U k j t lam (Fin.rev b) - ((col : ℤ) - (dual M lam b : ℤ) + 1)
def cont (t w M : ℕ) (ct : ℤ) : ℤ := ((M - w : ℕ) : ℤ) - (ct - maxB t w)
structure Rows (k j t w M : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) : Prop where
  low : ∀ a, w ≤ lam a
  high : ∀ a, lam a ≤ M
  cloud : ∀ a : Fin (k + j), a.val < k → xm ≤ U k j t lam a ∧ U k j t lam a ≤ xp
  rest : ∀ a : Fin (k + j), k ≤ a.val → U k j t lam a < xm
  above : maxB t w < xm
  le : xm ≤ xp
def RowsOfShape : Prop :=
  ∀ (k j t w M : ℕ) (lam : Fin (k + j) → ℕ) (hk : 0 < k), Antitone lam → (∀ a, w ≤ lam a ∧ lam a ≤ M) →
    Rows k j t w M lam (U k j t lam ⟨k - 1, by omega⟩) (U k j t lam ⟨0, by omega⟩)
def LabelIdentity : Prop :=
  ∀ (k j t w M : ℕ) (lam : Fin (k + j) → ℕ), (∀ a, w ≤ lam a ∧ lam a ≤ M) → ∀ (b : Fin (k + j)) (col : ℕ),
    ((M - w : ℕ) : ℤ) - ((col : ℤ) - (b.val : ℤ)) = label k j t M lam b col - maxB t w
def GoodLabels : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ), (∀ a, w ≤ lam a ∧ lam a ≤ M) →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ (b : Fin (k + j)) (col : ℕ), dual M lam b ≤ col → col < tau b →
      maxB t w < label k j t M lam b col ∧ label k j t M lam b col ≤ U k j t lam (Fin.rev b) - 1
def boxesOfLabel (t w M : ℕ) {r : ℕ} (lam tau : Fin r → ℕ) (ct : ℤ) : ℕ :=
  boxesOfContent (dual M lam) tau (cont t w M ct)
def cloudBoxes (k j t w M : ℕ) (lam tau : Fin (k + j) → ℕ) (ct : ℤ) : ℕ :=
  (Finset.univ.filter fun b : Fin (k + j) => (Fin.rev b).val < k ∧
    ((dual M lam b : ℤ) ≤ cont t w M ct + (b.val : ℤ) ∧ cont t w M ct + (b.val : ℤ) < (tau b : ℤ))).card
def CountsRows : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ,
      boxesOfLabel t w M lam tau ct ≤ (if ct < xm then j else 0) + cloudBoxes k j t w M lam tau ct
def CountsCloud : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ),
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ,
      cloudBoxes k j t w M lam tau ct ≤ k ∧ cloudBoxes k j t w M lam tau ct ≤ t
def CountsDeep : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp →
    ∀ tau ∈ shapes t (M - w) i (dual M lam), ∀ ct : ℤ, ct < xm →
      (cloudBoxes k j t w M lam tau ct : ℤ) * (xm - ct) ≤ (i : ℤ)
def MuBound : Prop :=
  ∀ (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), Rows k j t w M lam xm xp → ∀ ct : ℤ,
    (mu t (M - w) i (dual M lam) (cont t w M ct) : ℝ) ≤
      (if ct < xm then (j : ℝ) else 0) +
        min (min (k : ℝ) (t : ℝ)) (if ct < xm then (i : ℝ) / ((xm - ct : ℤ) : ℝ) else (k : ℝ))
def DnValSum : Prop :=
  ∀ (l k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    padicValInt l (Dn t (M - w) i (dual M lam)) =
      ∑ ct ∈ Finset.Ioo (maxB t w) xp, mu t (M - w) i (dual M lam) (cont t w M ct) * vl l (ct - maxB t w)
def FactorialValuationSum : Prop :=
  ∀ (l : ℕ) (xm mB : ℤ), l.Prime → mB < xm →
    ∑ ct ∈ Finset.Ioo mB xm, vl l (ct - mB) = padicValNat l ((xm - mB - 1).toNat).factorial ∧
      (padicValNat l ((xm - mB - 1).toNat).factorial : ℝ) ≤ (((xm - mB : ℤ) : ℝ) - 1) / ((l : ℝ) - 1)
def harm (l h : ℕ) (i : ℝ) : ℝ :=
  if h < l then 0 else (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ)))
def labelSumBoundPos (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ) : ℝ :=
  (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
    harm l h i
def HarmPosLog : Prop :=
  ∀ (l h : ℕ) (i : ℝ), 0 ≤ i →
    harm l h i ≤ (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))) ∧
      (1 ≤ l → l ≤ h → harm l h i = (i / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ))))
def LabelSumPlus : Prop :=
  ∀ (l k t h : ℕ) (i : ℝ) (xm xp mB : ℤ), l.Prime → 0 ≤ i → mB < xm → xm ≤ xp →
    xp - mB ≤ (h : ℤ) → h < l ^ 2 →
    labelLHS l k t i xm xp mB ≤ labelSumBoundPos l k t h i xm xp mB
def Step2Val : Prop :=
  ∀ (l k j t w M h i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 →
    (padicValInt l (Dn t (M - w) i (dual M lam)) : ℝ) ≤
      (j : ℝ) * ((((xm - maxB t w : ℤ) : ℝ) - 1) / ((l : ℝ) - 1)) +
        labelSumBoundPos l k t h (i : ℝ) xm xp (maxB t w)
def Step2ValUpTo : Prop :=
  ∀ (l k j t w M h i : ℕ) (I : ℝ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Rows k j t w M lam xm xp →
    xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 → (i : ℝ) ≤ I →
    (padicValInt l (Dn t (M - w) i (dual M lam)) : ℝ) ≤
      (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + labelSumBoundPos l k t h I xm xp (maxB t w)
def Step2Real : Prop :=
  LemmaDLast → ∀ (l k j t w M h : ℕ) (I : ℝ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ), l.Prime → Antitone lam →
    Rows k j t w M lam xm xp → xp - maxB t w ≤ (h : ℤ) → h < l ^ 2 →
    ∀ eL : ℕ, (∀ μ2 : Fin (k + j) → ℕ, ExpLe l (k + j) lam μ2 eL) →
      ∀ (i : ℕ) (μ : Fin (k + j + t) → ℕ), IsDepthLast t (k + j) w μ i → (i : ℝ) ≤ I →
        ExpLe l (k + j + t) (blockWtLast t (k + j) w lam) μ
          (eL + ⌊(j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + labelSumBoundPos l k t h I xm xp (maxB t w)⌋₊)
def cPrime (l k j t q h ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + (ecl : ℝ) + labelSumBoundPos l k t h I xm xp mB
def cCoarse (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) : ℝ :=
  ((q : ℝ) + 2 * (j : ℝ)) * (((h : ℝ) + (N' : ℝ)) / ((l : ℝ) - 1) + 6) + (ecl : ℝ) +
    (k : ℝ) * (((xp - xm : ℤ) : ℝ) / (l : ℝ) + IlInd l xm xp mB) +
    (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (I / (d0 l (xm - mB) : ℝ)) else 0) +
    (I / (l : ℝ)) * (1 + Real.posLog ((h : ℝ) / (l : ℝ)))
def CPrimeMono : Prop :=
  ∀ (l k j t q h ecl : ℕ) (xm xp mB : ℤ), Monotone (cPrime l k j t q h ecl xm xp mB)
def CCoarseMono : Prop :=
  ∀ (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ), Monotone (cCoarse l k j t q h N' ecl xm xp mB)
def CPrimeLeCoarse : Prop :=
  ∀ (l k j t q h N' ecl : ℕ) (xm xp mB : ℤ) (I : ℝ), 2 ≤ l → 0 ≤ I →
    cPrime l k j t q h ecl xm xp mB I ≤ cCoarse l k j t q h N' ecl xm xp mB I
def LogFormNegative : Prop :=
  ∃ (l k t h : ℕ) (xm xp mB : ℤ) (I : ℝ), l.Prime ∧ h < l ^ 2 ∧ 1 ≤ k ∧ 1 ≤ t ∧ mB < xm ∧ xm ≤ xp ∧
    xp - mB ≤ (h : ℤ) ∧ 0 ≤ I ∧ labelSumBound l k t h I xm xp mB < 0
def Total : Prop :=
  ∀ (l k j t q h ecl : ℕ) (xm xp mB : ℤ) (I : ℝ) (E eL : ℕ → ℕ) (v : ℕ),
    (∀ s < q, (E s : ℝ) ≤ (E (s + 1) : ℝ) + ((h : ℝ) - 1) / ((l : ℝ) - 1)) →
    E q ≤ eL 0 + v →
    (v : ℝ) ≤ (j : ℝ) * (((h : ℝ) - 1) / ((l : ℝ) - 1)) + labelSumBoundPos l k t h I xm xp mB →
    (∀ s < j, (eL s : ℝ) ≤ (eL (s + 1) : ℝ) + ((h : ℝ) - 1) / ((l : ℝ) - 1)) →
    eL j ≤ ecl →
    (E 0 : ℝ) ≤ cPrime l k j t q h ecl xm xp mB I ∧ E 0 ≤ ⌊cPrime l k j t q h ecl xm xp mB I⌋₊
def UN (N : ℕ) (lam : ℕ → ℕ) (a : ℕ) : ℤ := (lam a : ℤ) + (N : ℤ) - 1 - (a : ℤ)
def Application : Prop :=
  LemmaDLastGraded → ∀ (l k j t q h : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ k → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cPrime l k j t q h ecl (UN (k + j + t + q) lam (k - 1)) (UN (k + j + t + q) lam 0)
          (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊
def ApplicationCoarse : Prop :=
  LemmaDLastGraded → ∀ (l k j t q h N' : ℕ) (lam : ℕ → ℕ), l.Prime → 1 ≤ k → 1 ≤ t →
    (∀ a b, a ≤ b → b < k + j + t + q → lam b ≤ lam a) →
    (∀ a, k + j ≤ a → a < k + j + t → lam a = lam (k + j)) →
    lam 0 + (k + j + t + q) ≤ h + lam (k + j + t + q - 1) + 1 → h < l ^ 2 →
    ∀ ecl : ℕ, (∀ μ : Fin k → ℕ, ExpLe l k (res k lam) μ ecl) →
      ∀ I : ℕ, ExpUpTo l (k + j + t + q) lam (varpi (k + j)) (I : ℤ)
        ⌊cCoarse l k j t q h N' ecl (UN (k + j + t + q) lam (k - 1)) (UN (k + j + t + q) lam 0)
          (UN (k + j + t + q) lam (k + j)) (I : ℝ)⌋₊
def ShallowWeights : Prop :=
  ∀ (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] (ι : Type) [DecidableEq ι]
    (W : ι → Submodule R N), DirectSum.IsInternal W →
    ∀ D : Submodule R N, D = ⨆ ν, D ⊓ W ν →
    ∀ (l : R) (c : ℕ) (depth : ι → ℤ) (i : ℤ), (∀ ν, depth ν ≤ i → ∀ x ∈ W ν, l ^ c • x ∈ D) →
    ∀ A B : Submodule R N, D ≤ A → B ≤ D ⊔ (⊤ : Submodule R N).map ((l ^ c) • LinearMap.id) →
    ∀ ν, (∃ x ∈ B, x ∈ W ν ∧ x ∉ A) → i < depth ν
def TensorScale : Prop :=
  ∀ (R : Type) [CommRing R] (P X : Type) [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X]
    [Module.Flat R P] (l : R) (c : ℕ),
    Function.Injective
        (LinearMap.lTensor P (LinearMap.range ((l ^ c) • (LinearMap.id : X →ₗ[R] X))).subtype) ∧
      LinearMap.range
          (LinearMap.lTensor P (LinearMap.range ((l ^ c) • (LinearMap.id : X →ₗ[R] X))).subtype) =
        LinearMap.range ((l ^ c) • (LinearMap.id : TensorProduct R P X →ₗ[R] TensorProduct R P X))
def TensorGraded : Prop :=
  ∀ (R : Type) [CommRing R] (P N : Type) [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [Module.Flat R P] (D : Submodule R N),
    Function.Injective (LinearMap.lTensor P D.subtype) ∧
      Function.Exact (LinearMap.lTensor P D.subtype) (LinearMap.lTensor P D.mkQ) ∧
      Function.Surjective (LinearMap.lTensor P D.mkQ)
def TensorKill : Prop :=
  ∀ (R : Type) [CommRing R] (P X P' : Type) [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X]
    [AddCommGroup P'] [Module R P'] (l : R) (c : ℕ), (∀ x : X, l ^ c • x = 0) →
    ∀ z : TensorProduct R P (TensorProduct R X P'), l ^ c • z = 0
inductive Filtered {C : Type 1} [Category.{0} C] [HasZeroMorphisms C] (P : C → Prop) : C → Prop
  | zero (Y : C) : IsZero Y → Filtered P Y
  | step (S : ShortComplex C) : S.ShortExact → Filtered P S.X₁ → P S.X₃ → Filtered P S.X₂
def MidExact {C : Type 1} [Category.{0} C] [Abelian C] {O : Type} [CommRing O]
    (Φ : C ⥤ ModuleCat.{0} O) [Φ.PreservesZeroMorphisms] : Prop :=
  ∀ S : ShortComplex C, S.ShortExact → (S.map Φ).Exact
def Devissage : Prop :=
  ∀ (O : Type) [CommRing O] (C : Type 1) [Category.{0} C] [Abelian C]
    (Φ : C ⥤ ModuleCat.{0} O) [Φ.Additive], MidExact Φ →
    ∀ P : C → Prop, (∀ G, P G → IsZero (Φ.obj G)) → ∀ Y, Filtered P Y → IsZero (Φ.obj Y)
def chainMap {C : Type 1} [Category.{0} C] (A : ℕ → C) (inc : ∀ r, A r ⟶ A (r + 1)) : ∀ n, A 0 ⟶ A n
  | 0 => 𝟙 (A 0)
  | n + 1 => chainMap A inc n ≫ inc n
def TheoremWFunctor : Prop :=
  ∀ (O : Type) [CommRing O] (C : Type 1) [Category.{0} C] [Abelian C] [Linear O C]
    (Φ : C ⥤ ModuleCat.{0} O) [Φ.Additive] [Φ.Linear O], MidExact Φ →
    ∀ (l : O) (f : ℕ) (A Q : ℕ → C) (inc : ∀ r, A r ⟶ A (r + 1)) (pr : ∀ r, A (r + 1) ⟶ Q r)
      (zero : ∀ r, inc r ≫ pr r = 0), (∀ r < f, (ShortComplex.mk (inc r) (pr r) (zero r)).ShortExact) →
    ∀ (Λ : Type) (L : Λ → C) (cf : Λ → Prop) (depth : ℕ → Λ → ℤ) (i : ℕ → ℤ) (ex c' : ℕ → ℕ),
      (∀ μ, cf μ → ¬ IsZero (Φ.obj (L μ)) → ∀ r < f, depth r μ ≤ i r) →
      (∀ r < f, (l ^ ex r) • 𝟙 (Q r) = 0) →
      (∀ r < f, Filtered (fun G => ∃ μ, cf μ ∧ i r < depth r μ ∧ Nonempty (G ≅ L μ))
        (Limits.image ((l ^ c' r) • 𝟙 (Q r)))) →
      ∀ x : Φ.obj (A f), ∃ y : Φ.obj (A 0),
        (Φ.map (chainMap A inc f)).hom y = l ^ (∑ r ∈ Finset.range f, min (ex r) (c' r)) • x
def DeepFactors : Prop :=
  ∀ (O : Type) [CommRing O] (C : Type 1) [Category.{0} C] [Abelian C] (ι : Type)
    (wt : ι → C ⥤ ModuleCat.{0} O) [∀ ν, PreservesFiniteLimits (wt ν)] [∀ ν, PreservesFiniteColimits (wt ν)]
    (Λ : Type) (L : Λ → C) (hw : Λ → ι), (∀ μ, ¬ IsZero ((wt (hw μ)).obj (L μ))) →
    ∀ (P : Λ → Prop) (shallow : ι → Prop) (Y : C), (∀ ν, shallow ν → IsZero ((wt ν).obj Y)) →
      Filtered (fun G => ∃ μ, P μ ∧ Nonempty (G ≅ L μ)) Y →
      Filtered (fun G => ∃ μ, P μ ∧ ¬ shallow (hw μ) ∧ Nonempty (G ≅ L μ)) Y
def TheoremWWeights : Prop :=
  ∀ (O : Type) [CommRing O] (C : Type 1) [Category.{0} C] [Abelian C] [Linear O C]
    (Φ : C ⥤ ModuleCat.{0} O) [Φ.Additive] [Φ.Linear O], MidExact Φ →
    ∀ (ι : Type) (wt : ι → C ⥤ ModuleCat.{0} O) [∀ ν, (wt ν).Additive] [∀ ν, (wt ν).Linear O]
      [∀ ν, PreservesFiniteLimits (wt ν)] [∀ ν, PreservesFiniteColimits (wt ν)]
      (l : O) (f : ℕ) (A Q : ℕ → C) (inc : ∀ r, A r ⟶ A (r + 1)) (pr : ∀ r, A (r + 1) ⟶ Q r)
      (zero : ∀ r, inc r ≫ pr r = 0), (∀ r < f, (ShortComplex.mk (inc r) (pr r) (zero r)).ShortExact) →
    ∀ (Λ : Type) (L : Λ → C) (hw : Λ → ι) (cf : Λ → Prop) (depth : ℕ → ι → ℤ) (i : ℕ → ℤ) (ex c' : ℕ → ℕ),
      (∀ μ, ¬ IsZero ((wt (hw μ)).obj (L μ))) →
      (∀ μ, cf μ → ¬ IsZero (Φ.obj (L μ)) → ∀ r < f, depth r (hw μ) ≤ i r) →
      (∀ r < f, (l ^ ex r) • 𝟙 (Q r) = 0) →
      (∀ r < f, ∀ ν, depth r ν ≤ i r → ∀ z : (wt ν).obj (Q r), l ^ c' r • z = 0) →
      (∀ r < f, Filtered (fun G => ∃ μ, cf μ ∧ Nonempty (G ≅ L μ)) (Limits.image ((l ^ c' r) • 𝟙 (Q r)))) →
      ∀ x : Φ.obj (A f), ∃ y : Φ.obj (A 0),
        (Φ.map (chainMap A inc f)).hom y = l ^ (∑ r ∈ Finset.range f, min (ex r) (c' r)) • x
end Formalism.CohomologicalDescent.UnitNormBounds


