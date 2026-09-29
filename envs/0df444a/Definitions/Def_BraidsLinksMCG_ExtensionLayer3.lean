-- Prove2me | Definitions.Def_BraidsLinksMCG_ExtensionLayer3
-- name    : BraidsLinksMCG_ExtensionLayer3
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-24T12:05:36.945986+00:00
-- url     : https://prove2.me/theorems/1382281f-1cc5-453d-987a-21fa9986494a
-- title:
--   The moving-base family of standard loops in the strand extension
-- statement:
--   When the base point of the j-th standard loop of the punctured plane slides along the right moving point of the elementary half-twist of the strand extension, the resulting family of loops is continuous in the parameter; at the right end of the motion it is the ordinary j-th standard loop, at the left end it agrees pointwise in the plane with the j-th standard loop of the configuration with one extra far-right puncture, and throughout the motion the loop never passes through the left moving point.
-- source:
--   Layer 3 of the strand-extension geometry chain for the open target BraidsLinksMCG.extensionBoundaryHomotopy_inline_child_v4 (39872516-612f-4cb5-9ca6-4ee965218a2f), which supports the open targets BraidsLinksMCG.standardGen_image_strandExtension_conjugate_v1 (2273a291-a4e8-43a8-b38b-527095999a64) and BraidsLinksMCG.standardGen_image_last_eq_last_halfTwist_square_v1 (a5d61856-8526-4cf8-960c-b185fcf7fd81). Extends the published layers BraidsLinksMCG_ExtensionPairLayer and BraidsLinksMCG_ExtensionLayer2. The endpoint comparisons at parameter 0 are stated pointwise in the plane because E² - Q_n and E² - Q_{n+1} are different types and cannot be compared by a Path.cast.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1
import Definitions.Def_BraidsLinksMCG_ExtensionPairLayer
import Definitions.Def_BraidsLinksMCG_ExtensionLayer2

/-!
Layer 3 of the strand-extension geometry build: the moving-base family of standard loops.

The family is the standard loop around the `j`-th puncture of `E² - Q_n` whose base point
slides, with the parameter `s`, along the right moving point of the elementary half-twist of
the strand extension.  At `s = 1` the base point is the ordinary base point `n + 1` of the
punctured plane and the family is the ordinary `j`-th standard loop; at `s = 0` the base
point is the far-right point `n + 2` and the family agrees *pointwise in `ℂ`* with the `j`-th
standard loop of `E² - Q_{n+1}`.  Throughout the motion the loop avoids the left moving point.

Only pointwise comparisons are stated at `s = 0`: the two punctured planes `E² - Q_n` and
`E² - Q_{n+1}` are different types, so the endpoint comparison there cannot be a `Path.cast`
between them.
-/

open unitInterval BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension
open scoped unitInterval

namespace BraidsLinksMCG

noncomputable section

/-- The base point of the moving family at parameter `s`: the right moving point of the
elementary half-twist. -/
def extensionMovingBase (n : ℕ) (s : I) : PuncturedPlane n :=
  ⟨extensionPairRight n s, extensionPairRight_ne_fixed n s⟩

lemma extensionMovingBase_one (n : ℕ) :
    extensionMovingBase n 1 = basePunctured n := by
  apply Subtype.ext
  simpa [extensionMovingBase, basePunctured] using extensionPairRight_one n

/-- At parameter `0` the moving base point is the far-right point `n + 2`. -/
lemma extensionMovingBase_zero_val (n : ℕ) :
    (extensionMovingBase n 0).1 = (((n : ℝ) + 2 : ℝ) : ℂ) := by
  simpa [extensionMovingBase] using extensionPairRight_zero n

/-- The approach segment of the moving family: from the right moving point at parameter `s`
to the half-integer point above the `j`-th puncture. -/
def extensionAlphaPath (n : ℕ) (j : Fin n) (s : I) :
    Path (extensionMovingBase n s) (halfPt n j) where
  toFun := fun u => ⟨extensionApproach n j (s, u), extensionApproach_safe n j (s, u)⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (by
        show Continuous fun u : I => extensionApproach n j (s, u)
        unfold extensionApproach extensionPairRight twistPoint
        fun_prop)
      (fun u => extensionApproach_safe n j (s, u))
  source' := Subtype.ext (extensionApproach_zero n j s)
  target' := by
    apply Subtype.ext
    change extensionApproach n j (s, 1) = ((((j : ℕ) : ℝ) + 1 + 1 / 2 : ℝ) : ℂ)
    rw [extensionApproach_one]
    congr 1
    ring

/-- At parameter `1` the moving base is the base point, and the approach segment is the
ordinary approach path. -/
lemma extensionAlphaPath_one_cast (n : ℕ) (j : Fin n) :
    (extensionAlphaPath n j 1).cast (extensionMovingBase_one n).symm rfl
      = approachPath n j := by
  apply Path.ext
  funext u
  apply Subtype.ext
  change extensionApproach n j (1, u) = approachFun n j (u : ℝ)
  exact extensionApproach_at_right n j u

/-- At parameter `0` the approach segment agrees, pointwise in `ℂ`, with the approach path of
the configuration with one extra far-right puncture. -/
lemma extensionAlphaPath_zero_val (n : ℕ) (j : Fin n) (u : I) :
    (extensionAlphaPath n j 0 u).1 = (approachPath (n + 1) j.castSucc u).1 := by
  show extensionApproach n j (0, u) = approachFun (n + 1) j.castSucc (u : ℝ)
  exact extensionApproach_at_left n j u

/-- The circle around the `j`-th puncture agrees, pointwise in `ℂ`, with the circle of the
configuration with one extra far-right puncture. -/
lemma extensionCirclePath_val (n : ℕ) (j : Fin n) (u : I) :
    (circlePath n j u).1 = (circlePath (n + 1) j.castSucc u).1 := by
  show circleFun n j (u : ℝ) = circleFun (n + 1) j.castSucc (u : ℝ)
  rfl

/-- The standard loop around the `j`-th puncture, with its base point moving along the
half-twist pair of the strand extension. -/
def extensionMovingLoop (n : ℕ) (j : Fin n) (s : I) :
    Path (extensionMovingBase n s) (extensionMovingBase n s) :=
  (extensionAlphaPath n j s).trans
    ((circlePath n j).trans (extensionAlphaPath n j s).symm)

lemma extensionMovingLoop_source_val (n : ℕ) (j : Fin n) (s : I) :
    (extensionMovingLoop n j s 0).1 = extensionPairRight n s :=
  congrArg Subtype.val (extensionMovingLoop n j s).source

lemma extensionMovingLoop_target_val (n : ℕ) (j : Fin n) (s : I) :
    (extensionMovingLoop n j s 1).1 = extensionPairRight n s :=
  congrArg Subtype.val (extensionMovingLoop n j s).target

/-- At parameter `1` the moving loop is the ordinary `j`-th standard loop. -/
lemma extensionMovingLoop_one_cast (n : ℕ) (j : Fin n) :
    (extensionMovingLoop n j 1).cast (extensionMovingBase_one n).symm
      (extensionMovingBase_one n).symm = standardLoop n j := by
  simp [extensionMovingLoop, standardLoop, Path.cast_trans, Path.cast_symm,
    extensionAlphaPath_one_cast]

/-- At parameter `1` the moving loop agrees, pointwise in `ℂ`, with the ordinary `j`-th
standard loop. -/
lemma extensionMovingLoop_one_val (n : ℕ) (j : Fin n) (t : I) :
    (extensionMovingLoop n j 1 t).1 = (standardLoop n j t).1 := by
  have h := congrArg
    (fun p : Path (basePunctured n) (basePunctured n) => (p t).1)
    (extensionMovingLoop_one_cast n j)
  simpa [Path.cast_coe] using h

/-- At parameter `0` the moving loop agrees, pointwise in `ℂ`, with the `j`-th standard loop
of the configuration with one extra far-right puncture. -/
lemma extensionMovingLoop_zero_val (n : ℕ) (j : Fin n) (t : I) :
    (extensionMovingLoop n j 0 t).1 = (standardLoop (n + 1) j.castSucc t).1 := by
  have hα : ∀ u : I, (extensionAlphaPath n j 0 u).1 =
      (approachPath (n + 1) j.castSucc u).1 := fun u => extensionAlphaPath_zero_val n j u
  have hγ : ∀ u : I, (circlePath n j u).1 = (circlePath (n + 1) j.castSucc u).1 :=
    fun u => extensionCirclePath_val n j u
  rw [extensionMovingLoop, standardLoop]
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs
  · exact hα _
  · exact hγ _
  · exact hα _

lemma extensionAlphaPath_uncurry_continuous (n : ℕ) (j : Fin n) :
    Continuous fun x : I × I => extensionAlphaPath n j x.1 x.2 :=
  Continuous.subtype_mk
    (by
      show Continuous fun x : I × I => extensionApproach n j (x.1, x.2)
      unfold extensionApproach extensionPairRight twistPoint
      fun_prop)
    (fun x => extensionApproach_safe n j (x.1, x.2))

/-- The moving family depends continuously on the parameter, i.e. it is a homotopy between
its two endpoint loops. -/
lemma extensionMovingLoop_uncurry_continuous (n : ℕ) (j : Fin n) :
    Continuous fun x : I × I => extensionMovingLoop n j x.1 x.2 := by
  have hα : Continuous fun x : I × I => extensionAlphaPath n j x.1 x.2 :=
    extensionAlphaPath_uncurry_continuous n j
  have hαsymm := Path.symm_continuous_family (fun s : I => extensionAlphaPath n j s) hα
  have hγ : Continuous fun x : I × I => circlePath n j x.2 :=
    (circlePath n j).continuous.comp continuous_snd
  have hinner := Path.trans_continuous_family (fun _s : I => circlePath n j) hγ
    (fun s : I => (extensionAlphaPath n j s).symm) hαsymm
  exact Path.trans_continuous_family (fun s : I => extensionAlphaPath n j s) hα
    (fun s : I => (circlePath n j).trans (extensionAlphaPath n j s).symm) hinner

lemma path_trans_avoids {X : Type*} [TopologicalSpace X] {x y z : X} {p : Path x y}
    {q : Path y z} (f : X → ℂ) (a : ℂ)
    (hp : ∀ t, f (p t) ≠ a) (hq : ∀ t, f (q t) ≠ a) :
    ∀ t, f ((p.trans q) t) ≠ a := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

lemma path_symm_avoids {X : Type*} [TopologicalSpace X] {x y : X} {p : Path x y}
    (f : X → ℂ) (a : ℂ) (hp : ∀ t, f (p t) ≠ a) :
    ∀ t, f ((p.symm) t) ≠ a := by
  intro t
  rw [Path.symm_apply]
  exact hp _

/-- Throughout the motion the moving loop never passes through the left moving point. -/
lemma extensionMovingLoop_avoidsPairLeft (n : ℕ) (j : Fin n) (s : I) (t : I) :
    (extensionMovingLoop n j s t).1 ≠ extensionPairLeft n s := by
  have hα : ∀ u : I, (extensionAlphaPath n j s u).1 ≠ extensionPairLeft n s := by
    intro u
    show extensionApproach n j (s, u) ≠ extensionPairLeft n s
    exact extensionApproach_ne_pairLeft n j (s, u)
  have hγ : ∀ u : I, (circlePath n j u).1 ≠ extensionPairLeft n s := by
    intro u
    show circleFun n j (u : ℝ) ≠ extensionPairLeft n s
    exact circleFun_ne_pairLeft n j s (u : ℝ)
  rw [extensionMovingLoop]
  exact path_trans_avoids Subtype.val (extensionPairLeft n s) hα
    (path_trans_avoids Subtype.val (extensionPairLeft n s) hγ
      (path_symm_avoids Subtype.val (extensionPairLeft n s) hα)) t

end

end BraidsLinksMCG


