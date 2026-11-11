-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T04:53:40.709731+00:00
-- url     : https://prove2.me/theorems/080404eb-458d-4785-8771-0bfce3542b4d
-- title:
--   Native Geometric Avoidance
-- statement:
--   Definitions and structural lemmas for Native Geometric Avoidance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective

set_option autoImplicit false
namespace QEC.Coding.BDL26NativeGeometricAvoidance
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26FiniteAlternatingCore BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
noncomputable abbrev Presentation (S : OddScale) (n : ℕ) := (QEC.Coding.BDL26DecodingGraph.state S n).presentation
noncomputable abbrev Key (S : OddScale) (n : ℕ) := BDL26NativeTriangleColors.nativeKey S n
abbrev NativeEvent (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space) (r : ℝ) :=
  KeyEvent (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J r
noncomputable abbrev NativeSupport (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :=
  keySupport (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J r
noncomputable abbrev NativeBad (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r l : ℝ) (K : ℕ) :=
  keyBad (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J r l K
noncomputable abbrev NativeGood (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L) :=
  KeyGood (Presentation S n) (Key S n) (BDL26NativeTriangleColors.nativeKey_injective S n) J p
end QEC.Coding.BDL26NativeGeometricAvoidance


