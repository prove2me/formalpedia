-- Prove2me | Definitions.Def_PricingWithTips3DM_bee5ca8bac6e3d05c7e8dd30
-- name    : PricingWithTips3DM_bee5ca8bac6e3d05c7e8dd30
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:06:49.326379+00:00
-- url     : https://prove2.me/theorems/45d793bb-fb2e-42b7-838d-03974f8de196
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmSeparatorPrefixSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_bb4dfff051b6cd83a923236f
import Definitions.Def_PricingWithTips3DM_8596e3036db0561eca6c1166
import Definitions.Def_PricingWithTips3DM_645fa74d60687a6229a5303d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Growing separator-wire prefix of verifier-input arms

Candidate arm `i` consumes the outputs of precisely the first `i` separator
NOT gates.  The generic growing-prefix controller compiles this triangular
row family from the initial-boundary endpoint and candidate count.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Structured parameters of the separator-wire prefix family. -/
def verifierInputArmSeparatorPrefixRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameAffinePrefixRows :=
  { base := (verifierInitialBoundaryEndPolynomial W).eval input.length
    count := W.certificateBound.eval input.length + 1 }

/-- Exact growing marked-row byte stream. -/
def verifierInputArmSeparatorPrefixStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFrameAffinePrefixRowsStream
    (verifierInputArmSeparatorPrefixRows W input)

/-- Closed pointwise form of every separator-wire prefix row. -/
theorem verifierInputArmSeparatorPrefixStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputArmSeparatorPrefixStream W input =
      (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        encodeUnaryFrame (List.ofFn fun prefixIndex : Fin arm.val =>
          (verifierInitialBoundaryEndPolynomial W).eval input.length +
            prefixIndex.val)).flatMap fun row => row ++ [.frameEnd] := by
  unfold verifierInputArmSeparatorPrefixStream
    unaryFrameAffinePrefixRowsStream
    unaryFrameAffinePrefixRowValues
    verifierInputArmSeparatorPrefixRows
  have hrows :
      (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        encodeUnaryFrame (List.ofFn fun prefixIndex : Fin arm.val =>
          (verifierInitialBoundaryEndPolynomial W).eval input.length +
            prefixIndex.val)) =
      (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        List.ofFn fun prefixIndex : Fin arm.val =>
          (verifierInitialBoundaryEndPolynomial W).eval input.length +
            prefixIndex.val).map encodeUnaryFrame := by
    rw [List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext arm
    rfl
  rw [hrows, List.flatMap_map]

private theorem separatorPrefix_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> decide

/-- Typed marked-row view used by the same-input row interleavers. -/
def verifierInputArmSeparatorPrefixFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := List.ofFn fun arm :
      Fin (W.certificateBound.eval input.length + 1) =>
        encodeUnaryFrame (List.ofFn fun prefixIndex : Fin arm.val =>
          (verifierInitialBoundaryEndPolynomial W).eval input.length +
            prefixIndex.val)
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_ofFn] at hrow
      rcases hrow with ⟨arm, rfl⟩
      exact separatorPrefix_encodeUnaryFrame_frameEnd_free _ symbol hsymbol }

theorem verifierInputArmSeparatorPrefixFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierInputArmSeparatorPrefixFamily W input) =
      verifierInputArmSeparatorPrefixStream W input := by
  unfold encodeUnaryFrameMarkedRowFamily
    verifierInputArmSeparatorPrefixFamily
  exact (verifierInputArmSeparatorPrefixStream_eq W input).symm

/-- The structured controller input is exactly the existing two-polynomial
unary-frame source. -/
theorem verifierInputArmSeparatorPrefixRows_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameAffinePrefixRows
        (verifierInputArmSeparatorPrefixRows W input) =
      exactPolynomialUnaryFrames
        [verifierInitialBoundaryEndPolynomial W,
          verifierInputArmCountPolynomial W] input := by
  change encodeUnaryFrame
      [(verifierInitialBoundaryEndPolynomial W).eval input.length,
        W.certificateBound.eval input.length + 1] =
    encodeUnaryFrame
      [(verifierInitialBoundaryEndPolynomial W).eval input.length,
        (verifierInputArmCountPolynomial W).eval input.length]
  rw [verifierInputArmCountPolynomial_eval]

/-- One fixed polynomial-time TM2 computes the complete triangular
separator-prefix family directly from the raw verifier word. -/
noncomputable def
    verifierInputArmSeparatorPrefixFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmSeparatorPrefixFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let result :=
    exactPolynomialUnaryFrameAffinePrefixRowsStream_computableInPolyTime
      (Γ := Γ) (verifierInitialBoundaryEndPolynomial W)
        (verifierInputArmCountPolynomial W)
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        simpa only [Function.comp_apply, id_eq,
          verifierInputArmSeparatorPrefixFamily_encoding_eq W input,
          verifierInputArmSeparatorPrefixStream,
          verifierInputArmSeparatorPrefixRows,
          exactPolynomialUnaryFrameAffinePrefixRowsStream,
          exactPolynomialUnaryFrameAffinePrefixRows,
          verifierInputArmCountPolynomial_eval] using
          result.outputsFun input }

end CLRS.Chapter34.Turing.CookLevin


