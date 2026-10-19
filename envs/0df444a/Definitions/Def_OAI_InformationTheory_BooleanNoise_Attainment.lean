-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
-- name    : OAI_InformationTheory_BooleanNoise_Attainment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:13:35.094809+00:00
-- url     : https://prove2.me/theorems/bd835f63-6198-452b-a270-67a9446fcb58
-- title:
--   The information deficit vanishes for constant and fully smoothed functions
-- statement:
--   The Boolean cube is $\{0,1\}^n$, written as functions $x:\{0,\dots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and $x^{\oplus i}$ is $x$ with coordinate $i$ flipped. The information deficit of $g$ is $h(\mathbb{E}g)-\mathbb{E}h(g)$, where $h(v)=\log2-\psi(v)$ is the entropy of a sign with mean $v$, and $T_u$ is the noise operator. The following hold.
--
--   1. For a constant function $c$, $\mathbb{E}h(c)=h(c)$, and its information deficit is $0$.
--   2. For every correlation $u$, the deficit of $T_uc$ is $0$, since $T_u$ fixes constants.
--   3. For every $g$,
--   $$
--   h\bigl(\mathbb{E}\,T_0g\bigr)-\mathbb{E}\,h\bigl(T_0g\bigr)=0,
--   $$
--   because $T_0g$ is the constant $\mathbb{E}g$.
--
--   These trivial cases, without information or with complete noise, are the base cases of the information comparisons.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Attainment.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Attainment.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution

namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

@[simp] theorem entropyAverage_const (c : ℝ) :
    entropyAverage (fun _ : Cube n => c) = entropy c :=
  cubeAverage_const n (entropy c)

@[simp] theorem informationDeficit_const (c : ℝ) :
    informationDeficit (fun _ : Cube n => c) = 0 := by
  simp [informationDeficit]

@[simp] theorem informationDeficit_noise_const (u c : ℝ) :
    informationDeficit (noiseOperator u (fun _ : Cube n => c)) = 0 := by
  have h : noiseOperator u (fun _ : Cube n => c) = fun _ => c := by
    funext x
    exact noiseOperator_const u c x
  rw [h, informationDeficit_const]

@[simp] theorem informationDeficit_noise_zero (g : Cube n → ℝ) :
    informationDeficit (noiseOperator 0 g) = 0 := by
  have h : noiseOperator 0 g = fun _ => cubeAverage g := by
    funext x
    exact noiseOperator_zero_correlation g x
  rw [h, informationDeficit_const]

end LeanBlast.CourtadeKumar

end

end OAI


