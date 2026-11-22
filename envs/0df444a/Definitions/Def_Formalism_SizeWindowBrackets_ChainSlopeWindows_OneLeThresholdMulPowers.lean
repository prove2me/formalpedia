-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:28.099546+00:00
-- url     : https://prove2.me/theorems/762f9380-001e-4f31-9f3c-b47ea6dbae13
-- title:
--   One Le Threshold Mul Powers
-- statement:
--   Definitions and structural lemmas for One Le Threshold Mul Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
structure Facts (P : Par) (e K z u E X S sb v w8 : ℝ) : Prop where
  hx : 100 ≤ P.x
  he : 0 ≤ e
  hK : 1 ≤ K
  z1 : 1 ≤ z
  hz4 : 100 * K * z ^ 4 ≤ P.x
  u1 : 1 ≤ u
  uz : u ≤ z
  E1 : 1 ≤ E
  hXB : 100 * K * (E ^ 4 * P.x ^ 4) ≤ X
  S1 : 1 ≤ S
  hsb : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) ≤ sb
  hb : P.b = sb * sb
  ha : P.a = P.x * P.b
  hXp : P.Xp = X
  hvX : v * X = P.b
  v0 : 0 ≤ v
  hbp : P.bp = P.x * v
  hwpp : P.wpp = v / P.n
  hXpp : P.Xpp = P.x * P.n * X
  lx0 : 0 ≤ P.lx
  lxz : P.lx ≤ z
  elx : e * P.lx ≤ z
  logX : Real.log X = u
  loga : Real.log P.a = P.lx + z
  nx : P.x ^ 2 ≤ P.n
  n2x : P.x ^ 2 ≤ (2 : ℝ) ^ P.e₂
  n2n : (2 : ℝ) ^ P.e₂ ≤ P.n
  nE : P.n ≤ E
  kx : P.x ^ 2 ≤ P.k
  kE : P.k ≤ E
  N0 : 0 ≤ P.N
  NE : P.N ≤ E
  t0 : 0 ≤ P.t
  tE : P.t ≤ E
  px : P.x ^ 4 + 1 ≤ (P.p₀ : ℝ)
  pE : (P.p₀ : ℝ) ≤ E
  La0 : 0 ≤ P.La
  Laz : P.La ≤ z ^ 2
  r0 : 0 ≤ P.rG
  rE : P.rG ≤ E
  Sc0 : 0 ≤ P.Sc
  ScS : P.Sc ≤ S
  η0 : 0 ≤ P.η
  ηS : P.η ≤ S
  ρ0 : 0 ≤ P.ρ
  ρx : P.ρ ≤ (P.x ^ 2)⁻¹
  th0 : 0 ≤ P.th
  thx : P.th ≤ P.x⁻¹
  x_sq_le_threshold : P.x ^ 2 ≤ P.K₀
  dx : P.x ^ 2 ≤ (P.d : ℝ)
  C0 : 0 ≤ P.C
  CK : P.C ≤ K
  β0 : 0 ≤ P.β
  βK : P.β ≤ K * (P.x ^ 2)⁻¹
  Co0 : 0 ≤ P.Cord
  CoK : P.Cord ≤ K
  Y1 : 1 ≤ P.Y
  YX : P.Y ≤ 2 * X
  s0 : 0 ≤ P.s₀
  sx : P.s₀ ≤ (P.x ^ 2)⁻¹
  bo0 : 0 ≤ P.bo
  bosb : P.bo ≤ sb
  hδ : P.δ₁ = w8⁻¹
  w81 : 1 ≤ w8
  w8z : w8 ≤ z
  hθ : P.θ = z⁻¹
  Joz : (P.Jo : ℝ) ≤ z
  Ibu : (P.Ib : ℝ) ≤ u
  hE : E = P.x ^ e
  hu : u = P.x ^ (P.ε / 3)
  hz : z = P.x ^ P.ε
namespace Facts
variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F
end Facts
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds


