-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:55.854108+00:00
-- url     : https://prove2.me/theorems/7275587d-7abd-4073-bee4-8484a86be24a
-- title:
--   Bridge St
-- statement:
--   Definitions and structural lemmas for Bridge St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeSt.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
namespace PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
def Ym (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • Matrix.of B)⁻¹
def Yp (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • Matrix.of B)⁻¹
def vals (s : ℂ) (B : MC n) : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then Yp s B k.2.1 k.2.2 else Ym s B k.2.1 k.2.2
def evQ (s z : ℂ) (Q : Fm n) (B : MC n) : ℂ :=
  MvPolynomial.eval (vals s B) (MvPolynomial.map (Polynomial.evalRingHom z) Q)
def fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B : MC n) : ℂ := clsC s z m 0 1 B * evQ s z Q B
def HYm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 - (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Ym s (x + t • v) a d) (((Complex.I * s) • (Ym s x * Matrix.of v * Ym s x)) a d) 0
def HYp : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 + (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Yp s (x + t • v) a d) ((-(Complex.I * s) • (Yp s x * Matrix.of v * Yp s x)) a d) 0
def HCls : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (z : ℂ) (m : ℕ) (x v : MC n), x ∈ OmS s →
    HasDerivAt (fun t : ℂ => clsC s z m 0 1 (x + t • v))
      (clsC s z m 0 1 x * (Complex.I * s * ((m : ℂ) + z) * (Ym s x * Matrix.of v).trace -
        Complex.I * s * z * (Yp s x * Matrix.of v).trace)) 0
end PositivityTheory.Rg.Sw.SP


