-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- name    : ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:44.86253+00:00
-- url     : https://prove2.me/theorems/17040c2e-abbd-4a6f-9db9-87f17b6dd39c
-- title:
--   Hom Dens B
-- statement:
--   Definitions and structural lemmas for Hom Dens B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/LeviForms/HomDensB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
def zMat (N : ℕ) (z : Pairs N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ p : Pairs N, Matrix.single p.1.2 p.1.1 (z p)
def cpP (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ[X] :=
  ∑ k ∈ Finset.range N, (X ^ k : ℂ[X]) • ((((k.factorial : ℂ)⁻¹) • A ^ k).map C)
def gP (N : ℕ) (hd : Fin N → ℝ) (v : Pairs N → ℂ) : Matrix (Fin N) (Fin N) ℂ[X] :=
  cpP N (zMat N v)ᴴ * ((diagonal fun k => (hd k : ℂ)).map C * cpP N (zMat N v))
def Zm (N m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (zMat N v).submatrix (Fin.castLE hm) (Fin.castLE hm)
def Gm (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    Matrix (Fin m) (Fin m) ℂ[X] :=
  (gP N hd v).submatrix (Fin.castLE hm) (Fin.castLE hm)
def tL {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  1 - (X : ℂ[X]) • A.map C
def Gn (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    Matrix (Fin m) (Fin m) ℂ[X] :=
  tL (Zm N m hm v)ᴴ * Gm N hd m hm v * tL (Zm N m hm v)
end
end ReciprocityTheory.AnForm.P


