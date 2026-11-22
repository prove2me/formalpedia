-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ParamDefs
-- name    : Formalism_ThetaLogCoordinates_ProductIdealMonotone_ParamDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:59.612972+00:00
-- url     : https://prove2.me/theorems/0f322c09-b1fd-4554-b57a-668c4e3b4ca7
-- title:
--   Param Defs
-- statement:
--   Definitions and structural lemmas for Param Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ParamDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Formalism.InvariantFactorPaths.G0
def pp (x : ℝ) : ℝ := max x 0
def gam (p : ℝ) : ℝ := p / (p ^ 2 - 1)
def oddSum (f : ℕ → ℝ) : ℝ := ∑' i : ℕ, f (2 * i + 1)
def askF {n : ℕ} (p y : ℝ) (w : ZMod n → ℝ) (s : ZMod n) : ℝ :=
  oddSum fun e => pp (y / p ^ e - w (s + (e : ZMod n)))
def minF {n : ℕ} (p y : ℝ) (w : ZMod n → ℝ) (s : ZMod n) : ℝ :=
  oddSum fun e => min (y / p ^ e) (w (s + (e : ZMod n)))
def askOn {n : ℕ} (EE : Set ℕ) (p y : ℝ) (w : ZMod n → ℝ) (s : ZMod n) : ℝ :=
  oddSum fun e => if e ∈ EE then pp (y / p ^ e - w (s + (e : ZMod n))) else 0
structure Glob where
  p : ℝ
  a : ℝ
  bp : ℝ
  wpp : ℝ
  c : ℝ
  eta : ℝ
  Nm : ℝ
  x : ℝ
structure Orb (n m : ℕ) where
  T : Finset (ZMod n)
  a : ZMod n → ℝ
  b : ZMod n → ℝ
  w : Fin m → ZMod n → ℝ
variable {n m : ℕ}
def Orb.Tev (O : Orb n m) : Finset (ZMod n) := O.T.filter fun s => Even s.val
def Orb.Tod (O : Orb n m) : Finset (ZMod n) := O.T.filter fun s => ¬ Even s.val
def dst (s s' : ZMod n) : ℕ := if s' = s then n else (s' - s).val
def vonMangoldtClassSum (G : Glob) (O : Orb n m) (j : Fin m) (s : ZMod n) : ℝ := askF G.p (O.a s) (O.w j) s
def al (G : Glob) (O : Orb n m) (s : ZMod n) : ℝ := O.a s - 2 * G.c
def cap (G : Glob) (O : Orb n m) (j : Fin m) (s : ZMod n) : ℝ := O.w j s + G.c
def lp2a (G : Glob) : ℝ := Real.logb G.p (2 * G.a)
def dl (G : Glob) (O : Orb n m) : ℝ :=
  5 * (n : ℝ) * G.Nm ^ 2 * lp2a G + 4 * (O.T.card : ℝ) * lp2a G ^ 2
def allowed (O : Orb n m) (s : ZMod n) : Set ℕ :=
  {e | ∀ s' ∈ O.T, (Even s'.val ↔ ¬ Even s.val) → e ≠ dst s s'}
def g0raw (G : Glob) (O : Orb n m) (j : Fin m) : ℝ :=
  (∑ s ∈ O.T, askOn (allowed O s) G.p (al G O s) (cap G O j) s) - dl G O
def g0 (G : Glob) (O : Orb n m) (j : Fin m) : ℝ := max (g0raw G O j) 0
def gg (G : Glob) (O : Orb n m) (j : Fin m) : ℝ :=
  gam G.p * (∑ s ∈ O.T, al G O s) - (∑ s ∈ O.Tod, minF G.p (al G O s) (cap G O j) s) - dl G O
def Pr1 (G : Glob) (O : Orb n m) (j : Fin m) : ℝ :=
  (∑ s ∈ O.Tod, (O.w j s - O.b s)) + (n : ℝ) * (G.wpp + G.eta + G.c + G.Nm)
def Prr (G : Glob) (O : Orb n m) (r : ℝ) : ℝ :=
  r * ((O.T.card : ℝ) * (2 * G.bp + G.c) + (n : ℝ) * (G.wpp + G.eta + G.c + G.Nm))
def dEv (O : Orb n m) (y : ZMod n) : ℕ := sInf {e : ℕ | 1 ≤ e ∧ y - (e : ZMod n) ∈ O.Tev}
def yMinus (O : Orb n m) (y : ZMod n) : ZMod n := y - (dEv O y : ZMod n)
def kink (G : Glob) (O : Orb n m) : ℝ :=
  ∑ y ∈ O.Tod, min (O.b y) (O.a (yMinus O y) / G.p ^ dEv O y)
end Formalism.InvariantFactorPaths.G0


