-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_PromiseProtocols
-- name    : InterleavedUnitaryNOF_LowerBound_PromiseProtocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:03.153231+00:00
-- url     : https://prove2.me/theorems/3b77935b-6ac1-45d5-85c3-af8cd15f710b
-- title:
--   Two-sided IUP promise protocols with free local output
-- statement:
--   The published operational NOF protocol trees are reused with three players. A finite real public law chooses the tree independently of the input. The actual transcript selects a final speaker and that speaker's visible-input output function. Communication cost is exactly the base tree's execution cost, so local output is free.
--
--   $$F_n(x)=0\Rightarrow\Pr[\Pi(x)=1]\le\eta,\qquad F_n(x)=1\Rightarrow\Pr[\Pi(x)=1]\ge1-\eta.$$
--
--   There is no requirement where the promise function is undefined. The explicit announcement transformation replaces each stopping node by one visible-input branch, preserving the answer and adding exactly one bit.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), §2 Communication complexity, p.7; Theorem 1.3 proof, p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Protocols
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Input

namespace InterleavedUnitaryNOF.LowerBound

open NOFSeparation750.CodedGIP (BitProtocol PublicProtocol View visible)
abbrev InputSpaces (n : ℕ) : Fin 3 → Type := fun _ => Bits n
abbrev BitInput (n : ℕ) := (i : Fin 3) → Bits n
abbrev LocalAnswer (n : ℕ) := (i : Fin 3) × (View (InputSpaces n) i → Bool)

/-- Execute the published protocol tree, recording its actual transcript. -/
def transcript {n : ℕ} : BitProtocol (InputSpaces n) → BitInput n → List Bool
  | .leaf _, _ => []
  | .send i f p₀ p₁, x =>
      let b := f (visible i x)
      b :: (if b then transcript p₁ x else transcript p₀ x)

/-- A local output is chosen by seed and public transcript, and depends only on
its speaker's visible input. Leaves of the base trees are used as stopping nodes. -/
structure LocalPublicProtocol (n : ℕ) where
  base : PublicProtocol (InputSpaces n)
  output : Fin base.seeds → List Bool → LocalAnswer n

def LocalPublicProtocol.answer {n : ℕ} (P : LocalPublicProtocol n)
    (s : Fin P.base.seeds) (x : BitInput n) : Bool :=
  let a := P.output s (transcript (P.base.tree s) x)
  a.2 (visible a.1 x)

noncomputable def LocalPublicProtocol.acceptance {n : ℕ} (P : LocalPublicProtocol n)
    (x : BitInput n) : ℝ :=
  ∑ s, if P.answer s x then P.base.weight s else 0

def LocalPublicProtocol.Bounded {n : ℕ} (P : LocalPublicProtocol n) (t : ℕ) : Prop :=
  P.base.Bounded t

/-- Two-sided error only on the defined values of the partial promise problem. -/
def LocalPublicProtocol.Correct {n : ℕ} (P : LocalPublicProtocol n)
    (m : ℕ) (error : ℝ) : Prop :=
  (∀ x : BitInput n, iup m (x 0) (x 1) (x 2) = some false →
    P.acceptance x ≤ error) ∧
  (∀ x : BitInput n, iup m (x 0) (x 1) (x 2) = some true →
    1 - error ≤ P.acceptance x)

/-- Publish the free local output by one additional bit. The base tree and all
its input-dependent communication are preserved. The parameter is the history. -/
def announceTree {n : ℕ} (out : List Bool → LocalAnswer n) :
    BitProtocol (InputSpaces n) → List Bool → BitProtocol (InputSpaces n)
  | .leaf _, history =>
      let a := out history
      .send a.1 a.2 (.leaf false) (.leaf true)
  | .send i f p₀ p₁, history =>
      .send i f (announceTree out p₀ (history ++ [false]))
        (announceTree out p₁ (history ++ [true]))

def LocalPublicProtocol.announce {n : ℕ} (P : LocalPublicProtocol n) :
    PublicProtocol (InputSpaces n) :=
  { P.base with tree := fun s => announceTree (P.output s) (P.base.tree s) [] }

end InterleavedUnitaryNOF.LowerBound


