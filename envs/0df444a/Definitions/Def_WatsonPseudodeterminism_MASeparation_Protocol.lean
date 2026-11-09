-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Protocol
-- name    : WatsonPseudodeterminism_MASeparation_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:44.675279+00:00
-- url     : https://prove2.me/theorems/fdcbd274-a274-4f43-95f2-5d9dc40bde28
-- title:
--   Two-party binary protocol trees and acceptance probabilities
-- statement:
--   Let $X$ and $Y$ be Alice's and Bob's input spaces. A deterministic protocol is a finite binary tree. An Alice node chooses its outgoing edge from $x\in X$ alone, and a Bob node from $y\in Y$ alone. Leaves carry fixed Boolean output labels. Depth counts the largest number of transmitted bits on a root-to-leaf path. A partial function has values $0,1,\bot$, represented by `Option Bool`.
--
--   A public-coin randomized protocol is an input-independent probability mass function $D$ on these trees. Its acceptance probability is
--
--   $$D(x,y)=\Pr_{P\sim D}[P(x,y)=1].$$
--
--   A depth bound applies to every tree of positive probability. This interface separates communication locality and actual tree depth from correctness conditions. PMF probabilities have total mass one, so conversion from extended nonnegative reals is always finite.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §1.1, pp. 3–4 (deterministic protocols and D(x,y)); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Mathlib

namespace WatsonPseudodeterminism.MASeparation

/-- §1.1, pp. 3–4: a finite binary communication tree; the output is its leaf label. -/
inductive Protocol (X Y : Type) where
  | leaf (output : Bool)
  | alice (bit : X → Bool) (zero one : Protocol X Y)
  | bob (bit : Y → Bool) (zero one : Protocol X Y)

/-- The current speaker reads only their own input. -/
def Protocol.eval {X Y : Type} : Protocol X Y → X → Y → Bool
  | .leaf b, _, _ => b
  | .alice bit p q, x, y => if bit x then q.eval x y else p.eval x y
  | .bob bit p q, x, y => if bit y then q.eval x y else p.eval x y

/-- Worst root-to-leaf transmitted-bit count. -/
def Protocol.depth {X Y : Type} : Protocol X Y → ℕ
  | .leaf _ => 0
  | .alice _ p q => 1 + max p.depth q.depth
  | .bob _ p q => 1 + max p.depth q.depth

abbrev PartialFn (X Y : Type) := X → Y → Option Bool

/-- Public randomness, chosen independently of the input. -/
abbrev RandomProtocol (X Y : Type) := PMF (Protocol X Y)

/-- Every deterministic protocol with positive mass obeys the depth bound. -/
def DepthBound {X Y : Type} (D : RandomProtocol X Y) (d : ℕ) : Prop :=
  ∀ P ∈ D.support, P.depth ≤ d

/-- §1.1, p. 3: D(x,y) = Pr[P(x,y)=1]. A PMF has total mass one. -/
noncomputable def acceptance {X Y : Type} (D : RandomProtocol X Y) (x : X) (y : Y) : ℝ :=
  (D.toOuterMeasure {P | P.eval x y = true}).toReal

end WatsonPseudodeterminism.MASeparation


