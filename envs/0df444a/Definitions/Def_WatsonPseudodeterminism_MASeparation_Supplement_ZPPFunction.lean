-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_ZPPFunction
-- name    : WatsonPseudodeterminism_MASeparation_Supplement_ZPPFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:29:56.503139+00:00
-- url     : https://prove2.me/theorems/1951cb50-1ceb-461a-8982-41f96894e764
-- title:
--   The §3 separating function $F=f\circ g^n$ for ZPP versus psP
-- statement:
--   For $z\in\{0,1\}^n$ ($n$ even) let $z_\leftarrow=z_1\cdots z_{n/2}$ and $z_\rightarrow=z_{n/2+1}\cdots z_n$ be its halves and $|\cdot|$ the weight. Define $f:\{0,1\}^n\to\{0,1,\bot\}$ by
--   $$f(z)=\begin{cases}1&\text{if }|z_\rightarrow|\ge n/3\text{ and }|z_\leftarrow|=0,\\0&\text{if }|z_\leftarrow|\ge n/3\text{ and }|z_\rightarrow|=0,\\\bot&\text{otherwise.}\end{cases}$$
--   With block length $h=100\lceil\log_2 n\rceil$, blocks $S=\{0,1\}^h$, the inner-product gadget $g$ and its coordinatewise lift $g^n$, the communication problem is
--   $$F:S^n\times S^n\to\{0,1,\bot\},\qquad F(x,y)=f(g^n(x,y)).$$
--   The same function is also given on $nh$-bit strings via the standard block equivalence, and the family of these functions along $n=4(t+1)^2$, $t\ge0$, is a bit-string family of input lengths $N_t=n\,h(n)$.
--
--   This function separates ZPP from psP (Theorem 1). It is different from the §4 function used for Theorem 2.
--
--   **Formalization Note** The thresholds $n/3$ are compared in the reals. The weights of the halves, the block equivalence and the sizes $4(t+1)^2$ are the base mission's published `SeparatingFunction` definitions; $h$, $g$ and $g^n$ are its `Gadget` definitions.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §3, p. 8 (f and F); §2.2, p. 7 (S, g, g^n); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_SeparatingFunction

namespace WatsonPseudodeterminism.MASeparation.Supplement

/-- §3, p. 8: f(z) = 1 if |z→| ≥ n/3 and |z←| = 0; f(z) = 0 if |z←| ≥ n/3 and |z→| = 0;
⊥ otherwise. Thresholds are compared in ℝ. -/
noncomputable def zppOuterFn (n : ℕ) (z : Fin n → Bool) : Option Bool := by
  classical
  exact if (n : ℝ) / 3 ≤ (rightWeight z : ℝ) ∧ leftWeight z = 0 then some true
    else if (n : ℝ) / 3 ≤ (leftWeight z : ℝ) ∧ rightWeight z = 0 then some false
    else none

/-- §3, p. 8: F = f ∘ gⁿ on Sⁿ, with the §2.2 block length h = 100⌈log₂ n⌉. -/
noncomputable def zppLiftedFn (n : ℕ) : PartialFn
    (BlockInput (gadgetLength n) n) (BlockInput (gadgetLength n) n) :=
  fun x y => zppOuterFn n (gadgetPower x y)

/-- The same function on n·h-bit strings, via the base block equivalence. -/
noncomputable def zppFlatLiftedFn (n : ℕ) : PartialFn
    (Bits (n * gadgetLength n)) (Bits (n * gadgetLength n)) :=
  fun x y => zppLiftedFn n (blockEquiv n (gadgetLength n) x) (blockEquiv n (gadgetLength n) y)

/-- The §3 functions along the sizes n = 4(t+1)², as a bit-string family. -/
noncomputable def zppSeparationFamily : Family where
  length t := separationSize t * gadgetLength (separationSize t)
  fn t := zppFlatLiftedFn (separationSize t)

end WatsonPseudodeterminism.MASeparation.Supplement


