-- Prove2me | Definitions.Def_ShorAdditivityEquiv_MinOutputEntropyAdditive
-- name    : ShorAdditivityEquiv_MinOutputEntropyAdditive
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:15.135522+00:00
-- url     : https://prove2.me/theorems/26e147c1-ca16-4275-beff-5a0251dee36e
-- title:
--   Statement (i): additivity of the minimum output entropy for all pairs of channels
-- statement:
--   Statement (i) of Theorem 1, *the additivity of the minimum entropy output of a quantum channel*: for **every** pair of quantum channels $N_1$ (taking $\mathbb C^{d_{1,\mathrm{in}}\times d_{1,\mathrm{in}}}$ to $\mathbb C^{d_{1,\mathrm{out}}\times d_{1,\mathrm{out}}}$) and $N_2$ (taking $\mathbb C^{d_{2,\mathrm{in}}\times d_{2,\mathrm{in}}}$ to $\mathbb C^{d_{2,\mathrm{out}}\times d_{2,\mathrm{out}}}$), of every finite dimensions,
--   $$
--   \min_{|\phi\rangle} H\big((N_1\otimes N_2)(|\phi\rangle\langle\phi|)\big) = \min_{|\phi\rangle} H\big(N_1(|\phi\rangle\langle\phi|)\big) + \min_{|\phi\rangle} H\big(N_2(|\phi\rangle\langle\phi|)\big).
--   $$
--   This is a single proposition about all channels (a conjecture at the time of the paper; it was later shown to be false by Hastings, 2009). The mission does not assert it or its negation; it only uses it as one of the four equivalent statements.
--
--   **Formalization Note** The dimensions are nonempty finite types in `Type`; "CPT map" is `QAlgorithms.IsChannel`; $N_1\otimes N_2$ is `ShorEBAdditivity.tensorChannel`, which acts on entangled inputs; the minima are `minOutputEntropy`.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Theorem 1 (i), p. 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_ShorEBAdditivity_tensorChannel
import Definitions.Def_ShorAdditivityEquiv_minOutputEntropy

open QAlgorithms

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Theorem 1 (i), p.5: "The additivity of the minimum entropy output of a quantum
channel. Suppose we have two quantum channels (CPT maps) N1 (taking C^{d1,in×d1,in} to
C^{d1,out×d1,out}) and N2 (taking C^{d2,in×d2,in} to C^{d2,out×d2,out}). Then
min_{|φ⟩} H((N1 ⊗ N2)(|φ⟩⟨φ|)) = min_{|φ⟩} H(N1(|φ⟩⟨φ|)) + min_{|φ⟩} H(N2(|φ⟩⟨φ|))".

The proposition asserts this for **every** pair of channels of **every** finite dimensions; it
is a single global statement (one of the four equivalent conjectures), not a property of one pair.

**Formalization Note.** The spaces `C^d` are nonempty finite types in `Type` (a
0-dimensional space carries no state, so `Nonempty` excludes no instance of the paper). "CPT
map" is `QAlgorithms.IsChannel` (a finite Kraus representation, which the paper gives as an
equivalent characterization, pp.2–3). `N₁ ⊗ N₂` is `ShorEBAdditivity.tensorChannel`, which acts
on every (also entangled) input of `I₁ × I₂`. The minima are `minOutputEntropy` (infima over
unit vectors, attained). -/
def MinOutputEntropyAdditive : Prop :=
  ∀ (I₁ O₁ I₂ O₂ : Type) [Fintype I₁] [DecidableEq I₁] [Nonempty I₁] [Fintype O₁]
    [DecidableEq O₁] [Nonempty O₁] [Fintype I₂] [DecidableEq I₂] [Nonempty I₂] [Fintype O₂]
    [DecidableEq O₂] [Nonempty O₂] (N₁ : Superop I₁ O₁) (N₂ : Superop I₂ O₂),
    IsChannel N₁ → IsChannel N₂ →
    minOutputEntropy (ShorEBAdditivity.tensorChannel N₁ N₂) =
      minOutputEntropy N₁ + minOutputEntropy N₂

end ShorAdditivityEquiv


