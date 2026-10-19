-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
-- name    : OAI_Combinatorics_FiniteCircle_DyadicShifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:51:48.264524+00:00
-- url     : https://prove2.me/theorems/eac73ce2-c552-43bf-bd6c-62dac983e483
-- title:
--   Coordinate characters and coordinate frequencies of characters of $(\mathbb{Z}/M)^I$
-- statement:
--   Let $I$ be an index set, $M\in\mathbb{N}$, and let $\chi$ be an additive character of the group $(\mathbb{Z}/M)^I$ of $\mathbb{Z}/M$-valued functions on $I$, that is, a map $\chi:(\mathbb{Z}/M)^I\to\mathbb{C}$ with $\chi(0)=1$ and $\chi(u+v)=\chi(u)\chi(v)$. For $r\in I$ and $a\in\mathbb{Z}/M$ let $e_r(a)$ be the function equal to $a$ at $r$ and to $0$ elsewhere.
--
--   1. **Coordinate character.** $\chi_r(a)=\chi(e_r(a))$ defines an additive character $\chi_r$ of $\mathbb{Z}/M$, the restriction of $\chi$ to the $r$-th coordinate.
--   2. **Coordinate frequency.** For $M\ge1$, the frequency $\xi_r\in\mathbb{Z}/M$ is the unique residue with
--   $$
--   \chi\bigl(e_r(a)\bigr)=\exp\Bigl(\frac{2\pi\sqrt{-1}\,\xi_r\,a}{M}\Bigr)\qquad\text{for all }a\in\mathbb{Z}/M,
--   $$
--   obtained from the standard isomorphism between $\mathbb{Z}/M$ and its group of characters.
--
--   For finite $I$ the character factors as $\chi(u)=\prod_{r\in I}\exp\bigl(2\pi\sqrt{-1}\,\xi_r u_r/M\bigr)$, so $(\xi_r)_{r\in I}$ is the frequency vector of $\chi$. The circular sizes $|\tilde\xi_r|$ of these frequencies (with $\tilde\xi_r$ the representative of least absolute value) measure how fast $\chi$ oscillates along each coordinate; lower bounds on their sum are what the dyadic-shift estimates and the distortion argument use.
--
--   **Formalization Note** The definitions are `coordinateChar χ r`, the composition of $\chi$ with `AddMonoidHom.single` (it needs decidable equality on $I$), and `coordinateFrequency χ r`, the preimage of `coordinateChar χ r` under `AddChar.zmodAddEquiv`, which requires `NeZero M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/DyadicShifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/DyadicShifts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

noncomputable def coordinateChar {I : Type*} [DecidableEq I] {M : ℕ}
    (χ : AddChar (I → ZMod M) ℂ) (i : I) : AddChar (ZMod M) ℂ :=
  χ.compAddMonoidHom (AddMonoidHom.single (fun _ : I => ZMod M) i)

noncomputable def coordinateFrequency {I : Type*} [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (i : I) : ZMod M :=
  AddChar.zmodAddEquiv.symm (coordinateChar χ i)

end FiniteCircle

end OAI


