-- Prove2me | Definitions.Def_MMSDelta2_Supplement_NPHard
-- name    : MMSDelta2_Supplement_NPHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:04:53.227896+00:00
-- url     : https://prove2.me/theorems/f0c6fea2-d1b4-4a9b-971b-92fcbc895572
-- title:
--   NP-hardness and co-NP-hardness under polynomial-time many-one reductions
-- statement:
--   Let $L\subseteq\{0,1\}^*$ be a language.
--
--   1. $L$ is **NP-hard** if every language $L'\in\mathrm{NP}$, over any finite nonempty alphabet, reduces to $L$ by a polynomial-time many-one reduction: there is a polynomial-time computable $f$ with $x\in L'\iff f(x)\in L$ for every $x$.
--   2. $L$ is **co-NP-hard** if every language $L'\in\mathrm{coNP}$ (the complement of an NP language), over any finite nonempty alphabet, reduces to $L$ in the same way.
--
--   These are the hardness notions of Theorems 6.6, 1.2, 1.3 and 1.5 ("standard polynomial-time many-one reductions", p.12).
--
--   **Formalization Note** NP, coNP and many-one reducibility are those of the published `CookPvsNP_defs` (one-tape Turing machines), the machine model of the base mission's $\Delta_2^P$. The source alphabets range over all finite nonempty types, as in `CookPvsNP.NPComplete`.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §4 'Complexity classes and source problems', p.12 (PDF p.14)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace MMSDelta2.Supplement

/-!
# NP-hardness and co-NP-hardness of a language over `{0,1}`

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §4 "Complexity classes and source problems",
p.12 (PDF p.14): "We establish our hardness results using standard polynomial-time many-one
reductions."

**Formalization Note.** `NP`, `coNP` (complements of `NP` languages) and polynomial-time
many-one reducibility are those of the published `CookPvsNP_defs`, the machine model of the base
mission's `Δ₂ᴾ`. As in `CookPvsNP.NPComplete`, the source languages range over every finite
nonempty alphabet.
-/

/-- `L` is NP-hard: every `NP` language over any finite nonempty alphabet many-one reduces to `L`
in polynomial time (p.12). -/
def NPHard (L : Set (List Bool)) : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L' : CookPvsNP.Lang Sym),
    L' ∈ CookPvsNP.NP Sym → CookPvsNP.PolyReducible L' L

/-- `L` is co-NP-hard: every `coNP` language over any finite nonempty alphabet many-one reduces to
`L` in polynomial time (p.12). -/
def CoNPHard (L : Set (List Bool)) : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L' : CookPvsNP.Lang Sym),
    L' ∈ CookPvsNP.coNP Sym → CookPvsNP.PolyReducible L' L

end MMSDelta2.Supplement


