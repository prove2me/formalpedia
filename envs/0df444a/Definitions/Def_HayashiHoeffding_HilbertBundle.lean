-- Prove2me | Definitions.Def_HayashiHoeffding_HilbertBundle
-- name    : HayashiHoeffding_HilbertBundle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:16.217483+00:00
-- url     : https://prove2.me/theorems/b7ec78dd-0c37-4d29-bb48-2ddf54207a2a
-- title:
--   Bundled complex Hilbert space
-- statement:
--   A **bundled complex Hilbert space** is a type $E$ together with the structure of a normed additive group, a complex inner product compatible with the norm, and completeness of the induced metric.
--
--   This is the setting of the paper: "Let $\mathcal H$ be a Hilbert space which represents a physical system in interest." No finite dimension, separability or nontriviality is assumed.
--
--   The bundling serves one purpose: the tensor powers $\mathcal H^{\otimes n}$ are defined by recursion on $n$, and such a recursion must return a space together with its Hilbert structure.
--
--   **Formalization Note** A Lean `structure` with a field `carrier : Type u` and three instance fields (normed group, inner product space over $\mathbb C$, complete space), all registered as instances.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2

import Mathlib

namespace HayashiHoeffding

universe u

/-- A complex Hilbert space bundled with its instances: a carrier type together with a normed
additive group structure, a complex inner product space structure and completeness.

Hayashi, *Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to
Classical-Quantum Channel coding*, arXiv:quant-ph/0611013v2, "Formulation and main results",
p.2 ("Let H be a Hilbert space which represents a physical system in interest").

**Formalization Note.** This structure exists only so that the tensor powers
`H^{⊗(k+1)}` (`HayashiHoeffding.tensorPowBundle`) can be defined by recursion on `k : ℕ`: a
recursion producing types together with their instances needs a bundled carrier. -/
structure HilbertBundle : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [instNormedAddCommGroup : NormedAddCommGroup carrier]
  [instInnerProductSpace : InnerProductSpace ℂ carrier]
  [instCompleteSpace : CompleteSpace carrier]

attribute [instance] HilbertBundle.instNormedAddCommGroup HilbertBundle.instInnerProductSpace
  HilbertBundle.instCompleteSpace

end HayashiHoeffding


