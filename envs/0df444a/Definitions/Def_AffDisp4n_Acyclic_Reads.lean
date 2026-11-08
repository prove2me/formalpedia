-- Prove2me | Definitions.Def_AffDisp4n_Acyclic_Reads
-- name    : AffDisp4n_Acyclic_Reads
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:29.446133+00:00
-- url     : https://prove2.me/theorems/d01909cb-e924-4974-9a5d-080cdf3c540f
-- title:
--   Children of an internal value in the acyclic part
-- statement:
--   Gate $g$ **reads** the input $t$ if one of its two inputs is $t$; gate $h$ **reads** the gate $g$ if one of its two inputs is $g$. In the paper's terminology, $g$ (resp. $h$) is then a **child** of $t$ (resp. $g$). A gate that reads the same value twice is one child of that value.
--
--   These relations are the gate part of the degree of a parameter and of the "no children" condition of deletion (D2).
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.6, pp.17–18

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic

namespace AffDisp4n

/-- Gate `g` of `C` **reads the input `t`**: one of its two inputs is `t` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.6, pp.17–18: a gate
is a child of each internal value it reads, and reading the same value twice counts once). -/
def Acyclic.Reads {V : Type} (C : Acyclic V) (g : Fin C.size) (t : V) : Prop :=
  C.in₁ g = .input t ∨ C.in₂ g = .input t

/-- Gate `h` of `C` **reads the gate `g`**: one of its two inputs is the earlier gate `g`. Then `h` is a
child of `g` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.6, p.17). -/
def Acyclic.ReadsGate {V : Type} (C : Acyclic V) (h g : Fin C.size) : Prop :=
  ∃ hgh : g.val < h.val, C.in₁ h = .gate ⟨g.val, hgh⟩ ∨ C.in₂ h = .gate ⟨g.val, hgh⟩

end AffDisp4n


