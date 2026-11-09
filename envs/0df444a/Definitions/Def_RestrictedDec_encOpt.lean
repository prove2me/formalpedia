-- Prove2me | Definitions.Def_RestrictedDec_encOpt
-- name    : RestrictedDec_encOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:00.997209+00:00
-- url     : https://prove2.me/theorems/f67cd6f4-2e9e-4c1b-983d-f497e3be4603
-- title:
--   Bit-string code of $\mathcal M_\perp=\mathcal M\cup\{\perp\}$
-- statement:
--   Decryption outputs live in $\mathcal M_\perp=\mathcal M\cup\{\perp\}$, where $\perp$ is the output of $\mathrm{Dec}$ on invalid ciphertexts. To hand such a value to an algorithm, or to return it as an oracle answer, it is written as a bit string:
--
--   $$\mathrm{enc}(\perp)=1,\qquad \mathrm{enc}(m)=0\,m\quad(m\in\{0,1\}^*).$$
--
--   The code is injective, and $\mathrm{dec}$ inverts it ($0m\mapsto m$, every other string $\mapsto\perp$).
--
--   This is the common interface between the scheme, the permitted functions and the adversary in every game of the mission.
--
--   **Formalization Note** An element of $\mathcal M_\perp$ is an `Option Str`, `none` being $\perp$; the module also proves `decOpt (encOpt x) = x`.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §2.1, p.12

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- The code of an element of `M_⊥ = M ∪ {⊥}` as a bit string: `⊥ ↦ 1`, `m ↦ 0m`.
Nguyen–Susilo, *Between CPA and CCA: Security Hierarchies for Restricted Decryption*, STOC 2027
submission (manuscript sha256 6aeac40c…), §2.1, p.12 ("define M⊥ := M ∪ {⊥}, where ⊥ denotes the
output of Dec on invalid ciphertexts").

**Formalization Note.** Plaintexts are bit strings `Str`; an element of `M_⊥` is an `Option Str`,
`none` being `⊥`. The code is injective; `decOpt` inverts it. It is used to feed `M_⊥` values to
polynomial-time machines and to return oracle answers (`none` = query refused). -/
def encOpt : Option Str → Str
  | none => [true]
  | some m => false :: m

/-- The inverse of `encOpt`: `0m ↦ m`; every other string is `⊥`. -/
def decOpt : Str → Option Str
  | false :: m => some m
  | _ => none

@[simp] theorem decOpt_encOpt (x : Option Str) : decOpt (encOpt x) = x := by
  cases x <;> rfl

end RestrictedDec


