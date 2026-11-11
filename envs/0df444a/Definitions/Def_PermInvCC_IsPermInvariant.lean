-- Prove2me | Definitions.Def_PermInvCC_IsPermInvariant
-- name    : PermInvCC_IsPermInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:58.721883+00:00
-- url     : https://prove2.me/theorems/d5913f15-8314-4246-b7ec-98cfb0508154
-- title:
--   Permutation invariance $f(\pi x,\pi y)=f(x,y)$
-- statement:
--   For a permutation $\pi\in S_n$ the string $\pi x$ moves the symbol at position $i$ to position $\pi(i)$:
--   $$(\pi x)_{\pi(i)}:=x_i\qquad(i\in[n]).$$
--   A partial function $f$ is **permutation-invariant** if
--   $$f(\pi x,\pi y)=f(x,y)\quad\text{for all }x,y\text{ and all }\pi\in S_n .$$
--   The equality includes the value $*$, so the promise is invariant as well.
--
--   Such a function depends only on the joint type of $(x,y)$; it is the hypothesis of the paper's main theorem.
--
--   **Formalization Note** $\pi x$ is $x\circ\pi^{-1}$, which is exactly $(\pi x)_{\pi(i)}=x_i$.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.2, p.9

import Mathlib
import Definitions.Def_PermInvCC_PartialFn

namespace PermInvCC

/-- The action of a permutation `π ∈ Sₙ` on a string: `πx` moves the symbol at position `i` to
position `π(i)`, i.e. `(πx)_{π(i)} = x_i` (Y. Huang and Z. Ye, arXiv:2609.40116, held version
sha256 fe1797dd…, Definition 2.2, p.9).

**Formalization Note.** `(πx)_{π(i)} = x_i` for all `i` means `πx = x ∘ π⁻¹`. -/
def permAct {n : ℕ} {α : Type} (π : Equiv.Perm (Fin n)) (x : Fin n → α) : Fin n → α :=
  x ∘ π.symm

/-- **Permutation invariance** (arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.2,
p.9): `f(πx, πy) = f(x, y)` for every `x, y` and every `π ∈ Sₙ`. The equality includes the value
`∗` (`none`), so the promise is invariant as well. -/
def IsPermInvariant {n q : ℕ} (f : PartialFn n q) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x y : Fin n → Fin q), f (permAct π x) (permAct π y) = f x y

end PermInvCC


