-- Prove2me | Definitions.Def_MagnonCode_AQEDC_IsLocalOn
-- name    : MagnonCode_AQEDC_IsLocalOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:29.55522+00:00
-- url     : https://prove2.me/theorems/48293acf-849b-486c-9b2b-db08a01cebd5
-- title:
--   Operator acting only on a set $A$ of sites, $F = F_A\otimes I$
-- statement:
--   Let $A\subseteq\{1,\dots,n\}$ be a set of sites of $(\mathbb C^p)^{\otimes n}$. An operator $F$ **acts on $A$** if it has the form $F = F_A\otimes I$, with $F_A$ an operator on the qudits of $A$ and the identity on the complement. In matrix entries, indexed by basis strings $x,y$,
--
--   $$
--   F_{x,y} = \begin{cases} (F_A)_{x|_A,\,y|_A} & \text{if } x \text{ and } y \text{ agree off } A,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   The set $A$ is arbitrary. In particular it may be disconnected, which is the setting of the paper's error model.
--
--   **Formalization Note** Basis strings are functions from the sites `Fin n` to `Fin p`. The sites printed $1,\dots,n$ are $0,\dots,n-1$ in Lean.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, p. 5 and p. 63

import Mathlib

namespace MagnonCode.AQEDC

/-- **Operator acting on a set of sites** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 5 and p. 63):
`F` acts as `F_A ⊗ I`, i.e. only on the sites of `A` and as the identity on the complement of `A`.
There is an operator `G` on the qudits of `A` with `F x y = G (x|_A) (y|_A)` when `x, y` agree off
`A`, and `F x y = 0` otherwise.

**Formalization Note** Basis states of `(ℂ^p)^{⊗n}` are `Fin n → Fin p`; sites are `Fin n`, printed
`1, …, n`. The set `A` is arbitrary: it may be disconnected ("their support may be disconnected",
p. 5). -/
def IsLocalOn {n p : ℕ} (A : Finset (Fin n))
    (F : Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ) : Prop :=
  ∃ G : Matrix (A → Fin p) (A → Fin p) ℂ, ∀ x y : Fin n → Fin p,
    F x y = if ∀ i, i ∉ A → x i = y i then G (fun i => x i) (fun i => y i) else 0

end MagnonCode.AQEDC


