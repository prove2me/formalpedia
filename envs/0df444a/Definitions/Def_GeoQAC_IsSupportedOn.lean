-- Prove2me | Definitions.Def_GeoQAC_IsSupportedOn
-- name    : GeoQAC_IsSupportedOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:57.594311+00:00
-- url     : https://prove2.me/theorems/4cfb0b75-3686-408b-aefa-3a6569895e5a
-- title:
--   Operators supported on a set of qubits
-- statement:
--   An operator $A$ on the qubits $V$ is **supported on** $R\subseteq V$ when it acts as the identity on the complement of $R$:
--   $$
--   A = K\otimes I_{V\setminus R}
--   $$
--   for some operator $K$ on the qubits of $R$. Supported on $R$ and $R\subseteq R'$ imply supported on $R'$.
--
--   The companion operator $\mathrm{embed}_v(a)$ places a one-qubit operator $a$ on qubit $v$, with the identity elsewhere.
--
--   **Formalization Note** In matrix entries: $A_{x,y}=0$ unless the configurations $x,y$ agree off $R$, and then $A_{x,y}=K_{x|_R,\,y|_R}$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.2, p.10

import Mathlib

namespace GeoQAC

/-!
# Operators supported on a set of qubits

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §2.2, p.10: "An operator supported on R
acts as the identity on its complement."

**Formalization Note.** `IsSupportedOn R A` says `A = K ⊗ I_{Rᶜ}` for some operator `K` on the
qubits of `R`: the `(x, y)` entry of `A` vanishes unless `x` and `y` agree off `R`, and then equals
`K (x|_R) (y|_R)`. It is monotone in `R`. `embed1 v a` is the one-qubit operator `a` placed on
qubit `v` (identity elsewhere).
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `A` is supported on `R`: `A = K ⊗ I_{Rᶜ}` for an operator `K` on `R` (p.10). -/
def IsSupportedOn (R : Finset V) (A : Matrix (V → Bool) (V → Bool) ℂ) : Prop :=
  ∃ K : Matrix (R → Bool) (R → Bool) ℂ, ∀ x y : V → Bool,
    A x y = if (∀ v, v ∉ R → x v = y v) then K (fun v => x v) (fun v => y v) else 0

/-- The one-qubit operator `a` acting on qubit `v`, tensored with the identity on all other
qubits. -/
def embed1 (v : V) (a : Matrix Bool Bool ℂ) : Matrix (V → Bool) (V → Bool) ℂ :=
  Matrix.of fun x y => if (∀ u, u ≠ v → x u = y u) then a (x v) (y v) else 0

end GeoQAC


