-- Prove2me | Definitions.Def_WildeQIT_Degradable_PureInput
-- name    : WildeQIT_Degradable_PureInput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:13.261016+00:00
-- url     : https://prove2.me/theorems/31c15cab-789d-476c-a8ea-d4be67059981
-- title:
--   Pure input state $\varphi_{AA'}$ with a reference system of arbitrary dimension
-- statement:
--   A **pure input state** $\varphi_{AA'}$ for a channel with input $A'$ is a unit vector $|\varphi\rangle_{AA'}$ in $\mathcal H_A\otimes\mathcal H_{A'}$, where the reference system $A$ is a finite-dimensional Hilbert space of any dimension.
--
--   The mutual information $I(\mathcal N)$ (13.121) and the coherent information $Q(\mathcal N)$ (Definition 13.5.1) of a channel are maximized over these states.
--
--   **Formalization Note** The reference is `Fin m` with `m : ℕ` part of the data (every finite-dimensional Hilbert space is isometric to some $\mathbb C^m$, and the entropies are invariant under that relabeling); the joint index type is `Fin m × a`, with the reference as the left factor.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eqs. (13.120)–(13.121), pp. 406–407, and Definition 13.5.1, eq. (13.146), p. 411

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.4, p. 406, and Definition 13.5.1, p. 411
(the pure input states `φ_{AA′}` over which `I(N)` and `Q(N)` are maximized).
-/

namespace WildeQIT.Degradable

/-- **Pure input state `φ_{AA′}`** with a reference system `A` of arbitrary finite dimension
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, pp. 406–407, (13.121), and Definition 13.5.1, p. 411): a unit vector on `A ⊗ A′`.

**Formalization Note.** The book does not fix the dimension of the reference system `A`. Every
finite-dimensional Hilbert space is isometric to `ℂ^m` for some `m`, and all entropies are
invariant under such relabelings, so the reference is `Fin m` with `m : ℕ` part of the data. The
input `A′` is the right factor of `Fin m × a`. -/
structure PureInput (a : Type) [Fintype a] where
  /-- The dimension of the reference system `A`. -/
  m : ℕ
  /-- The state vector `|φ⟩_{AA′}`. -/
  ψ : EuclideanSpace ℂ (Fin m × a)
  /-- `|φ⟩` is a unit vector. -/
  norm_eq_one : ‖ψ‖ = 1

end WildeQIT.Degradable


