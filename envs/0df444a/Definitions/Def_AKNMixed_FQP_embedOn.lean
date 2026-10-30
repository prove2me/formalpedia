-- Prove2me | Definitions.Def_AKNMixed_FQP_embedOn
-- name    : AKNMixed_FQP_embedOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:55.171987+00:00
-- url     : https://prove2.me/theorems/20413c2c-87c9-4f09-a487-5dacf14c4ccd
-- title:
--   A $k$-qubit super-operator on chosen wires, extended by the identity ($T\otimes I$)
-- statement:
--   Let $w=(w_0,\dots,w_{k-1})$ be $k$ distinct wires of an $N$-qubit system and $T$ a super-operator on $k$ qubits. The extension $\mathrm{embedOn}_w(T)$ acts on an $N$-qubit matrix $X$ blockwise: for basis configurations $y,z\in\{0,1\}^N$,
--
--   $$\mathrm{embedOn}_w(T)(X)_{y,z}=T\bigl(B_{y,z}\bigr)_{y|_w,\;z|_w},\qquad (B_{y,z})_{a,b}=X_{\,y[w\leftarrow a],\;z[w\leftarrow b]},$$
--
--   where $y[w\leftarrow a]$ is $y$ with the bits $a$ written on the wires $w$ and $y|_w$ is the restriction of $y$ to the wires $w$ (in the order of $w$). For linear $T$ this is $T\otimes I$, with $T$ on the wires $w$ and the identity on the other $N-k$ wires.
--
--   This is how a gate acts on the whole system ("To extend the gates to operate on the whole set of n qubits, we tensor with the identity").
--
--   **Formalization Note** The same formula as `QAlgorithms.liftSuperop` without its environment factor; $y[w\leftarrow a]$ is `QAlgorithms.overwrite w y a`.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, §2, unnumbered, p. 6 (extension by tensor product with the identity); proof of Lemma 3, p. 8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel

namespace AKNMixed.FQP

open QAlgorithms

/-- **A super-operator on `k` chosen wires, extended by the identity to `N` wires (`T ⊗ I`).**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1, §2,
unnumbered, p. 6: "Super-operators can be extended to operate on larger spaces by taking tensor
product with the identity operator: T : L(N) → L(M) will be extended to
T ⊗ I : L(N ⊗ R) → L(M ⊗ R)"; p. 8 (proof of Lemma 3): "To extend the gates to operate on the
whole set of n qubits, we tensor with the identity."

For an injective listing `w : Fin k ↪ Fin N` of `k` distinct wires out of `N`, and a
super-operator `T` on `k` qubits, `embedOn w T` acts on an `N`-qubit matrix `X` blockwise: for
basis configurations `y, z` of the `N` wires,
`(embedOn w T X) y z = T(B_{y,z}) (y ∘ w) (z ∘ w)`, where `B_{y,z}` is the `k`-qubit block
`a, b ↦ X (y with a written on w) (z with b written on w)`. For linear `T` this is
`T ⊗ id` with `T` on the wires `w` (in the order `w 0, w 1, …`) and the identity on the others.

**Formalization Note.** This is `QAlgorithms.liftSuperop` without its extra environment
factor; `QAlgorithms.overwrite w y a` writes `a` onto the wires of `w` and keeps `y` elsewhere. -/
noncomputable def embedOn {k N : ℕ} (w : Fin k ↪ Fin N) (T : Superop (Qubits k) (Qubits k)) :
    Superop (Qubits N) (Qubits N) :=
  fun X => Matrix.of fun y z =>
    T (Matrix.of fun a b => X (overwrite w y a) (overwrite w z b)) (y ∘ w) (z ∘ w)

end AKNMixed.FQP


