-- Prove2me | Definitions.Def_AKNMixed_FQP_marginal
-- name    : AKNMixed_FQP_marginal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:02.858564+00:00
-- url     : https://prove2.me/theorems/7a31f724-586e-4bf7-89e5-afacd3e7d225
-- title:
--   Reduced density matrix $\rho|_A$ on a list of wires
-- statement:
--   Let $A=(w_0,\dots,w_{r-1})$ be $r$ distinct wires of an $N$-qubit system and $X$ an $N$-qubit matrix. The **reduced matrix** of $X$ on $A$ is the $r$-qubit matrix obtained by tracing out every other wire:
--
--   $$(X|_A)_{a,b}=\sum_{e}X_{(a,e),(b,e)},$$
--
--   where $(a,e)$ is the basis configuration with $a$ on the wires of $A$ (in the order of $A$) and $e$ on the other $N-r$ wires, and the sum runs over all $e\in\{0,1\}^{N-r}$.
--
--   It is used for the computed function (Definition 4) and for Lemma 4.
--
--   **Formalization Note** Written as a sum over all $y\in\{0,1\}^N$ whose restriction to $A$ is $a$, pairing $y$ with $y$ overwritten by $b$ on $A$.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, §2, unnumbered, p. 5 (reduced density matrix, "the rest of the system … is traced out"); Definition 4, p. 9; Lemma 4, p. 9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel

namespace AKNMixed.FQP

open QAlgorithms

/-- **The reduced density matrix `ρ|_A` on a list of wires (partial trace over the rest).**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1, §2,
unnumbered, p. 5 (the reduced density matrix of a subsystem, obtained when "the rest of the system
… is traced out", `ρ|_A = Tr_F ρ`); used in Definition 4, p. 9 and Lemma 4, p. 9.

For an injective listing `w : Fin r ↪ Fin N` of `r` wires and an `N`-qubit matrix `X`,
`marginal w X` is the `r`-qubit matrix
`(marginal w X) a b = Σ_e X (a, e) (b, e)`, the sum over the basis configurations `e` of the
wires outside `w`, where `(a, e)` is the configuration with `a` on the wires `w` (in the order of
`w`) and `e` elsewhere.

**Formalization Note.** Written as a sum over all `y : Qubits N` with `y ∘ w = a`, pairing `y`
with `y` overwritten by `b` on the wires `w` (`QAlgorithms.overwrite`). -/
noncomputable def marginal {r N : ℕ} (w : Fin r ↪ Fin N) (X : Matrix (Qubits N) (Qubits N) ℂ) :
    Matrix (Qubits r) (Qubits r) ℂ :=
  Matrix.of fun a b => ∑ y : Qubits N, if y ∘ w = a then X y (overwrite w y b) else 0

end AKNMixed.FQP


