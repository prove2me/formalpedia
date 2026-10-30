-- Prove2me | Definitions.Def_AKNMixed_FQP_IsLemma4Dilation
-- name    : AKNMixed_FQP_IsLemma4Dilation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:54.83659+00:00
-- url     : https://prove2.me/theorems/8c87b33d-623f-4857-af61-a337a4bc8c46
-- title:
--   $U$ is a Lemma-4 unitary dilation of the gate $g$
-- statement:
--   Let $g$ be a gate of order $(a,b)$ and $U$ a matrix on $a+b+\max(a,b)$ qubits. $U$ is a **Lemma-4 dilation** of $g$ when $U$ is unitary and
--
--   $$g\circ\rho=\Bigl(U\bigl(\rho\otimes|0\cdots0\rangle\langle0\cdots0|\bigr)U^{\dagger}\Bigr)\Big|_A\qquad\text{for every } \rho,$$
--
--   where $\rho$ occupies the first $a$ qubits, the $b+\max(a,b)$ blanks the remaining ones, and $A$ is the set of the first $b$ qubits. This is the property Lemma 4 asserts for $U_g$, and $\mathcal U_{\mathcal G}$ in Theorem 2 consists of such unitaries.
--
--   **Formalization Note** The identity is required for every matrix $\rho$; for a linear $g$ this is the same as for every density matrix. The register size is corrected: the paper prints $2a+b$ qubits with $a+b$ blanks, which equals $a+b+\max(a,b)$ when $b\le a$; for $b>a$ the printed size is too small (the order-$(1,2)$ map $\rho\mapsto\operatorname{Tr}(\rho)\,I/4$ has Choi rank $8$, but a unitary on $4$ qubits with $2$ qubits traced out gives at most $4$ Kraus operators), and $a+b+\max(a,b)$ is what the paper's proof ($V:\mathcal N\to\mathcal M\otimes\mathcal F$, $\dim\mathcal F=2^{a+b}$) needs.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 4, p. 9; notation before Theorem 2, p. 11 ("U_G the set of unitary gates corresponding to gates from G, according to lemma 4")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_marginal
import Definitions.Def_AKNMixed_FQP_padBlank

namespace AKNMixed.FQP

open QAlgorithms Matrix

/-- **`U` is a unitary dilation of the gate `g` in the sense of Lemma 4 (corrected register
size).**

Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 4, p. 9: "Let g be a quantum gate of order (n, m). There exists a unitary quantum gate U_g
on 2n + m qubits which satisfies: For any ρ, g ∘ ρ = (U_g ∘ (ρ ⊗ |0^{n+m}⟩⟨0^{n+m}|))|_A, where
A is the set of the first m qubits."; Theorem 2, p. 11: "we denote by U_G the set of unitary gates
corresponding to gates from G, according to lemma 4".

For a gate `g` of order `(a, b)` and a matrix `U` on `a + b + max a b` qubits,
`IsLemma4Dilation g U` says that `U` is unitary and that for every `a`-qubit matrix `ρ`,
`g ∘ ρ = (U (ρ ⊗ |0…0⟩⟨0…0|) U†)|_A` with `b + max a b` blank qubits and `A` the first `b` wires.

**Formalization Note.** Correction of the register size. The printed `2a + b` qubits (`a + b`
blanks) is right when `b ≤ a`, and then `a + b + max a b = 2a + b` and the blanks are the printed
`a + b`. When `b > a` it is too small: the map `ρ ↦ Tr(ρ) · I/4` of order `(1, 2)` (linear, trace
preserving, completely positive) has Choi rank `8`, while any `U` on `2·1 + 2 = 4` qubits with the
last `2` wires traced out gives a map with at most `4` Kraus operators; the proof on p. 9 itself
needs `M ⊗ F` with `F = ℂ^{2^{a+b}}`, i.e. `a + 2b` output qubits. The register used here has
`a + b + max a b` qubits, the printed size whenever the printed size works. `ρ` is on wires
`0, …, a − 1`, the blanks on the remaining wires (`padBlank`), and `A` is wires `0, …, b − 1`
(`Fin.castLEEmb`), in order. The identity is required for every matrix `ρ`, not only density
matrices; for a linear `g` the two are equivalent. -/
def IsLemma4Dilation (g : QGate)
    (U : Matrix (Qubits (g.inOrd + g.outOrd + max g.inOrd g.outOrd))
      (Qubits (g.inOrd + g.outOrd + max g.inOrd g.outOrd)) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Qubits (g.inOrd + g.outOrd + max g.inOrd g.outOrd)) ℂ ∧
    ∀ ρ : Matrix (Qubits g.inOrd) (Qubits g.inOrd) ℂ,
      g.map ρ = marginal
        (Fin.castLEEmb (by omega : g.outOrd ≤ g.inOrd + g.outOrd + max g.inOrd g.outOrd))
        (U * padBlank (by omega : g.inOrd ≤ g.inOrd + g.outOrd + max g.inOrd g.outOrd) ρ * Uᴴ)

end AKNMixed.FQP


