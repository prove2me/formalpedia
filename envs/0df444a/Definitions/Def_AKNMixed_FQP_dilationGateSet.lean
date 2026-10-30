-- Prove2me | Definitions.Def_AKNMixed_FQP_dilationGateSet
-- name    : AKNMixed_FQP_dilationGateSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:19:02.950869+00:00
-- url     : https://prove2.me/theorems/3f79e21c-792f-47a1-96f7-d83a56005dd3
-- title:
--   Gate set $\mathcal U_{\mathcal G}\cup\mathcal U_{\mathcal G}^\dagger\cup\{C,\text{Toffoli}\}$
-- statement:
--   Let $\mathcal G$ be a gate set and, for every $g\in\mathcal G$ of order $(a,b)$, let $U_g$ be a matrix on $a+b+\max(a,b)$ qubits (in Theorem 2, a Lemma-4 dilation of $g$). The gate set
--
--   $$\mathcal U_{\mathcal G}\cup\mathcal U_{\mathcal G}^{\dagger}\cup\{C,\ \text{Toffoli}\}$$
--
--   consists of the gates $U_g\cdot U_g^{\dagger}$, the gates $U_g^{\dagger}\cdot U_g$ ($g\in\mathcal G$), the controlled-not gate and the Toffoli gate.
--
--   **Formalization Note** The Toffoli gate is not in the printed set $\mathcal U_{\mathcal G}\cup\mathcal U^{\dagger}_{\mathcal G}\cup\mathcal C$; it is the correction of Theorem 2, which is false without it.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, notation before Theorem 2, p. 11; Toffoli added (correction of Theorem 2)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_unitaryGate
import Definitions.Def_AKNMixed_FQP_cnotGate
import Definitions.Def_AKNMixed_FQP_toffoliGate

namespace AKNMixed.FQP

open QAlgorithms

/-- **The gate set `U_G ∪ U_G† ∪ {C, Toffoli}`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1, §4.2,
unnumbered, p. 11: "For a family of gates G we denote by U_G the set of unitary gates
corresponding to gates from G, according to lemma 4. We denote by U_G† the set of daggered
unitary gates corresponding to gates from G. C is a special unitary gate on two qubits, the
controlled not gate."

Given, for every gate `g ∈ G`, a matrix `u g hg` on `inOrd + outOrd + max inOrd outOrd` qubits
(intended: a Lemma-4 dilation of `g`, `AKNMixed.FQP.IsLemma4Dilation`, whose register size is
corrected from the printed `2·inOrd + outOrd`), `dilationGateSet G u` consists of the gates `U · U†` for `U = u g hg`,
the gates `U† · U` for the same `U`, the controlled-not gate `C` and the Toffoli gate.

**Formalization Note.** The Toffoli gate is not in the printed set `U_G ∪ U_G† ∪ C`; it is the
correction of Theorem 2 (`AKNMixed.FQP.fqp_fqp_eq_fqp`), whose printed form is false without
it. -/
noncomputable def dilationGateSet (G : Set QGate)
    (u : ∀ g ∈ G, Matrix (Qubits (g.inOrd + g.outOrd + max g.inOrd g.outOrd))
      (Qubits (g.inOrd + g.outOrd + max g.inOrd g.outOrd)) ℂ) :
    Set QGate :=
  {x | ∃ (g : QGate) (hg : g ∈ G), x = unitaryGate (u g hg) ∨ x = unitaryGate (star (u g hg))} ∪
    {cnotGate, toffoliGate}

end AKNMixed.FQP


