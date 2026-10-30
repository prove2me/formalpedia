-- Prove2me | Definitions.Def_AKNMixed_FQP_IsQuantumOperation
-- name    : AKNMixed_FQP_IsQuantumOperation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:31.267298+00:00
-- url     : https://prove2.me/theorems/56a0d51e-6937-4a68-bbd8-2b3cc70b8045
-- title:
--   Quantum operation: linear, trace-preserving, completely positive super-operator
-- statement:
--   A **super-operator** is a map $T:\mathbf L(\mathcal N)\to\mathbf L(\mathcal M)$ from operators on a finite-dimensional space $\mathcal N$ (with basis indexed by $\iota$) to operators on $\mathcal M$ (basis indexed by $\kappa$). It is a **quantum operation** when
--
--   1. $T$ is $\mathbb C$-linear;
--   2. $T$ preserves the trace: $\operatorname{Tr}(T\rho)=\operatorname{Tr}\rho$ for every $\rho$;
--   3. $T$ is completely positive: for every $n$ and every positive semidefinite $R$ on $\mathcal N\otimes\mathbb C^n$, the matrix $(T\otimes I_n)(R)$ is positive semidefinite.
--
--   These are the "physically allowed quantum operations" of the paper, and Definition 1 requires exactly these three properties of a gate.
--
--   **Formalization Note** A super-operator is any function on matrices (`QAlgorithms.Superop`); the three properties are separate conditions. Complete positivity is `PeresTerno.IsCompletelyPositive` (ampliation by $\mathbb C^n$ for every $n$).
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, §2, unnumbered, pp. 5–6 ("physically allowed quantum operations are linear trace preserving completely positive maps"); Definition 1, p. 7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_PeresTerno_kraus_basics

namespace AKNMixed.FQP

open QAlgorithms

/-- **A physically allowed quantum operation: a linear, trace-preserving, completely positive
super-operator.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1, §2,
unnumbered, pp. 5–6: "physically allowed quantum operations are linear trace preserving
completely positive maps", where (p. 5) complete positivity means that "T ⊗ I_F must be positive
… on an arbitrary finite-dimensional Hilbert space F"; Definition 1, p. 7, uses exactly these
three properties for a gate.

`IsQuantumOperation T` holds when `T` is `ℂ`-linear, preserves the trace of every matrix, and is
completely positive in the sense of `PeresTerno.IsCompletelyPositive` (for every `n` and every
positive semidefinite `R` on `ι × Fin n`, the ampliation `(T ⊗ id_n) R` is positive
semidefinite).

**Formalization Note.** A super-operator is any function on matrices (`QAlgorithms.Superop`);
the three properties are stated separately, so a unitary conjugation or a partial trace is a
quantum operation by a proof, not by construction. Trace preservation is required on all
matrices, which for a linear map is the same as on density matrices. -/
def IsQuantumOperation {ι κ : Type} [Fintype ι] [Fintype κ] (T : Superop ι κ) : Prop :=
  IsLinearMap ℂ T ∧ (∀ ρ : Matrix ι ι ℂ, (T ρ).trace = ρ.trace) ∧
    PeresTerno.IsCompletelyPositive T

end AKNMixed.FQP


