-- Prove2me | Definitions.Def_KnillLaflammeQEC_codeError
-- name    : KnillLaflammeQEC_codeError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:10.416985+00:00
-- url     : https://prove2.me/theorems/cf076216-d05c-45c0-b35c-c2ce47b79c6b
-- title:
--   Error $E(\mathcal C,\mathcal R\{A\})$ of a code for one interaction operator
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space (the coding space), $\mathcal C\subseteq\mathcal H$ a subspace (the code), $\mathcal R=\{R_r\}$ a finite family of operators on $\mathcal H$ (the interaction operators of a recovery), and $A$ an operator on $\mathcal H$. The error of the code $(\mathcal C,\mathcal R)$ for the single interaction operator $A$ is
--
--   $$
--   E(\mathcal C,\mathcal R\{A\})=\max_{|\Psi\rangle\in\mathcal C,\ \|\Psi\|=1}\ \sum_r\big\|\big(R_rA-\langle\Psi|R_rA|\Psi\rangle\big)|\Psi\rangle\big\|^2 .
--   $$
--
--   Each summand is the squared distance of $R_rA|\Psi\rangle$ from its component along $|\Psi\rangle$; the error is zero exactly when every $R_rA$ maps every code state to a multiple of itself. Knill and Laflamme define the error $E(\mathcal C,\mathcal R\mathcal A)$ of a whole family $\mathcal A$ by summing also over $a$, and note that it vanishes iff the error vanishes for each $A_a$ separately; this per-operator error is the building block of the notion of an $\mathcal A$-correcting code.
--
--   **Formalization Note** $\mathcal H=\mathbb C^\iota$ (`EuclideanSpace ℂ ι`) for a finite type $\iota$, operators are matrices acting by `QAlgorithms.act`, and $\langle\Psi|X|\Psi\rangle$ is `inner ℂ ψ (act X ψ)`, conjugate-linear in the first argument. The maximum is a real `sSup` over the unit vectors of $\mathcal C$; this set of values is bounded and the supremum is attained, and for $\mathcal C=0$ the set is empty and the value is $0$. No normalization of $\mathcal R$ is assumed in the definition.
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, §3.1, p.11 (error of the code) and p.12 (per-operator form)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
§3.1, p.11 (the error of the code) and p.12 ("for each `A_a`, `E(C, RA_a) = 0`"): the error of
the code `C` with recovery `R = {R_r}` for the single interaction operator `A₀`,
`E(C, R{A₀}) = max_{|Ψ⟩ ∈ C} Σ_r ‖(R_r A₀ − ⟨Ψ|R_r A₀|Ψ⟩) |Ψ⟩‖²`.

**Formalization Note.** The coding space `H` is `EuclideanSpace ℂ ι` for a finite type `ι`
(`n = |ι|`); operators are matrices `Matrix ι ι ℂ` acting by `QAlgorithms.act`. The recovery is
a finite family `R : K → Matrix ι ι ℂ` (no normalization is assumed here). `⟨Ψ|X|Ψ⟩` is
`inner ℂ ψ (act X ψ)`, Mathlib's inner product being conjugate-linear in its first argument.
The maximum is over **unit** vectors `ψ ∈ C`, the states of the code, and is taken as a real
`sSup`: the function is continuous and the unit sphere of `C` is compact, so the set is bounded
and the supremum is attained (the paper's max). For `C = ⊥` the set is empty and the value is
`0`. -/
noncomputable def codeError {ι K : Type*} [Fintype ι] [Fintype K]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (R : K → Matrix ι ι ℂ) (A₀ : Matrix ι ι ℂ) : ℝ :=
  sSup ((fun ψ : EuclideanSpace ℂ ι => ∑ r, ‖QAlgorithms.act (R r * A₀) ψ -
      (inner ℂ ψ (QAlgorithms.act (R r * A₀) ψ)) • ψ‖ ^ 2) '' {ψ | ψ ∈ C ∧ ‖ψ‖ = 1})

end KnillLaflammeQEC


