-- Prove2me | Definitions.Def_ICSCompute_connectU
-- name    : ICSCompute_connectU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:08.482781+00:00
-- url     : https://prove2.me/theorems/5cf1e70f-3f9e-4cde-aaf7-1c7caaa4ab77
-- title:
--   Feedback connection $\operatorname{Tr}_R[(\bigotimes_i V_i)(U\otimes I_{H_E})]$
-- statement:
--   Let $U$ be an operator from $R, X$ to $R, Y$, where $R = R_1\cdots R_n$ consists of single-qubit feedback registers, and let $V_i$ be operators on $R_i, E_i$ for auxiliary registers $E = (E_1,\dots,E_n)$. The **feedback connection**
--   $$\operatorname{Tr}_R\Big[\Big(\bigotimes_{i=1}^n V_i\Big)\big(U\otimes I_{H_E}\big)\Big]$$
--   first applies $U$ (identity on $E$), then each $V_i$ on $R_i, E_i$ (identity on $Y$), and finally identifies the output and input copies of $R$ by the partial trace. It is an operator from $X, E$ to $Y, E$; the auxiliary registers remain external.
--
--   This is the operator whose unitarity characterizes pure PMGs (condition (4.2)), and with $U = U_C$ of (6.4) it is the matrix $T_{\mathbf V}$ of the validity proof of Theorem 6.1.
--
--   **Formalization Note** The auxiliary registers are arbitrary finite index types $E_i$; the registers are ordered $R, (Y, E)$ before the trace.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), Definition 4.8, eq. (4.2), p.21 (PDF p.23); §6.1, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_ICSCompute_ptraceR

namespace ICSCompute

open QAlgorithms

/-- `U ⊗ I_{H_E}` on `R, X, E → R, Y, E` for `U : R, X → R, Y`. -/
def onRQ {n : ℕ} {X Y : Type*} {E : Type*} [DecidableEq E]
    (U : Matrix (Qubits n × Y) (Qubits n × X) ℂ) :
    Matrix (Qubits n × (Y × E)) (Qubits n × (X × E)) ℂ :=
  Matrix.of fun o i => if o.2.2 = i.2.2 then U (o.1, o.2.1) (i.1, i.2.1) else 0

/-- `⨂ᵢ Vᵢ` with `Vᵢ` acting on `Rᵢ, Eᵢ`, as the identity on the remaining register `Y`. -/
def onRE {n : ℕ} {Y : Type*} [DecidableEq Y] {E : Fin n → Type*}
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ) :
    Matrix (Qubits n × (Y × ((i : Fin n) → E i))) (Qubits n × (Y × ((i : Fin n) → E i))) ℂ :=
  Matrix.of fun o i => if o.2.1 = i.2.1 then ∏ k, V k (o.1 k, o.2.2 k) (i.1 k, i.2.2 k) else 0

/-- **The feedback connection of local operators** `Tr_R[(⨂ᵢ Vᵢ)(U ⊗ I_{H_E})]` (Shmueli, *What
Can Be Computed with Indefinite Causal Structure?*, arXiv:2610.40573, version of 2026-11-03,
sha256 d3e36399…b606, Definition 4.8, eq. (4.2), p.21 (PDF p.23); the matrix `T_V` of §6.1,
p.32 (PDF p.34)).

For an operator `U` from `R, X` to `R, Y` (`R = R₁ ⋯ Rₙ` the single-qubit feedback registers)
and operators `Vᵢ` on `Rᵢ, Eᵢ`: first `U ⊗ I_E`, then `⨂ᵢ Vᵢ`, then the partial trace over
`R` ("we identify corresponding feedback input and output registers, and each operator acts as
the identity on registers not mentioned in its definition. The auxiliary registers remain
external and are not traced out"). The result is an operator from `X, E` to `Y, E`.

**Formalization Note** The registers are ordered `R, (Y, E)` before the trace and `Y, E` after;
`E = (E₁, …, Eₙ)` is the dependent product of the auxiliary index types. -/
def connectU {n : ℕ} {X Y : Type*} [Fintype Y] [DecidableEq Y] {E : Fin n → Type*} [∀ i, Fintype (E i)]
    [∀ i, DecidableEq (E i)] (U : Matrix (Qubits n × Y) (Qubits n × X) ℂ)
    (V : (i : Fin n) → Matrix (Bool × E i) (Bool × E i) ℂ) :
    Matrix (Y × ((i : Fin n) → E i)) (X × ((i : Fin n) → E i)) ℂ :=
  ptraceR (onRE (Y := Y) V * onRQ (E := (i : Fin n) → E i) U)

end ICSCompute


