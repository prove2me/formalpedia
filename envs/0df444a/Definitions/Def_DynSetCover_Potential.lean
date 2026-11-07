-- Prove2me | Definitions.Def_DynSetCover_Potential
-- name    : DynSetCover_Potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:06.07542+00:00
-- url     : https://prove2.me/theorems/08c1118b-1600-4566-9be4-f1f89acdf2dd
-- title:
--   §6.2 — $N_i$, $\alpha_e$, copy energy $Z_Q$, the potential $\Phi$ and its tails $\Phi_i$
-- statement:
--   For an integer cutoff $i$ the **normalized retained cost** is
--   $$N_i=\sum_{Q\in\mathcal S_t,\ q_Q\ge i}C_Q2^{-q_Q}.$$
--   Each active element has coefficient $\alpha_e=8$ if it lies in a pending list and $16$ otherwise, and each copy has **copy energy**
--   $$Z_Q=2C_Q2^{-q_Q}+C_Q2^{-h_Q}+16\,\mathrm{vol}(R_Q,h_Q).$$
--   The potential is
--   $$\Phi=\sum_{Q\in\mathcal S_t}Z_Q+\sum_{e\in A_t}\big(\alpha_e\mathrm{vol}(e,\ell(e))+12\eta(\ell(e)-b(e)+L+1)\big),$$
--   and with $d_i(e)=\ell(e)-\max\{i,b(e)-L\}+1$ its tail at cutoff $i$ is
--   $$\Phi_i=\sum_{Q\in\mathcal S_t,\ q_Q\ge i}Z_Q+\sum_{e\in A_t,\ \ell(e)\ge i}\big(\alpha_e\mathrm{vol}(e,\ell(e))+12\eta\,d_i(e)\big).$$
--
--   These potentials carry the approximation analysis of the faster algorithm: $2N_i\le\Phi_i$, and $\Phi_i$ is compared with $g_i(A_t)$.
--
--   **Formalization Note** All quantities are real numbers and all sums are finite sums over the retained copies and the active elements.
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), (23), p.25 (PDF 27) and p.45 (PDF 47); §6.2, pp.47–48 (PDF 49–50), α_e, (39), (40), d_i(e), (41)

import Mathlib
import Definitions.Def_DynSetCover_Algorithm

namespace DynSetCover

/-! # Normalized retained costs and the potentials of §6

Paul, Solomon, STOC 2027 submission (sha256 a671756b…): `N_i` (23), p.25 (PDF 27) and p.45
(PDF 47); the coefficients `α_e`, the copy energy `Z_Q` (39), the potential `Φ` (40), `d_i(e)`
and the tails `Φ_i` (41), pp.47–48 (PDF 49–50).

**Formalization Note.** All quantities are real numbers; sums over retained copies and active
elements are finite sums over filters. Integer level expressions are cast to `ℝ`. -/

variable (inst : Instance)

/-- The normalized retained-cost tail (23): `N_i = Σ_{Q∈S_t, q_Q ≥ i} C_Q 2^{−q_Q}`. -/
noncomputable def Ntail (s : State inst) (i : ℤ) : ℝ :=
  ∑ Q ∈ s.copies.filter (fun Q => i ≤ s.q Q), costQ inst Q * (2 : ℝ) ^ (-s.q Q)

/-- `α_e = 8` if `e` belongs to a pending list, `16` otherwise (p.47). -/
noncomputable def alpha (s : State inst) (e : Fin inst.u) : ℝ :=
  if ∃ Q ∈ s.copies, e ∈ s.P Q then 8 else 16

/-- The copy energy (39): `Z_Q = 2C_Q 2^{−q_Q} + C_Q 2^{−h_Q} + 16 vol(R_Q, h_Q)`. -/
noncomputable def Zcopy (N : ℕ) (s : State inst) (Q : Copy inst) : ℝ :=
  2 * costQ inst Q * (2 : ℝ) ^ (-s.q Q) + costQ inst Q * (2 : ℝ) ^ (-s.h Q) +
    16 * volSet inst N (s.R Q) (s.h Q)

/-- The potential (40):
`Φ = Σ_{Q∈S_t} Z_Q + Σ_{e∈A_t} (α_e vol(e, ℓ(e)) + 12η(ℓ(e) − b(e) + L + 1))`. -/
noncomputable def Phi (N : ℕ) (s : State inst) : ℝ :=
  (∑ Q ∈ s.copies, Zcopy inst N s Q) +
    ∑ e ∈ s.active, (alpha inst s e * vol inst N e (s.level e) +
      12 * eta N * ((s.level e - inst.base e + (capL N : ℤ) + 1 : ℤ) : ℝ))

/-- `d_i(e) = ℓ(e) − max{i, b(e) − L} + 1`, for `ℓ(e) ≥ i` (p.48). -/
noncomputable def dTail (N : ℕ) (s : State inst) (i : ℤ) (e : Fin inst.u) : ℤ :=
  s.level e - max i (inst.base e - (capL N : ℤ)) + 1

/-- The potential tail (41):
`Φ_i = Σ_{Q∈S_t, q_Q ≥ i} Z_Q + Σ_{e∈A_t, ℓ(e) ≥ i} (α_e vol(e, ℓ(e)) + 12η d_i(e))`. -/
noncomputable def PhiTail (N : ℕ) (s : State inst) (i : ℤ) : ℝ :=
  (∑ Q ∈ s.copies.filter (fun Q => i ≤ s.q Q), Zcopy inst N s Q) +
    ∑ e ∈ s.active.filter (fun e => i ≤ s.level e),
      (alpha inst s e * vol inst N e (s.level e) + 12 * eta N * ((dTail inst N s i e : ℤ) : ℝ))

end DynSetCover


