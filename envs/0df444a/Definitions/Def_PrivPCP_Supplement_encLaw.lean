-- Prove2me | Definitions.Def_PrivPCP_Supplement_encLaw
-- name    : PrivPCP_Supplement_encLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:56:53.333714+00:00
-- url     : https://prove2.me/theorems/0262f94e-c933-4fa0-a48a-4f43c839d87b
-- title:
--   The randomized tensor Reed–Solomon encoding $\mathrm{Enc}(A)=\mathrm{ev}_\Omega(P)$, $P\sim\mathrm{Unif}(R_d(A))$ (§5.2)
-- statement:
--   Let $D,\Omega\subseteq\mathbb F_q^k$ be grids and $d=(d_1,\dots,d_k)$ a degree vector. Write $\mathcal P_d$ for the polynomials $P\in\mathbb F_q[X_1,\dots,X_k]$ with $\deg_{X_i}P\le d_i$ for every $i$, and for a table $A:D\to\mathbb F_q$ put
--   $$
--   R_d(A)=\{P\in\mathcal P_d:\ P|_D=A\}.
--   $$
--   The **encoding** of $A$ is $\mathrm{Enc}(A)=\{\mathrm{ev}_\Omega(P):P\in R_d(A)\}$, the evaluation tables on $\Omega$ of these polynomials, and its law $\mathcal C_A$ is that of $\mathrm{ev}_\Omega(P)$ for $P$ uniform in $R_d(A)$. This is the randomized classical encoding (Definition 5.2) with respect to which Theorem 5.5's circuit is private and robust, with $d_i=h_i+\lceil s_i/128\rceil$.
--
--   **Formalization Note** Polynomials of $\mathcal P_d$ are their coefficient tensors. $R_d(A)$ is nonempty whenever $d_i\ge h_i-1$ for all $i$ (coordinatewise interpolation), which holds in the setting of Lemma 5.4; the point mass at $0$ used for an empty $R_d(A)$ never occurs there.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §5.2, p.30 (PDF p.32); Definition 5.2, p.27 (PDF p.29)

import Mathlib

set_option autoImplicit false

namespace PrivPCP.Supplement

open Classical

/-- A polynomial `P ∈ 𝔽_q[X_1, …, X_k]` with `deg_{X_i} P ⩽ d_i` for every `i`, as its coefficient
tensor (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256
c2cac1e0…), §5.2, p.30: the space `P_d`). -/
abbrev Coef (q k : ℕ) (d : Fin k → ℕ) : Type := (∀ i : Fin k, Fin (d i + 1)) → ZMod q

/-- The value `P(z)` of the polynomial with coefficient tensor `c` at `z ∈ 𝔽_q^k`. -/
def coefEval {q k : ℕ} {d : Fin k → ℕ} (c : Coef q k d) (z : Fin k → ZMod q) : ZMod q :=
  ∑ m, c m * ∏ i, z i ^ (m i : ℕ)

/-- `R_d(A) = {P ∈ P_d : P|_D = A}` (§5.2, p.30). -/
noncomputable def Rd {q k : ℕ} [NeZero q] (d : Fin k → ℕ) (D : Finset (Fin k → ZMod q))
    (A : ↥D → ZMod q) : Finset (Coef q k d) :=
  Finset.univ.filter fun c => ∀ z : ↥D, coefEval c z.1 = A z

/-- The **set `Enc(A) = {ev_Ω(P) : P ∈ R_d(A)}`** of encodings of a table `A : D → 𝔽_q` (§5.2, p.30;
Definition 5.2, p.27): evaluation tables on `Ω` of the polynomials of individual degree `⩽ d` that
agree with `A` on `D`. -/
def encSet {q k : ℕ} [NeZero q] (d : Fin k → ℕ) (D Ω : Finset (Fin k → ZMod q))
    (A : ↥D → ZMod q) : Set (↥Ω → ZMod q) :=
  {w | ∃ c ∈ Rd d D A, w = fun z => coefEval c z.1}

/-- The **law `C_A` of the randomized encoding** `Enc(A; r) = ev_Ω(P)` with `P ∼ Unif(R_d(A))`
(§5.2, p.30; Definition 5.2, p.27).

**Formalization Note** `R_d(A)` is nonempty whenever `d_i ⩾ h_i − 1` for every `i` (coordinatewise
interpolation, p.30), which holds in the setting of Lemma 5.4; the point mass at `0` for an empty
`R_d(A)` is never used there. -/
noncomputable def encLaw {q k : ℕ} [NeZero q] (d : Fin k → ℕ) (D Ω : Finset (Fin k → ZMod q))
    (A : ↥D → ZMod q) : PMF (↥Ω → ZMod q) :=
  if h : (Rd d D A).Nonempty then
    (PMF.uniformOfFinset _ h).map fun c z => coefEval c z.1
  else PMF.pure 0

end PrivPCP.Supplement


