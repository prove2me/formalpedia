-- Prove2me | Definitions.Def_MMSDelta2_Parameters
-- name    : MMSDelta2_Parameters
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:42.494264+00:00
-- url     : https://prove2.me/theorems/81c712d9-ca4e-466f-85d3-afb6b9a6693f
-- title:
--   Parameters of the §7 reduction: score, OPT, consistency numbers, $B$, penalties, $K$, $F$, $U$
-- statement:
--   Let $(W=\{a_1,\dots,a_{4\ell}\},T)$ be a 4-PARTITION instance, $m=4\ell$ and $R=m\ell=4\ell^2$. For $(i,j)\in[m]\times[\ell]$:
--
--   1. the **score weight** is $\omega_{i,j}=2^{R-(\ell(i-1)+j)}$, and the **score** of a solution $\mathcal S$ is $\mathrm{score}(\mathcal S)=\sum_{i=1}^m\sum_{j=1}^\ell\omega_{i,j}\,\mathrm{inc\text{-}mat}(\mathcal S)_{j,i}$; $P=2^R$, $W_{sc}=P-1$, and $\mathrm{OPT}=\max\{\mathrm{score}(\mathcal S):\mathcal S\text{ a solution}\}$;
--   2. with the base $D=\ell T+\ell+1$, the **consistency number** is $c_{i,j}=D^{i-1}+a_iD^{m+j-1}$ and the **target** is $B=\sum_{i=1}^mD^{i-1}+T\sum_{j=1}^\ell D^{m+j-1}$;
--   3. the **final-bit penalty** is $\varepsilon_{i,j}=1$ if $i=m$ and $j\ne\ell$, and $0$ otherwise;
--   4. for a set $S$ of assignment goods $h_{i,j}$: $c(S)=\sum_{h_{i,j}\in S}c_{i,j}$, $\omega(S)=\sum_{h_{i,j}\in S}\omega_{i,j}$, $\varepsilon(S)=\sum_{h_{i,j}\in S}\varepsilon_{i,j}$;
--   5. $C_{tot}=\sum_i\sum_jc_{i,j}$, $V_P=C_{tot}-(\ell-1)$, $K=2W_{sc}+2$, $F=2W_{sc}+1$ and $U=KC_{tot}+F+1$.
--
--   These integers define the valuations of the five-agent instance.
--
--   **Formalization Note** $\ell$ is $q$ and $a_i$ is $w_i$. Indices are 0-based, so $D^{i-1}$, $D^{m+j-1}$ and $\omega_{i,j}$ become $D^{i}$, $D^{m+j}$ and $2^{R-(\ell i+j+1)}$, and $\varepsilon_{i,j}=1$ iff $i=m-1$ and $j\ne\ell-1$. A set of assignment goods is a set of pairs $(i,j)$. $\mathrm{OPT}$ is the maximum over the finite set of solutions and is $0$ when there is none; every statement using it assumes a solution exists.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §7, p.27 and §7.1.2, pp.28–29 (PDF pp.29–31)

import Mathlib
import Definitions.Def_MMSDelta2_FourPartition

namespace MMSDelta2

/-!
# The parameters of the §7 reduction: score, `OPT`, consistency numbers, `B`, penalties, `K`, `F`, `U`

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §7 and §7.1.2, pp.27–29 (PDF pp.29–31). For a
source instance `(W = (a_1, …, a_{4ℓ}), T)` with `m = 4ℓ`: `R = mℓ`,
`ω_{i,j} = 2^{R−(ℓ(i−1)+j)}`, `score(S) = Σ_i Σ_j ω_{i,j} · inc-mat(S)_{j,i}`, `P = 2^R`,
`W_sc = P − 1`, `OPT = max{score(S) : S is a solution}`, `D = ℓT + ℓ + 1`,
`c_{i,j} = D^{i−1} + a_i D^{m+j−1}`, `B = Σ_{i=1}^m D^{i−1} + T Σ_{j=1}^ℓ D^{m+j−1}`,
`c(S) = Σ_{h_{i,j} ∈ S} c_{i,j}`, `ω(S) = Σ_{h_{i,j} ∈ S} ω_{i,j}`, `ε_{i,j} = 1` if `i = m` and
`j ≠ ℓ` (else `0`), `C_tot = Σ_i Σ_j c_{i,j}`, `V_P = C_tot − (ℓ − 1)`, `K = 2W_sc + 2`,
`F = 2W_sc + 1`, `U = K C_tot + F + 1`.

**Formalization Note.**
* `ℓ` is `I.q` and `a_i` is `I.w`. Indices are 0-based: `(i, j) : Fin (4ℓ) × Fin ℓ` is the paper's
  `(i+1, j+1)`, so `D^{i−1}` is `D^i`, `D^{m+j−1}` is `D^{m+j}`, `ω_{i,j}` is `2^{R−(ℓi+j+1)}` (the
  exponent is at least `0`), and `ε_{i,j} = 1` iff `i = m − 1` and `j ≠ ℓ − 1`.
* A set of assignment goods `h_{i,j}` is a `Finset (Fin (4ℓ) × Fin ℓ)`.
* `OPT` is the maximum over the (finite) set of solutions; it is `0` when there is no solution,
  and every statement about it assumes a solution exists (the promise).
* `V_P`, `K`, `F`, `U` are integers.
-/

namespace FourPartInstance

variable (I : FourPartInstance)

/-- `R = mℓ = 4ℓ²`, the length of the incidence string. -/
def R : ℕ := 4 * I.q * I.q

/-- The score weight `ω_{i,j} = 2^{R−(ℓ(i−1)+j)}` (1-based), here `2^{R−(ℓi+j+1)}`. -/
def omega (i : Fin (4 * I.q)) (j : Fin I.q) : ℕ := 2 ^ (I.R - (I.q * i.val + j.val + 1))

/-- `score(S) = Σ_i Σ_j ω_{i,j} · inc-mat(S)_{j,i}`. -/
def score (σ : Fin (4 * I.q) → Fin I.q) : ℕ :=
  ∑ i, ∑ j, I.omega i j * (if σ i = j then 1 else 0)

/-- `W_sc = P − 1 = 2^R − 1`. -/
def Wsc : ℕ := 2 ^ I.R - 1

open Classical in
/-- `OPT = max{score(S) : S is a solution of the source instance}`. -/
noncomputable def OPT : ℕ := (Finset.univ.filter I.IsSolution).sup I.score

/-- The base `D = ℓT + ℓ + 1`. -/
def D : ℕ := I.q * I.T + I.q + 1

/-- The consistency number `c_{i,j} = D^{i−1} + a_i D^{m+j−1}` (1-based). -/
def cons (i : Fin (4 * I.q)) (j : Fin I.q) : ℕ := I.D ^ i.val + I.w i * I.D ^ (4 * I.q + j.val)

/-- The target `B = Σ_{i=1}^m D^{i−1} + T Σ_{j=1}^ℓ D^{m+j−1}`. -/
def B : ℕ := ∑ i : Fin (4 * I.q), I.D ^ i.val + I.T * ∑ j : Fin I.q, I.D ^ (4 * I.q + j.val)

/-- `c(S) = Σ_{h_{i,j} ∈ S} c_{i,j}`. -/
def cSum (S : Finset (Fin (4 * I.q) × Fin I.q)) : ℕ := ∑ p ∈ S, I.cons p.1 p.2

/-- `ω(S) = Σ_{h_{i,j} ∈ S} ω_{i,j}`. -/
def omegaSum (S : Finset (Fin (4 * I.q) × Fin I.q)) : ℕ := ∑ p ∈ S, I.omega p.1 p.2

/-- The final-bit penalty `ε_{i,j} = 1` if `i = m` and `j ≠ ℓ` (1-based), else `0`. -/
def pen (i : Fin (4 * I.q)) (j : Fin I.q) : ℕ :=
  if i.val = 4 * I.q - 1 ∧ j.val ≠ I.q - 1 then 1 else 0

/-- `ε(S) = Σ_{h_{i,j} ∈ S} ε_{i,j}`. -/
def penSum (S : Finset (Fin (4 * I.q) × Fin I.q)) : ℕ := ∑ p ∈ S, I.pen p.1 p.2

/-- `C_tot = Σ_i Σ_j c_{i,j}`. -/
def Ctot : ℕ := ∑ i, ∑ j, I.cons i j

/-- `V_P = C_tot − (ℓ − 1)` (an integer). -/
def VP : ℤ := (I.Ctot : ℤ) - ((I.q : ℤ) - 1)

/-- `K = 2W_sc + 2`. -/
def K : ℤ := 2 * (I.Wsc : ℤ) + 2

/-- `F = 2W_sc + 1`. -/
def F : ℤ := 2 * (I.Wsc : ℤ) + 1

/-- `U = K C_tot + F + 1`. -/
def U : ℤ := I.K * (I.Ctot : ℤ) + I.F + 1

end FourPartInstance

end MMSDelta2


