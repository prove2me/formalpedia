-- Prove2me | Definitions.Def_GoodQLTC_Supplement_endpointDims
-- name    : GoodQLTC_Supplement_endpointDims
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:00:23.187977+00:00
-- url     : https://prove2.me/theorems/a064441a-aaaa-437e-8aad-5da4ed150dee
-- title:
--   Endpoint dimensions (14.1), (14.3), field exponent (14.4) and $Q_{\mathrm{end}}$ (14.5)
-- statement:
--   Fix an integer $h\ge1$ and put $s_h:=2^h$, $D_h:=s_h+1$. For a power of two $q\ge2$ let
--   $$e:=\Big\lfloor\frac{q-1}{D_h}\Big\rfloor,\qquad d:=q-1-s_he\qquad(14.1).$$
--   For integers $r$, $0\le a_1<\dots<a_t$, $q_i:=2^{r+a_i}$, $n_i:=q_i+1$, $e_i,d_i$ from (14.1) with $q=q_i$, and $L\subseteq[t]$, the **endpoint dimensions** are
--   $$(m_{i,0},m_{i,1}):=\begin{cases}(e_i+1,\ d_i+1),& i\in L,\\ (n_i-e_i-1,\ n_i-d_i-1),& i\notin L\end{cases}\qquad(14.3),$$
--   $m_{i,0}$ being the dimension at parity-$0$ endpoints. The field of (14.4) is $\mathbb F_{2^s}$ with $s:=\mathrm{lcm}\{2(r+a_i): i\in[t]\}$, and for $0<\epsilon<1/D_h<\beta<1/2$
--   $$Q_{\mathrm{end}}(h,\epsilon,\beta):=\max\Big\{2,\ \frac{1+D_h\epsilon}{1-D_h\epsilon},\ \frac{D_h(s_h-\beta)}{D_h\beta-1}\Big\}\qquad(14.5).$$
--
--   These are the parameters of the compatible Reed–Solomon cosheaves of Theorem 14.1.
--
--   **Formalization Note** `endpointDims r h a L i false` is $m_{i,0}$ and `… true` is $m_{i,1}$ (the convention of the published `GoodQLTC.BaseCodeData`). Natural-number division is the floor, and every truncated subtraction is exact ($s_he\le q-1$, $d+1\le q<n$).
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §14.1, p.52 (PDF 55) Eq. (14.1); §14.3, p.54 (PDF 57) Eqs. (14.3), (14.4); §14.4, p.55 (PDF 58) Eq. (14.5)

import Mathlib

namespace GoodQLTC.Supplement

/-- `s_h := 2^h` (arXiv:2609.20780, §14.1, p.52). -/
def sH (h : ℕ) : ℕ := 2 ^ h

/-- `D_h := s_h + 1` (arXiv:2609.20780, §14.1, p.52). -/
def DH (h : ℕ) : ℕ := sH h + 1

/-- `e := ⌊(q − 1)/D_h⌋`, Equation (14.1), arXiv:2609.20780 (held version), p.52.
**Formalization Note.** Natural-number division is the floor; `q ≥ 2` in every use. -/
def eDim (h q : ℕ) : ℕ := (q - 1) / DH h

/-- `d := q − 1 − s_h e`, Equation (14.1), arXiv:2609.20780 (held version), p.52.
**Formalization Note.** `s_h e ≤ D_h e ≤ q − 1`, so the truncated subtraction is exact. -/
def dDim (h q : ℕ) : ℕ := q - 1 - sH h * eDim h q

/-- The endpoint dimensions of Equation (14.3), Gay–Jeronimo, arXiv:2609.20780 (held version),
p.54, with `q_i := 2^{r+a_i}`, `n_i := q_i + 1`, `e_i, d_i` from (14.1) for `q = q_i`, and `L ⊆ [t]`:
`(m_{i,0}, m_{i,1}) := (e_i + 1, d_i + 1)` if `i ∈ L` and `(n_i − e_i − 1, n_i − d_i − 1)` if `i ∉ L`.

**Formalization Note.** `m i false = m_{i,0}` (parity-0 endpoint) and `m i true = m_{i,1}`, the
convention of the published `GoodQLTC.BaseCodeData`. `e_i + 1 ≤ d_i + 1 ≤ q_i < n_i`, so the
truncated subtractions are exact. -/
def endpointDims {t : ℕ} (r h : ℕ) (a : Fin t → ℕ) (Lset : Finset (Fin t)) : Fin t → Bool → ℕ :=
  fun i b =>
    let q := 2 ^ (r + a i)
    if i ∈ Lset then
      (if b then dDim h q + 1 else eDim h q + 1)
    else
      (if b then q + 1 - dDim h q - 1 else q + 1 - eDim h q - 1)

/-- The exponent `s := lcm{2(r + a_i) : i ∈ [t]}` of the field `F := F_{2^s}` of Equation (14.4),
arXiv:2609.20780 (held version), p.54. -/
def fieldExp {t : ℕ} (r : ℕ) (a : Fin t → ℕ) : ℕ :=
  Finset.univ.lcm fun i => 2 * (r + a i)

/-- `Q_end(h, ϵ, β) := max{2, (1 + D_h ϵ)/(1 − D_h ϵ), D_h(s_h − β)/(D_h β − 1)}`, Equation (14.5),
Gay–Jeronimo, arXiv:2609.20780 (held version), p.55. -/
noncomputable def Qend (h : ℕ) (ε β : ℝ) : ℝ :=
  max 2 (max ((1 + (DH h : ℝ) * ε) / (1 - (DH h : ℝ) * ε))
    ((DH h : ℝ) * ((sH h : ℝ) - β) / ((DH h : ℝ) * β - 1)))

end GoodQLTC.Supplement


