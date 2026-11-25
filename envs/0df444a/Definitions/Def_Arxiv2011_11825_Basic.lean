-- Prove2me | Definitions.Def_Arxiv2011_11825_Basic
-- name    : Arxiv2011_11825_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T09:15:51.02088+00:00
-- url     : https://prove2.me/theorems/457c4307-80ef-45fc-92f1-8bc38e164d1e
-- title:
--   Transmission-matrix model, output intensity and its segment terms
-- statement:
--   Objects of Section 2 and Supplement S1 of Guo, Zhang, Li and Pang (2020), on the transmission matrix (TM) of a scattering medium.
--
--   1. **Transmission model (eq. 1).** There are $N$ input modes (modulator pixels), with complex input field $E^{\mathrm{in}}=(E_1^{\mathrm{in}},\dots,E_N^{\mathrm{in}})\in\mathbb{C}^N$, and a complex transmission matrix $t=(t_{mi})$ whose rows are indexed by the output modes $m$. The field at output mode $m$ is
--   $$E_m^{\mathrm{out}}=\sum_{i=1}^N t_{mi}E_i^{\mathrm{in}}.$$
--   2. **Transmitted modes.** The contribution of input mode $i$ to output mode $m$ is $a_i=t_{mi}E_i^{\mathrm{in}}\in\mathbb{C}$.
--   3. **Segments.** The input modes are divided into $k$ disjoint segments $Q_1,\dots,Q_k$ covering all $N$ modes. This is encoded by a map $\sigma:\{1,\dots,N\}\to\{1,\dots,k\}$ with $Q_p=\sigma^{-1}(p)$.
--   4. **Intensity (eq. 2).** $I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2$.
--   5. **Terms of eq. (3).** For segments $p$ and $q$, with $a\cdot b=\mathrm{Re}(a\,\overline{b})$ the inner product of two phasors $a,b\in\mathbb{C}\cong\mathbb{R}^2$:
--      - the self terms $S_p=\sum_{i\in Q_p}|a_i|^2$;
--      - the interference inside $Q_p$, $A_p=\sum_{i\in Q_p}\sum_{j\in Q_p,\,j\ne i}a_i\cdot a_j$;
--      - the interference between $Q_p$ and $Q_q$, $C_{pq}=\sum_{i\in Q_p}\sum_{j\in Q_q}a_i\cdot a_j$;
--      - the bracket of segment $Q_p$, $B_p=S_p+A_p+\sum_{q\ne p}C_{pq}$.
--
--   **Formalization Note** The paper prints the terms as $(t_{mi}E_i^{\mathrm{in}})^2$ and $t_{mi}E_i^{\mathrm{in}}\cdot t_{mj}E_j^{\mathrm{in}}$ and calls them "inner products" of the modulated modes and "intensity contributions" (Sec. 2, pp. 2-3). They are therefore read as inner products of phasors: the square of $a_i$ is $|a_i|^2$ and $a_i\cdot a_j=\mathrm{Re}(a_i\overline{a_j})$. With this reading the paper's whole printed chain $I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2=(\sum_i a_i)^2=\dots$ holds. Read instead as complex multiplication, the link $|E_m^{\mathrm{out}}|^2=(E_m^{\mathrm{out}})^2$ would be false and the terms would not be intensity contributions. The paper's sum limits $\sum_{i=1,\,i\in Q_p}^{N_p}$ are read as sums over the $N_p$ modes of $Q_p$. The input modes are indexed by $\mathrm{Fin}\,N$ and the segments by $\mathrm{Fin}\,k$, so $Q_1,\dots,Q_k$ correspond to the indices $0,\dots,k-1$.
-- source:
--   Guo, Zhang, Li and Pang, Sequential Transmission Matrix Evaluation Via Spatiotemporal Transmitted Modes Decomposition, arXiv:2011.11825v1 (2020), Section 2, eqs. (1)-(3), PDF pp. 2-3; Supplement S1, eq. (S1), PDF p. 16

import Mathlib

/-!
Guo, Zhang, Li and Pang, *Sequential Transmission Matrix Evaluation Via Spatiotemporal
Transmitted Modes Decomposition*, arXiv:2011.11825v1 (2020): the transmission-matrix model of
Section 2 (eqs. (1)-(3)) and of Supplement S1 (eq. (S1)). The input plane carries `N` complex
input modes, the medium is a complex transmission matrix `t` (rows: output modes, columns: input
modes), and the input modes are divided into `k` disjoint segments `Q_1, ..., Q_k`, encoded by
the map `seg` sending each input mode to the index of its segment.
-/

noncomputable section

namespace Arxiv2011_11825

variable {M N k : ℕ}

/-- Section 2, eq. (1), PDF p. 2: the field at output mode `m`,
`E_m^out = ∑_{i=1}^N t_{mi} E_i^in`, for a complex transmission matrix `t` and complex input
field `E`. -/
def outField (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ) (m : Fin M) : ℂ :=
  ∑ i, t m i * E i

/-- Section 2, eq. (2), PDF p. 2: the contribution `t_{mi} E_i^in` of input mode `i` to the field
at output mode `m` (the transmitted mode). -/
def amp (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ) (m : Fin M) (i : Fin N) : ℂ :=
  t m i * E i

/-- Section 2, eq. (2), PDF p. 2: the intensity `I_m^out = |E_m^out|^2` of output mode `m`. -/
def outIntensity (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ) (m : Fin M) : ℝ :=
  Complex.normSq (outField t E m)

/-- Section 2, eq. (3), PDF p. 3, first term of each bracket: `∑_{i ∈ Q_p} (t_{mi} E_i^in)^2`,
the intensity contribution of each mode of segment `Q_p`. The paper calls these terms "inner
products of the modulated input modes themselves" (p. 2), so the square of the phasor `a_i` is
read as its squared modulus `|a_i|^2`. -/
def selfTerm (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ) (m : Fin M) (seg : Fin N → Fin k)
    (p : Fin k) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => seg i = p), Complex.normSq (amp t E m i)

/-- Section 2, eq. (3), PDF p. 3, second term of each bracket:
`∑_{i ∈ Q_p} ∑_{j ∈ Q_p, j ≠ i} t_{mi} E_i^in · t_{mj} E_j^in`, the interference between distinct
modes inside segment `Q_p`. The product `a_i · a_j` of two phasors is read as their inner product
in `ℝ^2`, `Re (a_i * conj a_j)`. -/
def intraTerm (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ) (m : Fin M) (seg : Fin N → Fin k)
    (p : Fin k) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => seg i = p),
    ∑ j ∈ Finset.univ.filter (fun j => seg j = p ∧ j ≠ i),
      (amp t E m i * (starRingEnd ℂ) (amp t E m j)).re

/-- Section 2, eq. (3), PDF p. 3, remaining terms of each bracket:
`∑_{i ∈ Q_p} ∑_{j ∈ Q_q} t_{mi} E_i^in · t_{mj} E_j^in`, the interference between the modes of
segment `Q_p` and those of segment `Q_q`, with `a_i · a_j` the phasor inner product
`Re (a_i * conj a_j)`. -/
def crossTerm (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ) (m : Fin M) (seg : Fin N → Fin k)
    (p q : Fin k) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => seg i = p),
    ∑ j ∈ Finset.univ.filter (fun j => seg j = q),
      (amp t E m i * (starRingEnd ℂ) (amp t E m j)).re

/-- Section 2, eq. (3.p), PDF p. 3: the square bracket of segment `Q_p`, i.e. the self terms of
`Q_p`, the interference inside `Q_p`, and the interference of `Q_p` with every other segment
`Q_q`, `q ≠ p`. -/
def segBracket (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ) (m : Fin M) (seg : Fin N → Fin k)
    (p : Fin k) : ℝ :=
  selfTerm t E m seg p + intraTerm t E m seg p +
    ∑ q ∈ Finset.univ.filter (fun q => q ≠ p), crossTerm t E m seg p q

end Arxiv2011_11825


