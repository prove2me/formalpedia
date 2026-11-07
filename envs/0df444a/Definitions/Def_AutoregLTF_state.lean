-- Prove2me | Definitions.Def_AutoregLTF_state
-- name    : AutoregLTF_state
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:42.268546+00:00
-- url     : https://prove2.me/theorems/9a8c97b4-7ab9-409b-a706-691c0ab571db
-- title:
--   The recursion (4)–(9) with several LTFs and the row encoding $\theta$
-- statement:
--   Fix $m\ge2$ and a labeling $\lambda\in\{0,1\}^{m\times m}$, and write $[m]=\{1,\dots,m\}$. The encoding of row $i$ is $\theta_i=\sum_{j=1}^m2^{j-1}\lambda_{i,j}$. For a selected row $i\in[m]$ and $t\ge0$ the state $f^t_{\theta,i}\in\{0,1\}^{3m+2}$ consists of row bits $f^t_{\theta,i,\mathrm{row},j}$ ($j\in[m]$), a test bit $f^t_{\theta,i,\mathrm{test}}$, output bits $f^t_{\theta,i,\mathrm{out},j}$ ($j\in[m]$) and pointer bits $f^t_{\theta,i,\mathrm{ptr},j}$ ($j\in[m+1]$). Initially (4)
--
--   $$f^0_{\mathrm{row},j}=\mathbf 1\{j=i\},\quad f^0_{\mathrm{test}}=f^0_{\mathrm{ptr},m+1}=1,\quad f^0_{\mathrm{out},j}=f^0_{\mathrm{ptr},j}=0\quad(j\in[m]),$$
--
--   and one round (5)–(9) is
--
--   $$\begin{aligned}
--   f^{t+1}_{\mathrm{row},j}&=f^t_{\mathrm{row},j},\\
--   f^{t+1}_{\mathrm{test}}&=\mathbf 1\Big\{\sum_{j=1}^m\theta_jf^t_{\mathrm{row},j}-\sum_{j=1}^m2^{j-1}\big(f^t_{\mathrm{out},j}+f^t_{\mathrm{ptr},j}\big)\ge0\Big\},\\
--   f^{t+1}_{\mathrm{out},j}&=\mathbf 1\{2f^t_{\mathrm{out},j}+f^t_{\mathrm{ptr},j}+f^{t+1}_{\mathrm{test}}\ge2\},\\
--   f^{t+1}_{\mathrm{ptr},j}&=f^t_{\mathrm{ptr},j+1}\ (j\in[m]),\qquad f^{t+1}_{\mathrm{ptr},m+1}=0.
--   \end{aligned}$$
--
--   The recursion reads off the binary digits of $\theta_i$ from the largest to the smallest; it is the computation that a single LTF later simulates.
--
--   **Formalization Note** Indices are the paper's 1-based ones as natural numbers. A state stores `row`, `out`, `ptr : ℕ → Bool`; only the paper's $3m+2$ bits are ever read. A labeling is `ℕ → ℕ → Bool` read at $[m]\times[m]$, and `enc m lab i` is $\theta_i$; the dynamics accept any `θ : ℕ → ℤ`.
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §2, encoding θ and (4)–(9), p.5

import Mathlib

namespace AutoregLTF

/-!
# The recursion (4)–(9) with several LTFs and the row encoding `θ`

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), §2, p.5.

Fix `m ≥ 2` and a labeling `λ ∈ {0,1}^{m×m}`. The encoding of row `i` is
`θ_i = ∑_{j=1}^m 2^{j−1} λ_{i,j}`. For a selected row `i ∈ [m]` and `t ≥ 0`, the state
`f^t_{θ,i} ∈ {0,1}^{3m+2}` consists of the row bits `f^t_{θ,i,row,j}` (`j ∈ [m]`), the test bit
`f^t_{θ,i,test}`, the output bits `f^t_{θ,i,out,j}` (`j ∈ [m]`) and the pointer bits
`f^t_{θ,i,ptr,j}` (`j ∈ [m + 1]`), defined by (4)–(9).

**Formalization Note.**
* Indices are the paper's 1-based ones, as natural numbers: `[m] = {1, …, m}`. A state stores
  `row`, `out`, `ptr : ℕ → Bool`; only `row j`, `out j` for `1 ≤ j ≤ m` and `ptr j` for
  `1 ≤ j ≤ m + 1` are the paper's `3m + 2` bits, and statements only read those. The values at other
  indices are fixed by the same formulas and carry no meaning.
* A labeling is `lab : ℕ → ℕ → Bool` read at `i, j ∈ [m]`; an encoding is any `θ : ℕ → ℤ` read at
  `j ∈ [m]` (the range `θ_j ∈ {0, …, 2^m − 1}` is a hypothesis where the paper has it).
* A bit `b` enters a sum as `b.toNat ∈ {0, 1}`.
-/

/-- The encoding `θ_i = ∑_{j=1}^m 2^{j−1} λ_{i,j}` of row `i` of the labeling `λ`, p.5. -/
def enc (m : ℕ) (lab : ℕ → ℕ → Bool) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * ((lab i j).toNat : ℤ)

/-- A state `f^t_{θ,i}` of the recursion (4)–(9): row bits, the test bit, output bits and pointer
bits, indexed as in the paper (`row j`, `out j` for `j ∈ [m]`, `ptr j` for `j ∈ [m + 1]`). -/
structure St where
  /-- `f_{row,j}`, `j ∈ [m]`. -/
  row : ℕ → Bool
  /-- `f_{test}`. -/
  test : Bool
  /-- `f_{out,j}`, `j ∈ [m]`. -/
  out : ℕ → Bool
  /-- `f_{ptr,j}`, `j ∈ [m + 1]`. -/
  ptr : ℕ → Bool

/-- The initial state (4): `f^0_{row,j} = 1{j = i}`, `f^0_{test} = f^0_{ptr,m+1} = 1`,
`f^0_{out,j} = f^0_{ptr,j} = 0` for `j ∈ [m]`. -/
def init (m i : ℕ) : St where
  row j := decide (j = i)
  test := true
  out _ := false
  ptr j := decide (j = m + 1)

/-- One round (5)–(9), p.5:
`f^{t+1}_{row,j} = f^t_{row,j}`;
`f^{t+1}_{test} = 1{∑_j θ_j f^t_{row,j} − ∑_j 2^{j−1}(f^t_{out,j} + f^t_{ptr,j}) ≥ 0}`;
`f^{t+1}_{out,j} = 1{2 f^t_{out,j} + f^t_{ptr,j} + f^{t+1}_{test} ≥ 2}`;
`f^{t+1}_{ptr,j} = f^t_{ptr,j+1}` for `j ∈ [m]` and `f^{t+1}_{ptr,m+1} = 0`. -/
def step (m : ℕ) (θ : ℕ → ℤ) (f : St) : St :=
  let test' : Bool :=
    decide (0 ≤ ∑ j ∈ Finset.Icc 1 m, θ j * ((f.row j).toNat : ℤ) -
      ∑ j ∈ Finset.Icc 1 m, 2 ^ (j - 1) * (((f.out j).toNat : ℤ) + ((f.ptr j).toNat : ℤ)))
  { row := f.row
    test := test'
    out := fun j => decide (2 ≤ 2 * (f.out j).toNat + (f.ptr j).toNat + test'.toNat)
    ptr := fun j => if j ≤ m then f.ptr (j + 1) else false }

/-- The state `f^t_{θ,i}` after `t` rounds, from (4) and (5)–(9). -/
def state (m : ℕ) (θ : ℕ → ℤ) (i : ℕ) : ℕ → St
  | 0 => init m i
  | t + 1 => step m θ (state m θ i t)

end AutoregLTF


