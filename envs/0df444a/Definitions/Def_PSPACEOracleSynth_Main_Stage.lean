-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Stage
-- name    : PSPACEOracleSynth_Main_Stage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:58.815542+00:00
-- url     : https://prove2.me/theorems/7ce09881-a324-42e3-88b9-a7ebb6d087f6
-- title:
--   One stage of the recursion: $Z(z)$, $U^{(j+1)}(z)$, the near-isometries $\mathcal E_N$, $\mathcal E'_N$ and the coefficient matrices $\Lambda_{\mathcal E}$, $\Lambda_{\mathcal E'}$
-- statement:
--   Fix $n$, $N\ge1$ and $\beta=nN+\lceil\log_2(N+1)\rceil$ (Definition 3.2), $\omega=e^{2\pi i/2^\beta}$ and $\kappa=3/4$ (Equation (3.2)). Let $G$ be a $d\times d$ matrix, $d=k+s$, with **leading coordinates** $c=1,\dots,k$ (basis states $|c-1\rangle$) and **trailing coordinates** $\lambda=1,\dots,s$ (basis states $|k+\lambda-1\rangle$), and blocks $G_{11},G_{12},G_{21},G_{22}$.
--
--   1. Each trailing coordinate has the frequency vector $v_\lambda=(1,\lambda,\dots,\lambda^N)$; a control string $z\in\mathbb Z_{2^\beta}^{N+1}$ gives $Z(z)=\operatorname{diag}\bigl(\omega^{v_\lambda\cdot z}\bigr)_{\lambda=1,\dots,s}$.
--   2. (Equation (3.4)) $X(z)=(I-G_{22}Z(z))^{-1}G_{21}$ and $U^{(j+1)}(z)=G_{11}+G_{12}Z(z)X(z)$.
--   3. $E_N(z)=\begin{pmatrix}I\\ \sum_{h<N}Z(z)(G_{22}Z(z))^hG_{21}\end{pmatrix}$, and $E'_N(z)$ is $E_N(-z)$ for $G^\dagger$.
--   4. (Equation (3.7)) $\mathcal E_N=2^{-\beta(N+1)/2}\sum_z|z\rangle\otimes E_N(z)^\dagger$ and $\mathcal E'_N=2^{-\beta(N+1)/2}\sum_z|z\rangle\otimes E'_N(z)^\dagger$, maps from $H_d$ to the control register and the leading coordinates.
--   5. With $F_{2^\beta}^{\otimes(N+1)}|\zeta\rangle=2^{-\beta(N+1)/2}\sum_z\omega^{\zeta\cdot z}|z\rangle$, the coefficient matrices are defined by $\mathcal E_N=(F_{2^\beta}^{\otimes(N+1)}\otimes I)\Lambda_{\mathcal E}$ and $\mathcal E'_N=(F_{2^\beta}^{\otimes(N+1)}\otimes I)\Lambda_{\mathcal E'}$; their rows are indexed by a frequency $\zeta$ and a leading coordinate $c$.
--   6. A family of sparsity patterns (one per choice of $n,N,k,s$) is **computable from the row index in space polynomial in $n+N$** if one oracle-free machine, given $n,N,k,s$ and a row $(\zeta,c)$, lists the positions of that row using at most $p(n+N)$ cells, for one polynomial $p$.
--
--   These are the objects of Lemma 3.5.
--
--   **Formalization Note.** $G$ is a `Matrix (Fin (k+s)) (Fin (k+s)) ℂ`; trailing coordinate $\lambda$ is `r : Fin s` with $\lambda=r+1$. Control strings and frequencies are `Fin (N+1) → Fin (2^β)`; exponents of $\omega$ are computed in $\mathbb N$, which is the same as in $\mathbb Z_{2^\beta}$ because $\omega^{2^\beta}=1$. Since $Z(-z)=Z(z)^\dagger$, $E'_N(z)$ is written as the truncated series for $G^\dagger$ with $Z(z)^\dagger$. $\Lambda_{\mathcal E}$ is $(F^{\otimes(N+1)\dagger}\otimes I)\mathcal E_N$, the Fourier transform being unitary. The matrix inverse is Mathlib's, which agrees with the true inverse whenever $\|G_{22}\|<1$. The pattern machine reads `tup [1^n, 1^N, bin k, bin s, tup [bin ζ_0, …, bin ζ_N], bin c]` and writes the list of positions in binary.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), Definition 3.2, p. 16; Equation (3.2), p. 16; §3.3, Equations (3.4)–(3.7), p. 19; Λ_E, Λ_E′, p. 20

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_OTM

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace PSPACEOracleSynth.Main

/-!
# One stage of the recursion: smaller unitaries and the two near-isometries `E_N`, `E′_N`

Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission #1740 (October 2026),
§3.1–§3.3, pp. 15–20: Definition 3.2 (p. 16), Equation (3.2) (`κ = 3/4`, p. 16), Equations
(3.4) and (3.7) (p. 19), and the coefficient matrices `Λ_E`, `Λ_E′` (p. 20).

A unitary `G` on `H_d`, `d = k + s`, is a `(k + s) × (k + s)` matrix. The **leading coordinates**
`c = 1, …, k` are the indices `0, …, k − 1` and the **trailing coordinates** `λ = 1, …, s` are the
indices `k, …, k + s − 1` (index `k + λ − 1`); `G₁₁, G₁₂, G₂₁, G₂₂` are the four blocks, `G₂₂` the
trailing block. In Lean a trailing coordinate is `r : Fin s` with `λ = r + 1`.

* `β = nN + ⌈log₂(N + 1)⌉` (Definition 3.2), `ω = e^{2πi/2^β}`.
* A control string is `z ∈ ℤ_{2^β}^{N+1}`, encoded as `Fin (N + 1) → Fin (2^β)`.
* The trailing coordinate `λ` has the frequency vector `v_λ = (1, λ, λ², …, λ^N)`, and
  `Z(z) = diag(ω^{v_λ · z})_{λ = 1, …, s}`.
* `X(z) = (I − G₂₂ Z(z))^{−1} G₂₁`, `U^{(j+1)}(z) = G₁₁ + G₁₂ Z(z) X(z)` (Equation (3.4)).
* `E_N(z) = [I ; Σ_{h<N} Z(z) (G₂₂ Z(z))^h G₂₁]` (a `d × k` matrix), and `E′_N(z)` is `E_N(−z)` for
  `G†`; since `Z(−z) = Z(z)†`, it is the same formula for `G†` with `Z(z)†` in place of `Z(z)`.
* `E_N = 2^{−β(N+1)/2} Σ_z |z⟩ ⊗ E_N(z)†` and `E′_N` likewise (Equation (3.7)), maps from `H_d` to
  the control register ⊗ the leading coordinates.
* `F_{2^β}^{⊗(N+1)} |ζ⟩ = 2^{−β(N+1)/2} Σ_z ω^{ζ·z} |z⟩`, and `Λ_E`, `Λ_E′` are defined by
  `E_N = (F_{2^β}^{⊗(N+1)} ⊗ I) Λ_E`, `E′_N = (F_{2^β}^{⊗(N+1)} ⊗ I) Λ_E′`.
-/

/-- `κ = 3/4` (Equation (3.2), p. 16). -/
noncomputable def kappa : ℝ := 3 / 4

/-- `β = nN + ⌈log₂(N + 1)⌉` (Definition 3.2, p. 16). -/
def betaN (n N : ℕ) : ℕ := n * N + Nat.clog 2 (N + 1)

/-- The control strings `z ∈ ℤ_{2^β}^{N+1}`, `β = betaN n N`. -/
abbrev Ctrl (n N : ℕ) := Fin (N + 1) → Fin (2 ^ betaN n N)

/-- `ω = e^{2πi/2^β}`. -/
noncomputable def omegaB (β : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / 2 ^ β)

/-- The normalization `2^{−β(N+1)/2}`. -/
noncomputable def ctrlScale (n N : ℕ) : ℂ := ((Real.sqrt (2 ^ (betaN n N * (N + 1))))⁻¹ : ℝ)

/-- `v_λ · z = Σ_{e=0}^{N} λ^e z_e` (as a natural number; only its residue mod `2^β` matters in
`ω^{v_λ·z}`). -/
def freqDot {n N : ℕ} (lam : ℕ) (z : Ctrl n N) : ℕ := ∑ e : Fin (N + 1), lam ^ e.val * (z e).val

/-- `Z(z) = diag(ω^{v_λ · z})_{λ = 1, …, s}`, the trailing coordinate `r : Fin s` being `λ = r + 1`. -/
noncomputable def Zdiag (n N s : ℕ) (z : Ctrl n N) : Matrix (Fin s) (Fin s) ℂ :=
  Matrix.diagonal fun r => omegaB (betaN n N) ^ freqDot (r.val + 1) z

/-- The leading block `G₁₁`. -/
def blk11 {k s : ℕ} (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => G (Fin.castAdd s i) (Fin.castAdd s j)

/-- The block `G₁₂` (leading rows, trailing columns). -/
def blk12 {k s : ℕ} (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) : Matrix (Fin k) (Fin s) ℂ :=
  Matrix.of fun i j => G (Fin.castAdd s i) (Fin.natAdd k j)

/-- The block `G₂₁` (trailing rows, leading columns). -/
def blk21 {k s : ℕ} (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) : Matrix (Fin s) (Fin k) ℂ :=
  Matrix.of fun i j => G (Fin.natAdd k i) (Fin.castAdd s j)

/-- The trailing block `G₂₂`. -/
def blk22 {k s : ℕ} (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) : Matrix (Fin s) (Fin s) ℂ :=
  Matrix.of fun i j => G (Fin.natAdd k i) (Fin.natAdd k j)

/-- `U^{(j+1)} = G₁₁ + G₁₂ Z X` with `X = (I − G₂₂ Z)^{−1} G₂₁` (Equation (3.4)), for a diagonal
unitary `Z` on the trailing coordinates. (When `‖G₂₂‖ ≤ κ < 1`, `I − G₂₂ Z` is invertible.) -/
noncomputable def nextU {k s : ℕ} (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ)
    (Z : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  blk11 G + blk12 G * Z * ((1 - blk22 G * Z)⁻¹ * blk21 G)

/-- The truncated series `E_N = [I ; Σ_{h<N} Z (G₂₂ Z)^h G₂₁]` as a `(k + s) × k` matrix: the
leading rows form the identity, the trailing rows the truncated series. -/
noncomputable def truncE {k s : ℕ} (N : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ)
    (Z : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin (k + s)) (Fin k) ℂ :=
  Matrix.of fun x c =>
    if h : x.val < k then (if x.val = c.val then 1 else 0)
    else (∑ i ∈ Finset.range N, Z * (blk22 G * Z) ^ i * blk21 G)
      ⟨x.val - k, by have := x.isLt; omega⟩ c

/-- `E_N(z)` for `G` (p. 19). -/
noncomputable def ENz (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) (z : Ctrl n N) :
    Matrix (Fin (k + s)) (Fin k) ℂ :=
  truncE N G (Zdiag n N s z)

/-- `E′_N(z)`: `E_N(−z)` for `G†` (p. 19), i.e. the truncated series for `G†` with
`Z(−z) = Z(z)†`. -/
noncomputable def ENz' (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) (z : Ctrl n N) :
    Matrix (Fin (k + s)) (Fin k) ℂ :=
  truncE N G.conjTranspose (Zdiag n N s z).conjTranspose

/-- `E_N = 2^{−β(N+1)/2} Σ_z |z⟩ ⊗ E_N(z)†` (Equation (3.7)): rows indexed by a control string and a
leading coordinate, columns by `H_d`. -/
noncomputable def bigE (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) :
    Matrix (Ctrl n N × Fin k) (Fin (k + s)) ℂ :=
  Matrix.of fun zc x => ctrlScale n N * star (ENz n N k s G zc.1 x zc.2)

/-- `E′_N = 2^{−β(N+1)/2} Σ_z |z⟩ ⊗ E′_N(z)†` (Equation (3.7)). -/
noncomputable def bigE' (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) :
    Matrix (Ctrl n N × Fin k) (Fin (k + s)) ℂ :=
  Matrix.of fun zc x => ctrlScale n N * star (ENz' n N k s G zc.1 x zc.2)

/-- `⊕_z U^{(j+1)}(z) = Σ_z |z⟩⟨z| ⊗ U^{(j+1)}(z)` on the control register ⊗ the leading
coordinates. -/
noncomputable def sumNextU (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) :
    Matrix (Ctrl n N × Fin k) (Ctrl n N × Fin k) ℂ :=
  Matrix.of fun zc zc' => if zc.1 = zc'.1 then nextU G (Zdiag n N s zc.1) zc.2 zc'.2 else 0

/-- The Fourier transform `F_{2^β}^{⊗(N+1)}` of the control register: the entry in row `z`, column
`ζ` is `2^{−β(N+1)/2} ω^{ζ·z}`, `ζ·z = Σ_e ζ_e z_e`. -/
noncomputable def fourierCtrl (n N : ℕ) : Matrix (Ctrl n N) (Ctrl n N) ℂ :=
  Matrix.of fun z ζ =>
    ctrlScale n N * omegaB (betaN n N) ^ (∑ e : Fin (N + 1), (ζ e).val * (z e).val)

/-- `Λ_E`, defined by `E_N = (F_{2^β}^{⊗(N+1)} ⊗ I) Λ_E` (p. 20): since the Fourier transform is
unitary, `Λ_E = (F_{2^β}^{⊗(N+1)†} ⊗ I) E_N`. Rows are indexed by a frequency `ζ` and a leading
coordinate `c`. -/
noncomputable def lamE (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) :
    Matrix (Ctrl n N × Fin k) (Fin (k + s)) ℂ :=
  Matrix.kronecker (fourierCtrl n N).conjTranspose (1 : Matrix (Fin k) (Fin k) ℂ) * bigE n N k s G

/-- `Λ_E′`, defined by `E′_N = (F_{2^β}^{⊗(N+1)} ⊗ I) Λ_E′` (p. 20). -/
noncomputable def lamE' (n N k s : ℕ) (G : Matrix (Fin (k + s)) (Fin (k + s)) ℂ) :
    Matrix (Ctrl n N × Fin k) (Fin (k + s)) ℂ :=
  Matrix.kronecker (fourierCtrl n N).conjTranspose (1 : Matrix (Fin k) (Fin k) ℂ) * bigE' n N k s G

/-- The row index `(ζ, c)` together with the sizes `n, N, k, s`, as one bit string:
`tup [1^n, 1^N, bin k, bin s, tup [bin ζ₀, …, bin ζ_N], bin c]`. -/
def rowInput (n N k s : ℕ) (r : Ctrl n N × Fin k) : Str :=
  tup [unary n, unary N, Nat.bits k, Nat.bits s,
    tup (List.ofFn fun e => Nat.bits (r.1 e).val), Nat.bits r.2.val]

/-- A family of sparsity patterns `pat n N k s : (ζ, c) ↦ set of column positions` (one for each
choice of sizes) is **computable from the row index in space polynomial in `n + N`**: one
deterministic machine without oracle and one polynomial `p` such that, for all sizes with
`1 ≤ N` and `k + s ≤ 2^n` and every row `(ζ, c)`, the machine on `rowInput n N k s (ζ, c)` halts
having used at most `p(n + N)` cells, with output the list of the positions of the row (in
binary). -/
def PatternComputable (pat : (n N k s : ℕ) → Ctrl n N × Fin k → Finset (Fin (k + s))) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ (n N k s : ℕ), 1 ≤ N → k + s ≤ 2 ^ n →
    ∀ r : Ctrl n N × Fin k, ∃ (T : ℕ) (l : List ℕ),
      M.result (fun _ => false) (rowInput n N k s r) T ≠ none ∧
      M.space (fun _ => false) (rowInput n N k s r) T ≤ p.eval (n + N) ∧
      M.output (fun _ => false) (rowInput n N k s r) T = tup (l.map Nat.bits) ∧
      ∀ j : Fin (k + s), j ∈ pat n N k s r ↔ j.val ∈ l

end PSPACEOracleSynth.Main


