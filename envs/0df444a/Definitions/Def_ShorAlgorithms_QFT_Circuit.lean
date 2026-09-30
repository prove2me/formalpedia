-- Prove2me | Definitions.Def_ShorAlgorithms_QFT_Circuit
-- name    : ShorAlgorithms_QFT_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T07:59:56.608804+00:00
-- url     : https://prove2.me/theorems/5d079012-ab46-4f60-9f20-f323001ba454
-- title:
--   The gates R_j, S_{j,k} and the quantum Fourier transform circuit (4.4)
-- statement:
--   States on $l$ bits are amplitude vectors $\psi$ indexed by bit strings $b = (b_{l-1}, \dots, b_0)$. Gates are given as matrices whose **rows are input basis vectors and whose columns are output basis vectors** (Shor, §2, p. 1489), and a gate acting on some of the bits acts on those bits and leaves the other bits alone (§2, p. 1490).
--
--   1. The one-bit gate $R_j$ (eq. (4.2)) acts on bit $j$ with matrix
--   $$R = \begin{pmatrix} \tfrac{1}{\sqrt2} & \tfrac{1}{\sqrt2} \\ \tfrac{1}{\sqrt2} & -\tfrac{1}{\sqrt2} \end{pmatrix}$$
--   in the basis $|0\rangle, |1\rangle$. On a state $\psi$ it produces the state whose amplitude at $b$ is
--   $$\sum_{u \in \{0,1\}} \psi(b[j \mapsto u])\, R_{u,\, b_j},$$
--   where $b[j \mapsto u]$ is $b$ with bit $j$ replaced by $u$.
--   2. The two-bit gate $S_{j,k}$, $j < k$ (eq. (4.3)), acts on bits $j$ and $k$ with the diagonal matrix $\mathrm{diag}(1, 1, 1, e^{i\theta_{k-j}})$ in the basis $|00\rangle, |01\rangle, |10\rangle, |11\rangle$ of (bit $j$, bit $k$), where $\theta_{k-j} = \pi / 2^{k-j}$. On a state $\psi$ it produces the state whose amplitude at $b$ is $\sum_{u, v} \psi(b[j \mapsto u][k \mapsto v])\, S_{(u,v),(b_j,b_k)}$; that is, it multiplies the amplitude at $b$ by $e^{i\pi/2^{k-j}}$ when $b_j = b_k = 1$ and leaves it unchanged otherwise.
--   3. The circuit is the list of gates (eq. (4.4)), applied from left to right:
--   $$R_{l-1}\, S_{l-2,l-1}\, R_{l-2}\, S_{l-3,l-1}\, S_{l-3,l-2}\, R_{l-3} \cdots R_1\, S_{0,l-1}\, S_{0,l-2} \cdots S_{0,2}\, S_{0,1}\, R_0 .$$
--   For $j = l-1, l-2, \dots, 0$ in turn it applies $S_{j,l-1}, S_{j,l-2}, \dots, S_{j,j+1}$ and then $R_j$. On 3 bits the list is $R_2 S_{1,2} R_1 S_{0,2} S_{0,1} R_0$.
--   4. Running a gate list on a state applies its gates one at a time, the leftmost gate first.
--
--   This is Shor's construction, following Coppersmith and Ekert–Jozsa, of the Fourier transform $A_q$ for $q = 2^l$ out of $l$ one-bit gates and $l(l-1)/2$ two-bit gates. The circuit is defined as the gate list itself, not as the matrix it is claimed to compute.
--
--   **Formalization Note** The gate type has two constructors, `R j` and `S j k`; the list built here only uses `S j k` with $j < k$, so the natural-number subtraction $k - j$ in $\theta_{k-j}$ is exact. The one- and two-bit actions are written as explicit sums over the replaced bits, which is the tensor product of the gate matrix with the identity on the remaining bits in the row = input convention.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1496, §4, eqs. (4.2)–(4.4); gate conventions §2, pp. 1489–1490 ("The rows correspond to input basis vectors"; "If we apply a gate to only two bits of a longer vector")

import Mathlib

namespace ShorAlgorithms.QFT

/-- The one-bit gate `R_j` of eq. (4.2): rows are input basis vectors `|0⟩, |1⟩`, columns are
output basis vectors; entries `1/√2` except the `(|1⟩, |1⟩)` entry `-1/√2`. -/
noncomputable def Rmat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹;
     (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- The two-bit gate `S_{j,k}` of eq. (4.3) for a gap `d = k - j`, indexed by the pair
(bit `j`, bit `k`): the diagonal matrix `diag(1, 1, 1, e^{iθ_d})` with `θ_d = π / 2^d`. -/
noncomputable def Smat (d : ℕ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal fun p =>
    if p = (1, 1) then Complex.exp (((Real.pi / 2 ^ d : ℝ) : ℂ) * Complex.I) else 1

/-- Apply a one-bit gate `M` (rows = inputs, columns = outputs) to bit `j` of a state on `l`
bits, leaving the other bits alone: the output amplitude at `b` is
`∑_u ψ(b[j ↦ u]) · M u (b j)`. -/
noncomputable def applyOneBit {l : ℕ} (M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin l)
    (ψ : (Fin l → Fin 2) → ℂ) : (Fin l → Fin 2) → ℂ :=
  fun b => ∑ u : Fin 2, ψ (Function.update b j u) * M u (b j)

/-- Apply a two-bit gate `M` (rows = inputs, columns = outputs, basis indexed by
(bit `j`, bit `k`)) to bits `j` and `k` of a state on `l` bits, leaving the other bits alone:
the output amplitude at `b` is `∑_{u,v} ψ(b[j ↦ u][k ↦ v]) · M (u, v) (b j, b k)`.
Only used with `j ≠ k`. -/
noncomputable def applyTwoBit {l : ℕ} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (j k : Fin l) (ψ : (Fin l → Fin 2) → ℂ) : (Fin l → Fin 2) → ℂ :=
  fun b => ∑ u : Fin 2, ∑ v : Fin 2,
    ψ (Function.update (Function.update b j u) k v) * M (u, v) (b j, b k)

/-- The gates of Shor's Fourier-transform circuit on `l` bits: `R j` is `R_j`, and `S j k` is
`S_{j,k}` (the circuit only uses it with `j < k`). -/
inductive Gate (l : ℕ) where
  | R (j : Fin l) : Gate l
  | S (j k : Fin l) : Gate l
  deriving DecidableEq, Repr

/-- The action of one gate on a state: `R_j` on bit `j`; `S_{j,k}` on bits `j, k` with angle
`θ_{k-j} = π / 2^{k-j}` (natural-number subtraction, exact since the circuit has `j < k`). -/
noncomputable def applyGate {l : ℕ} : Gate l → ((Fin l → Fin 2) → ℂ) → (Fin l → Fin 2) → ℂ
  | Gate.R j => applyOneBit Rmat j
  | Gate.S j k => applyTwoBit (Smat ((k : ℕ) - (j : ℕ))) j k

/-- The gate sequence (4.4), read from left to right:
`R_{l-1} S_{l-2,l-1} R_{l-2} S_{l-3,l-1} S_{l-3,l-2} R_{l-3} … R_1 S_{0,l-1} … S_{0,1} R_0`,
i.e. for `j = l-1, l-2, …, 0` the gates `S_{j,l-1}, S_{j,l-2}, …, S_{j,j+1}` followed by `R_j`. -/
def qftGates (l : ℕ) : List (Gate l) :=
  (List.finRange l).reverse.flatMap fun j =>
    (((List.finRange l).reverse.filter fun k => decide (j < k)).map fun k => Gate.S j k)
      ++ [Gate.R j]

/-- Run a gate list on a state, the leftmost gate acting first. -/
noncomputable def runCircuit {l : ℕ} (gs : List (Gate l)) (ψ : (Fin l → Fin 2) → ℂ) :
    (Fin l → Fin 2) → ℂ :=
  gs.foldl (fun φ G => applyGate G φ) ψ

end ShorAlgorithms.QFT


