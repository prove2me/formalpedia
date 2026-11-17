-- Prove2me | Definitions.Def_SoftmaxAttnFD_Supplement_MaxIPReduction
-- name    : SoftmaxAttnFD_Supplement_MaxIPReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:41:54.430193+00:00
-- url     : https://prove2.me/theorems/b80904d8-3fa6-45e5-82ee-422d6bea2107
-- title:
--   The attention instances of Theorem 3.1 ($Q=\beta_0X$, $K=Y$, $V\in\{Y,dB\,Y\}$) and the contracts of one-call and $d$-call reductions
-- statement:
--   Fix an instance $X\in\mathbb Z^{m\times d}$, $Y\in\mathbb Z^{n\times d}$, $B\ge1$ of $\mathrm{BatchMaxIP}_d$. Following §3.1 of the paper, set $C=8$ and
--
--   $$\beta_0=8\lceil\log_2(n+1)\rceil,\qquad \varepsilon_0=2^{-\lceil\log_2(8dB)\rceil},\qquad \varepsilon_c=\tfrac14 .$$
--
--   The attention instance has queries $Q=\beta_0X$ and keys $K=Y$, all entries written as integer triples; the value matrix is $V=Y$ (part (a)) or $V=dB\,Y$ (part (b)); the error tolerance $2^{-p}$ uses $p=\lceil\log_2(8dB)\rceil$ or $p=2$. Column $t$ of $V$ is a single-channel value matrix (part (c)).
--
--   The item defines two contracts for a pair of coin-free programs $(\mathrm{Pre},\mathrm{Post})$, constants $C>0$, $K$, a precision rule $p(d,B)$ and a value rule $V(n,d,B,Y)$. Write $\lambda=\log_2(m+n)+\log_2(d+1)+\log_2(B+1)$.
--
--   1. **One-call reduction.** For every $m$, every $n,d,B\ge1$ and all $X,Y$ with entries of absolute value at most $B$: $\mathrm{Pre}$, run on the $\mathrm{BatchMaxIP}_d$ input, writes the full Attention$_d$ input $(p,Q,K,V)$ right after its own input within bit cost $C(m+n)d\lambda^K$; and for **every** attention output memory within error $2^{-p}$ of $\mathrm{Att}(Q,K,V)$ whose $3md$ output cells have bit length at most $L$, $\mathrm{Post}$, run on the $\mathrm{BatchMaxIP}_d$ input followed by those output cells, writes the exact maxima $M_i$ within bit cost $C(m+n)d(\lambda+L)^K$.
--   2. **$d$-call reduction.** The same, except that $\mathrm{Pre}$ writes the cells $m,n,p,Q,K$ shared by the $d$ calls once, followed by the $d$ value columns (column $t$ in the $3n$ cells starting $3nt$ after the shared cells), and $\mathrm{Post}$ reads the output cells of all $d$ single-channel calls, each within error $2^{-p}$.
--
--   The attention calls are not charged. These contracts express "solves $\mathrm{BatchMaxIP}_d$ with one call (resp. $d$ calls) and deterministic additional time" in Theorem 3.1.
--
--   **Formalization Note** The post-processing cost may grow polynomially with the bit length $L$ of the attention output it reads: the paper's outputs are dyadic of logarithmic encoding length (§2.1, p.11), and the contract covers every output within the tolerance. $\lceil\log_2 x\rceil$ is `Nat.clog 2 x`. The input of call $t$ in part (c) is literally the shared cells followed by column $t$.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), §3.1 and Theorem 3.1, p.13 (PDF p.16); Definition 2.1, p.10; §2.1, p.11

import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_SoftmaxAttnFD_Attention
import Definitions.Def_SoftmaxAttnFD_Supplement_BatchMaxIP

namespace SoftmaxAttnFD

namespace Supplement

/-- `β₀ = C⌈log₂(n + 1)⌉` with `C = 8` (arXiv:2611.06055, sha256 a60f7609…, §3.1, p.13).
`Nat.clog 2 (n + 1)` is the least `k` with `n + 1 ≤ 2^k`, i.e. `⌈log₂(n + 1)⌉`. -/
def beta0 (n : ℕ) : ℕ := 8 * Nat.clog 2 (n + 1)

/-- The precision of part (a) of Theorem 3.1: `ε₀ = 2^{−⌈log₂(CdB)⌉}` with `C = 8` (§3.1, p.13), so
`ε₀ = 2^{−p}` with `p = ⌈log₂(8dB)⌉ = Nat.clog 2 (8dB)`. -/
def pA (d B : ℕ) : ℕ := Nat.clog 2 (8 * d * B)

/-- The precision of part (b) of Theorem 3.1: `ε_c = 1/4 = 2^{−2}` (§3.1, p.13). -/
def pB : ℕ := 2

/-- The query matrix of Theorem 3.1: `Q = β₀X`, entrywise encoded as integers. -/
def redQ {m d : ℕ} (n : ℕ) (X : Fin m → Fin d → ℤ) : Fin m → Fin d → RatEnc :=
  intMat fun i l => (beta0 n : ℤ) * X i l

/-- The value matrix of part (a) of Theorem 3.1: `V = Y`. -/
def valA (n d _B : ℕ) (Y : Fin n → Fin d → ℤ) : Fin n → Fin d → ℤ := Y

/-- The value matrix of part (b) of Theorem 3.1: `V = dB·Y`. -/
def valB (n d B : ℕ) (Y : Fin n → Fin d → ℤ) : Fin n → Fin d → ℤ :=
  fun j l => ((d * B : ℕ) : ℤ) * Y j l

/-- Column `t` of a value matrix, as a single-channel value matrix (part (c) of Theorem 3.1). -/
def col {n r : ℕ} (V : Fin n → Fin r → RatEnc) (t : Fin r) : Fin n → Fin 1 → RatEnc :=
  fun j _ => V j t

/-- The memory holds the list `l` from address `a` on: cell `a + i` is `l[i]`. Other cells are
unconstrained. -/
def HoldsAt (mem : ℕ → ℕ) (a : ℕ) (l : List ℕ) : Prop :=
  ∀ (i : ℕ) (h : i < l.length), mem (a + i) = l[i]

/-- The part of the Attention_d input shared by calls with the same `p`, `Q`, `K`: the cells
`m, n, p`, then `Q` and `K` row by row. `attnShared p Q K ++ matCells V = attnInput p Q K V`. -/
def attnShared {m n d : ℕ} (p : ℕ) (Q : Fin m → Fin d → RatEnc) (K : Fin n → Fin d → RatEnc) :
    List ℕ :=
  [m, n, p] ++ matCells Q ++ matCells K

/-- The `3mr` output cells of an Attention_d output memory `o` (the region `attnGood` constrains):
cell `k` is `o (attnBase m n d r + k)`, so entry `(i, t)` is the triple at `3(ir + t)`. -/
def outCells (m n d r : ℕ) (o : ℕ → ℕ) : List ℕ :=
  (List.range (3 * (m * r))).map fun k => o (attnBase m n d r + k)

/-- The soft-O base of §3.1, p.13 ("soft-O suppresses only logarithmic factors in `m + n, d, B`"):
`log₂(m + n) + log₂(d + 1) + log₂(B + 1)`, at least `1` when `d ≥ 1`. -/
noncomputable def lamRed (m n d B : ℕ) : ℝ :=
  Real.logb 2 ((m : ℝ) + n) + Real.logb 2 ((d : ℝ) + 1) + Real.logb 2 ((B : ℝ) + 1)

/-- A one-call reduction from BatchMaxIP_d to Attention_d (arXiv:2611.06055, Theorem 3.1 (a), (b),
p.13) with error tolerance `2^{−p d B}` and value matrix `V n d B Y`, keys `K = Y` and queries
`Q = β₀X`, at deterministic additional bit cost `C·(m + n)·d·λ^K`. For every `m` and every `n, d, B ≥ 1` and all
integer `X ∈ ℤ^{m×d}`, `Y ∈ ℤ^{n×d}` with entries of absolute value at most `B`:

1. the coin-free pre-processing `Pre`, run on the BatchMaxIP_d input, writes the Attention_d input
   `attnInput p Q K V` right after its own input, within cost `C·(m + n)·d·λ^K`;
2. for **every** memory `o` satisfying `attnGood` for that instance (any output of any attention
   algorithm within error `2^{−p}`) whose `3md` output cells have bit length at most `L`, the
   coin-free post-processing `Post`, run on the BatchMaxIP_d input followed by those output cells,
   writes the exact maxima `M_i` (`bmipGood`) right after its input, within cost
   `C·(m + n)·d·(λ + L)^K`.

The attention call itself is not charged.

**Formalization Note** The post-processing cost may grow polynomially with the bit length `L` of the
attention output it reads; on the paper's dyadic outputs `L` is logarithmic in `m + n, d, B` (§2.1,
p.11; proof of Theorem 3.1), and the statement covers every output within the tolerance. -/
def OneCallReduction (Pre Post : TimeSpaceMA.Program) (C : ℝ) (K : ℕ) (p : ℕ → ℕ → ℕ)
    (V : (n d B : ℕ) → (Fin n → Fin d → ℤ) → Fin n → Fin d → ℤ) : Prop :=
  ∀ (m n d B : ℕ), 1 ≤ n → 1 ≤ d → 1 ≤ B →
    ∀ (X : Fin m → Fin d → ℤ) (Y : Fin n → Fin d → ℤ), IntBounded X B → IntBounded Y B →
      DeterministicWithin Pre (memOf (bmipInput B X Y))
          (fun out => HoldsAt out (bmipInput B X Y).length
            (attnInput (p d B) (redQ n X) (intMat Y) (intMat (V n d B Y))))
          (C * ((m : ℝ) + n) * d * lamRed m n d B ^ K) ∧
        ∀ (o : ℕ → ℕ) (L : ℕ),
          attnGood (p d B) (redQ n X) (intMat Y) (intMat (V n d B Y)) o →
          (∀ c ∈ outCells m n d d o, c.size ≤ L) →
          DeterministicWithin Post (memOf (bmipInput B X Y ++ outCells m n d d o))
            (bmipGood X Y (bmipInput B X Y ++ outCells m n d d o).length)
            (C * ((m : ℝ) + n) * d * (lamRed m n d B + L) ^ K)

/-- A reduction from BatchMaxIP_d to `d` single-channel Attention_d calls (arXiv:2611.06055,
Theorem 3.1 (c), p.13): call `t` has queries `Q = β₀X`, keys `K = Y`, column `t` of the value matrix
`V n d B Y` as its one value channel, and error tolerance `2^{−p d B}`. For every `m` and every `n, d, B ≥ 1` and
all integer `X`, `Y` with entries of absolute value at most `B`:

1. the coin-free `Pre`, run on the BatchMaxIP_d input, writes the shared cells `m, n, p, Q, K`
   (`attnShared`) once, right after its input, followed by the `d` value columns, column `t` in the
   `3n` cells starting `3nt` after the shared cells, within cost `C·(m + n)·d·λ^K`; the input of call
   `t` is the shared cells followed by column `t`, which is `attnInput p Q K (col V t)`;
2. for **every** family of memories `o t` satisfying `attnGood` for call `t`, whose output cells have
   bit length at most `L`, the coin-free `Post`, run on the BatchMaxIP_d input followed by the output
   cells of calls `0, …, d − 1`, writes the exact maxima `M_i` right after its input, within cost
   `C·(m + n)·d·(λ + L)^K`.

The attention calls are not charged. `Q` and `K` are written once, not once per call. -/
def ScalarCallsReduction (Pre Post : TimeSpaceMA.Program) (C : ℝ) (K : ℕ) (p : ℕ → ℕ → ℕ)
    (V : (n d B : ℕ) → (Fin n → Fin d → ℤ) → Fin n → Fin d → ℤ) : Prop :=
  ∀ (m n d B : ℕ), 1 ≤ n → 1 ≤ d → 1 ≤ B →
    ∀ (X : Fin m → Fin d → ℤ) (Y : Fin n → Fin d → ℤ), IntBounded X B → IntBounded Y B →
      DeterministicWithin Pre (memOf (bmipInput B X Y))
          (fun out =>
            HoldsAt out (bmipInput B X Y).length (attnShared (p d B) (redQ n X) (intMat Y)) ∧
              ∀ t : Fin d,
                HoldsAt out ((bmipInput B X Y).length +
                    (attnShared (p d B) (redQ n X) (intMat Y)).length + 3 * n * t.val)
                  (matCells (col (intMat (V n d B Y)) t)))
          (C * ((m : ℝ) + n) * d * lamRed m n d B ^ K) ∧
        ∀ (o : Fin d → ℕ → ℕ) (L : ℕ),
          (∀ t, attnGood (p d B) (redQ n X) (intMat Y) (col (intMat (V n d B Y)) t) (o t)) →
          (∀ t, ∀ c ∈ outCells m n d 1 (o t), c.size ≤ L) →
          DeterministicWithin Post
            (memOf (bmipInput B X Y ++ (List.finRange d).flatMap fun t => outCells m n d 1 (o t)))
            (bmipGood X Y
              (bmipInput B X Y ++ (List.finRange d).flatMap fun t => outCells m n d 1 (o t)).length)
            (C * ((m : ℝ) + n) * d * (lamRed m n d B + L) ^ K)

end Supplement

end SoftmaxAttnFD


