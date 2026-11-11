-- Prove2me | Definitions.Def_ExactDFTRefine_Main_Moments
-- name    : ExactDFTRefine_Main_Moments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:00:26.779396+00:00
-- url     : https://prove2.me/theorems/daad3867-855e-49d3-a12e-f7fbdd0a2f3d
-- title:
--   Table 1 rank multisets P, T, moments M_t, the constants C, t, ε, U, L, E, γ, η, δ, β, the series S_N, U_N, tensor powers, and the completed and split unit P′, T′
-- statement:
--   For a finite multiset $A$ of natural numbers and real $t$, the **moment** is $M_t(A) = \sum_{r \in A} r^t$, counting multiplicity, with $r^t$ the real power. The **charged-block multiset** $P$ and the **target multiset** $T$ are those of Table 1 (rank × count):
--   $$P = \{1\times41946, 2\times6984, 3\times8892, 4\times2646, 5\times648, 8\times144, 16\times448, 24\times448, 32\times448, 40\times448, 48\times448, 56\times448, 64\times448, 72\times224\},$$
--   $$T = \{4\times504, 7\times126, 8\times846, 9\times5868, 17\times448, 25\times448, 33\times448, 41\times448, 49\times448, 57\times448, 65\times448, 73\times224, 145\times224\},$$
--   where $r \times m$ denotes $m$ copies of rank $r$. Write $P_t = M_t(P)$, $T_t = M_t(T)$.
--
--   The constants are the exact rationals $C = 60403319/20000000000$, $t = 1 - C$, $\varepsilon = 27/10^{12}$ (Eq. (3)); $U = 1661483013014771/10^{12}$, $L = 1661483013061537/10^{12}$ (Eqs. (6), (7)); $E = 251500221699/250000000000$ (Eq. (8)); $\gamma = 99857/100000$, $\eta = 9583/10000$ (Eq. (10)); the final saving $\delta = 30201659/10^{10}$ (Theorem 1.1) and the intermediate saving $\beta = 3020165925/10^{12}$ (proof of Theorem 1.1).
--
--   For $N \in \mathbb N$ and real $x$: $S_N(x) = \sum_{j=0}^{N-1} x^j/j!$ and $U_N(x) = S_N(x) + \frac{N+1}{N\,N!}x^N$ (Appendix A); Lemma 3.1's $S_6$ is $S_N$ at $N = 6$.
--
--   The **tensor product** $A \otimes B$ contains every product $ab$, with multiplicity, for $a \in A$, $b \in B$; the **tensor power** is $A^{\otimes 0} = \{1\}$, $A^{\otimes (v+1)} = A^{\otimes v} \otimes A$, so $A^{\otimes 1} = A$.
--
--   **Completion and splitting** (p. 5), for $v \in \mathbb N$ and positive integers $J < B$: each target $K \in T^{\otimes v}$ with $K < B$ is completed to rank $B$ by a charged block of rank $B - K$; targets with $K \ge B$ are unchanged. So $T' = \{\max(K, B) : K \in T^{\otimes v}\}$. The charged blocks $P^{\otimes v}$ together with the completion blocks $\{B - K : K \in T^{\otimes v},\ K < B\}$ are then split: a block of rank $R > J$ becomes $\lfloor R/J \rfloor$ blocks of rank $J$ and one block of rank $R \bmod J$ when that is nonzero; a block of rank $R \le J$ is kept. The result is $P'$.
--
--   **Formalization Note.** Multisets are `Multiset ℕ`; `moment t A`, `blocksP`, `targetsT`, `Cpar`, `tpar`, `eps`, `Ubound`, `Lbound`, `Ebound`, `gam`, `eta`, `delta`, `beta`, `SN`, `UN`, `tensor`, `tpow`, `completeTargets`, `completionBlocks`, `splitBlock`, `splitBlocks`, `Pprime P T v J B`, `Tprime T v B`. Every constant is a quotient of real numerals, never a natural-number division.
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 2 (δ, M_t); p. 3 (Table 1, Eq. (3), Lemma 3.1's S_6); p. 4 (Eqs. (6)–(8), (10)); p. 5 (§4: ⊗, completion and splitting); p. 6 (β); p. 8 (Appendix A: S_N, U_N)

import Mathlib

/-!
# Rank multisets of Table 1, moments `M_t`, the constants of §§1, 3, 4, the series `S_N`, `U_N`,
# tensor powers, and the completed and split tensor unit

Yao, Liu, *A Numerical Refinement of an Exact Discrete Fourier Transform Bound*,
arXiv:2611.01257v1: p. 2 (`δ`, Theorem 1.1; the moment `M_t`), p. 3 (Table 1, Eq. (3),
Lemma 3.1's `S_6`), p. 4 (Eqs. (6)–(8), (10)), p. 5 (§4: `⊗`, completion and splitting),
p. 6 (`β`), p. 8 (Appendix A: `S_N`, `U_N`).

Conventions.
* A rank multiset is a `Multiset ℕ`; the Table 1 multisets have positive entries.
* `moment t A = ∑_{r ∈ A} r^t` counts multiplicity; `r^t` is the real power `Real.rpow`.
* Every constant is the exact rational of the paper, cast to `ℝ`.
* `tensor A B` holds every product `a b`, with multiplicity, for `a ∈ A`, `b ∈ B`;
  `tpow A v` is the `v`-fold tensor power (`tpow A 0 = {1}`, so `tpow A 1 = A`).
* Completion and splitting (p. 5), for positive integers `J < B`: a target of rank `K < B` is
  raised to rank `B` and contributes a charged block of rank `B - K`; a target of rank at least
  `B` is unchanged. A charged block of rank `R > J` is split into `⌊R/J⌋` blocks of rank `J` and
  one remainder block of rank `R mod J` when that is nonzero; a block of rank `R ≤ J` is kept.
-/

namespace ExactDFTRefine.Main

noncomputable section

/-- `S_N(x) = ∑_{j=0}^{N-1} x^j / j!` (Appendix A; Lemma 3.1's `S_6` is `SN 6`). -/
def SN (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, x ^ j / (j.factorial : ℝ)

/-- `U_N(x) = S_N(x) + ((N + 1)/(N · N!)) x^N` (Appendix A). -/
def UN (N : ℕ) (x : ℝ) : ℝ :=
  SN N x + ((N : ℝ) + 1) / ((N : ℝ) * (N.factorial : ℝ)) * x ^ N

/-- The moment `M_t(A) = ∑_{r ∈ A} r^t`, with multiplicity, `r^t` a real power. -/
def moment (t : ℝ) (A : Multiset ℕ) : ℝ :=
  (A.map fun r => (r : ℝ) ^ t).sum

/-- The charged-block multiset `P` of Table 1 (rank × count). -/
def blocksP : Multiset ℕ :=
  Multiset.replicate 41946 1 + Multiset.replicate 6984 2 + Multiset.replicate 8892 3 +
  Multiset.replicate 2646 4 + Multiset.replicate 648 5 + Multiset.replicate 144 8 +
  Multiset.replicate 448 16 + Multiset.replicate 448 24 + Multiset.replicate 448 32 +
  Multiset.replicate 448 40 + Multiset.replicate 448 48 + Multiset.replicate 448 56 +
  Multiset.replicate 448 64 + Multiset.replicate 224 72

/-- The target-job multiset `T` of Table 1 (rank × count). -/
def targetsT : Multiset ℕ :=
  Multiset.replicate 504 4 + Multiset.replicate 126 7 + Multiset.replicate 846 8 +
  Multiset.replicate 5868 9 + Multiset.replicate 448 17 + Multiset.replicate 448 25 +
  Multiset.replicate 448 33 + Multiset.replicate 448 41 + Multiset.replicate 448 49 +
  Multiset.replicate 448 57 + Multiset.replicate 448 65 + Multiset.replicate 224 73 +
  Multiset.replicate 224 145

/-- `C = 60403319/20000000000` (Eq. (3)). -/
def Cpar : ℝ := 60403319 / 20000000000

/-- `t = 1 - C` (Eq. (3)). -/
def tpar : ℝ := 1 - Cpar

/-- `ε = 27/10^12` (Eq. (3)). -/
def eps : ℝ := 27 / 10 ^ 12

/-- `U = 1661483013014771/10^12` (Eq. (6)). -/
def Ubound : ℝ := 1661483013014771 / 10 ^ 12

/-- `L = 1661483013061537/10^12` (Eq. (7)). -/
def Lbound : ℝ := 1661483013061537 / 10 ^ 12

/-- `E = 251500221699/250000000000` (Eq. (8)). -/
def Ebound : ℝ := 251500221699 / 250000000000

/-- `γ = 99857/100000` (Eq. (10)). -/
def gam : ℝ := 99857 / 100000

/-- `η = 9583/10000` (Eq. (10)). -/
def eta : ℝ := 9583 / 10000

/-- The final saving `δ = 30201659/10^10` (Theorem 1.1). -/
def delta : ℝ := 30201659 / 10 ^ 10

/-- The intermediate saving `β = 3020165925/10^12` (proof of Theorem 1.1, p. 6). -/
def beta : ℝ := 3020165925 / 10 ^ 12

end

/-- The tensor product `A ⊗ B`: every product `a b`, with multiplicity, `a ∈ A`, `b ∈ B`. -/
def tensor (A B : Multiset ℕ) : Multiset ℕ :=
  (A ×ˢ B).map fun p => p.1 * p.2

/-- The tensor power `A^{⊗v}`: `A^{⊗0} = {1}`, `A^{⊗(v+1)} = A^{⊗v} ⊗ A` (so `A^{⊗1} = A`). -/
def tpow (A : Multiset ℕ) : ℕ → Multiset ℕ
  | 0 => {1}
  | v + 1 => tensor (tpow A v) A

/-- Completed targets: each target rank `K` becomes `max K B`. -/
def completeTargets (B : ℕ) (X : Multiset ℕ) : Multiset ℕ :=
  X.map fun K => max K B

/-- Completion blocks: one charged block of rank `B - K` for each target of rank `K < B`. -/
def completionBlocks (B : ℕ) (X : Multiset ℕ) : Multiset ℕ :=
  (X.filter fun K => K < B).map fun K => B - K

/-- Splitting one charged block of rank `R` at `J`: kept if `R ≤ J`; otherwise `⌊R/J⌋` blocks
of rank `J` and one block of rank `R mod J` when that is nonzero. -/
def splitBlock (J R : ℕ) : Multiset ℕ :=
  if R ≤ J then {R}
  else Multiset.replicate (R / J) J + (if R % J = 0 then 0 else {R % J})

/-- Splitting every charged block of `X` at `J`. -/
def splitBlocks (J : ℕ) (X : Multiset ℕ) : Multiset ℕ :=
  X.bind (splitBlock J)

/-- `P′`: the charged blocks of the completed and split `v`-fold tensor unit, from block
multiset `P` and target multiset `T`, maximum block rank `J`, minimum target rank `B`. -/
def Pprime (P T : Multiset ℕ) (v J B : ℕ) : Multiset ℕ :=
  splitBlocks J (tpow P v + completionBlocks B (tpow T v))

/-- `T′`: the targets of the completed `v`-fold tensor unit, minimum target rank `B`. -/
def Tprime (T : Multiset ℕ) (v B : ℕ) : Multiset ℕ :=
  completeTargets B (tpow T v)

end ExactDFTRefine.Main


