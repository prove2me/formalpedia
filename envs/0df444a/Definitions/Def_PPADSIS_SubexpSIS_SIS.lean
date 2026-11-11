-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_SIS
-- name    : PPADSIS_SubexpSIS_SIS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:47:47.753368+00:00
-- url     : https://prove2.me/theorems/77e41f4e-66d4-49ea-997d-d53ea35fc34f
-- title:
--   Short Integer Solutions SIS_{n,m,q,β}: advantage, polynomial and 2^{n^ν} hardness, max-entry norm (Definition 3.4)
-- statement:
--   For lattice parameters $n,m,q:\mathbb N\to\mathbb N$ and $\beta:\mathbb N\to\mathbb R$ depending on $\lambda$, the **SIS advantage** of an adversary $A$ at $\lambda$ is
--   $$\Pr\bigl[\mathbf A\mathbf u=0 \bmod q\ \wedge\ 0<\|\mathbf u\|\le\beta \;:\; \mathbf A\leftarrow\mathbb Z_q^{n\times m},\ \mathbf u\leftarrow A(\mathbf A)\bigr],$$
--   with $\mathbf A$ uniform, $\mathbf u\in\mathbb Z^m$ and $\|\mathbf u\|=\max_j|u_j|$ the **max-entry norm**. Following Definition 3.4, $\mathrm{SIS}_{n,m,q,\beta}$ **holds against size-$s$ adversaries with advantage $\delta$** if every adversary of size $s(\lambda)$ has advantage at most $\delta(\lambda)$, at every $\lambda$. It is **polynomially hard** if for every polynomial size bound there is a negligible advantage bound, and, for a constant $\nu>0$, **$2^{n^\nu}$-hard** if it holds against size-$2^{n(\lambda)^\nu}$ adversaries with a negligible advantage $\delta$ (one $\delta$ for all of them, as in Definition 3.4).
--
--   The matrix is given to the adversary as `encNat n`, `encNat m`, `encNat q` followed by its entries in $[0,q)$, row by row, each in $\lfloor\log_2 q\rfloor+1$ bits big-endian; the adversary's output counts only if it is the code of an integer vector $\mathbf u$ (entries by `encInt`).
--
--   **Formalization Note** The size bound $2^{n^\nu}$ is a real number. Success requires $\mathbf u\ne0$, so the zero vector never counts.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 21, Definition 3.4 and the two sentences after it

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_PPADSIS_SubexpSIS_Adversary

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- The **max-entry norm** `‖u‖ = max_j |u_j|` of an integer vector (§3, p. 19: "Integer vectors
and matrices are measured in the max-entry norm"). -/
def maxNorm {m : ℕ} (u : Fin m → ℤ) : ℕ := Finset.univ.sup (fun j => (u j).natAbs)

/-- Code of an integer vector, as output by an SIS adversary: the entries' codes `encInt`. -/
def encIntVec {m : ℕ} (u : Fin m → ℤ) : List Bool := (List.ofFn u).flatMap encInt

/-- Code of a matrix `A ∈ ℤ_q^{n×m}` (entries in `[0, q)`): `encNat n`, `encNat m`, `encNat q`,
then the entries row by row, each in `Nat.size q` bits, big-endian. For fixed `n, m, q` all codes
have the same length. -/
def encMat {n m q : ℕ} (A : Fin n → Fin m → Fin q) : List Bool :=
  encNat n ++ encNat m ++ encNat q ++
    (List.ofFn fun i => List.ofFn fun j => bitsBE (Nat.size q) (A i j).val).flatten.flatten

/-- `u` is an **SIS solution** for `A` with norm bound `β`: `Au = 0 mod q` and `0 < ‖u‖ ≤ β`. -/
def IsSISSolution {n m q : ℕ} (A : Fin n → Fin m → Fin q) (β : ℝ) (u : Fin m → ℤ) : Prop :=
  (∀ i, (q : ℤ) ∣ ∑ j, ((A i j).val : ℤ) * u j) ∧ 0 < maxNorm u ∧ (maxNorm u : ℝ) ≤ β

/-- The **SIS advantage** of an adversary at `λ` (Definition 3.4, p. 21): the probability, over a
uniform `A ← ℤ_q^{n×m}` (`n = n(λ)`, `m = m(λ)`, `q = q(λ)`) and the adversary's coins, that the
adversary's output on `A` is the code of an SIS solution `u ∈ ℤ^m` with `Au = 0 mod q` and
`0 < ‖u‖ ≤ β(λ)`. -/
noncomputable def sisAdvantage (n m q : ℕ → ℕ) (β : ℕ → ℝ) (A : Adversary) (lam : ℕ) : ℝ :=
  (∑ M : Fin (n lam) → Fin (m lam) → Fin (q lam),
      A.prob lam (encMat M) (fun y => ∃ u : Fin (m lam) → ℤ, y = encIntVec u ∧
        IsSISSolution M (β lam) u)) / ((q lam : ℝ) ^ (n lam * m lam))

/-- `SIS_{n,m,q,β}` **holds against size-`s` adversaries with advantage `δ`** (Definition 3.4,
p. 21): for every adversary `A` of size `s(λ)` and every `λ`, the SIS advantage at `λ` is at most
`δ(λ)`. -/
def SISHoldsAgainst (n m q : ℕ → ℕ) (β : ℕ → ℝ) (s : ℕ → ℝ) (δ : ℕ → ℝ) : Prop :=
  ∀ A : Adversary, A.SizeLE s → ∀ lam, sisAdvantage n m q β A lam ≤ δ lam

/-- `SIS_{n,m,q,β}` is **polynomially hard** (p. 21): it holds against size-`poly(λ)` adversaries
with advantage `negl(λ)`, i.e. for every polynomial size bound `(λ + 2)^c` there is a negligible
advantage bound. -/
def SISPolyHard (n m q : ℕ → ℕ) (β : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ δ : ℕ → ℝ, Negligible δ ∧
    SISHoldsAgainst n m q β (fun lam => ((lam : ℝ) + 2) ^ c) δ

/-- `SIS_{n,m,q,β}` is **`2^{n^ν}`-hard** (p. 21): it holds against size-`2^{n^ν}` adversaries with
advantage `negl(λ)`; the size bound `2^{n(λ)^ν}` is a real number. -/
def SISSubexpHard (n m q : ℕ → ℕ) (β : ℕ → ℝ) (ν : ℝ) : Prop :=
  ∃ δ : ℕ → ℝ, Negligible δ ∧
    SISHoldsAgainst n m q β (fun lam => (2 : ℝ) ^ ((n lam : ℝ) ^ ν)) δ

end PPADSIS.SubexpSIS


