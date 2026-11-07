-- Prove2me | Definitions.Def_ArbSlowFP_binomBasis
-- name    : ArbSlowFP_binomBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:45:51.974432+00:00
-- url     : https://prove2.me/theorems/d551e600-5a1d-4a37-8e92-9fdfb779fc5d
-- title:
--   Binomial basis, shift matrices, transfer matrices and compatibility-test matrices
-- statement:
--   The **binomial basis** is $p_{s-1}(q)=(1,q,\binom q2,\dots,\binom q{s-1})^\top$ for an integer $q$, with indices from $0$, and $\binom qj=q(q-1)\cdots(q-j+1)/j!$ also for negative $q$. The shift matrices are $N_s$ with $(N_s)_{i,i-1}=1$, $T_s=I_s+N_s$ and $B_s=T_s^{-1}$. They satisfy $p_{s-1}(q+1)=T_sp_{s-1}(q)$.
--
--   The **transfer matrices** $E_a$ and $F_\tau$ of width $k+1$ are the integer matrices with
--   $$p_{k-1}(aq)=E_ap_k(q),\qquad \sum_{\sigma=\tau q}^{2\tau q-1}p_{k-1}(\sigma)=F_\tau p_k(q).$$
--   The **compatibility-test matrices** are built from $V^{(h)}_{ij}=(-1)^i\mathbf 1\{i+j=h\}$ by
--   $$Z^{(h)}_{DP}=e^{-N_0/2}V^{(h)},\qquad Z^{(h)}=S_wZ^{(h)}_{DP}S_w^\top ,$$
--   where $N_0=N_{k+1}$ and $S_w$ is the change of basis $p_k(q)=S_w(1,q,q^2/2!,\dots,q^k/k!)^\top$. The module also has the inner product $\langle U,V\rangle=\sum_{i,j}U_{ij}V_{ij}$, the operator $L(E)=E-E^\top B$, and the norm $\|Z\|_*=\max\{\max_j\sum_i|Z_{ij}|,\max_i\sum_j|Z_{ij}|\}$.
--
--   These tables turn polynomial phase identities into finite matrix identities.
--
--   **Formalization Note** $E_a$, $F_\tau$, $B_s$ and $S_w$ are given by closed forms (footnote 1, p.35; signed Stirling numbers for $S_w$), so no matrix inverse or choice occurs. The binomial uses `Ring.choose` on $\mathbb Z$. A bound $\|Z\|_*\le K$ is `NormStarLE Z K`. Rational and integer codes (`QCode`, `decodeQ`, `decodeZ`) exist for the computation clause of Lemma 7.2, since Mathlib has `Primcodable` for $\mathbb N$, products and lists but not for $\mathbb Z$ or $\mathbb Q$.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), pp.14–15, 35, 37, 43, 48; eqs. (9), (25), (29), (40), (45)

import Mathlib

open Matrix

namespace ArbSlowFP

/-- The binomial basis `p_{s-1}(q) = (1, q, C(q,2), …, C(q,s-1))⊤` of §3.2, p.14, with indices from
`0`, at an integer phase index.

**Formalization Note.** `Ring.choose` on `ℤ` is the polynomial `q(q-1)⋯(q-j+1)/j!`, also at negative
arguments, which (25) and `ζ(q-1)` at `q = 0` require; `Nat.choose` would be a different function. -/
def binomBasis (s : ℕ) (q : ℤ) : Fin s → ℚ := fun j => ((Ring.choose q (j : ℕ) : ℤ) : ℚ)

/-- The row `e⊤_{0,s} = (1, 0, …, 0)`, p.14. -/
def e0Row (s : ℕ) : Fin s → ℚ := fun j => if (j : ℕ) = 0 then 1 else 0

/-- The first-subdiagonal shift `N_s`, `(N_s)_{i,i-1} = 1`, p.15. Also the matrix `N₀` of (29). -/
def shiftN (s : ℕ) : Matrix (Fin s) (Fin s) ℚ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- The forward shift `T_s = I_s + N_s`, p.15. -/
def shiftT (s : ℕ) : Matrix (Fin s) (Fin s) ℚ := 1 + shiftN s

/-- The backward shift `B_s = T_s⁻¹`, p.15, in closed form: `(B_s)_{ij} = (-1)^{i-j}` for `j ≤ i` and
`0` otherwise, as in the printed `B₂`, `B₃`.

**Formalization Note.** The closed form uses no matrix inverse. `shiftT s * shiftB s = 1` is proved
in the mission's sanity file. -/
def shiftB (s : ℕ) : Matrix (Fin s) (Fin s) ℚ :=
  Matrix.of fun i j => if (j : ℕ) ≤ (i : ℕ) then (-1) ^ ((i : ℕ) - (j : ℕ)) else 0

/-- The transfer matrix `E_a` of (25), p.35, `p_{k-1}(aq) = E_a p_k(q)`, in the explicit form of
footnote 1: `(E_a)_{ij} = Σ_{h ≤ j} (-1)^{j-h} C(j,h) C(ah,i)`. -/
def transE (k a : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j =>
    ∑ h ∈ Finset.range ((j : ℕ) + 1),
      (-1 : ℚ) ^ ((j : ℕ) - h) * ((j : ℕ).choose h : ℚ) * ((a * h).choose (i : ℕ) : ℚ)

/-- The transfer matrix `F_τ` of (25), p.35, `Σ_{σ=τq}^{2τq-1} p_{k-1}(σ) = F_τ p_k(q)`, in the
explicit form `(F_τ)_{ij} = Σ_{h ≤ j} (-1)^{j-h} C(j,h) (C(2τh,i+1) - C(τh,i+1))` of footnote 1. -/
def transF (k τ : ℕ) : Matrix (Fin k) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j =>
    ∑ h ∈ Finset.range ((j : ℕ) + 1),
      (-1 : ℚ) ^ ((j : ℕ) - h) * ((j : ℕ).choose h : ℚ) *
        (((2 * τ * h).choose ((i : ℕ) + 1) : ℚ) - ((τ * h).choose ((i : ℕ) + 1) : ℚ))

/-- Signed Stirling numbers of the first kind: `q(q-1)⋯(q-n+1) = Σ_i s(n,i) q^i`. -/
def signedStirling : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => -(n : ℚ) * signedStirling n 0
  | n + 1, i + 1 => signedStirling n i - (n : ℚ) * signedStirling n (i + 1)

/-- The change of basis `S_w` of p.37, `p_k(q) = S_w (1, q, q²/2!, …, q^k/k!)⊤`: entry `(i, j)` is
`s(i,j) j!/i!`, since `C(q,i) = Σ_j s(i,j) (j!/i!) q^j/j!`. -/
def scaleS (w : ℕ) : Matrix (Fin w) (Fin w) ℚ :=
  Matrix.of fun i j =>
    signedStirling (i : ℕ) (j : ℕ) * ((j : ℕ).factorial : ℚ) / ((i : ℕ).factorial : ℚ)

/-- The exponential `e^{sN₀}` of p.37, as the finite sum `Σ_{j ≤ w} s^j N₀^j / j!` (`N₀^w = 0`). -/
def expN0 (w : ℕ) (s : ℚ) : Matrix (Fin w) (Fin w) ℚ :=
  ∑ j ∈ Finset.range (w + 1), (s ^ j / (j.factorial : ℚ)) • shiftN w ^ j

/-- The matrix `V^(h)` of (29), p.37: `V^(h)_{ij} = (-1)^i 1{i+j=h}`, `0 ≤ i, j ≤ k`. -/
def testV (k h : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  Matrix.of fun i j => if (i : ℕ) + (j : ℕ) = h then (-1) ^ (i : ℕ) else 0

/-- `Z^(h)_DP = e^{-N₀/2} V^(h)` of (29), p.37. -/
def testZDP (k h : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  expN0 (k + 1) (-1 / 2) * testV k h

/-- `Z^(h) = S_w Z^(h)_DP S_w⊤` of (29), p.37. -/
def testZ (k h : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  scaleS (k + 1) * testZDP k h * (scaleS (k + 1))ᵀ

/-- The matrix inner product `⟨U, V⟩ = Σ_{i,j} U_ij V_ij`, p.43. -/
def frob {a b : Type*} [Fintype a] [Fintype b] (U V : Matrix a b ℚ) : ℚ :=
  ∑ i, ∑ j, U i j * V i j

/-- The operator `L(E) = E - E⊤B` of (40), p.42. -/
def opL {w : ℕ} (E : Matrix (Fin w) (Fin w) ℚ) : Matrix (Fin w) (Fin w) ℚ :=
  E - Eᵀ * shiftB w

/-- The last coefficient `x_{k-1}` of a width-`k` row. The value at `k = 0` is never used: an order-k
clock has `k ≥ 2`. -/
def lastCoef {k : ℕ} (x : Fin k → ℚ) : ℚ := if h : 0 < k then x ⟨k - 1, by omega⟩ else 0

/-- `‖Z‖∗ ≤ K` for the norm (45), p.48, `‖Z‖∗ = max{max_j Σ_i |Z_ij|, max_i Σ_j |Z_ij|}`, written as
the two inequalities it abbreviates, so that no supremum over a possibly empty index arises. -/
def NormStarLE {a b : Type*} [Fintype a] [Fintype b] (Z : Matrix a b ℚ) (K : ℚ) : Prop :=
  (∀ j, ∑ i, |Z i j| ≤ K) ∧ ∀ i, ∑ j, |Z i j| ≤ K

/-- A rational number code `(pos, neg, den)`, standing for `(pos - neg)/(den + 1)`, for the "computed
in finitely many steps" clause of Lemma 7.2 (Mathlib has `Primcodable` for `ℕ`, products and lists,
not for `ℤ` or `ℚ`). -/
abbrev QCode := ℕ × ℕ × ℕ

/-- The rational number with a given code. Every rational number has a code. -/
def decodeQ (c : QCode) : ℚ := ((c.1 : ℚ) - (c.2.1 : ℚ)) / ((c.2.2 : ℚ) + 1)

/-- The integer with code `(pos, neg)`, standing for `pos - neg`. -/
def decodeZ (c : ℕ × ℕ) : ℚ := (c.1 : ℚ) - (c.2 : ℚ)

/-- A list of rational codes is a code of the width-`s` row `x`. -/
def IsRowCode {s : ℕ} (L : List QCode) (x : Fin s → ℚ) : Prop :=
  L.length = s ∧ ∀ j : Fin s, decodeQ (L.getD (j : ℕ) (0, 0, 0)) = x j

/-- A list of lists of rational codes is a code of the `s × t` matrix `Z`, row by row. -/
def IsMatCode {s t : ℕ} (L : List (List QCode)) (Z : Matrix (Fin s) (Fin t) ℚ) : Prop :=
  L.length = s ∧ ∀ i : Fin s, IsRowCode (L.getD (i : ℕ) []) (Z i)

end ArbSlowFP


