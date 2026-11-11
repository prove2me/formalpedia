-- Prove2me | Definitions.Def_MongeApprox_Sparsify_Partition
-- name    : MongeApprox_Sparsify_Partition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:02:13.892237+00:00
-- url     : https://prove2.me/theorems/1c453825-6175-4372-808b-d5deaeb3d28d
-- title:
--   The staircase replacement, the recursive dyadic partition with division rule (15), and the sparsified matrix $\widehat A$ (§7)
-- statement:
--   **Staircase** (proof of Lemma 7.5): for $\mu$ on a rectangle $R$ with $T:=\mu(R)$, partition $[0,T)$ into consecutive intervals, one per row of $R$ in decreasing order of rows (bottom first), each of length the row sum, and likewise one per column in increasing order of columns; $\widehat\mu_{ab}$ is the length of the intersection of the interval of row $a$ with that of column $b$. **Recursive partition** (p. 37): for a simple $p\times q$ matrix $A$ with $\mu:=A^\square$, let $\ell_0$ be the smallest power of two with $\ell_0\ge\max\{p,q\}-1$, and regard $\mu$ on $[0..\ell_0)^2$ padded with zeros. A square of side $\ell$ is $C=[x..x+\ell)\times[y..y+\ell)\subseteq[0..\ell_0)^2$ with $\ell$ a power of two dividing $x$ and $y$; its corner value is $\beta(C):=\mu(Q_{x+\ell-1,y+1})$. Starting with the root $[0..\ell_0)^2$, a processed square of side $\ell>1$ with $\mu(C)>0$ is divided (its four quarters processed) iff $\beta(C)=0$ or ($\beta(C)\le K$ and $\mu(C)>\varepsilon\max\{1,\beta(C)\}$) (15); all other processed squares are leaves. $\widehat\mu$ is the staircase replacement on every leaf of positive mass, and $\widehat A$ the simple $p\times q$ matrix with density $\widehat\mu$, i.e. $\widehat A_{ij}=\widehat\mu(Q_{ij})$.
--
--   **Formalization Note.** `staircase μ R` is $\max\{0,\min(\text{hi}_a,\text{hi}_b)-\max(\text{lo}_a,\text{lo}_b)\}$ on $R$ and $0$ outside, using all rows and columns of $R$ (rows and columns of zero sum get empty intervals, so only the nonzero ones matter). Squares are indexed by the exponent $s$ of their side $2^s$ and natural corners; $\ell_0=2^e$ with `e = Nat.clog 2 (max p q - 1)`. `Processed` says every enclosing dyadic square of side $2^{s'}$, $s<s'\le e$, is divided, which is equivalent to the recursive description. `sparsifiedDensity` sums the staircases of the leaves of positive mass; `sparsify A K ε` is $\widehat A$.
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), proof of Lemma 7.5, printed p. 36 (PDF 38); Recursive partition and (15), printed p. 37 (PDF 39)

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Monge
import Definitions.Def_MongeApprox_Sparsify_Quadrant

/-!
# The staircase replacement, the recursive dyadic partition, and the sparsified matrix `Â`

Gorbachev, *Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes*
(2026, PDF sha256 b7eeb435…), proof of Lemma 7.5, printed p. 36 (PDF 38); "Recursive partition"
and (15), printed p. 37 (PDF 39).

Conventions.
* `staircase µ R` is the construction in the proof of Lemma 7.5: with `T := µ(R)`, `[0, T)` is cut
  into consecutive intervals, one per row of `R` in decreasing order of rows (bottom row first),
  each of length its row sum within `R`, and again into intervals, one per column of `R` in
  increasing order of columns; `µ̂_ab` is the length of the intersection of the interval of row `a`
  with the interval of column `b` (`max 0 (min hi hi′ − max lo lo′)`), for `(a, b) ∈ R`, and `0`
  outside `R`. Rows and columns with zero sum get empty intervals, so only nonzero rows and
  columns matter, as in the paper. It reads `µ` only inside `R`, so it is the replacement of the
  restriction of `µ` to `R`.
* Squares: `ℓ0 = 2^e` with `e = levelExp p q = Nat.clog 2 (max p q − 1)`, the smallest power of
  two with `ℓ0 ≥ max{p, q} − 1`. A square of side `2^s` is `[x..x+2^s) × [y..y+2^s)` with
  `x, y < 2^e` naturals divisible by `2^s` (`sqRect s x y`). Its corner value is
  `β(C) := µ(Q_{x+ℓ−1, y+1})` (`cornerValue`).
* (15): a processed square of side `ℓ = 2^s > 1` with `µ(C) > 0` is divided iff `β(C) = 0` or
  (`β(C) ≤ K` and `µ(C) > ε max{1, β(C)}`) (`Divided`, with `K ∈ [0, +∞]`). The root
  `[0..ℓ0)²` is processed; the quarters of a processed divided square are processed. Equivalently
  (`Processed`): every strictly larger dyadic square containing it, up to the root, is divided.
  A leaf is a processed square that is not divided.
* `sparsifiedDensity µ K ε e` is `µ̂`: the sum over the leaves `L` of positive mass of
  `staircase µ L` (leaves are disjoint, so at each position at most one term is nonzero).
* `sparsify A K ε` is `Â`: the `p × q` matrix with `Â_ij := µ̂(Q_ij)` where `µ := A□` (as a
  function on `ℤ²`, zero outside `[0..p−1) × [0..q−1)`), i.e. the simple matrix with density `µ̂`
  by (13).
-/

namespace MongeApprox.Sparsify

open scoped ENNReal

/-- The staircase replacement of the proof of Lemma 7.5 for `µ` on `R`. -/
noncomputable def staircase (μ : ℤ × ℤ → ℝ) (R : Rect) (z : ℤ × ℤ) : ℝ :=
  open Classical in
  if z ∈ R.toSet then
    let rowLo := ∑ a' ∈ Finset.Ico (z.1 + 1) R.x', ∑ b' ∈ Finset.Ico R.y R.y', μ (a', b')
    let rowHi := rowLo + ∑ b' ∈ Finset.Ico R.y R.y', μ (z.1, b')
    let colLo := ∑ b' ∈ Finset.Ico R.y z.2, ∑ a' ∈ Finset.Ico R.x R.x', μ (a', b')
    let colHi := colLo + ∑ a' ∈ Finset.Ico R.x R.x', μ (a', z.2)
    max 0 (min rowHi colHi - max rowLo colLo)
  else 0

/-- The exponent `e` of `ℓ0 = 2^e`, the smallest power of two with `ℓ0 ≥ max{p, q} − 1`. -/
def levelExp (p q : ℕ) : ℕ :=
  Nat.clog 2 (max p q - 1)

/-- The square `[x..x+2^s) × [y..y+2^s)`. -/
def sqRect (s x y : ℕ) : Rect :=
  ⟨(x : ℤ), (x : ℤ) + 2 ^ s, (y : ℤ), (y : ℤ) + 2 ^ s⟩

/-- The corner value `β(C) := µ(Q_{x+ℓ−1, y+1})` of `C = [x..x+ℓ) × [y..y+ℓ)`, `ℓ = 2^s`. -/
noncomputable def cornerValue (μ : ℤ × ℤ → ℝ) (s x y : ℕ) : ℝ :=
  mass μ (Q ((x : ℤ) + 2 ^ s - 1) ((y : ℤ) + 1))

/-- The division rule (15) for the square of side `2^s` at `(x, y)`: side `> 1`, positive mass,
and `β(C) = 0` or (`β(C) ≤ K` and `µ(C) > ε max{1, β(C)}`). -/
def Divided (μ : ℤ × ℤ → ℝ) (K : ℝ≥0∞) (ε : ℝ) (s x y : ℕ) : Prop :=
  0 < s ∧ 0 < mass μ (sqRect s x y).toSet ∧
    (cornerValue μ s x y = 0 ∨
      (LeThreshold (cornerValue μ s x y) K ∧
        ε * max 1 (cornerValue μ s x y) < mass μ (sqRect s x y).toSet))

/-- The square of side `2^s` at `(x, y)` inside `[0..2^e)²` is processed: it is a dyadic square
and every dyadic square of side `2^{s'}`, `s < s' ≤ e`, containing it is divided. -/
def Processed (μ : ℤ × ℤ → ℝ) (K : ℝ≥0∞) (ε : ℝ) (e s x y : ℕ) : Prop :=
  s ≤ e ∧ x < 2 ^ e ∧ y < 2 ^ e ∧ 2 ^ s ∣ x ∧ 2 ^ s ∣ y ∧
    ∀ s', s < s' → s' ≤ e → Divided μ K ε s' (x / 2 ^ s' * 2 ^ s') (y / 2 ^ s' * 2 ^ s')

/-- A leaf: a processed square that is not divided. -/
def Leaf (μ : ℤ × ℤ → ℝ) (K : ℝ≥0∞) (ε : ℝ) (e s x y : ℕ) : Prop :=
  Processed μ K ε e s x y ∧ ¬ Divided μ K ε s x y

/-- `µ̂`: the staircase replacement applied to every leaf of positive mass, `µ` kept nowhere else
(the leaves partition `[0..2^e)²`, and outside the leaves of positive mass `µ` vanishes when it is
supported on `[0..2^e)²`). -/
noncomputable def sparsifiedDensity (μ : ℤ × ℤ → ℝ) (K : ℝ≥0∞) (ε : ℝ) (e : ℕ)
    (z : ℤ × ℤ) : ℝ :=
  open Classical in
  ∑ s ∈ Finset.range (e + 1), ∑ x ∈ Finset.range (2 ^ e), ∑ y ∈ Finset.range (2 ^ e),
    if Leaf μ K ε e s x y ∧ 0 < mass μ (sqRect s x y).toSet then
      staircase μ (sqRect s x y) z
    else 0

/-- `Â`: the simple `p × q` matrix with density `µ̂ = sparsifiedDensity (A□) K ε e`, i.e.
`Â_ij := µ̂(Q_ij)`, where `ℓ0 = 2^e` is the smallest power of two `≥ max{p, q} − 1`. -/
noncomputable def sparsify {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (K : ℝ≥0∞) (ε : ℝ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j => mass (sparsifiedDensity (densityZ A) K ε (levelExp p q)) (Q (i : ℤ) (j : ℤ))

end MongeApprox.Sparsify


