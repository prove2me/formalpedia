-- Prove2me | Definitions.Def_LSSInterface
-- name    : LSSInterface
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-28T13:26:29.045253+00:00
-- url     : https://prove2.me/theorems/a6fc7247-12bd-4c14-9ca1-1258c84131b7
-- title:
--   Leng–Sah–Sawhney interface: quasi-polynomial inverse theorem and Schmidt property for a class of structured functions
-- statement:
--   Vocabulary for the structural input of the Leng–Sah–Sawhney density increment argument. Throughout, $\mathrm{Str}(N,Q,\varphi)$ is an arbitrary predicate on $N\in\mathbb N$, $Q\in\mathbb R$ and $\varphi:\mathbb Z\to\mathbb R$, read as "$\varphi$ is a structured function of complexity at most $Q$ on $\{1,\dots,N\}$".
--
--   * `gowersZ N d g` is the unnormalised Gowers sum $\sum_{x\in[1,N]}\sum_{h_1,\dots,h_d\in(-N,N)}\prod_{\omega\in\{0,1\}^d} g(x+\omega\cdot h)$, defined recursively via the multiplicative derivative `dmul h g x = g x * g (x+h)`.
--   * `qp C x` $=\exp\big(C(1+\log x)^C\big)$ (quasi-polynomial growth).
--   * `apSet a d len` $=\{a,a+d,\dots,a+(len-1)d\}\subseteq\mathbb Z$, and `APPart N` is a partition of $\{1,\dots,N\}$ into finitely many such progressions with positive common differences.
--   * `InvWith Str s C`: for every $N$, every $0<\delta\le 1/2$ and every $f:\mathbb Z\to[-1,1]$ supported on $\{1,\dots,N\}$ with `gowersZ N (s+1) f` $\ge \delta^{2^{s+1}}N^{s+2}$, there is $\varphi$ with $\mathrm{Str}(N,Q,\varphi)$, $|\varphi|\le Q$ and $\big|\sum_{x=1}^N f(x)\varphi(x)\big|\ge N/Q$, where $Q=\mathrm{qp}(C,1/\delta)$. `InvHyp Str s` means $\exists C>0$ with `InvWith Str s C` (a quasi-polynomial inverse theorem for the $U^{s+1}[N]$ norm).
--   * `SchmidtWith Str C`: for all $N,T$, $Q\ge 1$ and $\varphi_1,\dots,\varphi_T$ with $\mathrm{Str}(N,Q,\varphi_i)$, writing $V=\mathrm{qp}(C,(T+2)(Q+2))$, there is a partition of $\{1,\dots,N\}$ into $L$ progressions with $L\,N^{1/V}\le 2N$ such that $|\varphi_i(x)-\varphi_i(y)|\le V N^{-1/V}$ whenever $x,y$ lie in the same piece. `SchmidtHyp Str` means $\exists C>0$ with `SchmidtWith Str C`.
--
--   In the literature the class is that of Lipschitz nilsequences $F(g(n)\Gamma)$ of degree $s$ with dimension at most $1+\log Q$ and complexity and Lipschitz constant at most $Q$.
-- source:
--   J. Leng, A. Sah, M. Sawhney, Improved bounds for Szemerédi's theorem, arXiv:2402.17995, Theorem 3.1 (inverse theorem, from arXiv:2402.17994 Theorem 1.2) and Lemma 2.1 (Schmidt for nilsequences)

import Mathlib



/-!
# The abstract interface for the Leng–Sah–Sawhney argument

The density-increment argument of Leng–Sah–Sawhney uses two external inputs about a class of
"structured functions" (in the paper: Lipschitz nilsequences of bounded complexity):

* `InvHyp Str s`: the inverse theorem for the `U^{s+1}[N]` norm with quasi-polynomial bounds;
* `SchmidtHyp Str`: any `T` structured functions are simultaneously almost constant on the
  pieces of a partition of `{1, …, N}` into long arithmetic progressions.

Here the class is an arbitrary predicate `Str N Q φ` ("`φ : ℤ → ℝ` is structured of complexity
at most `Q` on `{1, …, N}`").
-/

open Finset

namespace LSS

noncomputable section

/-- Multiplicative derivative on `ℤ`. -/
def dmul (h : ℤ) (g : ℤ → ℝ) : ℤ → ℝ := fun x => g x * g (x + h)

/-- The (unnormalised) Gowers sum of order `d` of a function supported on `{1, …, N}`:
`gowersZ N d g = ∑_{x, h_1, …, h_d} ∏_{ω ∈ {0,1}^d} g (x + ω · h)`. -/
def gowersZ (N : ℕ) : ℕ → (ℤ → ℝ) → ℝ
  | 0, g => ∑ x ∈ Icc (1 : ℤ) N, g x
  | d + 1, g => ∑ h ∈ Ioo (-(N : ℤ)) N, gowersZ N d (dmul h g)

/-- `g` vanishes outside `{1, …, N}`. -/
def SupportedOn (N : ℕ) (g : ℤ → ℝ) : Prop := ∀ x, g x ≠ 0 → 1 ≤ x ∧ x ≤ N

/-- Quasi-polynomial growth: `qp C x = exp (C (1 + log x)^C)`. -/
def qp (C x : ℝ) : ℝ := Real.exp (C * (1 + Real.log x) ^ C)

/-- The arithmetic progression `{a, a + d, …, a + (len - 1) d}`. -/
def apSet (a : ℤ) (d len : ℕ) : Finset ℤ := (range len).image (fun i : ℕ => a + d * i)

/-- A partition of `{1, …, N}` into arithmetic progressions with positive common difference. -/
structure APPart (N : ℕ) where
  L : ℕ
  a : Fin L → ℤ
  d : Fin L → ℕ
  len : Fin L → ℕ
  hd : ∀ j, 0 < d j
  disj : ∀ i j, i ≠ j → Disjoint (apSet (a i) (d i) (len i)) (apSet (a j) (d j) (len j))
  cover : ∀ x, x ∈ Icc (1 : ℤ) N ↔ ∃ j, x ∈ apSet (a j) (d j) (len j)

/-- The piece number `j` of a partition. -/
def APPart.piece {N : ℕ} (P : APPart N) (j : Fin P.L) : Finset ℤ :=
  apSet (P.a j) (P.d j) (P.len j)

/-- The inverse theorem with constant `C`: a `1`-bounded function on `{1, …, N}` with Gowers sum
at least `δ^{2^{s+1}} N^{s+2}` correlates with a structured function of complexity at most
`qp C (1/δ) = exp (C (1 + log (1/δ))^C)`. -/
def InvWith (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) (s : ℕ) (C : ℝ) : Prop :=
  ∀ (N : ℕ) (δ : ℝ) (f : ℤ → ℝ), 0 < δ → δ ≤ 1 / 2 → (∀ x, |f x| ≤ 1) →
    SupportedOn N f → δ ^ (2 ^ (s + 1)) * (N : ℝ) ^ (s + 2) ≤ gowersZ N (s + 1) f →
    ∃ φ : ℤ → ℝ, Str N (qp C (1 / δ)) φ ∧ (∀ x, |φ x| ≤ qp C (1 / δ)) ∧
      (N : ℝ) / qp C (1 / δ) ≤ |∑ x ∈ Icc (1 : ℤ) N, f x * φ x|

/-- **Inverse theorem hypothesis** (quasi-polynomial `U^{s+1}[N]` inverse theorem). -/
def InvHyp (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) (s : ℕ) : Prop := ∃ C : ℝ, 0 < C ∧ InvWith Str s C

/-- The Schmidt-type property with constant `C`: `T` structured functions of complexity at most
`Q` are simultaneously almost constant on the pieces of a partition of `{1, …, N}` into few
(hence long on average) arithmetic progressions, with quasi-polynomial dependence on
`(T + 2)(Q + 2)`. -/
def SchmidtWith (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) (C : ℝ) : Prop :=
  ∀ (N T : ℕ) (Q : ℝ) (φ : Fin T → ℤ → ℝ), 1 ≤ Q → (∀ i, Str N Q (φ i)) →
    ∃ P : APPart N,
      (P.L : ℝ) * (N : ℝ) ^ (1 / qp C ((T + 2) * (Q + 2))) ≤ 2 * N ∧
      ∀ i j, ∀ x ∈ P.piece j, ∀ y ∈ P.piece j,
        |φ i x - φ i y| ≤ qp C ((T + 2) * (Q + 2)) * (N : ℝ) ^ (-(1 / qp C ((T + 2) * (Q + 2))))

/-- **Schmidt-type hypothesis.** -/
def SchmidtHyp (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) : Prop := ∃ C : ℝ, 0 < C ∧ SchmidtWith Str C

end

end LSS


