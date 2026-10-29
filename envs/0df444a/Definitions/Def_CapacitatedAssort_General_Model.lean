-- Prove2me | Definitions.Def_CapacitatedAssort_General_Model
-- name    : CapacitatedAssort_General_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:55.131274+00:00
-- url     : https://prove2.me/theorems/1427f253-3452-415a-a80c-1bad2ddba78b
-- title:
--   Cap-General, geometric guesses, rounding and the runtime expression
-- statement:
--   An instance consists of $n$ items, $M$ linear coefficient columns, real weights $w_i$, capacity $W$, a split $k$ and a real function $g$ on $\mathbb R^M$. The standing assumptions require $n,M>0$, $k\le M$, every coefficient strictly positive, every weight nonnegative, and $W\ge0$. For a subset $S$, define $A_m(S)=\sum_{i\in S}a_{im}$, $w(S)=\sum_{i\in S}w_i$ and $f(S)=g(A(S))$. Feasibility is $w(S)\le W$; the empty subset is included. The optimum is the attained maximum of the finite feasible family. Its fallback zero is only for an empty feasible family, excluded by the standing assumptions.
--
--   Column minima and maxima define the minimal covering geometric grid $a_{\min,m}(1+\epsilon)^\ell$, $0\le\ell\le L_m$, where $L_m$ is the least exponent reaching $nA_{\max,m}$. If no such exponent exists, the total definition returns zero; this fallback is outside the source domain $\epsilon>0$. A guess is feasible when a capacity-feasible subset has sums at least its increasing coordinates and at most its decreasing coordinates. Rounding uses floor or ceiling of $na_{im}/(\epsilon h_m)$ according to the split. The signed terminal demands are $I_1=\lfloor n/\epsilon\rfloor-n$ and $I_2=\lceil n/\epsilon\rceil+n$.
--
--   The runtime scale is $(\log(nA_{\max}))^M n^{M+1}/\epsilon^{4M}$, with $A_{\max}=\max_m A_{\max,m}/a_{\min,m}$. Empty-column extrema have zero defaults, and the ratio fold starts at one; under the standing assumptions this is exactly the maximum ratio. No normalization restricts the original real data.
-- source:
--   Désir, Goyal and Zhang (2021), Technical Note—Capacitated Assortment Optimization: Hardness and Approximation, https://doi.org/10.1287/opre.2021.2142, held source.pdf, §3.1, equations (7)–(9), PDF/printed pp. 10–13

import Definitions.Def_CapacitatedAssort_General_Functions

noncomputable section

namespace CapacitatedAssort.General
open Finset

/-- Section 3.1 data. All numerical data remain real. -/
structure Instance (n M : ℕ) where
  a : Fin n → Fin M → ℝ
  w : Fin n → ℝ
  W : ℝ
  split : ℕ
  g : (Fin M → ℝ) → ℝ

def Standing {n M : ℕ} (D : Instance n M) : Prop :=
  0 < n ∧ 0 < M ∧ D.split ≤ M ∧
  (∀ i m, 0 < D.a i m) ∧ (∀ i, 0 ≤ D.w i) ∧ 0 ≤ D.W

def weight {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : ℝ := ∑ i ∈ S, D.w i

def sums {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : Fin M → ℝ :=
  fun m => ∑ i ∈ S, D.a i m

def value {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : ℝ := D.g (sums D S)

def Feasible {n M : ℕ} (D : Instance n M) (S : Finset (Fin n)) : Prop := weight D S ≤ D.W

/-- Attained finite maximum. The fallback occurs only when even ∅ is infeasible. -/
def optimum {n M : ℕ} (D : Instance n M) : ℝ := by
  classical
  let F := (univ : Finset (Finset (Fin n))).filter (Feasible D)
  exact if h : F.Nonempty then F.sup' h (value D) else 0

/-- Empty-column defaults are outside Standing. -/
def amin {n M : ℕ} (D : Instance n M) (m : Fin M) : ℝ :=
  ((List.finRange n).map (fun i => D.a i m)).foldl min (if h : 0 < n then D.a ⟨0,h⟩ m else 0)

def amax {n M : ℕ} (D : Instance n M) (m : Fin M) : ℝ :=
  ((List.finRange n).map (fun i => D.a i m)).foldl max (if h : 0 < n then D.a ⟨0,h⟩ m else 0)

/-- The theorem's unindexed A_max is the largest column ratio. -/
def ratio {n M : ℕ} (D : Instance n M) : ℝ :=
  ((List.finRange M).map (fun m => amax D m / amin D m)).foldl max 1

/-- Minimal covering exponent, not a restriction on the real coefficients. -/
def gridLength {n M : ℕ} (D : Instance n M) (ε : ℝ) (m : Fin M) : ℕ := by
  classical
  exact if h : ∃ L : ℕ, (n : ℝ) * amax D m ≤ amin D m * (1 + ε)^L then Nat.find h else 0

def GridGuess {n M : ℕ} (D : Instance n M) (ε : ℝ) (h : Fin M → ℝ) : Prop :=
  ∀ m, ∃ ℓ : ℕ, ℓ ≤ gridLength D ε m ∧ h m = amin D m * (1 + ε)^ℓ

def GuessFeasible {n M : ℕ} (D : Instance n M) (h : Fin M → ℝ) (S : Finset (Fin n)) : Prop :=
  Feasible D S ∧ ∀ m, if m.val < D.split then h m ≤ sums D S m else sums D S m ≤ h m

def Rounded {n M : ℕ} (D : Instance n M) (ε : ℝ) (h : Fin M → ℝ) (i : Fin n) (m : Fin M) : ℤ :=
  if m.val < D.split then ⌊(n : ℝ) * D.a i m / (ε * h m)⌋
  else ⌈(n : ℝ) * D.a i m / (ε * h m)⌉

def lowerDemand (n : ℕ) (ε : ℝ) : ℤ := ⌊(n : ℝ) / ε⌋ - (n : ℤ)
def upperDemand (n : ℕ) (ε : ℝ) : ℤ := ⌈(n : ℝ) / ε⌉ + (n : ℤ)

/-- The printed runtime expression, evaluated only with n*ratio ≥ 2 and 0<ε<1. -/
def runtimeScale {n M : ℕ} (D : Instance n M) (ε : ℝ) : ℝ :=
  (Real.log ((n : ℝ) * ratio D))^M * (n : ℝ)^(M+1) / ε^(4*M)

end CapacitatedAssort.General


