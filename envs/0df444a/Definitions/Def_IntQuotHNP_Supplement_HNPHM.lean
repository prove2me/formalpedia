-- Prove2me | Definitions.Def_IntQuotHNP_Supplement_HNPHM
-- name    : IntQuotHNP_Supplement_HNPHM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:04:08.272054+00:00
-- url     : https://prove2.me/theorems/92f9c4e9-c3fa-48a4-94da-7d34963548d0
-- title:
--   Definition 6.1 and (22) — HNPHM inputs, consistent secrets, the sampling model, and $\Delta_N$, $\sigma_N$
-- statement:
--   Let $p$ be prime, $N\ge1$ and $1\le X<p$, and put $k=2N+1$. A **public HNPHM input** consists of approximations $v=(v_1,\dots,v_k)\in\mathbb Z_p^k$ and, for leading-bit observations, integer intervals in $\mathbb Z_p$ for the $k$ approximated integers. A secret $y\in\mathbb Z_p\setminus\{0\}$ is **consistent** with the input when there are multipliers $t_1,\dots,t_N\in\mathbb Z_p\setminus\{0\}$ with
--   $$
--   |y-v_1|\le X,\qquad |t_i-v_{i+1}|\le X,\qquad |[yt_i]_p-v_{N+i+1}|\le X\qquad(i\in[N]),
--   $$
--   the differences taken in $\mathbb Z$, and with $y$, $t_i$, $[yt_i]_p$ in their supplied intervals. The input is **promised** when a consistent secret exists. The **solution set** is the set of consistent secrets.
--
--   The **polynomials** of (22) are $P_i(x)=(v_1+x_1)(v_{i+1}+x_{i+1})-(v_{N+i+1}+x_{N+i+1})$ for $i\in[N]$, followed by $P_{N+i}=px_{i+1}$ ($i\in[N]$) and $P_{2N+1}=px_1$.
--
--   In the **sampling model** a secret $y^*\in\mathbb Z_p\setminus\{0\}$ is fixed, the multipliers are independent and uniform in $\mathbb Z_p\setminus\{0\}$, and an **approximation rule** produces the approximations (and intervals) as any function of the multipliers satisfying the displayed bounds for $y^*$. Finally
--   $$
--   \Delta_N=\frac{X^{3N+1}}{(p-1)^N},\qquad \sigma_N=\frac{N}{3N+1}.
--   $$
--
--   **Formalization Note** Residues are natural numbers below $p$. The paper's index $j\in[k]$ is the Lean index $j-1$: `v 0` approximates $y$, `v (i+1)` the multiplier $t_{i+1}$, and `v (N+i+1)` the product $[yt_{i+1}]_p$. The input code writes $p$, $X$, $N$, the approximations and the optional intervals with the published self-delimiting binary code. Leading-bit intervals are allowed to be any integer intervals in $\mathbb Z_p$.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 6.1, p.37 (PDF p.38); Theorem 6.2, p.37 (PDF p.38); §6.1, eq. (22), p.38 (PDF p.39)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_IntQuotHNP_Supplement_CoeffMap

open ExponomialAssortment.FPTAS (encodeNat)

namespace IntQuotHNP

namespace Supplement

/-- **A public HNPHM input** (Definition 6.1).
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 6.1, p.37 (PDF p.38):
"Let p be prime, let N ≥ 1 and 1 ≤ X < p be integers, and put k = 2N + 1. The public input
consists of approximations v = (v₁, . . . , v_k) ∈ ℤ_p^k. … For leading-bit observations, the
input also supplies the original integer intervals specified by the revealed bits."

The record holds `p`, `X`, `N`, the approximations `v` and, optionally, one integer interval
`[lo_j, hi_j]` for each of the `k = 2N + 1` approximated integers.

**Formalization Note.** Residues are natural numbers. The paper's index `j ∈ [k]` is the Lean index
`j − 1 ∈ Fin (2N + 1)`: `v 0` approximates the secret, `v (i + 1)` the multiplier `t_{i+1}` and
`v (N + i + 1)` the product `[y t_{i+1}]_p`, for `i ∈ Fin N`. `iv = none` is an input without
leading-bit intervals. -/
structure HNPHMInput where
  /-- the prime modulus `p` -/
  p : ℕ
  /-- the approximation radius `X` -/
  X : ℕ
  /-- the number `N` of multiplier–product pairs -/
  N : ℕ
  /-- the approximations `v₁, …, v_k`, `k = 2N + 1` -/
  v : Fin (2 * N + 1) → ℕ
  /-- the optional leading-bit intervals `[lo_j, hi_j]` -/
  iv : Option (Fin (2 * N + 1) → ℕ × ℕ)

/-- **The approximated integers of a secret and multipliers**: index `0` is `y`, index `i + 1` is
`t_i` and index `N + i + 1` is `[y t_i]_p` (paper: `y`, `t_{i+1}`, `[y t_{i+1}]_p`). -/
def hnphmValues (p N : ℕ) (y : ℕ) (t : Fin N → ℕ) (j : Fin (2 * N + 1)) : ℕ :=
  if h : j.val = 0 then y
  else if h' : j.val ≤ N then t ⟨j.val - 1, by omega⟩
  else (y * t ⟨j.val - N - 1, by omega⟩) % p

/-- **A secret and multipliers consistent with an HNPHM input** (Definition 6.1, (20)).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 6.1, p.37 (PDF p.38):
"|y∗ − v₁| ≤ X, |t∗_i − v_{i+1}| ≤ X, |[y∗t∗_i]_p − v_{N+i+1}| ≤ X (i ∈ [N]). (20) … the
differences in (20) are in ℤ. … A secret y ∈ ℤ_p \ {0} is consistent with the input if there exist
multipliers t₁, . . . , t_N ∈ ℤ_p \ {0} such that the displayed approximation bounds hold with y,
t_i in place of y∗, t∗_i, and all supplied leading-bit constraints also hold."

`HNPHMConsistent I y t` says `1 ≤ y < p`, `1 ≤ t_i < p` for all `i`, each approximated integer is
within `X` of its approximation (as integers), and, if intervals are supplied, each approximated
integer lies in its interval.

**Formalization Note.** The products are the least nonnegative residues `(y t_i) mod p`; the
differences are taken in `ℤ` between these residues and the approximations. -/
def HNPHMConsistent (I : HNPHMInput) (y : ℕ) (t : Fin I.N → ℕ) : Prop :=
  1 ≤ y ∧ y < I.p ∧ (∀ i, 1 ≤ t i ∧ t i < I.p) ∧
    (∀ j, |(hnphmValues I.p I.N y t j : ℤ) - I.v j| ≤ I.X) ∧
    ∀ L, I.iv = some L → ∀ j, (L j).1 ≤ hnphmValues I.p I.N y t j ∧
      hnphmValues I.p I.N y t j ≤ (L j).2

/-- **A promised HNPHM input** (Definition 6.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 6.1, p.37 (PDF p.38):
"Let p be prime, let N ≥ 1 and 1 ≤ X < p … approximations v ∈ ℤ_p^k. It is promised to have a
hidden secret y∗ ∈ ℤ_p \ {0} and multipliers t∗₁, . . . , t∗_N ∈ ℤ_p \ {0} satisfying (20). … These
intervals lie in ℤ_p and contain the corresponding values y∗, t∗_i, and [y∗t∗_i]_p."

**Formalization Note.** Every clause is a conjunct: `p` prime, `N ≥ 1`, `1 ≤ X < p`, `v ∈ ℤ_p^k`,
supplied intervals inside `ℤ_p`, and a consistent secret with multipliers (which also lie in the
intervals). Leading-bit intervals are allowed to be any integer intervals in `ℤ_p`, not only those
cut out by revealed bits. -/
def HNPHMPromised (I : HNPHMInput) : Prop :=
  I.p.Prime ∧ 1 ≤ I.N ∧ 1 ≤ I.X ∧ I.X < I.p ∧ (∀ j, I.v j < I.p) ∧
    (∀ L, I.iv = some L → ∀ j, (L j).2 < I.p) ∧ ∃ y t, HNPHMConsistent I y t

open Classical in
/-- **The secrets satisfying the input constraints**: the exact output required by Theorem 6.2.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Theorem 6.2, p.37 (PDF p.38):
"Algorithm 1 deterministically returns exactly the secrets satisfying the input constraints". -/
noncomputable def hnphmSolutionSet (I : HNPHMInput) : Finset ℕ :=
  (Finset.range I.p).filter fun y => ∃ t : Fin I.N → ℕ, HNPHMConsistent I y t

/-- **The binary code of a public HNPHM input**: `p`, `X`, `N`, `v₁, …, v_k`, then `0` for no
intervals or `1` followed by the endpoints `lo_j, hi_j` (`j` increasing), each number written with
the published self-delimiting code `encodeNat`. The code is injective. -/
def hnphmEncodeInput (I : HNPHMInput) : List Bool :=
  encodeNat I.p ++ encodeNat I.X ++ encodeNat I.N ++ (List.ofFn I.v).flatMap encodeNat ++
    match I.iv with
    | none => [false]
    | some L => true :: (List.ofFn L).flatMap fun q => encodeNat q.1 ++ encodeNat q.2

/-- **The HNPHM polynomials** ((22) and the appended `p x_j`).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §6.1, p.38 (PDF p.39):
"P_i(x) = (v₁ + x₁)(v_{i+1} + x_{i+1}) − (v_{N+i+1} + x_{N+i+1}) (i ∈ [N]). (22) Set m = 2N + 1
and append P_{N+i} = px_{i+1} (i ∈ [N]), P_m = px₁."

Lean index `h`: for `h < N` the product relation of the `(h + 1)`-st pair; for `N ≤ h < 2N` the
polynomial `p·x_{h−N+2}` (Lean variable `h − N + 1`); for `h = 2N` the polynomial `p·x₁`. -/
noncomputable def hnphmPolys (I : HNPHMInput) :
    Fin (2 * I.N + 1) → MvPolynomial (Fin (2 * I.N + 1)) ℤ :=
  fun h =>
    if h1 : h.val < I.N then
      (MvPolynomial.C (I.v ⟨0, by omega⟩ : ℤ) + MvPolynomial.X ⟨0, by omega⟩) *
          (MvPolynomial.C (I.v ⟨h.val + 1, by omega⟩ : ℤ) + MvPolynomial.X ⟨h.val + 1, by omega⟩) -
        (MvPolynomial.C (I.v ⟨I.N + h.val + 1, by omega⟩ : ℤ) +
          MvPolynomial.X ⟨I.N + h.val + 1, by omega⟩)
    else if h2 : h.val < 2 * I.N then
      MvPolynomial.C (I.p : ℤ) * MvPolynomial.X ⟨h.val - I.N + 1, by omega⟩
    else
      MvPolynomial.C (I.p : ℤ) * MvPolynomial.X ⟨0, by omega⟩

/-- **The HNPHM sampling domain**: tuples `(t₁, …, t_N)` of nonzero residues.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 6.1, p.37 (PDF p.38):
"fix y∗ ∈ ℤ_p \ {0} and sample t∗₁, . . . , t∗_N independently and uniformly from ℤ_p \ {0}."

**Formalization Note.** Independent uniform sampling with replacement is the uniform distribution
on this product set; it is averaged with the published `IntQuotHNP.avg` and `IntQuotHNP.prob`. -/
def hnphmMults (p N : ℕ) : Finset (Fin N → Fin p) :=
  Finset.univ.filter fun t => ∀ i, (t i : ℕ) ≠ 0

/-- An approximation rule: the approximations and optional intervals as a function of the sampled
multipliers. -/
abbrev HNPHMRule (p N : ℕ) : Type :=
  (Fin N → Fin p) → (Fin (2 * N + 1) → ℕ) × Option (Fin (2 * N + 1) → ℕ × ℕ)

/-- The sampled input produced by an approximation rule on the multipliers `t`. -/
def hnphmSampled (p X N : ℕ) (rule : HNPHMRule p N) (t : Fin N → Fin p) : HNPHMInput where
  p := p
  X := X
  N := N
  v := (rule t).1
  iv := (rule t).2

/-- **An admissible approximation rule** for the secret `y` (sampling model of Definition 6.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 6.1, p.37 (PDF p.38):
"The approximations may be functions of all the samples, provided they satisfy (20) for this y∗
and these multipliers. Any supplied leading-bit intervals must also contain the corresponding
values."

For every sampled tuple `t`, the rule's approximations lie in `ℤ_p`, its intervals lie in `ℤ_p`,
and `(y, t)` is consistent with the resulting input. -/
def HNPHMIsRule (p X N y : ℕ) (rule : HNPHMRule p N) : Prop :=
  ∀ t ∈ hnphmMults p N, (∀ j, (rule t).1 j < p) ∧
    (∀ L, (rule t).2 = some L → ∀ j, (L j).2 < p) ∧
    HNPHMConsistent (hnphmSampled p X N rule t) y fun i => (t i : ℕ)

/-- **`Δ_N = X^{3N+1}/(p − 1)^N`** of Theorem 6.2 (p.37), as a real number. -/
noncomputable def hnphmDelta (N X p : ℕ) : ℝ :=
  (X : ℝ) ^ (3 * N + 1) / ((p : ℝ) - 1) ^ N

/-- **`σ_N = N/(3N + 1)`** of Theorem 6.2 (p.37). -/
noncomputable def sigmaN (N : ℕ) : ℝ :=
  (N : ℝ) / (3 * N + 1)

end Supplement

end IntQuotHNP


