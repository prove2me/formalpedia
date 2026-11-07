-- Prove2me | Definitions.Def_GuardedSSSP_Thresholds
-- name    : GuardedSSSP_Thresholds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:03.46802+00:00
-- url     : https://prove2.me/theorems/50d896af-f7d5-41ba-ad70-493f0acf2b56
-- title:
--   Thresholds $T_d$, the maximal legal generation $D_*(x)$, and $R$, $A_0$
-- statement:
--   Let $T_4$ be an integer base threshold. Define
--
--   $$T_{d+1}=2^{64(T_d+1)^2}\ (d\ge4),\qquad X_4=T_5,\qquad D_*(x)=\max\{d\ge4: T_{d+1}\le x\}\quad(x\ge X_4).$$
--
--   Further $R(y)=256(y+1)^2$ and $A_0=R(T_4)=256(T_4+1)^2$.
--
--   $D_*(x)$ is the generation the paper's solver selects on a core of measured size $x$; the thresholds guarantee that every lower call it makes is legal.
--
--   **Formalization Note** The base threshold is a parameter `T4`; Specification A.1 (p.22) fixes "a sufficiently large integer $T_4\ge16$", and the theorems are stated for every $T_4\ge16$. `Th T4 r` is $T_{4+r}$ and `Tpaper T4 d` is $T_d$ for $d\ge4$. $D_*(x)$ is an `sSup` over $\mathbb N$; the thresholds increase without bound, so for $x\ge X_4$ it is the maximum, and for $x<X_4$ its value $0$ is junk that no statement uses.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §3.2, displays (12)–(13), p.7 (PDF p.8); Lemma 8.2, p.18 (PDF p.19)

import Mathlib

namespace GuardedSSSP

/-!
# The thresholds `T_d`, the maximal legal generation `D*(x)`, and `R`, `A₀`

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), §3.2, displays (12)–(13), p.7 (PDF p.8); Lemma 8.2, p.18
(PDF p.19). "Let T₄ be the fixed base threshold in specification A.1. Define
T_{d+1} = 2^{64(T_d+1)²}, X_d = T_{d+1}. (12) For x ≥ X₄, define D∗(x) = max{d ≥ 4 : T_{d+1} ≤ x}. (13)
… Put A₀ = 256(T₄ + 1)²." Lemma 8.2: "Let R(y) = 256(y + 1)² and A₀ = R(T₄)."

**Formalization Note.**
* The base threshold `T₄` is a parameter `T4 : ℕ`; Specification A.1 (p.22) fixes "a sufficiently large
  integer T₄ ≥ 16", and the theorems of the mission are stated for every `T4 ≥ 16`.
* `Th T4 r` is `T_{4+r}`, so `Th T4 0 = T₄`. `Tpaper T4 d` is the paper's `T_d` for `d ≥ 4` (for `d < 4` it
  is `T₄`, a value no statement uses). `X4 T4 = T₅`.
* `Dstar T4 x` is the `sSup` over `ℕ` of `{d ≥ 4 | T_{d+1} ≤ x}`. The thresholds increase without bound, so
  for `x ≥ X₄` the set is finite and nonempty and this is the paper's maximum; for `x < X₄` the value `0` is
  a junk value, and every statement using `D*(x)` assumes `x ≥ X₄` or is eventual in `x`.
-/

/-- `Th T4 r = T_{4+r}`: `T₄ = T4` and `T_{d+1} = 2^{64(T_d+1)²}`, display (12). -/
def Th (T4 : ℕ) : ℕ → ℕ
  | 0 => T4
  | r + 1 => 2 ^ (64 * (Th T4 r + 1) ^ 2)

/-- The paper's threshold `T_d` for `d ≥ 4`. -/
def Tpaper (T4 d : ℕ) : ℕ := Th T4 (d - 4)

/-- `X₄ = T₅`, display (12). -/
def X4 (T4 : ℕ) : ℕ := Th T4 1

/-- The maximal legal generation `D*(x) = max{d ≥ 4 : T_{d+1} ≤ x}`, display (13). -/
noncomputable def Dstar (T4 : ℕ) (x : ℝ) : ℕ :=
  sSup {d : ℕ | 4 ≤ d ∧ ((Tpaper T4 (d + 1) : ℕ) : ℝ) ≤ x}

/-- `R(y) = 256(y + 1)²` (Lemma 8.2). -/
def R (y : ℝ) : ℝ := 256 * (y + 1) ^ 2

/-- `A₀ = 256(T₄ + 1)² = R(T₄)` (§3.2 and Lemma 8.2). -/
def A0 (T4 : ℕ) : ℝ := R T4

end GuardedSSSP


