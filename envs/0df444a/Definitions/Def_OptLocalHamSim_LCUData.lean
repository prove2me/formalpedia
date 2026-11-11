-- Prove2me | Definitions.Def_OptLocalHamSim_LCUData
-- name    : OptLocalHamSim_LCUData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:39.596237+00:00
-- url     : https://prove2.me/theorems/adbb1c6f-6e09-4fe3-8f55-6fd91b0d745a
-- title:
--   The LCU of §3: labels, $W_z$, $d(z)$, $\pi(z)$, $\tilde b_u$, $\gamma$, $f$, $\kappa$, $\chi_\lambda$, $z_{\lambda,\beta}$, $\zeta_u$, $\hat A_Q$; paths, $d_\Gamma$, $W_\Gamma$, $A_Q$
-- statement:
--   Fix a residual table $(c_\lambda,\omega_\lambda,P_\lambda)_{0\le\lambda<A}$, a step operator $C=C(h)$, an order $p$, $r$ microsteps, a degree threshold $Q\ge p+1$, a step $h$ and constants $c_*,\omega_*$. With
--
--   $$
--   K_0:=\lfloor Q/(p+1)\rfloor,\quad N:=r+K_0,\quad m:=\lceil\log_2(Q-p)\rceil,\quad B_0:=2^m,
--   $$
--
--   a label assignment is $z=(X_u,\lambda_u,J_u)_{u<N}$ with $X_u\in\{0,1\}$, $\lambda_u<A$, $J_u<B_0$. With $j_u:=\sum_{a<u}(1-X_a)$ and $e_u:=[j_u<r]$:
--
--   1. $G_u(z)$ is $P_{\lambda_u}$ if $e_uX_u=1$, $C$ if $e_u=1,X_u=0$, and $I$ if $e_u=0$; $W_z:=G_{N-1}(z)\cdots G_0(z)$;
--   2. $d(z):=\sum_{u:\,e_uX_u=1}(p+J_u+1)$;
--   3. $a:=1-2^{-1/r}$, $Z_0:=\sum_{J<B_0}2^{-J}$, $\pi(z):=\prod_u a^{X_u}(1-a)^{1-X_u}\frac1A\frac{2^{-J_u}}{Z_0}$;
--   4. $\tilde b_{-1}:=0$, $\tilde b_u:=(\tilde b_{u-1}+J_u+p+1)\bmod L_b$ if $X_u=1$ and $0$ otherwise, $L_b:=2^{\lceil\log_2(Q+1)\rceil}$;
--   5. $\gamma(b):=1/b$ for $1\le b\le Q$ and $1$ otherwise; $f(J):=p!/(p+J)!$; $t_\omega:=\omega_*h$;
--   6. $\kappa:=\frac{AZ_0c_*h\,t_\omega^p}{a\,p!}$, $\chi_\lambda:=\kappa\frac{-ic_\lambda}{c_*}\bigl(\frac{i\omega_\lambda}{\omega_*}\bigr)^p$, $z_{\lambda,\beta}:=(2i\omega_\lambda h)^{2^\beta}$;
--   7. $\zeta_u(z):=f(J_u)\gamma(\tilde b_u)\chi_{\lambda_u}\prod_{\beta<m}z_{\lambda_u,\beta}^{J_{u,\beta}}$ if $e_uX_u=1$ and $1$ otherwise, with $J_{u,\beta}$ the bits of $J_u$;
--   8. $\hat A_Q:=2\sum_z\pi(z)\bigl(\prod_u\zeta_u(z)\bigr)W_z$.
--
--   A **path** $\Gamma$ lists, for each microstep $j$, insertions $(\lambda_{j,i},q_{j,i})$ with $q_{j,i}\ge p$; $b_{j,i}:=\sum_{a\le i}(q_{j,a}+1)$, $|\Gamma|:=\sum_{j,i}(q_{j,i}+1)$,
--
--   $$
--   d_\Gamma:=\prod_{j,i}\frac{-ic_{\lambda_{j,i}}(i\omega_{\lambda_{j,i}})^{q_{j,i}}h^{q_{j,i}+1}}{q_{j,i}!\,b_{j,i}},\qquad W_\Gamma:=[C\,P_{\lambda_{r,m_r}}\cdots P_{\lambda_{r,1}}]\cdots[C\,P_{\lambda_{1,m_1}}\cdots P_{\lambda_{1,1}}],
--   $$
--
--   and $A_Q:=\sum_{|\Gamma|\le Q}d_\Gamma W_\Gamma$. Finally $A(\xi):=\frac{c_*Ah\,t_\omega^p\xi^{p+1}}{p!(1-t_\omega\xi)}$. The module also defines the generator $K(s)=\sum_\lambda c_\lambda e^{i\omega_\lambda s}P_\lambda$ of a table, the predicate that $E$ solves $E'=-iKE$, $E(0)=I$ with $K$ of the form (26), and the terms of the Dyson expansion (34).
--
--   These objects define the finite LCU whose low-degree part matches the exact path expansion (Lemma 9) and whose error Lemma 10 bounds.
--
--   **Formalization Note** $P_\lambda$ and $C$ are arbitrary matrices; statements add their own hypotheses. Paths are encoded with insertion counts and degrees at most $Q$, which loses no path with $|\Gamma|\le Q$.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §3.2–§3.4, eqs. (25)–(26), (34)–(38), (40)–(54), (56), pp.16–22

import Mathlib

namespace OptLocalHamSim

/-- The generator of a residual table, eq. (25), p.16 (Shen, Wu, Yao, Yuan, Zhang, STOC 2027
submission, held version, sha256 44a9768a…): `K(s) := ∑_{λ=0}^{A−1} c_λ e^{iω_λ s} P_λ`. -/
noncomputable def tableGen {n : Type} {A : ℕ} (c : Fin A → ℂ) (ω : Fin A → ℝ)
    (P : Fin A → Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  ∑ l, (c l * Complex.exp (Complex.I * (ω l : ℂ) * (s : ℂ))) • P l

/-- `E` is the **residual evolution** of the table `(c, ω, P)` of order `p` (eqs. (25)–(26), p.16):
`E′(s) = −iK(s)E(s)` for all `s`, `E(0) = I`, and the generator has the expansion (26)
`K(s) = ∑_λ ∑_{q ≥ p} c_λ (iω_λ)^q/q! s^q P_λ` (its Taylor coefficients of order `< p` vanish). -/
def SolvesResidual {n : Type} [Fintype n] [DecidableEq n] {A : ℕ} (c : Fin A → ℂ) (ω : Fin A → ℝ)
    (P : Fin A → Matrix n n ℂ) (p : ℕ) (E : ℝ → Matrix n n ℂ) : Prop :=
  E 0 = 1 ∧
  (∀ s : ℝ, HasDerivAt E (-(Complex.I • (tableGen c ω P s * E s))) s) ∧
  (∀ s : ℝ, HasSum (fun j : ℕ => ∑ l, (c l * (Complex.I * (ω l : ℂ)) ^ (j + p) /
      ((j + p).factorial : ℂ) * (s : ℂ) ^ (j + p)) • P l) (tableGen c ω P s))

/-- The term of the Dyson expansion (34), p.17, indexed by `k` and the insertion data
`(λ_i, q_i)_{i<k}` with `q_i = p + J_i ≥ p`:
`(∏_{i} −i c_{λ_i}(iω_{λ_i})^{q_i} h^{q_i+1} / (q_i! b_i)) P_{λ_k} ⋯ P_{λ_1}`, with
`b_i := ∑_{a ≤ i} (q_a + 1)`. -/
noncomputable def dysonTerm {n : Type} [Fintype n] [DecidableEq n] {A : ℕ} (c : Fin A → ℂ)
    (ω : Fin A → ℝ) (P : Fin A → Matrix n n ℂ) (p : ℕ) (h : ℝ)
    (x : Σ k : ℕ, (Fin k → Fin A) × (Fin k → ℕ)) : Matrix n n ℂ :=
  (∏ i, (-Complex.I * c (x.2.1 i) * (Complex.I * (ω (x.2.1 i) : ℂ)) ^ (p + x.2.2 i) *
      (h : ℂ) ^ (p + x.2.2 i + 1)) /
    (((p + x.2.2 i).factorial : ℂ) *
      ((∑ a ∈ Finset.univ.filter (fun a => a ≤ i), (p + x.2.2 a + 1) : ℕ) : ℂ))) •
  (List.ofFn fun i => P (x.2.1 i)).reverse.prod

/-- The data of the LCU of §3.2–§3.3 (Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm
for Geometrically Local Hamiltonian Simulation*, STOC 2027 submission, held version, sha256 44a9768a…,
pp.17–20): a residual table `(c_λ, ω_λ, P_λ)_{0 ≤ λ < A}` (Lemma 7, p.16), the product-formula step
`C = C(h)`, the order `p`, the number `r` of microsteps, the degree threshold `Q`, the step `h = τ/r`,
and the model constants `c∗, ω∗` with `|c_λ| ≤ c∗`, `|ω_λ| ≤ ω∗`.

**Formalization Note** The table entries `P_λ` and the step `C` are arbitrary matrices on a finite
index type `n`; the statements that use this structure state their own hypotheses on them. -/
structure LCUData (n : Type) where
  /-- The number `A` of table entries. -/
  A : ℕ
  /-- The coefficients `c_λ ∈ ℂ`. -/
  c : Fin A → ℂ
  /-- The real frequencies `ω_λ`. -/
  ω : Fin A → ℝ
  /-- The Pauli strings `P_λ`. -/
  P : Fin A → Matrix n n ℂ
  /-- The product-formula step `C(h)`. -/
  C : Matrix n n ℂ
  /-- The order `p` of the product formula. -/
  p : ℕ
  /-- The number `r` of microsteps. -/
  r : ℕ
  /-- The degree threshold `Q`. -/
  Q : ℕ
  /-- The microstep length `h`. -/
  h : ℝ
  /-- The coefficient bound `c∗`. -/
  cs : ℝ
  /-- The frequency bound `ω∗`. -/
  ωs : ℝ

namespace LCUData

variable {n : Type} [Fintype n] [DecidableEq n] (d : LCUData n)

/-- `K₀ := ⌊Q/(p+1)⌋`, eq. (40), p.18. -/
def K0 : ℕ := d.Q / (d.p + 1)
/-- `N := r + K₀`, the number of slots, eq. (40). -/
def N : ℕ := d.r + d.K0
/-- `m := ⌈log₂(Q − p)⌉`, eq. (40) (`m = 0` when `Q = p + 1`). -/
def m : ℕ := Nat.clog 2 (d.Q - d.p)
/-- `B₀ := 2^m`, eq. (40). -/
def B0 : ℕ := 2 ^ d.m

/-- A complete label assignment `z = (X_u, λ_u, J_u)_{u=0}^{N−1}` (p.18): `X_u ∈ {0,1}` (`true` = 1, an
insertion), the address `λ_u ∈ {0,…,A−1}` and the offset `J_u ∈ {0,…,B₀−1}`. -/
abbrev Label : Type := Fin d.N → Bool × Fin d.A × Fin d.B0

/-- `j_u := ∑_{a<u} (1 − X_a)`, the number of formula steps before slot `u`, eq. (41). -/
def fsteps (z : d.Label) (u : Fin d.N) : ℕ :=
  (Finset.univ.filter fun a : Fin d.N => a < u ∧ (z a).1 = false).card

/-- `e_u = 1`, i.e. slot `u` is active: `j_u < r`, eq. (41). -/
def IsActive (z : d.Label) (u : Fin d.N) : Prop := d.fsteps z u < d.r

instance (z : d.Label) (u : Fin d.N) : Decidable (d.IsActive z u) :=
  inferInstanceAs (Decidable (_ < _))

/-- `G_u(z)`, eq. (42): `P_{λ_u}` if `e_u X_u = 1`, `C(h)` if `e_u = 1, X_u = 0`, and `I` if `e_u = 0`. -/
def G (z : d.Label) (u : Fin d.N) : Matrix n n ℂ :=
  if d.IsActive z u then (if (z u).1 then d.P (z u).2.1 else d.C) else 1

/-- `W_z := G_{N−1}(z) ⋯ G_0(z)`, eq. (42). -/
def Wz (z : d.Label) : Matrix n n ℂ := (List.ofFn (d.G z)).reverse.prod

/-- The insertion degree `d(z) := ∑_{u : e_u X_u = 1} (p + J_u + 1)`, eq. (43), p.19. -/
def deg (z : d.Label) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => d.IsActive z u ∧ (z u).1 = true), (d.p + (z u).2.2 + 1)

/-- `a := 1 − 2^{−1/r}`, eq. (45). -/
noncomputable def a : ℝ := 1 - (2 : ℝ) ^ (-(1 / (d.r : ℝ)))

/-- `Z₀ := ∑_{J=0}^{B₀−1} 2^{−J}`, eq. (45). -/
noncomputable def Z0 : ℝ := ∑ J : Fin d.B0, (1 / 2 : ℝ) ^ (J : ℕ)

/-- `π(z) := ∏_u a^{X_u}(1−a)^{1−X_u} (1/A) 2^{−J_u}/Z₀`, eq. (46). -/
noncomputable def prob (z : d.Label) : ℝ :=
  ∏ u, (if (z u).1 then d.a else 1 - d.a) * (1 / (d.A : ℝ)) * ((1 / 2 : ℝ) ^ ((z u).2.2 : ℕ) / d.Z0)

/-- `L_b := 2^{⌈log₂(Q+1)⌉}`, p.19. -/
def Lb : ℕ := 2 ^ Nat.clog 2 (d.Q + 1)

/-- The recurrence (48): `btilAux z (u+1) = b̃_u`, with `b̃_{−1} := 0` and
`b̃_u := (b̃_{u−1} + J_u + p + 1) mod L_b` if `X_u = 1`, `0` if `X_u = 0`. -/
def btilAux (z : d.Label) : ℕ → ℕ
  | 0 => 0
  | u + 1 =>
    if hu : u < d.N then
      (if (z ⟨u, hu⟩).1 then (btilAux z u + ((z ⟨u, hu⟩).2.2 : ℕ) + d.p + 1) % d.Lb else 0)
    else 0

/-- The cumulative denominator `b̃_u` modulo `L_b`, eq. (48). -/
def btil (z : d.Label) (u : Fin d.N) : ℕ := d.btilAux z (u + 1)

/-- `γ(b) := 1/b` for `1 ≤ b ≤ Q`, `1` otherwise, eq. (49). -/
noncomputable def gam (b : ℕ) : ℝ := if 1 ≤ b ∧ b ≤ d.Q then 1 / (b : ℝ) else 1

/-- `f(J) := p!/(p+J)!`, eq. (50). -/
noncomputable def fJ (J : ℕ) : ℝ := (d.p.factorial : ℝ) / ((d.p + J).factorial : ℝ)

/-- `t_ω := ω∗ h`, p.20. -/
noncomputable def tω : ℝ := d.ωs * d.h

/-- `κ := A Z₀ c∗ h t_ω^p / (a p!)`, eq. (51). -/
noncomputable def κ : ℝ := d.A * d.Z0 * d.cs * d.h * d.tω ^ d.p / (d.a * d.p.factorial)

/-- `χ_λ := κ (−i c_λ/c∗) (iω_λ/ω∗)^p`, eq. (51). -/
noncomputable def χ (l : Fin d.A) : ℂ :=
  (d.κ : ℂ) * (-Complex.I * d.c l / d.cs) * (Complex.I * d.ω l / d.ωs) ^ d.p

/-- `z_{λ,β} := (2iω_λ h)^{2^β}`, eq. (51). -/
noncomputable def zfac (l : Fin d.A) (β : ℕ) : ℂ := (2 * Complex.I * d.ω l * d.h) ^ (2 ^ β)

/-- The slot coefficient `ζ_u(z)`, eq. (52): `f(J_u) γ(b̃_u) χ_{λ_u} ∏_{β<m} z_{λ_u,β}^{J_{u,β}}` if
`e_u X_u = 1` and `1` otherwise; `J_{u,β}` is bit `β` of `J_u`. -/
noncomputable def ζ (z : d.Label) (u : Fin d.N) : ℂ :=
  if d.IsActive z u ∧ (z u).1 = true then
    (d.fJ (z u).2.2 : ℂ) * (d.gam (d.btil z u) : ℂ) * d.χ (z u).2.1 *
      ∏ β : Fin d.m, (if ((z u).2.2 : ℕ).testBit β then d.zfac (z u).2.1 β else 1)
  else 1

/-- **The finite LCU operator** `Â_Q := 2 ∑_z π(z) (∏_u ζ_u(z)) W_z`, eq. (53), p.20. -/
noncomputable def AhatQ : Matrix n n ℂ :=
  ∑ z : d.Label, ((2 * d.prob z : ℝ) * ∏ u, d.ζ z u) • d.Wz z

/-- A path `Γ` of bounded size (§3.2, p.17): for each microstep `j ∈ {1,…,r}` a number `m_j` of
insertions and, for each insertion `i`, its address `λ_{j,i}` and degree `q_{j,i}`.

**Formalization Note** The counts and degrees are bounded by `Q` (`Fin (Q+1)`), which loses no path
with `|Γ| ≤ Q`: such a path has every `q_{j,i} + 1 ≤ Q` and every `m_j ≤ Q`. Each such path has exactly
one representative. -/
abbrev Path : Type := Fin d.r → Σ k : Fin (d.Q + 1), (Fin k → Fin d.A × Fin (d.Q + 1))

/-- A path is admissible if every degree satisfies `q_{j,i} ≥ p`. -/
def PathValid (Γ : d.Path) : Prop := ∀ j (i : Fin (Γ j).1), d.p ≤ (((Γ j).2 i).2 : ℕ)

instance (Γ : d.Path) : Decidable (d.PathValid Γ) := by unfold PathValid; infer_instance

/-- `|Γ| := ∑_j ∑_i (q_{j,i} + 1)`, eq. (36). -/
def pdeg (Γ : d.Path) : ℕ := ∑ j, ∑ i : Fin (Γ j).1, ((((Γ j).2 i).2 : ℕ) + 1)

/-- `b_{j,i} := ∑_{a ≤ i} (q_{j,a} + 1)`, eq. (35). -/
def bpath (Γ : d.Path) (j : Fin d.r) (i : Fin (Γ j).1) : ℕ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (Γ j).1 => a ≤ i), ((((Γ j).2 a).2 : ℕ) + 1)

/-- The path coefficient `d_Γ := ∏_j ∏_i −i c_λ (iω_λ)^q h^{q+1} / (q! b_{j,i})`, eq. (37). -/
noncomputable def dpath (Γ : d.Path) : ℂ :=
  ∏ j, ∏ i : Fin (Γ j).1,
    (-Complex.I * d.c ((Γ j).2 i).1 * (Complex.I * d.ω ((Γ j).2 i).1) ^ (((Γ j).2 i).2 : ℕ) *
        (d.h : ℂ) ^ ((((Γ j).2 i).2 : ℕ) + 1)) /
      (((((Γ j).2 i).2 : ℕ).factorial : ℂ) * (d.bpath Γ j i : ℂ))

/-- `W_Γ := [C(h) P_{λ_{r,m_r}} ⋯ P_{λ_{r,1}}] ⋯ [C(h) P_{λ_{1,m_1}} ⋯ P_{λ_{1,1}}]`, eq. (38). -/
def Wpath (Γ : d.Path) : Matrix n n ℂ :=
  (List.ofFn fun j : Fin d.r =>
    d.C * (List.ofFn fun i : Fin (Γ j).1 => d.P ((Γ j).2 i).1).reverse.prod).reverse.prod

/-- **The truncated path expansion** `A_Q := ∑_{|Γ| ≤ Q} d_Γ W_Γ`, eq. (54), p.21. -/
noncomputable def AQ : Matrix n n ℂ :=
  ∑ Γ ∈ Finset.univ.filter (fun Γ : d.Path => d.PathValid Γ ∧ d.pdeg Γ ≤ d.Q), d.dpath Γ • d.Wpath Γ

/-- The weight `A(ξ) := c∗ A h t_ω^p ξ^{p+1} / (p! (1 − t_ω ξ))`, eq. (56), p.22. -/
noncomputable def Aξ (ξ : ℝ) : ℝ :=
  d.cs * d.A * d.h * d.tω ^ d.p * ξ ^ (d.p + 1) / (d.p.factorial * (1 - d.tω * ξ))

end LCUData

end OptLocalHamSim


